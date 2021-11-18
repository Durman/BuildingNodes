import bisect
import inspect
import random
import sys
import traceback
from abc import ABC, abstractmethod
from collections import namedtuple, defaultdict, deque
from enum import Enum, auto
from graphlib import TopologicalSorter
from itertools import count, chain, cycle, repeat, accumulate
from math import isclose, inf
from typing import Optional, Iterable, NamedTuple, Type, get_type_hints, Literal, Any, Union, overload, Generic, TypeVar

import bmesh
import bpy
import numpy as np
from bmesh.types import BMEdge, BMFace, BMLoop, BMVert, BMesh
from bpy.app.handlers import persistent
from bpy.props import StringProperty, BoolProperty, EnumProperty
from bpy.types import NodeTree, Node, NodeSocket, Panel, Operator, PropertyGroup, Menu
import nodeitems_utils
from mathutils import Vector
from nodeitems_utils import NodeCategory, NodeItem


FACE_STYLE_LAYER_NAME = "BnStyleName"  # should be unchanged between versions


class FacadeTreeNames(PropertyGroup):
    identifier: bpy.props.StringProperty()
    user_name: bpy.props.StringProperty()


class BuildingStyleTree(NodeTree):
    bl_idname = 'bn_BuildingStyleTree'
    bl_label = "Building Style Editor"
    bl_icon = 'HOME'
    was_changes = False  # flag to timer

    inst_col: bpy.props.PointerProperty(type=bpy.types.Collection, description="Keep all panels to be instanced")
    was_changed: bpy.props.BoolProperty(description="If True the tree should be reevaluated")
    facade_names: bpy.props.CollectionProperty(type=FacadeTreeNames)

    def update(self):
        BuildingStyleTree.was_changes = True
        self.was_changed = True

    def apply(self, obj):
        obj_props: ObjectProperties = obj.building_props
        gn_tree = obj_props.get_gn_tree()

        # set position and attributes
        if obj_props.points is None:
            obj_props.points = bpy.data.objects.new('Points', bpy.data.meshes.new('Points'))
        if obj.mode == 'EDIT':
            bm = bmesh.from_edit_mesh(obj.data)
        else:
            bm = bmesh.new()
            bm.from_mesh(obj.data)
        bm.faces.ensure_lookup_table()
        obj_fac_names = [names.obj_facade_name for names in obj_props.facade_names_mapping]
        points_bm = self.get_points(bm, obj_fac_names)
        points_bm.to_mesh(obj_props.points.data)
        points_bm.free()
        if obj.mode != 'EDIT':
            bm.to_mesh(obj.data)  # assign new attributes
            bm.free()
        gn_tree.set_points(obj_props.points)

        # set instances
        gn_tree.set_instances(self.inst_col)

    def get_points(self, base_bm, obj_facade_names):
        self.store_instances()
        sock_data = dict()
        for node, prev_socks in self.walk():
            in_data = dict()
            for from_sock, to_sock in zip(prev_socks, node.inputs):
                if from_sock is not None:
                    in_data[to_sock.identifier] = sock_data[from_sock]
                elif hasattr(to_sock, 'value'):
                    def sock_value(build, *, _value=to_sock.value):
                        return _value
                    in_data[to_sock.identifier] = sock_value
                else:
                    in_data[to_sock.identifier] = None

            is_last_node = node.bl_idname == BuildingStyleNode.bl_idname
            # collect properties
            if is_last_node:
                props = base_bm
            elif node.props_template:
                props = node.props_template
            elif hasattr(node, 'Props'):
                props = node.Props(*[getattr(node, n) for n in node.Props._fields])
            else:
                props = None

            # find inputs mapping
            if node.input_template:  # this says that sockets have appropriate identifiers
                input_data = node.Inputs(*[in_data[key] for key in node.Inputs._fields])  # key words
            else:  # positional
                input_data = (Inp := node.gen_input_mapping()) and Inp(*in_data.values())

            res = node.execute(input_data, props)
            if is_last_node:
                return res
            if not isinstance(res, tuple):
                res = (res, )
            for data, out_sok in zip(res, node.outputs):
                sock_data[out_sok] = data

    def _get_points(self, base_bm: bmesh.types.BMesh):
        bm = bmesh.new()
        norm_lay = bm.verts.layers.float_vector.new("Normal")
        scale_lay = bm.verts.layers.float_vector.new("Scale")
        ind_lay = bm.verts.layers.int.new("Wall index")
        wall_lay = base_bm.faces.layers.int.get("Is wall")
        if wall_lay is None:
            wall_lay = base_bm.faces.layers.int.new("Is wall")
        panel_size = Vector((2, 2))
        panel_num = len(self.inst_col.all_objects)
        for fi, face in enumerate(base_bm.faces):
            random.seed(fi)
            if isclose(face.normal.dot(Vector((0, 0, 1))), 0, abs_tol=0.1):
                min_v = Vector((min(v.co.x for v in face.verts), min(v.co.y for v in face.verts),
                                min(v.co.z for v in face.verts)))
                max_v = Vector((max(v.co.x for v in face.verts), max(v.co.y for v in face.verts),
                                max(v.co.z for v in face.verts)))
                xy_dir = (max_v - min_v) * Vector((1, 1, 0))
                xy_len = xy_dir.length
                xy_num = max(int(xy_len / panel_size.x), 1)
                xy_scale = xy_len / (xy_num * panel_size.x)
                xy_step = xy_dir.normalized() * (xy_scale * panel_size.x)
                z_dir = (max_v - min_v) * Vector((0, 0, 1))
                z_len = z_dir.length
                z_num = max(int(z_len / panel_size.y), 1)
                z_scale = z_len / (z_num * panel_size.y)
                z_step = z_dir.normalized() * (z_scale * panel_size.y)
                for zi in range(0, z_num):
                    vec = bm.verts.new(min_v + xy_step * 0.5 + z_step * 0.5 + z_step * zi)
                    vec[norm_lay] = face.normal
                    vec[scale_lay] = (xy_scale, z_scale, 1)
                    vec[ind_lay] = random.randrange(panel_num)
                    for xyi in range(1, xy_num):
                        v = bm.verts.new(vec.co + xy_step * xyi)
                        v[norm_lay] = face.normal
                        v[scale_lay] = (xy_scale, z_scale, 1)
                        v[ind_lay] = random.randrange(panel_num)
                face[wall_lay] = 1
            else:
                face[wall_lay] = 0
        return bm

    def store_instances(self) -> bpy.types.Collection:
        if self.inst_col is None:
            self.inst_col = bpy.data.collections.new('Panel instances')

        for obj in self.inst_col.all_objects:
            self.inst_col.objects.unlink(obj)
        for node in self.nodes:
            if node.bl_idname == PanelNode.bl_idname:
                sock = node.get_socket('object', is_input=True)
                if sock.value is not None:
                    try:
                        self.inst_col.objects.link(sock.value)
                    except RuntimeError:
                        pass  # Already was linked

        # let panels know their indexes
        obj_index = {obj: i for i, obj in enumerate(sorted(self.inst_col.objects, key=lambda o: o.name))}
        for node in self.nodes:
            if node.bl_idname == PanelNode.bl_idname and node.inputs[0].value:
                node.panel_index = obj_index[node.inputs[0].value]

        return self.inst_col

    def walk(self):  # todo support reroutes
        node_graph = defaultdict(set)
        prev_sock = dict()
        for link in (l for l in self.links if not l.is_muted):
            node_graph[link.to_node].add(link.from_node)
            prev_sock[link.to_socket] = link.from_socket
        for node in TopologicalSorter(node_graph).static_order():
            yield node, [prev_sock[s] if s in prev_sock else None for s in node.inputs]

    def walk_back(self, from_node: Node) -> Iterable[Node]:
        nodes = {l.to_socket: l.from_node for l in self.links}
        prev_nodes = [from_node]
        visited = set()
        while prev_nodes:
            if (node := prev_nodes.pop()) in visited:
                continue
            yield node
            visited.add(node)
            prev_nodes.extend(prev_node for s in node.inputs if (prev_node := nodes.get(s)) is not None)

    def update_facade_names(self):
        # todo make interface of all output nodes equal
        for node in self.nodes:
            if node.bl_idname == BuildingStyleNode.bl_idname:
                self.facade_names.clear()
                for socket in node.inputs[1:]:
                    sock_names: FacadeTreeNames = self.facade_names.add()
                    sock_names.identifier = socket.identifier
                    sock_names.user_name = socket.user_name or socket.default_name

    def update_sockets(self):
        """ Supports (only for nodes with template attributes):
        - adding sockets from a template which identifier was not found in a sockets collection
        - marking sockets as deprecated which identifiers are not found in a template
        """
        for node in self.nodes:
            if node.input_template:
                socks = {s.identifier: s for s in node.inputs}
                for pos, (key, template) in enumerate(zip(node.input_template._fields, node.input_template)):
                    if key not in socks:
                        template.init(node, is_input=True, identifier=key)
                        node.inputs.move(len(node.inputs) - 1, pos)
                for key, sock in socks.items():
                    sock.is_deprecated = not hasattr(node.input_template, key)
            if node.output_template:
                socks = {s.identifier: s for s in node.outputs}
                for pos, (key, template) in enumerate(zip(node.output_template._fields, node.output_template)):
                    if key not in socks:
                        template.init(node, is_input=False, identifier=key)
                        node.outputs.move(len(node.outputs) - 1, pos)
                for key, sock in socks.items():
                    sock.is_deprecated = not hasattr(node.output_template, key)

    def show_in_areas(self, is_to_show):
        for area in bpy.context.screen.areas:
            if area.ui_type == BuildingStyleTree.bl_idname:
                area.spaces[0].node_tree = self if is_to_show else None


class BaseSocket:
    show_text = True

    def update_is_to_show(self, context):
        self.enabled = self.is_to_show
        self.update_value(context)

    user_name: bpy.props.StringProperty(description="Socket name given by user")  # todo tag redraw
    is_deprecated: bpy.props.BoolProperty(description="In case the socket is not used by a node any more")
    is_to_show: bpy.props.BoolProperty(
        default=True, description="To display the socket in node interface", update=update_is_to_show)

    def update_value(self, context):
        self.id_data.update()  # https://developer.blender.org/T92635

    def draw(self, context, layout, node, text):
        if self.is_deprecated:
            row = layout.row()
            row.alert = True
            value = self.value if hasattr(self, 'value') else ''
            value_name = value.name if hasattr(value, 'name') else value
            row.label(text=f'{value_name or self.user_name or text or self.default_name} (deprecated)')
            row.operator(EditSocketsOperator.bl_idname, text='', icon='REMOVE').operation = 'delete'

        elif hasattr(self, 'value') and not self.is_output and not self.is_linked:
            col = layout.column()
            col.prop(self, 'value', text=(self.user_name or text or self.default_name) if self.show_text else '')

        elif self.node.bl_idname == PanelNode.bl_idname:
            row = layout.row(align=True)
            row.alignment = 'RIGHT'
            row.prop(self.node.get_socket('object', is_input=True), 'value', text='')
            row.operator(self.node.settings_viewer.bl_idname, text='', icon='PREFERENCES')

        elif self.is_output and self.node.settings_viewer and self.index == 0:
            row = layout.row()
            row.alignment = 'RIGHT'
            row.operator(self.node.settings_viewer.bl_idname, text='Settings', icon='PREFERENCES')
            row.label(text=self.user_name or text or self.default_name)

        else:
            layout.label(text=self.user_name or text or self.default_name)

    def draw_color(self, context, node):
        return self.color

    @property
    def index(self):
        sockets = self.node.outputs if self.is_output else self.node.inputs
        for ind, sock in enumerate(sockets):
            if sock.identifier == self.identifier:
                return ind
        raise LookupError


class FacadeSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_FacadeSocket'
    bl_label = "Facade Socket"
    color = 0.65, 0.25, 0.8, 1.0
    default_name = 'Facade'

    def draw(self, context, layout, node, text):
        super().draw(context, layout, node, text)
        if hasattr(node, 'edit_sockets') and node.edit_sockets:
            if self.identifier == node.inputs[0].identifier:
                layout.operator(EditSocketsOperator.bl_idname, text='', icon='ADD').operation = 'add'
            else:
                layout.operator(EditSocketsOperator.bl_idname, text='', icon='GREASEPENCIL').operation = 'rename'
                layout.operator(EditSocketsOperator.bl_idname, text='', icon='TRIA_UP').operation = 'move_up'
                layout.operator(EditSocketsOperator.bl_idname, text='', icon='TRIA_DOWN').operation = 'move_down'
                layout.operator(EditSocketsOperator.bl_idname, text='', icon='ADD').operation = 'add'
                layout.operator(EditSocketsOperator.bl_idname, text='', icon='REMOVE').operation = 'delete'


class FloorSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_FloorSocket'
    bl_label = "Floor Socket"
    color = 0.35, 0.35, 1.0, 1.0
    default_name = 'Floor'


class PanelSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_PanelSocket'
    bl_label = "Panel Socket"
    color = 0.0, 0.8, 0.8, 1.0
    default_name = 'Panel'


class FloatSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_FloatSocket'
    bl_label = "Float Socket"
    color = 0.5, 0.5, 0.5, 1.0
    default_name = 'Float'
    value: bpy.props.FloatProperty(update=BaseSocket.update_value)


class ObjectSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_ObjectSocket'
    bl_label = "Object Socket"
    default_name = 'Object'
    color = 1.0, 0.6, 0.45, 1.0
    show_text = False

    def poll_objects(self, obj):
        if obj.type != 'MESH':
            return False
        props: ObjectProperties = obj.building_props
        if props.building_style == self.id_data:  # object can't be instanced inside itself
            return False
        scl_attr, wal_attr = obj.data.attributes.get('Scale'), obj.data.attributes.get('Wall index')
        if obj.name.split('.')[0] == 'Points' and scl_attr and wal_attr:  # most likely it's helper object
            return False
        return True

    value: bpy.props.PointerProperty(type=bpy.types.Object, update=BaseSocket.update_value, poll=poll_objects)


class IntSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_IntSocket'
    bl_label = "Int Socket"
    color = 0.0, 0.6, 0.0, 1.0
    default_name = 'Integer'
    value: bpy.props.IntProperty(update=BaseSocket.update_value)


class StringSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_StringSocket'
    bl_label = "String Socket"
    color = 0.4, 0.6, 0.8, 1.0
    default_name = 'String'
    value: bpy.props.StringProperty(update=BaseSocket.update_value)


class BoolSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_BoolSocket'
    bl_label = "Bool Socket"
    default_name = 'Bool'
    color = 0.75, 0.55, 0.75, 1.0
    value: bpy.props.BoolProperty(update=BaseSocket.update_value)


class VectorSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_VectorSocket'
    bl_label = "Vector Socket"
    default_name = 'Vector'
    color = 0.4, 0.3, 0.7, 1.0
    value: bpy.props.FloatVectorProperty(update=BaseSocket.update_value)


class Vector4Socket(BaseSocket, NodeSocket):
    bl_idname = 'bn_Vector4Socket'
    bl_label = "Vector 4 Socket"
    default_name = 'Vector4'
    color = 0.4, 0.3, 0.7, 1.0
    value: bpy.props.FloatVectorProperty(update=BaseSocket.update_value, size=4)


class Categories(Enum):
    BUILDING = auto()
    FACADE = auto()
    FLOOR = auto()
    PANEL = auto()
    UTILS = auto()

    @property
    def color(self):
        colors = {
            Categories.PANEL: (0.3, 0.45, 0.5),
            Categories.FLOOR: (0.25, 0.25, 0.4),
            Categories.FACADE: (0.4, 0.25, 0.4),
            Categories.BUILDING: (0.3, 0.15, 0.15),
        }
        return colors.get(self)


class ShowSocketsMenu(Menu):
    bl_idname = "OBJECT_MT_show_sockets"
    bl_label = "Show/hide sockets"

    def draw(self, context):
        for sock in context.node.inputs:
            if sock.is_linked:
                col = self.layout.column()
                col.active = False
                col.prop(sock, 'is_to_show', text=(sock.name or sock.default_name) + ' (connected)', emboss=False)
            else:
                col = self.layout.column()
                col.prop(sock, 'is_to_show', text=sock.name or sock.default_name)


class SocketTemplate(NamedTuple):
    type: NodeSocket
    name: str = ''
    enabled: bool = True
    display_shape: Literal['CIRCLE', 'SQUARE', 'DIAMOND', 'CIRCLE_DOT', 'SQUARE_DOT', 'DIAMOND_DOT'] = None
    default_value: Any = None

    def init(self, node: Node, is_input, identifier=None):
        node_sockets = node.inputs if is_input else node.outputs
        sock = node_sockets.new(self.type.bl_idname, self.name, identifier=identifier or '')
        if not self.enabled:
            sock.is_to_show = False
        if self.display_shape:
            sock.display_shape = self.display_shape
        if self.default_value is not None:
            sock.value = self.default_value


class NodeSettingsOperator:
    bl_label = "Edit the node options"
    bl_options = {'INTERNAL', }

    # internal usage
    tree_name: StringProperty()
    node_name: StringProperty()

    def execute(self, context):  # without this method the Operator is considered as disabled :/
        return {'FINISHED'}

    @property
    def node(self):
        tree = bpy.data.node_groups[self.tree_name]
        node = tree.nodes[self.node_name]  # todo https://developer.blender.org/T92835
        return node

    @node.setter
    def node(self, node):
        self.tree_name = node.id_data.name
        self.node_name = node.name

    def invoke(self, context, event):
        node = context.node
        self.node = node
        wm = context.window_manager
        return wm.invoke_props_dialog(self)

    @staticmethod
    def draw_settings(layout, node):  # should be used by the operator and the node side panel
        NodeSettingsOperator.draw_sockets(layout, node)

    def draw(self, context):
        self.draw_settings(self.layout, self.node)

    @staticmethod
    def draw_sockets(layout, node):
        for sock in node.inputs:
            if sock.is_linked:
                col = layout.column()
                col.active = False
                col.prop(sock, 'is_to_show', text=(sock.name or sock.default_name) + ' (connected)', emboss=False)
            else:
                col = layout.column()
                if hasattr(sock, 'value'):
                    row = col.row()
                    row.prop(sock, 'value', text=sock.user_name or sock.name or sock.default_name)
                    row.prop(sock, 'is_to_show', text='')
                else:
                    col.prop(sock, 'is_to_show', text=sock.name or sock.default_name)


class BaseNode:
    category: Categories = None
    repeat_last_socket = False
    repeat_first_socket = False
    input_template: tuple[SocketTemplate] = []  # only for static sockets, cause it is used for checking sockets API
    output_template: tuple[SocketTemplate] = []  # only for static sockets, cause it is used for checking sockets API
    props_template: tuple = []
    settings_viewer = None

    @classmethod
    def poll(cls, tree):
        return tree.bl_idname == BuildingStyleTree.bl_idname

    def init(self, context):
        # update node colors
        if self.category is not None:
            self.use_custom_color = True
            self.color = self.category.color
        # create sockets
        for key, s_template in zip(self.input_template and self.input_template._fields, self.input_template):
            s_template.init(self, is_input=True, identifier=key)
        for key, s_template in zip(self.output_template and self.output_template._fields, self.output_template):
            s_template.init(self, is_input=False, identifier=key)

        self.node_init()

    def node_init(self):
        pass

    def draw_buttons_ext(self, context, layout):
        if self.settings_viewer:
            self.settings_viewer.draw_settings(layout, self)

    def update(self):
        # update sockets
        links = {l.to_socket: l for l in self.id_data.links}
        if self.repeat_last_socket:
            sock_id_name = self.inputs[-1].bl_idname
            if self.inputs[-1].is_linked:
                self.inputs.new(sock_id_name, "")
            for socket in list(self.inputs)[-2::-1]:
                if socket.bl_idname == self.inputs[-1].bl_idname and socket not in links:
                    self.inputs.remove(socket)
        if self.repeat_first_socket:
            sock_id_name = self.inputs[0].bl_idname
            if self.inputs[0].is_linked:
                s = self.inputs.new(sock_id_name, "")
                self.inputs.move(len(self.inputs) - 1, 0)
            for socket in list(self.inputs)[:0:-1]:
                if socket.bl_idname == self.inputs[0].bl_idname and not socket.is_linked:
                    self.inputs.remove(socket)

        self.node_update()

    def node_update(self):
        pass

    @staticmethod
    def execute(inputs, props):
        pass

    def gen_input_mapping(self) -> Optional[Type[NamedTuple]]:
        if self.repeat_last_socket or self.bl_idname == BuildingStyleNode.bl_idname:
            input_names = []
            index = count()
            for sock in self.inputs:
                inp_name = sock.name or sock.default_name + str(next(index))
                input_names.append(inp_name.lower().replace(' ', '_'))
            return namedtuple('Inputs', input_names) if input_names else None
        elif hasattr(self, 'Inputs'):
            return self.Inputs

    def get_socket(self, identifier, is_input) -> Optional[NodeSocket]:
        for socket in self.inputs if is_input else self.outputs:
            if socket.identifier == identifier:
                return socket


class BuildingStyleNode(BaseNode, Node):
    bl_idname = 'bn_BuildingStyleNode'
    bl_label = "Building Style"
    category = Categories.BUILDING
    Inputs = namedtuple('Inputs', ['facade'])
    input_template = Inputs(SocketTemplate(FacadeSocket))

    @staticmethod
    def execute(inputs: Inputs, base_bm: bmesh.types.BMesh):
        build = Building(base_bm)
        if inputs.facade:
            for facade in build.facades:
                if inputs.facade(facade):
                    facade.do_instance(build)
        return build.bm


class ObjectInputNode(BaseNode, Node):
    bl_idname = 'bn_ObjectInputNode'
    bl_label = "Object Input"

    model: bpy.props.PointerProperty(type=bpy.types.Object)

    def node_init(self):
        self.outputs.new(ObjectSocket.bl_idname, "")

    def draw_buttons(self, context, layout):
        layout.prop(self, 'model')


class PanelNodeSettingsOperator(NodeSettingsOperator, Operator):
    bl_idname = 'bn.panel_node_settings'


class PanelNode(BaseNode, Node):
    bl_idname = 'bn_PanelNode'
    bl_label = "Panel"
    category = Categories.PANEL
    settings_viewer = PanelNodeSettingsOperator
    Inputs = namedtuple('Inputs', ['object', 'scalable', 'scope_padding', 'probability'])
    Props = namedtuple('Props', ['panel_index'])
    input_template = Inputs(
        SocketTemplate(ObjectSocket, enabled=False),
        SocketTemplate(BoolSocket, 'Scalable', enabled=False),
        SocketTemplate(Vector4Socket, 'Scope padding', enabled=False),
        SocketTemplate(FloatSocket, 'Probability', enabled=False, default_value=1),
    )
    Outputs = namedtuple('Outputs', ['panel'])
    output_template = Outputs(SocketTemplate(PanelSocket))

    panel_index: bpy.props.IntProperty(description="Penal index in the collection")

    def draw_label(self):
        obj_socket = self.get_socket('object', is_input=True)
        return obj_socket.value and obj_socket.value.name or self.bl_label

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        size_v_catch = None

        def panel_gen(facade: Facade):
            # panel is expected to be in XY orientation
            nonlocal size_v_catch
            if size_v_catch is None:
                obj = inputs.object(facade)
                if obj is None:
                    return None
                if obj.mode == 'EDIT':
                    bm = bmesh.from_edit_mesh(obj.data)
                    sc_lay = bm.verts.layers.int.get('Is scope')
                    verts = [v for v in bm.verts if v[sc_lay]] if sc_lay else list(bm.verts)
                else:
                    attr = obj.data.attributes.get('Is scope')
                    verts = [v for v, a in zip(obj.data.vertices, attr.data.values()) if a.value]\
                        if attr else obj.data.vertices
                min_v = Vector((min(v.co.x for v in verts), min(v.co.y for v in verts)))
                max_v = Vector((max(v.co.x for v in verts), max(v.co.y for v in verts)))
                size_v_catch = max_v - min_v
            panel = Panel(props.panel_index, size_v_catch)
            panel.probability = inputs.probability(facade)
            panel.set_scope_padding(inputs.scope_padding(facade))  # for now it works only as scale
            return panel
        return panel_gen


class PanelAttributesNode(BaseNode, Node):
    bl_idname = 'bn_PanelAttributesNode'
    bl_label = "Panel Attributes"
    category = Categories.PANEL

    def node_init(self):
        self.outputs.new(IntSocket.bl_idname, "Index").display_shape = 'DIAMOND'

    @staticmethod
    def execute(inputs, props):
        def panel_index(facade: Facade):
            return facade.cur_panel_ind
        return panel_index


class SetPanelAttributeNode(BaseNode, Node):
    bl_idname = 'bn_SetPanelAttributeNode'
    bl_label = "Set Panel Attribute"
    category = Categories.PANEL
    Inputs = namedtuple('Inputs', ['panel', 'scalable', 'probability', 'dist_step', 'top_padding', 'bottom_padding',
                                   'left_padding', 'right_padding', 'scope_position'])
    Props = namedtuple('Props', ['attribute'])

    def update_attribute(self, context):
        self.inputs['Scalable'].enabled = 'scalable' == self.attribute
        self.inputs['Probability'].enabled = 'probability' == self.attribute
        self.inputs['Distribute step'].enabled = 'distribute step' == self.attribute
        self.inputs['Top padding'].enabled = 'scope padding' == self.attribute
        self.inputs['Bottom padding'].enabled = 'scope padding' == self.attribute
        self.inputs['Left padding'].enabled = 'scope padding' == self.attribute
        self.inputs['Right padding'].enabled = 'scope padding' == self.attribute
        self.inputs['Scope position'].enabled = 'scope position' == self.attribute

    attribute: bpy.props.EnumProperty(
        items=[(i.lower(), i, '') for i in ['Scalable', 'Probability', 'Distribute step', 'Scope padding',
                                            'Scope position']],
        update=update_attribute)

    def node_init(self):
        self.inputs.new(PanelSocket.bl_idname, "")
        self.inputs.new(BoolSocket.bl_idname, "Scalable")
        s = self.inputs.new(FloatSocket.bl_idname, "Probability")
        s.value = 1
        s.display_shape = 'DIAMOND_DOT'
        self.inputs.new(FloatSocket.bl_idname, "Distribute step").value = 3
        self.inputs.new(FloatSocket.bl_idname, "Top padding")
        self.inputs.new(FloatSocket.bl_idname, "Bottom padding")
        self.inputs.new(FloatSocket.bl_idname, "Left padding")
        self.inputs.new(FloatSocket.bl_idname, "Right padding")
        self.inputs.new(VectorSocket.bl_idname, "Scope position")
        self.outputs.new(PanelSocket.bl_idname, "")
        self.update_attribute(None)

    def draw_buttons(self, context, layout):
        layout.prop(self, "attribute", text='')

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        def set_panel_attr(build: Building):
            panel: Panel = inputs.panel(build)
            if props.attribute == 'probability':
                panel.probability = inputs.probability(build)
            return panel
        return set_panel_attr


class PanelRandomizePropsOperator(NodeSettingsOperator, Operator):
    bl_idname = "bn.panel_randomize_props"

    def invoke(self, context, event):
        node = context.node
        self.node = node
        panel_names = []
        for search_node in node.id_data.walk_back(node):
            if search_node.bl_idname == PanelNode.bl_idname:
                panel_names.append(search_node.name)
        node['panel_names'] = panel_names
        wm = context.window_manager
        return wm.invoke_props_dialog(self)

    @staticmethod
    def draw_settings(layout, node):
        tree = node.id_data
        col = layout.column()
        col.use_property_split = True
        col.use_property_decorate = False
        col.prop(node.inputs['Seed'], 'value', text='Node seed')
        col = col.column(align=True)
        for panel_node_name in node['panel_names']:
            panel_node = tree.nodes[panel_node_name]
            socket = panel_node.get_socket('probability', is_input=True)
            col.prop(socket, 'value', text=f"{panel_node.draw_label()} probability")


class PanelRandomizeNode(BaseNode, Node):
    bl_idname = 'bn_PanelRandomizeNode'
    bl_label = "Panel Randomize"
    category = Categories.PANEL
    repeat_last_socket = True
    settings_viewer = PanelRandomizePropsOperator
    Inputs = namedtuple('Inputs', ['seed', 'panel0', 'panel1', 'panel2', 'panel3'])

    def node_init(self):
        self.inputs.new(IntSocket.bl_idname, "Seed").display_shape = 'DIAMOND_DOT'
        self.inputs.new(PanelSocket.bl_idname, "")
        self.outputs.new(PanelSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, params):
        random_streams = dict()

        def randomize_panels(facade: Facade):
            stream = random_streams.get(facade.cur_floor_ind)
            if stream is None:
                stream = random.Random(int(inputs.seed(facade)))
                random_streams[facade.cur_floor_ind] = stream
            panels = [p for inp in inputs[1: -1] if (p := inp(facade)) is not None]
            return stream.choices(panels, weights=[p.probability for p in panels])[0]
        return randomize_panels


class PanelSwitchNode(BaseNode, Node):
    bl_idname = 'bn_PanelSwitchNode'
    bl_label = "Panel Switch"
    category = Categories.PANEL
    Inputs = namedtuple('Inputs', ['bool', 'true_panel', 'false_panel'])

    def node_init(self):
        self.inputs.new(BoolSocket.bl_idname, "").display_shape = 'DIAMOND_DOT'
        self.inputs.new(PanelSocket.bl_idname, "True panel")
        self.inputs.new(PanelSocket.bl_idname, "False panel")
        self.outputs.new(PanelSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, props):
        def switch_panel(build):
            true_panel = inputs.true_panel(build) if inputs.true_panel else None
            false_panel = inputs.false_panel(build) if inputs.false_panel else None
            return true_panel if inputs.bool(build) else false_panel
        return switch_panel


class StackPanelsNode(BaseNode, Node):
    bl_idname = 'bn_StackPanelsNode'
    bl_label = "Stack Panels Node"
    category = Categories.PANEL
    repeat_last_socket = True

    def node_init(self):
        self.inputs.new(PanelSocket.bl_idname, "")
        self.outputs.new(PanelSocket.bl_idname, "")


class PanelItemsNode(BaseNode, Node):
    bl_idname = 'bn_PanelItemsNode'
    bl_label = "Panel Items"
    category = Categories.PANEL
    repeat_last_socket = True
    Inputs = namedtuple('Inputs', ['index', 'panel0', 'panel1', 'panel2'])
    Props = namedtuple('Props', ['match_mode'])

    match_mode: EnumProperty(items=[(i.upper(), i, '') for i in ['None', 'Repeat', 'Cycle']],
                             update=lambda s, c: s.id_data.update())

    def node_init(self):
        self.inputs.new(IntSocket.bl_idname, "Index").display_shape = 'DIAMOND_DOT'
        self.inputs.new(PanelSocket.bl_idname, "")
        self.outputs.new(PanelSocket.bl_idname, "")

    def draw_buttons(self, context, layout):
        row = layout.row()
        row.prop(self, 'match_mode', expand=True)

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        def get_facade_item(build: Building):
            panel_funcs = {i: f for i, f in enumerate(inputs[1:]) if f is not None}
            if props.match_mode == 'NONE':
                index = inputs.index(build)
            elif props.match_mode == 'REPEAT':
                index = min(len(panel_funcs) - 1, inputs.index(build))
            elif props.match_mode == 'CYCLE':
                index = inputs.index(build) % len(panel_funcs)
            panel_f = panel_funcs.get(index)
            if panel_f:
                return panel_f(build)

        return get_facade_item


class FloorPatternNodeSettings(NodeSettingsOperator, Operator):
    bl_idname = 'bn.floor_pattern_node_settings'


class FloorPatternNode(BaseNode, Node):
    bl_idname = 'bn_FloorPatternNode'
    bl_label = "Floor Pattern"
    category = Categories.FLOOR
    settings_viewer = FloorPatternNodeSettings
    Inputs = namedtuple('Inputs', ['height', 'left', 'fill', 'distribute', 'right'])
    input_template = Inputs(
        SocketTemplate(FloatSocket, 'Height', False, 'DIAMOND_DOT', 3),
        SocketTemplate(PanelSocket, 'Left'),
        SocketTemplate(PanelSocket, 'Fill'),
        SocketTemplate(PanelSocket, 'Distribute'),
        SocketTemplate(PanelSocket, 'Right'),
    )
    Outputs = namedtuple('Outputs', ['floor'])
    output_template = Outputs(SocketTemplate(FloorSocket))
    Props = namedtuple('Props', ['use_height'])

    @property
    def props_template(self) -> Props:
        return self.Props(self.get_socket('height', is_input=True).is_to_show)

    @classmethod
    def execute(cls, inputs: Inputs, props: Props):
        catch = None

        def floor_gen(facade: Facade):
            floor = facade.get_floor()
            pan_stack = floor.panels_stack
            if inputs.left:
                facade.cur_panel_ind = 0
                panel = inputs.left(facade)
                try:
                    pan_stack.append(panel)
                except IndexError:
                    pass
            if inputs.fill:
                for _ in range(1000):
                    for _ in range(10):
                        facade.cur_panel_ind = len(pan_stack)
                        panel = inputs.fill(facade)
                        if panel:
                            break
                    if panel is None:
                        break
                    try:
                        pan_stack.append(panel)
                    except IndexError:
                        break
            if inputs.right:
                facade.cur_panel_ind = len(pan_stack) - 1
                panel = inputs.right(facade)
                replaced = pan_stack.replace(panel, DistSlice(pan_stack.max_width - panel.size.x, None))
                if len(replaced) != 1:
                    facade.cur_panel_ind = len(pan_stack) - len(replaced)
                    panel = inputs.right(facade)
                    pan_stack.replace(panel, DistSlice(pan_stack.max_width - panel.size.x, None))

            if pan_stack:
                if props.use_height:
                    floor.height = inputs.height(facade)
                else:
                    floor.height = max((p.size.y for p in pan_stack), default=0)
                pan_stack.fit_scale()
                return floor

        return floor_gen


class FloorAttributesNode(BaseNode, Node):
    bl_idname = 'bn_FloorAttributesNode'
    bl_label = "Floor Attributes"
    category = Categories.FLOOR
    Outputs = namedtuple('Outputs', ['width', 'height', 'index'])
    output_template = Outputs(
        SocketTemplate(FloatSocket, 'Width', display_shape='DIAMOND'),
        SocketTemplate(FloatSocket, 'Height', display_shape='DIAMOND'),
        SocketTemplate(IntSocket, 'Index', display_shape='DIAMOND'),
    )

    @staticmethod
    def execute(inputs, props):
        def floor_width(facade: Facade):
            return facade.size.x

        def floor_height(facade: Facade):
            return None

        def floor_index(facade: Facade):
            facade.depth.add('floor_index')
            return facade.cur_floor_ind

        return floor_width, floor_height, floor_index


class FloorSwitchNode(BaseNode, Node):
    bl_idname = 'bn_FloorSwitchNode'
    bl_label = "Floor Switch"
    category = Categories.FLOOR
    Inputs = namedtuple('Inputs', ['bool', 'true_floor', 'false_floor'])

    def node_init(self):
        self.inputs.new(BoolSocket.bl_idname, "").display_shape = 'DIAMOND_DOT'
        self.inputs.new(FloorSocket.bl_idname, "True floor")
        self.inputs.new(FloorSocket.bl_idname, "False floor")
        self.outputs.new(FloorSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, props):
        catch = dict()
        depth = set()
        last_facade = None

        def switch_floor(facade: Facade):
            if inputs.bool is None:
                return
            nonlocal last_facade
            if facade != last_facade:  # the catch should exist per facade
                last_facade = facade
                catch.clear()
                depth.clear()
            switch_state = None
            if inputs.bool not in catch:
                facade.depth.clear()
                switch_state = inputs.bool(facade)
                catch[inputs.bool] = None if facade.depth else switch_state
                depth.update(facade.depth)
            return_true = switch_state or catch[inputs.bool] or inputs.bool(facade)
            if return_true:
                if inputs.true_floor:
                    true_floor = None
                    if inputs.true_floor not in catch:
                        facade.depth.clear()
                        true_floor = inputs.true_floor(facade)
                        catch[inputs.true_floor] = None if facade.depth else true_floor
                        depth.update(facade.depth)
                    facade.depth = depth.copy()
                    floor = true_floor or (c := catch[inputs.true_floor]) and c.copy(facade) or inputs.true_floor(facade)
                    return floor
            else:
                if inputs.false_floor:
                    false_floor = None
                    if inputs.false_floor not in catch:
                        facade.depth.clear()
                        false_floor = inputs.false_floor(facade)
                        catch[inputs.false_floor] = None if facade.depth else false_floor
                        depth.update(facade.depth)
                    facade.depth = depth.copy()
                    floor = false_floor or (c := catch[inputs.false_floor]) and c.copy(facade) or inputs.false_floor(facade)
                    return floor

        return switch_floor


class StackFloorsNode(BaseNode, Node):
    bl_idname = 'bn_StackFloorsNode'
    bl_label = "Stack Floors"
    category = Categories.FACADE
    repeat_first_socket = True
    Inputs = namedtuple('Inputs', ['floor0', 'floor1', 'floor2', 'floor3'])

    def node_init(self):
        self.inputs.new(FloorSocket.bl_idname, "First floor")
        self.outputs.new(FacadeSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, params):
        def stack_floors(build: Building):
            pass
        return stack_floors


class FacadePatternNode(BaseNode, Node):
    bl_idname = 'bn_FacadePatternNode'
    bl_label = "Facade Pattern"
    category = Categories.FACADE
    Inputs = namedtuple('Inputs', ['contribution', 'last', 'fill', 'distribute', 'first'])
    input_template = Inputs(
        SocketTemplate(FloatSocket, 'Contribution', False, default_value=1),
        SocketTemplate(FloorSocket, 'Last'),
        SocketTemplate(FloorSocket, 'Fill'),
        SocketTemplate(FloorSocket, 'Distribute'),
        SocketTemplate(FloorSocket, 'First'),
    )
    Outputs = namedtuple('Outputs', ['facade'])
    output_template = Outputs(SocketTemplate(FacadeSocket))

    @staticmethod
    def execute(inputs: Inputs, params):
        def facade_generator(facade: Facade):
            floors_stack = facade.floors_stack

            # generate floors
            if inputs.first:
                facade.cur_floor_ind = len(facade.floors_stack)
                floor = inputs.first(facade)
                floors_stack.append(floor)
            if inputs.fill:
                for i in range(10000):
                    for _ in range(10):
                        facade.cur_floor_ind = len(facade.floors_stack)
                        floor = inputs.fill(facade)
                        if floor:
                            break
                    if floor is None:
                        break
                    try:
                        floors_stack.append(floor)
                    except IndexError:
                        break
            if inputs.last:
                facade.cur_floor_ind = len(facade.floors_stack) - 1
                floor = inputs.last(facade)
                replaced = floors_stack.replace(floor, DistSlice(floors_stack.max_width - floor.stack_size, None))
                if len(replaced) != 1:
                    facade.cur_floor_ind = len(facade.floors_stack) - len(replaced)
                    floor = inputs.last(facade)
                    floors_stack.replace(floor, DistSlice(floors_stack.max_width - floor.stack_size, None))

            if floors_stack:
                floors_stack.fit_scale()
                return True
            else:
                return False

        return facade_generator


class FacadeAttributesNode(BaseNode, Node):
    bl_idname = 'bn_FacadeAttributesNode'
    bl_label = 'Facade Attributes'
    category = Categories.FACADE
    Outputs = namedtuple('Outputs', ['left_angle', 'right_angle', 'azimuth', 'mat_id'])
    output_template = Outputs(
        SocketTemplate(FloatSocket, 'Left corner angle', display_shape='DIAMOND'),
        SocketTemplate(FloatSocket, 'Right corner angle', display_shape='DIAMOND'),
        SocketTemplate(FloatSocket, 'Azimuth', display_shape='DIAMOND'),
        SocketTemplate(IntSocket, 'Material index', display_shape='DIAMOND'),
    )

    @staticmethod
    def execute(inputs, props):
        def left_corner_angle(build: Building):
            return build.cur_facade.left_wall_angle

        def right_corner_angle(build: Building):
            return build.cur_facade.right_wall_angle

        def azimuth(build: Building):
            return build.cur_facade.azimuth

        def material_id(facade: Facade):
            return facade.material_index
        return left_corner_angle, right_corner_angle, azimuth, material_id


class SetFacadeAttributeNode(BaseNode, Node):
    bl_idname = 'bn_SetFacadeAttributeNode'
    bl_label = "Set Facade Attribute"
    category = Categories.FACADE

    def update_attribute(self, context):
        self.inputs['Name'].enabled = 'Name' == self.attribute

    attribute: bpy.props.EnumProperty(
        items=[(i, i, '') for i in ['Name', ]],
        update=update_attribute)

    def node_init(self):
        self.inputs.new(FacadeSocket.bl_idname, "")
        self.inputs.new(StringSocket.bl_idname, "Name")
        self.outputs.new(FacadeSocket.bl_idname, "")
        self.update_attribute(None)

    def draw_buttons(self, context, layout):
        layout.prop(self, "attribute", text='')


class FacadeItemsNode(BaseNode, Node):
    bl_idname = 'bn_FacadeItemsNode'
    bl_label = "Facade Items"
    category = Categories.FACADE
    repeat_last_socket = True
    Inputs = namedtuple('Inputs', ['index', 'facade0', 'facade1', 'facade2'])

    def node_init(self):
        self.inputs.new(IntSocket.bl_idname, "Index").display_shape = 'DIAMOND_DOT'
        self.inputs.new(FacadeSocket.bl_idname, "")
        self.outputs.new(FacadeSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, props):
        def get_facade_item(facade: Facade):
            facade_funcs = {i: f for i, f in enumerate(inputs[1:])}
            facade_f = facade_funcs.get(inputs.index(facade))
            if facade_f:
                return facade_f(facade)

        return get_facade_item


class MathNode(BaseNode, Node):
    bl_idname = 'bn_MathNode'
    bl_label = "Math"
    Inputs = namedtuple('Inputs', ['val1', 'val2', 'tolerance'])
    Props = namedtuple('Props', ['mode'])

    def update_mode(self, context):
        self.inputs['Tolerance'].enabled = self.mode == 'is_close'
        self.id_data.update()

    mode: bpy.props.EnumProperty(
        items=[(i.lower(), i, '') for i in [
            'Add', 'Multiply', 'Grater_than', 'Less_than', 'Remainder', 'Is_close', 'And', 'Or']],
        update=update_mode,
    )

    def node_init(self):
        self.inputs.new(FloatSocket.bl_idname, "").display_shape = 'DIAMOND_DOT'
        self.inputs.new(FloatSocket.bl_idname, "").display_shape = 'DIAMOND_DOT'
        s = self.inputs.new(FloatSocket.bl_idname, "Tolerance")
        s.display_shape = 'DIAMOND_DOT'
        s.value = 0.01
        self.outputs.new(FloatSocket.bl_idname, "").display_shape = 'DIAMOND_DOT'
        self.update_mode(None)

    def draw_buttons(self, context, layout):
        layout.prop(self, "mode", text='')

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        funcs = {
            'add': lambda v1, v2, _: v1 + v2,
            'multiply': lambda v1, v2, _: v1 * v2,
            'grater_than': lambda v1, v2, _: v1 > v2,
            'less_than': lambda v1, v2, _: v1 < v2,
            'remainder': lambda v1, v2, _: v1 % v2,
            'is_close': lambda v1, v2, v3: isclose(v1, v2, abs_tol=v3),
            'and': lambda v1, v2, _: bool(v1) and bool(v2),
            'or': lambda v1, v2, _: bool(v1) or bool(v2),
        }

        def math(build):
            return funcs[props.mode](inputs.val1(build), inputs.val2(build), inputs.tolerance(build))
        return math


class ObjectPanel(Panel):
    bl_idname = "VIEW3D_PT_ObjectPanel"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "Building nodes"
    bl_label = "Building properties"

    def draw(self, context):
        col = self.layout.column()
        obj = context.object
        if obj is None:
            return
        if obj.building_props.error:
            col.label(text=obj.building_props.error, icon='ERROR')
        if obj:
            props: ObjectProperties = obj.building_props
            row = col.row(align=True, heading="Facade style:")
            row.active = props.building_style is not None
            row.prop(props, 'show_in_edit_mode', text='', icon='EDITMODE_HLT')
            row.prop(props, 'realtime', text='', icon='RESTRICT_VIEW_OFF' if props.realtime else 'RESTRICT_VIEW_ON')
            row.prop(props, 'show_in_render', text='',
                     icon='RESTRICT_RENDER_OFF' if props.show_in_render else 'RESTRICT_RENDER_ON')
            col.template_ID(props, 'building_style', new=AddNewBuildingStyleOperator.bl_idname,
                            unlink=UnlinkBuildingStyleOperator.bl_idname)

            col.prop(props, 'show_facade_names',
                     icon='DOWNARROW_HLT' if props.show_facade_names else 'RIGHTARROW', emboss=False)
            if props.show_facade_names and props.building_style:
                col.use_property_split = True
                col.use_property_decorate = False
                for f_map in props.facade_names_mapping:
                    row = col.row(align=True)
                    row.prop(f_map, 'obj_facade_name', text=f_map.tree_facade_name)
                    if obj.mode == 'EDIT':
                        add_op = row.operator(EditBuildingAttributesOperator.bl_idname, text='', icon='ADD')
                        add_op.operation = 'add'
                        add_op.attr_name = f_map.obj_facade_name
                        remove_op = row.operator(EditBuildingAttributesOperator.bl_idname, text='', icon='REMOVE')
                        remove_op.operation = 'remove'
                        remove_op.attr_name = f_map.obj_facade_name
                if obj.mode == 'EDIT':
                    row = col.row(align=True)
                    add_op = row.operator(EditBuildingAttributesOperator.bl_idname,
                                          text='Add to fill facade', icon='ADD')
                    add_op.operation = 'add'
                    add_op.attr_name = ''
        else:
            col.label(text='Select object')


class PanelPanel(Panel):
    bl_idname = "VIEW3D_PT_PanelPanel"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "Building nodes"
    bl_label = "Panel properties"

    def draw(self, context):
        col = self.layout.column()
        col.operator(EditPanelAttributesOperator.bl_idname, text="Set scope").operation = 'set_scope'
        # col.operator(EditPanelAttributesOperator.bl_idname, text="Origin to scope center").operation = 'set_origin'


class GeometryTreeInterface:
    VERSION = "0.10"
    VERSION_KEY = 'bn_version'

    def __init__(self, obj, tree=None):
        if tree is None:
            tree = bpy.data.node_groups.new('Hostage tree', 'GeometryNodeTree')
            self._arrange_tree(tree, obj)
            tree[self.VERSION_KEY] = self.VERSION
        elif self.VERSION_KEY not in tree:
            if len(tree.nodes) > 2:
                raise ValueError(f'Given tree={tree} was created by user - changes are forbidden')
            else:
                self._arrange_tree(tree, obj)
                tree[self.VERSION_KEY] = self.VERSION
        elif tree[self.VERSION_KEY] != self.VERSION:
            self._arrange_tree(tree, obj)
            tree[self.VERSION_KEY] = self.VERSION
        self._tree = tree

    def set_points(self, obj: bpy.types.Object):
        obj_node = None
        for n in self._tree.nodes:
            if n.bl_idname == 'GeometryNodeObjectInfo':
                obj_node = n
                break
        obj_node.inputs[0].default_value = obj

    def set_instances(self, col: bpy.types.Collection):
        col_node = None
        for n in self._tree.nodes:
            if n.bl_idname == 'GeometryNodeCollectionInfo':
                col_node = n
                break
        col_node.inputs[0].default_value = col

    @classmethod
    def is_hostage_tree(cls, tree) -> bool:
        return cls.VERSION_KEY in tree

    @staticmethod
    def _arrange_tree(tree, obj):
        tree.nodes.clear()

        # add nodes
        out_n = tree.nodes.new('NodeGroupOutput')
        in_n = tree.nodes.new('NodeGroupInput')
        del_n = tree.nodes.new('GeometryNodeDeleteGeometry')
        join_n = tree.nodes.new('GeometryNodeJoinGeometry')
        obj_n = tree.nodes.new('GeometryNodeObjectInfo')
        inst_n = tree.nodes.new('GeometryNodeInstanceOnPoints')
        col_n = tree.nodes.new('GeometryNodeCollectionInfo')
        math_n = tree.nodes.new('ShaderNodeVectorMath')
        scale_n = tree.nodes.new('ShaderNodeVectorMath')  # todo this node can be removed
        rotate_n1 = tree.nodes.new('FunctionNodeAlignEulerToVector')
        rotate_n2 = tree.nodes.new('FunctionNodeAlignEulerToVector')

        # add links
        tree.links.new(join_n.inputs[0], del_n.outputs[0])
        tree.links.new(del_n.inputs[0], in_n.outputs[0])
        tree.links.new(inst_n.inputs[0], obj_n.outputs['Geometry'])
        tree.links.new(inst_n.inputs['Instance'],  col_n.outputs[0])
        tree.links.new(inst_n.inputs['Rotation'], rotate_n2.outputs[0])
        tree.links.new(rotate_n2.inputs['Vector'], scale_n.outputs[0])
        tree.links.new(scale_n.inputs[0], in_n.outputs[1])
        tree.links.new(math_n.inputs[0], in_n.outputs[1])
        tree.links.new(rotate_n1.inputs['Vector'], math_n.outputs[0])
        tree.links.new(rotate_n2.inputs['Rotation'], rotate_n1.outputs[0])
        tree.links.new(inst_n.inputs['Scale'], in_n.outputs[2])
        tree.links.new(del_n.inputs['Selection'], in_n.outputs[3])
        tree.links.new(inst_n.inputs['Instance Index'], in_n.outputs[4])
        tree.links.new(join_n.inputs[0], inst_n.outputs[0])
        tree.links.new(out_n.inputs[0], join_n.outputs[0])

        # set node properties
        inst_n.inputs['Pick Instance'].default_value = True
        math_n.operation = 'CROSS_PRODUCT'
        math_n.inputs[1].default_value = (0, 0, -1)
        scale_n.operation = 'SCALE'
        scale_n.inputs[3].default_value = 1
        rotate_n1.pivot_axis = 'Z'
        rotate_n2.axis = 'Z'
        rotate_n2.pivot_axis = 'X'
        col_n.inputs['Separate Children'].default_value = True
        col_n.inputs['Reset Children'].default_value = True
        del_n.domain = 'FACE'
        del_n.mode = 'ONLY_FACE'

        # set modifier properties
        obj.modifiers['BuildingStyle']["Input_2_use_attribute"] = 1
        obj.modifiers['BuildingStyle']["Input_2_attribute_name"] = "Normal"
        obj.modifiers['BuildingStyle']["Input_3_use_attribute"] = 1
        obj.modifiers['BuildingStyle']["Input_3_attribute_name"] = "Scale"
        obj.modifiers['BuildingStyle']["Input_4_use_attribute"] = 1
        obj.modifiers['BuildingStyle']["Input_4_attribute_name"] = "Is wall"
        obj.modifiers['BuildingStyle']["Input_5_use_attribute"] = 1
        obj.modifiers['BuildingStyle']["Input_5_attribute_name"] = "Wall index"


class FacadeNamesMapping(PropertyGroup):
    def update_obj_facade_name(self, context):
        # rename event
        prev_name_key = 'prev_name'
        if prev_name_key in self and self[prev_name_key] != '':
            bpy.ops.bn.edit_facade_attributes(
                operation='rename', attr_name=self[prev_name_key], new_attr_name=self.obj_facade_name)
        self[prev_name_key] = self.obj_facade_name

    tree_facade_identifier: bpy.props.StringProperty(description="Socket identifier")
    tree_facade_name: bpy.props.StringProperty()
    obj_facade_name: bpy.props.StringProperty(update=update_obj_facade_name)


class ObjectProperties(PropertyGroup):
    def is_building_tree(self, tree):
        return tree.bl_idname == BuildingStyleTree.bl_idname

    def update_style(self, context):
        if self.building_style is None:
            mod = self.get_modifier()
            if mod is not None:
                self.id_data.modifiers.remove(mod)
            self.error = ''
        else:
            self.building_style.show_in_areas(True)
            self.update_mapping()
            try:
                self.building_style.apply(self.id_data)
            except Exception as e:
                self.error = str(e)
                raise
            else:
                self.error = ''

    def update_show_in_edit(self, context):
        mod = self.get_modifier()
        if mod is not None:
            mod.show_in_editmode = self.show_in_edit_mode

    def update_realtime(self, context):
        mod = self.get_modifier()
        if mod is not None:
            mod.show_viewport = self.realtime
            if self.realtime:
                self.building_style.apply(self.id_data)

    def update_show_in_render(self, context):
        mod = self.get_modifier()
        if mod is not None:
            mod.show_render = self.show_in_render

    building_style: bpy.props.PointerProperty(
        type=bpy.types.NodeTree, poll=is_building_tree, name="Building Style", update=update_style)
    points: bpy.props.PointerProperty(type=bpy.types.Object)  # todo should be removed in object copies
    error: bpy.props.StringProperty()
    show_in_edit_mode: bpy.props.BoolProperty(
        default=True, description="Show building style in edit mode", update=update_show_in_edit)
    realtime: bpy.props.BoolProperty(
        default=True, description='Display building style in viewport', update=update_realtime)
    show_in_render: bpy.props.BoolProperty(
        default=True, description='Use building style during render', update=update_show_in_render)
    show_facade_names: bpy.props.BoolProperty(name='Named facades', default=True)
    facade_names_mapping: bpy.props.CollectionProperty(type=FacadeNamesMapping)

    def apply_style(self):
        if self.id_data.mode == 'EDIT':
            can_be_updated = self.building_style and self.realtime and self.show_in_edit_mode
        else:
            can_be_updated = self.building_style and self.realtime
        if can_be_updated:
            try:
                self.building_style.apply(self.id_data)
            except Exception as e:
                self.error = str(e)
                traceback.print_exc()
            else:
                self.error = ''

    def get_modifier(self) -> Optional[bpy.types.Modifier]:
        obj = self.id_data
        for mod in obj.modifiers:
            if mod.type == 'NODES' and mod.node_group and GeometryTreeInterface.is_hostage_tree(mod.node_group):
                return mod

    def get_gn_tree(self) -> GeometryTreeInterface:
        obj = self.id_data
        modifier = self.get_modifier()

        # add new modifier
        if modifier is None:
            modifier = obj.modifiers.new("BuildingStyle", 'NODES')

        return GeometryTreeInterface(obj, modifier.node_group)

    def update_mapping(self):
        mapping = {m.tree_facade_identifier: m.obj_facade_name for m in self.facade_names_mapping}
        if self.building_style:
            self.facade_names_mapping.clear()
            facade: FacadeTreeNames
            for facade in self.building_style.facade_names:
                f_map: FacadeNamesMapping = self.facade_names_mapping.add()

                # new facade name
                if facade.identifier not in mapping:
                    f_map.tree_facade_identifier = facade.identifier
                    f_map.tree_facade_name = facade.user_name
                else:
                    f_map.tree_facade_identifier = facade.identifier
                    f_map.tree_facade_name = facade.user_name
                    f_map.obj_facade_name = mapping[facade.identifier]

    def facade_names_mapping(self) -> Iterable[tuple[str, Optional[bpy.types.FaceMap]]]:
        yield from zip((n.name for n in self.building_style.facade_names), chain(self.id_data.face_maps, cycle([None])))


class AddNewBuildingStyleOperator(Operator):
    bl_idname = "bn.add_new_building_style"
    bl_label = "Add new building style"
    bl_description = "Add new building style to the object"
    bl_options = {'INTERNAL', }

    @classmethod
    def poll(cls, context):
        return context.object is not None

    def execute(self, context):
        obj = context.object
        obj_props: ObjectProperties = obj.building_props
        tree = bpy.data.node_groups.new("BuildingStyle", BuildingStyleTree.bl_idname)
        node1 = tree.nodes.new(PanelNode.bl_idname)
        node2: Node = tree.nodes.new(FloorPatternNode.bl_idname)
        node3: Node = tree.nodes.new(FacadePatternNode.bl_idname)
        node4: Node = tree.nodes.new(BuildingStyleNode.bl_idname)
        tree.links.new(node2.inputs[2], node1.outputs[0])
        tree.links.new(node3.inputs[1], node2.outputs[0])
        tree.links.new(node4.inputs[0], node3.outputs[0])
        node2.location = Vector((200, 0))
        node3.location = Vector((400, 0))
        node4.location = Vector((600, 0))
        try:
            obj_props.building_style = tree
        finally:
            tree.show_in_areas(True)
        return {'FINISHED'}


class UnlinkBuildingStyleOperator(Operator):
    bl_idname = "bn.unlink_building_style"
    bl_label = "Unlink building style"
    bl_description = "Unlink building style from the object"
    bl_options = {'INTERNAL', }

    @classmethod
    def poll(cls, context):
        return context.object is not None

    def execute(self, context):
        obj = context.object
        obj_props: ObjectProperties = obj.building_props
        try:
            obj_props.building_style.show_in_areas(False)
        finally:
            obj_props.building_style = None
        return {'FINISHED'}


class EditSocketsOperator(Operator):
    bl_idname = "bn.edit_sockets"
    bl_label = "Edit socket"
    bl_options = {'INTERNAL', }

    operation: bpy.props.EnumProperty(items=[(i, i, '') for i in ['move_up', 'move_down', 'rename', 'add', 'delete']])

    # for internal usage only
    tree_name: bpy.props.StringProperty()
    node_name: bpy.props.StringProperty()
    socket_identifier: bpy.props.StringProperty()
    is_output: BoolProperty()
    old_socket_name: bpy.props.StringProperty()
    new_socket_name: bpy.props.StringProperty(name='New name')

    @classmethod
    def description(cls, context, properties):
        descriptions = {
            'move_up': "Move the socket upper",
            'move_down': "Move the socket downer",
            'rename': "Rename the socket",
            'add': "Add a new socket below",
            'delete': "Delete the socket",
        }
        return descriptions[properties.operation]

    def execute(self, context):
        tree = bpy.data.node_groups[self.tree_name]
        node = tree.nodes[self.node_name]
        sock_col = node.outputs if self.is_output else node.inputs
        socket = next(s for s in sock_col if s.identifier == self.socket_identifier)
        if self.operation == 'add':
            sock_col.new(socket.bl_idname, '')
            position = next(i for i, s in enumerate(sock_col) if s.identifier == socket.identifier) + 1
            sock_col.move(len(sock_col) - 1, position)
        elif self.operation == 'delete':
            sock_col.remove(socket)
        elif self.operation == 'rename':
            if self.new_socket_name.lower() == 'fill':
                self.report({'ERROR_INVALID_INPUT'}, f'"{self.new_socket_name}" socket name is forbidden')
                return {'CANCELLED'}
            socket.user_name = self.new_socket_name
        elif self.operation == 'move_up':
            current_index = next(i for i, s in enumerate(sock_col) if s.identifier == socket.identifier)
            sock_col.move(current_index, max([current_index - 1, 1]))
        elif self.operation == 'move_down':
            current_index = next(i for i, s in enumerate(sock_col) if s.identifier == socket.identifier)
            sock_col.move(current_index, current_index + 1)
        else:
            raise TypeError(f"It is not known how to handle the operation={self.operation}")
        tree.update_facade_names()
        for obj in bpy.data.objects:
            props: ObjectProperties = obj.building_props
            if props.building_style and props.building_style.bl_idname == BuildingStyleTree.bl_idname:
                props.update_mapping()
        return {'FINISHED'}

    def invoke(self, context, event):
        self.tree_name = context.node.id_data.name
        self.node_name = context.node.name
        self.socket_identifier = context.socket.identifier
        self.is_output = context.socket.is_output
        self.old_socket_name = context.socket.user_name
        self.new_socket_name = context.socket.name
        wm = context.window_manager
        if self.operation == 'rename':
            return wm.invoke_props_dialog(self)
        else:
            return self.execute(context)

    def draw(self, context):
        self.layout.prop(self, 'new_socket_name')


class EditBuildingAttributesOperator(Operator):
    bl_idname = "bn.edit_building_attributes"
    bl_label = "Edit facade attributes"
    bl_options = {'INTERNAL', }

    operation: bpy.props.EnumProperty(items=[(i, i, '') for i in ['add', 'remove', 'rename']])
    attr_name: bpy.props.StringProperty()
    new_attr_name: bpy.props.StringProperty(description='New facade name to rename')

    @classmethod
    def description(cls, context, properties):
        descriptions = {
            'rename': "Replace values with style name to new style name",
            'add': f'Assign selected faces to "{properties.attr_name}" style',
            'remove': f'Remove selected faces from "{properties.attr_name}" style',
        }
        return descriptions[properties.operation]

    @classmethod
    def poll(cls, context):
        return context.object

    def execute(self, context):
        obj = context.object
        if context.object.mode != 'EDIT' and self.operation in {'add', 'remove'}:
            self.report('ERROR_INVALID_CONTEXT',
                        f'The operator does not support "{self.operation}" operation in object mode')
            return {'CANCELLED'}
        if context.object.mode == 'EDIT':
            bm = bmesh.from_edit_mesh(obj.data)
            f_lay = bm.faces.layers.string.get(FACE_STYLE_LAYER_NAME)
            if f_lay is None:
                f_lay = bm.faces.layers.string.new(FACE_STYLE_LAYER_NAME)
        if self.operation == 'add':
            for face in (f for f in bm.faces if f.select):
                face[f_lay] = self.attr_name.encode()
        elif self.operation == 'remove':
            for face in (f for f in bm.faces if f.select):
                if face[f_lay].decode() == self.attr_name:
                    face[f_lay] = ''.encode()
        elif self.operation == 'rename':
            if obj.mode == 'EDIT':
                for face in bm.faces:
                    if face[f_lay].decode() == self.attr_name:
                        face[f_lay] = self.new_attr_name.encode()
            else:
                attr = obj.data.attributes.get(FACE_STYLE_LAYER_NAME)
                if attr is None:
                    attr = obj.data.attributes.new(FACE_STYLE_LAYER_NAME, 'STRING', 'FACE')
                for face_attr in attr.data.values():
                    if face_attr.value == self.attr_name:
                        face_attr.value = self.new_attr_name
        try:
            obj.building_props.building_style.apply(obj)
        except:
            traceback.print_exc()
        return {'FINISHED'}


class EditPanelAttributesOperator(Operator):
    bl_idname = "bn.edit_panel_attributes"
    bl_label = "Edit panel attributes"
    bl_options = {'INTERNAL', }

    operation: bpy.props.EnumProperty(items=[(i, i, '') for i in ['set_scope', 'set_origin']])

    @classmethod
    def description(cls, context, properties):
        descriptions = {
            'set_scope': "Mark selected points as scope of the panel",
            # 'set_origin': "Put origin into the center of the panel scope or bounding box",
        }
        return descriptions[properties.operation]

    @classmethod
    def poll(cls, context):
        return context.object and context.object.mode == 'EDIT'

    def execute(self, context):
        obj = context.object
        bm = bmesh.from_edit_mesh(obj.data)
        sc_lay = bm.verts.layers.int.get('Is scope') or bm.verts.layers.int.new('Is scope')
        if self.operation == 'set_scope':
            for vert in bm.verts:
                vert[sc_lay] = vert.select
            points = [v for v in bm.verts if v[sc_lay]] or bm.verts
            center = Geometry.get_bounding_center(points)
            glob_center = center * obj.scale
            glob_center.rotate(obj.rotation_euler)
            obj.location += glob_center
            for vert in bm.verts:
                vert.co -= center
        obj.data.update()
        for fac_obj in (o for o in bpy.data.objects if o.building_props.building_style):
            props: ObjectProperties = fac_obj.building_props
            if obj in {panel for panel in props.building_style.inst_col.objects}:
                props.apply_style()
        return {'FINISHED'}


classes = dict()
for name, member in inspect.getmembers(sys.modules[__name__]):
    is_module_cls = inspect.isclass(member) and member.__module__ == __name__
    if is_module_cls:
        if any(base_cls in member.__bases__ for base_cls
               in [NodeTree, NodeSocket, Node, Panel, Operator, PropertyGroup, Menu]):
            # property groups should be added before dependent classes
            # (doesn't take into account dependent Property groups)
            for annotation in get_type_hints(member).values():
                if isinstance(annotation, bpy.props._PropertyDeferred):
                    annotation_class = annotation.keywords.get('type')
                    if annotation_class is not None and annotation_class.__module__ == __name__:
                        classes[annotation_class] = None
            classes[member] = None


class DistSlice:
    def __init__(self, start: float = None, stop: float = None):
        if start is None and stop is None:
            raise TypeError('Distance slice should either start or stop limit')
        self.start: Optional[float] = start
        self.stop: Optional[float] = stop

    @property
    def length(self):
        return self.stop - self.start

    def __repr__(self):
        start = self.start.__format__('.2f') if self.start is not None else None
        stop = self.stop.__format__('.2f') if self.stop is not None else None
        return f"<DistSlice({start}, {stop})>"


class Shape(ABC):
    @property
    @abstractmethod
    def stack_size(self):
        ...

    @abstractmethod
    def scale_along_stack(self, factor: float):
        ...

    @abstractmethod
    def copy(self):
        ...


class Panel(Shape):
    def __init__(self, obj_index: int, size: Vector):
        # panel is expected to be in XY orientation
        self.obj_index = obj_index  # index of object in the collection
        self.size: Vector = size
        self.scale: Vector = Vector((1, 1))

        # user attributes
        self.probability = 1

    def copy(self):
        panel = Panel(self.obj_index, self.size)
        panel.scale = self.scale
        panel.probability = self.probability
        return panel

    @property
    def stack_size(self):
        return self.size.x * self.scale.x

    def scale_along_stack(self, factor: float):
        self.scale *= Vector((factor, 1))

    def set_scope_padding(self, padding):
        self.size.x += padding[0] + padding[2]
        self.size.y += padding[1] + padding[3]

    def do_instance(self, build: 'Building', location: Vector, scale: Vector, normal: Vector):
        vec = build.bm.verts.new(location)
        vec[build.norm_lay] = normal
        vec[build.scale_lay] = (*(self.scale * scale), 1)
        vec[build.ind_lay] = self.obj_index

    def __repr__(self):
        return f"<Panel:{self.obj_index}>"


class Floor(Shape):
    def __init__(self, facade: 'Facade'):
        self.index = facade.cur_floor_ind
        self.height = None
        self.z_scale = 1
        self.panels_stack: ShapesStack[Panel] = ShapesStack(facade.size.x)

    def copy(self, facade: 'Facade'):
        floor = Floor(facade)
        floor.height = self.height
        floor.z_scale = self.z_scale
        floor.panels_stack = self.panels_stack.copy()
        return floor

    @property
    def stack_size(self):
        return self.height * self.z_scale

    def scale_along_stack(self, factor: float):
        self.z_scale *= factor

    def do_instance(self, build: 'Building', start: Vector, direction: Vector, normal: Vector, panels_range: DistSlice,
                    z_factor):
        """    +--+--+--+   3D
        start  *  │  │  │
               +--+--+--+--------→ direction
        """
        xy_shift = 0
        panels = self.panels_stack[panels_range]
        xy_factor = panels_range.length / sum(p.stack_size for p in panels)
        for panel in panels:
            size_x = panel.stack_size * xy_factor
            z_scale = self.stack_size / panel.size.y * z_factor
            xy_shift += size_x / 2
            panel.do_instance(build, start + direction * xy_shift, Vector((xy_factor, z_scale)), normal)
            xy_shift += size_x / 2

    def __repr__(self):
        return f"<Floor i={self.index}, {self.panels_stack}>"


ShapeType = TypeVar('ShapeType')


class ShapesStack(Generic[ShapeType]):
    """Before replacing or adding new element it remove panels from right side if the size of the stack is too big"""
    def __init__(self, max_width):
        self._shapes: list[Shape] = []
        self._cum_width: list[float] = [0]
        self.max_width = max_width

    def copy(self):
        stack = ShapesStack(self.max_width)
        stack._shapes = [shape.copy() for shape in self._shapes]
        stack._cum_width = self._cum_width.copy()
        return stack

    def append(self, shape: Shape):
        if self.can_be_added(shape):
            self._cum_width.append(self._cum_width[-1] + (shape and shape.stack_size or 0))
            self._shapes.append(shape)
        else:
            raise IndexError("Given shape is too big or shape stuck is full")

    def replace(self, shape: Shape, position: DistSlice) -> list[Shape]:
        replace_ind = self._range_to_indexes(position)
        removed_panels = self[replace_ind]
        self[replace_ind] = shape
        return removed_panels

    @property
    def is_full(self):
        return self._cum_width[-1] > self.max_width

    @property
    def width(self):
        return self._cum_width[-1]

    def fit_scale(self):
        scale = self.max_width / self.width
        for shape in self._shapes:
            shape.scale_along_stack(scale)
        self._cum_width = list(accumulate((p.stack_size for p in self._shapes), initial=0))

    def can_be_added(self, shape: Shape) -> bool:
        """               │←-→│ the scale distance if the shape will be added
        +-------+------+------+-----
        │ *     │ *    │  new │
                          │
                          │
                       │←→│     the scale distance if the shape won't be added
        +-------+------+------  in this case the panel should not be added
        │ *     │ *    │
        """
        cur_scale_dist = abs(self.max_width - self.width)
        new_scale_dist = abs(self.width + shape.stack_size - self.max_width)
        return new_scale_dist < cur_scale_dist

    def copy_range(self, dist_range: DistSlice) -> 'ShapesStack':
        stack = ShapesStack(None)
        panels_range = self._range_to_indexes(dist_range)
        stack._shapes = self._shapes[panels_range]
        stack._cum_width = self._cum_width[panels_range.start: panels_range.stop + 2]
        stack._cum_width -= dist_range.start
        return stack

    def _range_to_indexes(self, dist_range: DistSlice) -> slice:
        """
        slice      0 1   2  3   4  5     6
        sh_index    0  1  2   3  4    5
        width -     1  3  2   3  2    5
        shapes     +-+---+--+---+--+-----+-----------
        in stack   │ │   │  │   │  │     │
                   +-+---+--+---+--+-----+-----------
        cum_width  0 1   4  6   9  11    16
        slice     0 1  2   3  4   5    6    7
        """
        if dist_range.start is None:
            left_shape_ind = None
        else:
            left_shape_ind = bisect.bisect(self._cum_width, dist_range.start) - 1
            is_first_shape = left_shape_ind == -1
            before_dist = inf if is_first_shape else dist_range.start - self._cum_width[left_shape_ind]
            is_last_shape = left_shape_ind == len(self._cum_width) - 1
            after_dist = inf if is_last_shape else self._cum_width[left_shape_ind + 1] - dist_range.start
            if before_dist > after_dist:
                left_shape_ind += 1
        if dist_range.stop is None:
            right_shape_ind = None
        else:
            right_shape_ind = bisect.bisect(self._cum_width, dist_range.stop) - 1
            is_first_shape = right_shape_ind == -1
            before_dist = inf if is_first_shape else dist_range.stop - self._cum_width[right_shape_ind]
            is_last_shape = right_shape_ind == len(self._cum_width) - 1
            after_dist = inf if is_last_shape else self._cum_width[right_shape_ind + 1] - dist_range.stop
            if before_dist > after_dist:
                right_shape_ind += 1
        return slice(left_shape_ind, right_shape_ind)

    @overload
    def __getitem__(self, key: int) -> ShapeType: ...
    @overload
    def __getitem__(self, key: slice) -> list[ShapeType]: ...
    @overload
    def __getitem__(self, key: DistSlice) -> list[ShapeType]: ...

    def __getitem__(self, key):
        if isinstance(key, (int, slice)):
            return self._shapes[key]
        if isinstance(key, DistSlice):
            return self._shapes[self._range_to_indexes(key)]
        raise TypeError

    def __setitem__(self, key, shape: Shape):
        if isinstance(key, int):
            index = key
            old_panel_size = self._cum_width[index + 1] - self._cum_width[index]
            new_panel_size = shape.stack_size
            impact_size = new_panel_size - old_panel_size
            self._shapes[index] = shape
            self._cum_width = [self._cum_width[:index + 1]] + [old_s + impact_size for old_s in
                                                               self._cum_width[index + 1:]]
        elif isinstance(key, slice):
            start = key.start if key.start is not None else 0
            stop = key.stop if key.stop is not None else len(self._shapes)
            old_shapes_size = sum(s - s_prev for s, s_prev in zip(
                self._cum_width[start + 1: stop + 1], self._cum_width[start: stop]))
            impact_size = shape.stack_size - old_shapes_size
            self._shapes[start: stop] = [shape]
            self._cum_width[start + 1: stop + 1] = [self._cum_width[start] + shape.stack_size]
            self._cum_width = self._cum_width[:start + 2] + [old_s + impact_size for old_s
                                                                 in self._cum_width[start + 2:]]
        else:
            raise TypeError

    def __len__(self):
        return len(self._shapes)

    def __bool__(self):
        return bool(self._shapes)

    def __iter__(self) -> Iterable[ShapeType]:
        return iter(self._shapes)

    def __repr__(self):
        str_panels = ', '.join(str(p) for p in self._shapes)
        return f"[{str_panels}]"


class Facade:
    def __init__(self, grid: 'CentredMeshGrid', mat_index: int):
        self.cur_floor: Floor = None
        self.cur_floor_ind = None  # it's not always the last index in the floors stack
        self.cur_panel_ind = None  # it's not always the last index in the panels stack
        self.grid: CentredMeshGrid = grid
        self.floors_stack: ShapesStack[Floor] = ShapesStack(grid.size.y)

        self.depth: set[Literal['floor_index']] = set()

        self.material_index = mat_index
        self.left_wall_angle = None
        self.right_wall_angle = None

    @property
    def size(self) -> Vector:
        return self.grid.size

    def get_floor(self) -> Floor:
        floor = Floor(self)
        self.cur_floor = floor
        return floor

    def do_instance(self, build: 'Building'):
        """     ↑ direction 3D
                +------------+
                │  floor     │
        start   *------------+-----→ Panels direction
        """
        for face_i, floors_pos, panel_pos in self.grid.cells_and_positions:
            face = build._base_bm.faces[face_i]
            start, max_l = Geometry.get_bounding_loops(face)
            direction = Vector((0, 0, 1))
            panels_direction = ((max_l.vert.co - start.vert.co) * Vector((1, 1, 0))).normalized()
            z_shift = 0
            floors = self.floors_stack[floors_pos]
            z_factor = floors_pos.length / sum(f.stack_size for f in floors)
            for floor in self.floors_stack[floors_pos]:
                size = floor.stack_size * z_factor
                z_shift += size / 2
                floor.do_instance(build, start.vert.co + direction * z_shift, panels_direction, face.normal, panel_pos, z_factor)
                z_shift += size / 2

    def __repr__(self):
        floors = '\n'.join([repr(floor) for floor in self.floors_stack[::-1]])
        return f"<Facade: \n{floors}>"


class Building:
    def __init__(self, base_bm):
        bm = bmesh.new()
        self.norm_lay = bm.verts.layers.float_vector.new("Normal")
        self.scale_lay = bm.verts.layers.float_vector.new("Scale")
        self.ind_lay = bm.verts.layers.int.new("Wall index")
        self.bm: BMesh = bm

        self.cur_facade: Facade = None

        self._base_bm: BMesh = base_bm

    @property
    def facades(self) -> Iterable[Facade]:
        wall_lay = self._base_bm.faces.layers.int.get("Is wall") or self._base_bm.faces.layers.int.new("Is wall")
        crease_lay = self._base_bm.edges.layers.crease.active

        visited = set()
        for face in self._base_bm.faces:
            if face in visited:
                continue
            is_vertical = isclose(face.normal.dot(Vector((0, 0, 1))), 0, abs_tol=0.1)
            is_valid = is_vertical and len(face.verts) > 3 and not isclose(face.calc_area(), 0, abs_tol=0.1)
            if is_valid:

                facade_grid = Geometry.connected_coplanar_faces(face, crease_lay)
                facade = Facade(facade_grid, face.material_index)
                self.cur_facade = facade
                yield facade

                for face_ind in facade_grid:
                    _face = self._base_bm.faces[face_ind]
                    visited.add(_face)
                    _face[wall_lay] = 1
            else:
                face[wall_lay] = 0

    @staticmethod
    def calc_azimuth(vec: Vector):
        vec = vec.normalized()
        north = Vector((0, 1, 0))
        is_right = vec.cross(north).normalized().z < 0
        return vec @ north + 3 if is_right else 1 - vec @ north


class CentredMeshGrid:
    """      Y
    row 1    ↑  +-----+-----+
             │  │     │     │
    row 0       +-----+-----+
                │     │     │
    row -1      +-----+-----+   --→ X
           col-1   col 0   col 1

    >>> gr = CentredMeshGrid()
    >>> gr.add(Vector((0, 0)), Vector((1., 1.)), 0)
    >>> gr.add(Vector((1, 0)), Vector((2., 1.)), 1)
    >>> gr.add(Vector((0, 1)), Vector((1., 3.)), 2)
    >>> gr.clean_grid()
    >>> gr._grid
    array([[ 0,  1],
           [ 2, -1]])
    >>> gr._size_x
    array([1., 2.])
    >>> gr._size_y
    array([1., 3.])
    >>> [fi for fi in gr]
    [0, 1, 2]
    >>> print("\\n".join([str(i) for i in gr.cells_and_positions]))
    (0, <DistSlice(0.00, 1.00)>, <DistSlice(0.00, 1.00)>)
    (1, <DistSlice(0.00, 1.00)>, <DistSlice(1.00, 3.00)>)
    (2, <DistSlice(1.00, 4.00)>, <DistSlice(0.00, 1.00)>)
    """
    def __init__(self):
        self._grid = np.full((100, 100), -1)
        self._size_x = np.full(100, -1.0)
        self._size_y = np.full(100, -1.0)

        self._center_row = 50
        self._center_col = 50

    def add(self, cord: Vector, size: Vector, face_ind: int):
        grid_pos = self._to_ind(cord)
        self._grid[grid_pos] = face_ind
        self._size_x[grid_pos[1]] = size.x
        self._size_y[grid_pos[0]] = size.y

    def clean_grid(self):
        self._size_x = self._size_x[np.any(self._grid != -1, 0)]
        self._size_y = self._size_y[np.any(self._grid != -1, 1)]
        self._grid = self._grid[..., np.any(self._grid != -1, 0)][np.any(self._grid != -1, 1), ...]

    @property
    def size(self) -> Vector:
        return Vector((np.sum(self._size_x[self._size_x > 0]), np.sum(self._size_y[self._size_y > 0])))

    @property
    def cells_and_positions(self) -> Iterable[tuple[int, DistSlice, DistSlice]]:
        cum_size_x = list(accumulate(self._size_x, initial=0))
        cum_size_y = list(accumulate(self._size_y, initial=0))
        for i_row, row in enumerate(self._grid):
            for i_col, face_ind in enumerate(row):
                if face_ind != -1:
                    yield face_ind, DistSlice(cum_size_y[i_row], cum_size_y[i_row + 1]),\
                          DistSlice(cum_size_x[i_col], cum_size_x[i_col + 1])

    def _to_ind(self, coord: Vector) -> tuple[int, int]:
        return self._center_row + int(coord.y), self._center_col + int(coord.x)

    def __iter__(self):
        def face_indexes() -> Iterable[int]:
            for row in self._grid:
                for face_ind in row:
                    if face_ind != -1:
                        yield face_ind
        return face_indexes()

    def __repr__(self):
        return repr(self._grid[::-1])


class Geometry:
    @staticmethod
    def get_bounding_verts(verts: list[BMVert]) -> tuple[Vector, Vector]:  # min, max
        min_v = Vector((min(v.co.x for v in verts), min(v.co.y for v in verts),
                        min(v.co.z for v in verts)))
        max_v = Vector((max(v.co.x for v in verts), max(v.co.y for v in verts),
                        max(v.co.z for v in verts)))
        return min_v, max_v

    @staticmethod
    def get_bounding_center(verts: list[BMVert]) -> Vector:
        min_v, max_v = Geometry.get_bounding_verts(verts)
        return (max_v - min_v) * 0.5 + min_v

    @staticmethod
    def left_right_loops(face: BMFace) -> tuple[Optional[BMLoop], Optional[BMLoop]]:
        """
                Z → ↑   left→ o←-------o  Only 4 vertices are expected
        direction   │   loop  │        ↑
                    │         │        │
                    │         ↓        │  right
                    │         o-------→o ←loop
        """
        if len(face.verts) != 4:
            return None, None
        for loop in face.loops:
            loop_dir = (loop.link_loop_next.vert.co - loop.vert.co).normalized()
            z_angle = Vector((0, 0, 1)).dot(loop_dir)
            is_right = isclose(1, z_angle, abs_tol=0.3)  # 45 degrees
            is_left = isclose(-1, z_angle, abs_tol=0.3)
            if is_left or is_right:
                break
        if is_left:
            return loop, loop.link_loop_next.link_loop_next
        elif is_right:
            return loop.link_loop_next.link_loop_next, loop
        return None, None

    @staticmethod
    def get_bounding_loops(face: BMFace) -> tuple[Optional[BMLoop], Optional[BMLoop]]:
        """
                                    right bounding loop
                                            ↓
                Z → ↑         o←------------o  Any number of vertices are expected
        direction   │         │             ↑  but the shape should be close to quad
                    │         ↓             │
                    │         o             o
                    │         │             ↑
                    │         ↓             │
                    │         o-----→o-----→o
                              ↑
                    left bounding loop
        """
        left_l, right_l = None, None
        for loop in face.loops:  # https://developer.blender.org/T92620
            loop_dir = (loop.link_loop_next.vert.co - loop.vert.co).normalized()
            z_angle = Vector((0, 0, 1)).dot(loop_dir)
            is_z_up = isclose(1, z_angle, abs_tol=0.3)  # 45 degrees
            if is_z_up:
                next_loop = loop.link_loop_next
                next_loop_dir = (next_loop.link_loop_next.vert.co - next_loop.vert.co).normalized()
                next_z_angle = Vector((0, 0, 1)).dot(next_loop_dir)
                is_next_z_up = isclose(1, next_z_angle, abs_tol=0.3)
                if not is_next_z_up:
                    right_l = next_loop

            elif is_z_down := isclose(-1, z_angle, abs_tol=0.3):
                next_loop = loop.link_loop_next
                next_loop_dir = (next_loop.link_loop_next.vert.co - next_loop.vert.co).normalized()
                next_z_angle = Vector((0, 0, 1)).dot(next_loop_dir)
                is_next_z_down = isclose(-1, next_z_angle, abs_tol=0.3)
                if not is_next_z_down:
                    left_l = next_loop

            if left_l and right_l:
                break

        return left_l, right_l

    @staticmethod
    def get_bounding_vertices(face: BMFace) -> tuple[Optional[BMVert], Optional[BMVert]]:
        """Works the same as 'get_bounding_loops' but with vertices. Expects the face aligned along Z axis
        Vertices has the same order as loops"""
        left_v, right_v = None, None
        for last_vert, vert, next_vert in zip(
                chain([face.verts[-1]], face.verts[:-1]), face.verts, chain(face.verts[1:]), [face.verts[0]]):
            direction = (vert.co - last_vert.co).normalized()
            z_angle = Vector((0, 0, 1)).dot(direction)
            is_z_up = isclose(1, z_angle, abs_tol=0.3)  # 45 degrees
            if is_z_up:
                next_vert_dir = (next_vert.co - vert.co).normalized()
                next_z_angle = Vector((0, 0, 1)).dot(next_vert_dir)
                is_next_z_up = isclose(1, next_z_angle, abs_tol=0.3)
                if not is_next_z_up:
                    right_v = next_vert

            elif is_z_down := isclose(-1, z_angle, abs_tol=0.3):
                next_vert_dir = (next_vert.co - vert.co).normalized()
                next_z_angle = Vector((0, 0, 1)).dot(next_vert_dir)
                is_next_z_down = isclose(-1, next_z_angle, abs_tol=0.3)
                if not is_next_z_down:
                    left_v = next_vert

            if left_v and right_v:
                break

        return left_v, right_v

    @staticmethod
    def mesh_loop_walk(direction_loop: BMLoop) -> Iterable[BMLoop]:
        prev_loop = direction_loop
        while (opos_loop := prev_loop.link_loop_radial_next) != prev_loop:
            next_direction_loop = opos_loop.link_loop_next.link_loop_next
            if len(next_direction_loop.face.verts) != 4:
                break
            yield next_direction_loop
            prev_loop = next_direction_loop

    @staticmethod
    def connected_coplanar_faces(start_face: BMFace, crease_layer=None, split_by_material=True) -> CentredMeshGrid:
        def is_radial_face_valid(n_loop) -> bool:
            _current_face = n_loop.face
            _next_face = n_loop.link_loop_radial_next.face
            if _next_face == face or _next_face in visited:  # last condition does not protect entirely
                pass
            elif split_by_material and _current_face.material_index != _next_face.material_index:
                pass
            elif crease_layer and n_loop.edge[crease_layer] == 1:
                pass
            elif len(_next_face.edges) != 4:
                pass
            elif isclose(n_loop.edge.calc_face_angle(3.14), 0, abs_tol=0.17):
                return True
            return False

        gr = CentredMeshGrid()
        left_loop, right_loop = Geometry.get_bounding_loops(start_face)
        if len(start_face.verts) != 4:
            xy_size = ((right_loop.vert.co - left_loop.vert.co) * Vector((1, 1, 0))).length
            z_size = (right_loop.vert.co - left_loop.vert.co).z
            gr.add(Vector((0, 0)), Vector((xy_size, z_size)), start_face.index)
            gr.clean_grid()
            return gr
        visited: set[BMFace] = set()
        next_faces: list[tuple[tuple[BMLoop, BMLoop], Vector]] = [((left_loop, right_loop), Vector((0, 0)))]
        while next_faces:
            (left_loop, right_loop), pos = next_faces.pop()
            face = left_loop.face
            if face in visited:
                continue
            face_size = Vector((left_loop.edge.calc_length(), right_loop.link_loop_prev.edge.calc_length()))
            gr.add(pos, face_size, face.index)
            visited.add(face)

            # face below
            if is_radial_face_valid(left_loop):
                left_next = left_loop.link_loop_radial_next.link_loop_next.link_loop_next
                right_next = left_loop.link_loop_radial_next
                next_faces.append(((left_next, right_next), pos + Vector((0, -1))))
            # face right
            if is_radial_face_valid(left_loop.link_loop_next):
                left_next = left_loop.link_loop_next.link_loop_radial_next.link_loop_next
                right_next = left_next.link_loop_next.link_loop_next
                next_faces.append(((left_next, right_next), pos + Vector((1, 0))))
            # face up
            if is_radial_face_valid(right_loop):
                left_next = right_loop.link_loop_radial_next
                right_next = left_next.link_loop_next.link_loop_next
                next_faces.append(((left_next, right_next), pos + Vector((0, 1))))
            # face left
            if is_radial_face_valid(right_loop.link_loop_next):
                left_next = right_loop.link_loop_next.link_loop_radial_next.link_loop_prev
                right_next = left_next.link_loop_next.link_loop_next
                next_faces.append(((left_next, right_next), pos + Vector((-1, 0))))
        gr.clean_grid()
        return gr


def update_tree_timer():
    if BuildingStyleTree.was_changes:
        update_trees = []
        for obj in bpy.context.scene.objects:  # objects after deleting are still in data.objects
            obj_props: ObjectProperties = obj.building_props
            if obj_props.building_style and obj_props.building_style.was_changed and obj_props.realtime:
                try:
                    obj_props.building_style.apply(obj)
                except Exception as e:
                    traceback.print_exc()
                    obj_props.error = str(e)
                else:
                    obj_props.error = ''
                finally:
                    update_trees.append(obj_props.building_style)
        for tree in update_trees:
            tree.was_changed = False
        BuildingStyleTree.was_changes = False
    return 0.01


@persistent
def update_active_object(scene):
    obj = bpy.context.object

    # change active object event, update tree property of Building tree editors
    try:  # todo also changes of the tree editor type should tracked
        if (prev_obj := scene['active_obj']) != obj:  # todo handle removing objects
            scene['active_obj'] = obj
            if cur_tree := obj.building_props.building_style:
                cur_tree.show_in_areas(True)
            elif prev_tree := prev_obj.building_props.building_style:
                prev_tree.show_in_areas(False)
    except KeyError:
        scene['active_obj'] = obj

    # update active object
    if obj is None:
        return
    obj_props: ObjectProperties = obj.building_props

    if obj.mode == 'EDIT':
        obj['was_in_edit'] = True
        obj_props.apply_style()
    else:
        if 'was_in_edit' in obj:
            del obj['was_in_edit']
            obj_props.apply_style()


def get_node_categories():
    class Base:
        @classmethod
        def poll(cls, context):
            return context.space_data.tree_type == BuildingStyleTree.bl_idname

    category_classes = {c: type(c.name.lower(), (Base, NodeCategory), {}) for c in Categories}
    category_items = {c: [] for c in Categories}
    for node_cls in (c for c in classes if BaseNode in c.__bases__):
        category_items[node_cls.category or Categories.UTILS].append(NodeItem(node_cls.bl_idname))
    return [category_classes[cat](cat.name, cat.name.capitalize().replace('_', ' '), items=category_items[cat])
            for cat in Categories]


def register():
    for cls in classes:
        bpy.utils.register_class(cls)

    nodeitems_utils.register_node_categories('CUSTOM_NODES', get_node_categories())
    bpy.types.Object.building_props = bpy.props.PointerProperty(type=ObjectProperties)
    bpy.app.handlers.depsgraph_update_post.append(update_active_object)
    bpy.app.handlers.load_post.append(update_tree_timer)  # this is hack to store function somewhere
    bpy.app.timers.register(update_tree_timer, persistent=True)
    for tree in (t for t in bpy.data.node_groups if t.bl_idname == BuildingStyleTree.bl_idname):
        tree.update_sockets()  # todo should be used on file loading


def unregister():
    try:
        fun_ind = [f.__name__ for f in bpy.app.handlers.load_post].index(update_tree_timer.__name__)
        fun = bpy.app.handlers.load_post[fun_ind]
    except ValueError:
        pass
    else:
        bpy.app.handlers.load_post.remove(fun)
        bpy.app.timers.unregister(fun)
    try:
        fun_ind = [f.__name__ for f in bpy.app.handlers.depsgraph_update_post].index(update_active_object.__name__)
    except ValueError:
        pass
    else:
        bpy.app.handlers.depsgraph_update_post.remove(bpy.app.handlers.depsgraph_update_post[fun_ind])
    if hasattr(bpy.types.Object, 'building_props'):
        del bpy.types.Object.building_props
    try:
        nodeitems_utils.unregister_node_categories('CUSTOM_NODES')
    except KeyError:
        pass

    for cls in reversed(classes):
        real_cls = cls.__base__.bl_rna_get_subclass_py(cls.__name__)
        if real_cls is not None:  # in case it was not registered yet
            bpy.utils.unregister_class(real_cls)


def _update_colors():
    for tree in (t for t in bpy.data.node_groups if t.bl_idname == BuildingStyleTree.bl_idname):
        for node in tree.nodes:
            if node.category is not None:
                node.use_custom_color = True
                node.color = node.category.color


if __name__ == "__main__":
    unregister()
    register()
    _update_colors()
