import inspect
import random
import sys
import traceback
from collections import namedtuple, defaultdict, deque
from enum import Enum, auto
from graphlib import TopologicalSorter
from itertools import count, chain, cycle, repeat
from math import isclose
from typing import Optional, Iterable, NamedTuple, Type, get_type_hints, Literal, Any

import bmesh
import bpy
import numpy as np
from bmesh.types import BMEdge, BMFace, BMLoop, BMVert
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

            if node.bl_idname == BuildingStyleNode.bl_idname:
                return node.execute(node.gen_input_mapping()(*in_data.values()), base_bm, obj_facade_names)
            else:
                # collect properties
                if node.props_template:
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
            row.label(text=f'{self.user_name or text or self.default_name} (deprecated)')
            row.operator(EditSocketsOperator.bl_idname, text='', icon='REMOVE').operation = 'delete'

        elif hasattr(self, 'value') and not self.is_output and not self.is_linked:
            col = layout.column()
            col.prop(self, 'value', text=(self.user_name or text or self.default_name) if self.show_text else '')

        else:
            layout.label(text=self.user_name or text or self.default_name)

    def draw_color(self, context, node):
        return self.color


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


class BaseNode:
    category: Categories = None
    repeat_last_socket = False
    repeat_first_socket = False
    input_template: tuple[SocketTemplate] = []  # only for static sockets, cause it is used for checking sockets API
    output_template: tuple[SocketTemplate] = []  # only for static sockets, cause it is used for checking sockets API
    props_template: tuple = []

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
    Inputs = namedtuple('Inputs', ['facade', 'facade0', 'facade1', 'facade2'])

    edit_sockets: bpy.props.BoolProperty(name='Edit')

    def node_init(self):
        self.inputs.new(FacadeSocket.bl_idname, "Fill")

    def draw_buttons(self, context, layout):
        layout.prop(self, 'edit_sockets', toggle=1)

    @staticmethod
    def execute(inputs: Inputs, base_bm: bmesh.types.BMesh, obj_facade_names: list[str]):
        build = Building(min(v.co.z for v in base_bm.verts))
        input_ind = {'': 0}
        for i, obj_f_name in enumerate(obj_facade_names, start=1):
            if obj_f_name != '':
                input_ind[obj_f_name] = i

        f_lay = base_bm.faces.layers.string.get(FACE_STYLE_LAYER_NAME) \
                or base_bm.faces.layers.string.new(FACE_STYLE_LAYER_NAME)
        wall_lay = base_bm.faces.layers.int.get("Is wall") or base_bm.faces.layers.int.new("Is wall")

        visited = set()
        for face in base_bm.faces:
            if face in visited:
                continue
            is_vertical = isclose(face.normal.dot(Vector((0, 0, 1))), 0, abs_tol=0.1)
            is_valid = is_vertical and len(face.verts) > 3 and not isclose(face.calc_area(), 0, abs_tol=0.1)
            facade_name = face[f_lay].decode()
            facade_func = inputs[ind] if (ind := input_ind.get(facade_name, 0)) < len(inputs) else inputs[0]
            if is_valid and facade_func:

                face_loops = build.get_floor_polygons(face)
                build.cur_facade = Facade(face_loops)

                for facade_face in build.cur_facade.facade_faces_stack.facade_face_inter(build):
                    visited.add(facade_face.face)
                    build.cur_facade_face = facade_face
                    if facade_func(build):
                        facade_face.face[wall_lay] = 1
                    else:
                        facade_face.face[wall_lay] = 0

            else:
                face[wall_lay] = 0

        return build.bm


class ObjectInputNode(BaseNode, Node):
    bl_idname = 'bn_ObjectInputNode'
    bl_label = "Object Input"

    model: bpy.props.PointerProperty(type=bpy.types.Object)

    def node_init(self):
        self.outputs.new(ObjectSocket.bl_idname, "")

    def draw_buttons(self, context, layout):
        layout.prop(self, 'model')


class PanelNode(BaseNode, Node):
    bl_idname = 'bn_PanelNode'
    bl_label = "Panel"
    category = Categories.PANEL
    Inputs = namedtuple('Inputs', ['object', 'scalable', 'scope_padding', 'probability'])
    Props = namedtuple('Props', ['panel_index'])
    input_template = Inputs(
        SocketTemplate(ObjectSocket),
        SocketTemplate(BoolSocket, 'Scalable', enabled=False),
        SocketTemplate(Vector4Socket, 'Scope padding', enabled=False),
        SocketTemplate(FloatSocket, 'Probability', enabled=False, default_value=1),
    )
    Outputs = namedtuple('Outputs', ['panel'])
    output_template = Outputs(SocketTemplate(PanelSocket))

    mode: bpy.props.EnumProperty(items=[(i, i, '') for i in ['Object', 'Collection']])
    panel_index: bpy.props.IntProperty(description="Penal index in the collection")

    def draw_buttons(self, context, layout):
        row = layout.row(align=True)
        row.prop(self, "mode", expand=True)
        row.menu(ShowSocketsMenu.bl_idname, text='', icon='DOWNARROW_HLT')

    def draw_label(self):
        obj_socket = self.get_socket('object', is_input=True)
        return obj_socket.value and obj_socket.value.name or self.bl_label

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        size_v_catch = None

        def panel_gen(build: Building):
            # panel is expected to be in XY orientation
            nonlocal size_v_catch
            if size_v_catch is None:
                obj = inputs.object(build)
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
            panel.probability = inputs.probability(build)
            panel.set_scope_padding(inputs.scope_padding(build))  # for now it works only as scale
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
        def panel_index(build: Building):
            return build.cur_facade.cur_panel_ind
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


class PanelRandomizePropsOperator(Operator):
    bl_idname = "bn.panel_randomize_props"
    bl_label = "Edit the node options"
    bl_options = {'INTERNAL', }

    # internal usage
    tree_name: StringProperty()
    node_name: StringProperty()

    def execute(self, context):
        return {'FINISHED'}

    def invoke(self, context, event):
        node = context.node
        self.tree_name = node.id_data.name
        self.node_name = node.name
        panel_names = []
        for search_node in node.id_data.walk_back(node):
            if search_node.bl_idname == PanelNode.bl_idname:
                panel_names.append(search_node.name)
        node['panel_names'] = panel_names
        wm = context.window_manager
        return wm.invoke_props_dialog(self)

    def draw(self, context):
        tree = bpy.data.node_groups[self.tree_name]
        node = tree.nodes[self.node_name]  # todo https://developer.blender.org/T92835
        col = self.layout.column()
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
    Inputs = namedtuple('Inputs', ['seed', 'panel0', 'panel1', 'panel2', 'panel3'])

    def node_init(self):
        self.inputs.new(IntSocket.bl_idname, "Seed").display_shape = 'DIAMOND_DOT'
        self.inputs.new(PanelSocket.bl_idname, "")
        self.outputs.new(PanelSocket.bl_idname, "")

    def draw_buttons(self, context, layout):
        layout.operator(PanelRandomizePropsOperator.bl_idname, text='Settings', icon='PREFERENCES')

    @staticmethod
    def execute(inputs: Inputs, params):
        random_streams = dict()

        def randomize_panels(build: Building):
            stream = random_streams.get(build.cur_facade.cur_floor_ind)
            if stream is None:
                stream = random.Random(int(inputs.seed(build)))
                random_streams[build.cur_facade.cur_floor_ind] = stream
            panels = [p for inp in inputs[1: -1] if (p := inp(build)) is not None]
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


class FloorPatternNode(BaseNode, Node):
    bl_idname = 'bn_FloorPatternNode'
    bl_label = "Floor Pattern"
    category = Categories.FLOOR
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

    def draw_buttons(self, context, layout):
        layout.menu(ShowSocketsMenu.bl_idname, text='Show sockets')

    @classmethod
    def execute(cls, inputs: Inputs, props: Props):
        def floor_gen(build: Building, precompute=False):
            if precompute:
                floor = Floor(build.cur_facade.cur_floor_ind)
                floor.height = inputs.height(build)
                return floor

            floor = Floor(build.cur_facade.cur_floor_ind)
            build.cur_floor = floor
            pan_stack = floor.panels_stack
            if "LEFT" in build.cur_facade_face.position and inputs.left:
                pan_stack.add_panel(build, inputs.left, 'LEFT')
            if 'RIGHT' in build.cur_facade_face.position and inputs.right:
                pan_stack.add_panel(build, inputs.right, 'RIGHT')
            if inputs.fill and not pan_stack.is_full(build):
                for i in range(1000):
                    panel = None
                    for _ in range(10):
                        panel = pan_stack.add_panel(build, inputs.fill)
                        if panel:
                            break
                    if panel is None or pan_stack.is_full(build):
                        break

            if pan_stack.has_panels:
                if props.use_height:
                    floor.height = inputs.height(build)
                else:
                    floor.height = max((p.size.y for p in pan_stack.all_panels), default=0)
                pan_stack.update_location_scale(build)
                return floor
            else:
                return None
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
        def floor_width(build: Building):
            return build.cur_facade.size.x

        def floor_height(build: Building):
            return None

        def floor_index(build: Building):
            build.depth.add('floor_index')
            return build.cur_facade.cur_floor_ind

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
        last_facade_face = None

        def switch_floor(build: Building, precompute=False):
            if precompute:
                if inputs.bool(build):
                    if inputs.true_floor is not None:
                        return inputs.true_floor(build, precompute=precompute)
                else:
                    if inputs.false_floor is not None:
                        return inputs.false_floor(build, precompute=precompute)

            if inputs.bool is None:
                return
            nonlocal last_facade_face
            if build.cur_facade_face != last_facade_face:  # the catch should exist per facade face
                last_facade_face = build.cur_facade_face
                catch.clear()
                depth.clear()
            switch_state = None
            if inputs.bool not in catch:
                build.depth.clear()
                switch_state = inputs.bool(build)
                catch[inputs.bool] = None if build.depth else switch_state
                depth.update(build.depth)
            return_true = switch_state or catch[inputs.bool] or inputs.bool(build)
            if return_true:
                if inputs.true_floor:
                    true_floor = None
                    if inputs.true_floor not in catch:
                        build.depth.clear()
                        true_floor = inputs.true_floor(build)
                        catch[inputs.true_floor] = None if build.depth else true_floor
                        depth.update(build.depth)
                    build.depth = depth.copy()
                    floor = true_floor or catch[inputs.true_floor] or inputs.true_floor(build)
                    return floor
            else:
                if inputs.false_floor:
                    false_floor = None
                    if inputs.false_floor not in catch:
                        build.depth.clear()
                        false_floor = inputs.false_floor(build)
                        catch[inputs.false_floor] = None if build.depth else false_floor
                        depth.update(build.depth)
                    build.depth = depth.copy()
                    floor = false_floor or catch[inputs.false_floor] or inputs.false_floor(build)
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
        def facade_generator(build: Building):
            facade_face = build.cur_facade_face
            floors_stack = facade_face.floors_stack
            # searching first floor index
            if floors_stack.first_index is None:
                is_fill_fixed = False
                floors_stack.first_index = 0
                start_height = facade_face.start.z - build.start_level
                if not isclose(start_height, 0, abs_tol=0.1):
                    if inputs.first:
                        floors_stack.add_floor(build, inputs.first, mockup=True)
                    if inputs.fill:
                        for i in range(10000):
                            if floors_stack.is_full(start_height):
                                break
                            if not is_fill_fixed:
                                floor = None
                                for _ in range(10):
                                    floor = floors_stack.add_floor(build, inputs.fill, mockup=True)
                                    if floor:
                                        break
                                if floor is None:
                                    break
                                is_fill_fixed = not build.depth
                            else:
                                floors_stack.repeat_last()
                    start_index = len(floors_stack.floors)
                    floors_stack.clear(start_index)

            # generate floors
            is_fill_fixed = False
            if inputs.first and floors_stack.first_index == 0:
                floors_stack.add_floor(build, inputs.first)
            if inputs.fill:
                for i in range(10000):
                    if inputs.last and 'TOP' in build.cur_facade_face.position:
                        if floors_stack.will_be_last_floor(build, inputs.last, build.cur_facade.size.y):
                            floors_stack.add_floor(build, inputs.last)
                            break
                    else:
                        if floors_stack.is_full(build.cur_facade.size.y):
                            break

                    if not is_fill_fixed:
                        floor = None
                        for _ in range(10):
                            floor = floors_stack.add_floor(build, inputs.fill)
                            if floor:
                                break
                        if floor is None:
                            break
                        is_fill_fixed = not build.depth
                    else:
                        floors_stack.repeat_last()
            elif inputs.last and 'TOP' in build.cur_facade_face.position\
                    and not floors_stack.is_full(build.cur_facade.size.y):
                floors_stack.add_floor(build, inputs.last)

            if facade_face:
                floors_stack.instance_floors(build, inputs.fill or floors_stack.is_full(build.cur_facade.size.y))
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

        def material_id(build: Building):
            return build.cur_facade_face.material_ind
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
        def get_facade_item(build: Building):
            facade_funcs = {i: f for i, f in enumerate(inputs[1:])}
            facade_f = facade_funcs.get(inputs.index(build))
            if facade_f:
                return facade_f(build)

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
        node2 = tree.nodes.new(FloorPatternNode.bl_idname)
        node3 = tree.nodes.new(FacadePatternNode.bl_idname)
        node4 = tree.nodes.new(BuildingStyleNode.bl_idname)
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
            center = Geometry(points).get_bounding_center()
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


class Panel:
    def __init__(self, obj_index: int, size: Vector):
        # panel is expected to be in XY orientation
        self.obj_index = obj_index  # index of object in the collection
        self.size: Vector = size
        self.location: Vector = None
        self.scale: Vector = Vector((1, 1))

        self.probability = 1

    @property
    def instance_size(self) -> Vector:
        return self.size * self.scale

    def set_scope_padding(self, padding):
        self.size.x += padding[0] + padding[2]
        self.size.y += padding[1] + padding[3]

    def instance(self, build, floor_level: float, floor_scale: float):
        facade_face = build.cur_facade_face
        vec = build.bm.verts.new(self.location + Vector((0, 0, floor_level)))
        vec[build.norm_lay] = facade_face.normal
        vec[build.scale_lay] = (self.scale.x, self.scale.y * floor_scale, 1)
        vec[build.ind_lay] = self.obj_index

    def __repr__(self):
        return f"<Panel:{self.obj_index}, loc=({self.location.x:.2f}, {self.location.y:.2f})>"


class PanelsStack:
    def __init__(self):
        self._left_panel = []
        self._panels = []
        self._right_panel = []
        self._stack_width = 0

    def add_panel(self, build, panel_f, p_type: Literal['LEFT', 'FILL', 'RIGHT'] = 'FILL'):
        build.cur_facade.cur_panel_ind = len(self._panels) if p_type == 'FILL' else 0
        panel: Panel = panel_f(build)
        self._stack_width += panel and panel.size.x or 0
        if p_type == 'FILL':
            self._panels.append(panel)
        elif p_type == 'LEFT':
            self._left_panel.append(panel)
        elif p_type == 'RIGHT':
            self._right_panel.append(panel)
        return panel

    def is_full(self, build):
        return self._stack_width > build.cur_facade_face.size.x

    def update_location_scale(self, build):
        if not self.has_panels:
            return
        facade_face = build.cur_facade_face
        xy_scale = build.cur_facade_face.size.x / self._stack_width
        xy_shift = 0
        for panel in (p for p in self.all_panels if p):
            z_scale = build.cur_floor.height / panel.size.y
            panel.scale *= Vector((xy_scale, z_scale))
            size = panel.instance_size.x
            xy_shift += size / 2
            panel.location = facade_face.start + facade_face.direction * xy_shift
            xy_shift += size / 2

    @property
    def has_panels(self) -> bool:
        return any(self.all_panels)

    @property
    def all_panels(self) -> Iterable[Panel]:
        return (p for p in chain(self._left_panel, self._panels, self._right_panel) if p is not None)

    def __repr__(self):
        str_panels = ', '.join(str(p) for p in chain([self._left_panel], self._panels, [self._right_panel]) if p)
        return f"[{str_panels}]"


class Floor:
    def __init__(self, index=None):
        self.index = index
        self.height = None
        self.z_level = None
        self.z_scale = None
        self.panels_stack: PanelsStack = PanelsStack()

    def instance_panels(self, build):
        for panel in self.panels_stack.all_panels:
            panel.instance(build, self.z_level, self.z_scale)

    def __repr__(self):
        return f"<Floor i={self.index}, {self.panels_stack}>"


class FloorsStack:
    def __init__(self, first_index=None):
        self.floors: list[Optional[Floor]] = []
        self._current_height = 0
        self._last_ind = first_index

    def clear(self, new_first_index=None):
        self.floors.clear()
        self._current_height = 0
        self._last_ind = new_first_index

    @property
    def first_index(self):
        return self._last_ind

    @first_index.setter
    def first_index(self, value):
        self._last_ind = value

    def add_floor(self, build, floor_f, mockup=False) -> Optional[Floor]:
        build.cur_facade.cur_floor_ind = self._last_ind
        floor = floor_f(build, precompute=mockup)
        self.floors.append(floor)
        self._last_ind += 1
        self._current_height += floor.height if floor else 0
        return floor

    def repeat_last(self):
        self.floors.append(self.floors[-1])
        self._current_height += last_floor.height if (last_floor := self.floors[-1]) else 0
        self._last_ind += 1

    def will_be_last_floor(self, build, floor_f, height) -> Optional[bool]:
        build.cur_facade.cur_floor_ind = self._last_ind
        floor = floor_f(build, precompute=True)
        return height < (self._current_height + (floor and floor.height or 0))

    def is_full(self, height: float):
        return height < self._current_height

    def instance_floors(self, build, is_to_scale):
        z_scale = (build.cur_facade_face.size.y / self._current_height) if self._current_height and is_to_scale else 1
        real_floors_height = 0
        for floor in self.floors:
            if not floor:
                continue
            height = floor.height * z_scale
            floor.z_level = real_floors_height + height / 2
            floor.z_scale = z_scale
            floor.instance_panels(build)
            real_floors_height += height

    def __repr__(self):
        floors = '\n'.join(repr(f) for f in reversed(self.floors))
        return f"[{floors}]"


class FacadeFace:
    def __init__(self, left_loop, right_loop, pos: set[Literal['LEFT', 'RIGHT', 'TOP']], template: 'FacadeFace' = None):
        dist_vec = right_loop.vert.co - left_loop.vert.co
        xy_size = (dist_vec * Vector((1, 1, 0))).length

        self.size: Vector = Vector((xy_size, dist_vec.z))
        self.start: Vector = left_loop.vert.co
        self.direction: Vector = (dist_vec * Vector((1, 1, 0))).normalized()
        self.normal: Vector = left_loop.face.normal
        self.material_ind: int = left_loop.face.material_index
        first_index = template.floors_stack.floors[0].index if template is not None and template.floors_stack.floors else None
        self.floors_stack: FloorsStack = FloorsStack(first_index)
        self.position: set[Literal['LEFT', 'RIGHT', 'TOP']] = pos
        self.template_floors = template
        self.face: BMFace = left_loop.face

        self.azimuth = None

    def __repr__(self):
        return f"<FFace {self.floors_stack}>"

    def __bool__(self):
        return bool(self.floors_stack.floors)


class FacadeFacesStack:
    def __init__(self, face_loops: list[tuple[BMLoop, BMLoop]]):
        self._corner_loops_stack: list[tuple[BMLoop, BMLoop]] = face_loops
        self._size: Vector = None

    @property
    def size(self) -> Vector:
        if self._size is None:
            xy_size = sum(((lr.vert.co - ll.vert.co) * Vector((1, 1, 0))).length for ll, lr in self._corner_loops_stack)
            first_ll, first_lr = self._corner_loops_stack[0]
            z_size = (first_lr.vert.co - first_ll.vert.co).z
            size = Vector((xy_size, z_size))
            self._size = size
        return self._size

    def facade_face_inter(self, build) -> Iterable[FacadeFace]:
        positions = chain(['LEFT'], repeat(None, len(self._corner_loops_stack) - 2), ['RIGHT'])
        prev_face = None
        for (left_loop, right_loop), pos in zip(self._corner_loops_stack, positions):
            pos = {pos} if pos else set()
            if right_loop.edge.calc_face_angle(3.14) > 0.17:  # 10 degrees
                pos.add('TOP')
            facade_face = FacadeFace(left_loop, right_loop, pos, prev_face)
            build.cur_facade_face = facade_face
            yield facade_face
            prev_face = facade_face


class Facade:
    def __init__(self, face_loops: list[tuple[BMLoop, BMLoop]]):
        self.cur_floor_ind = None
        self.cur_panel_ind = None
        self.facade_faces_stack: FacadeFacesStack = FacadeFacesStack(face_loops)

        self.left_wall_angle = face_loops[0][0].link_loop_prev.edge.calc_face_angle(3.14)
        self.right_wall_angle = face_loops[-1][1].link_loop_prev.edge.calc_face_angle(3.14)

    @property
    def size(self) -> Vector:
        return self.facade_faces_stack.size


class Building:
    def __init__(self, start_level: float):
        bm = bmesh.new()
        self.norm_lay = bm.verts.layers.float_vector.new("Normal")
        self.scale_lay = bm.verts.layers.float_vector.new("Scale")
        self.ind_lay = bm.verts.layers.int.new("Wall index")
        self.bm: bmesh.types.BMesh = bm
        self.start_level: float = start_level

        self.cur_facade: Facade = None
        self.cur_facade_face: FacadeFace = None
        self.cur_floor: Floor = None

        self.depth: set[Literal['floor_index']] = set()

    @staticmethod
    def calc_azimuth(vec: Vector):
        vec = vec.normalized()
        north = Vector((0, 1, 0))
        is_right = vec.cross(north).normalized().z < 0
        return vec @ north + 3 if is_right else 1 - vec @ north

    @staticmethod
    def get_floor_polygons(base_face) -> deque[tuple[BMLoop, BMLoop]]:
        visited: set[BMFace] = {base_face}  # protection from infinite mesh loop
        mesh_loop: deque[tuple[BMLoop, BMLoop]] = deque()
        left_loop, right_loop = Geometry.left_right_loops(base_face)
        if len(base_face.verts) == 4:
            mesh_loop.append((left_loop.link_loop_next, left_loop.link_loop_prev))
        else:
            mesh_loop.append(Geometry.get_bounding_loops(base_face))
        # if faces are coplanar the angle is zero, with signed version the angle has `-` if angle is inside
        if left_loop and isclose(left_loop.edge.calc_face_angle(3.14), 0, abs_tol=0.17):  # 10 degrees
            for next_left_loop in Geometry.mesh_loop_walk(left_loop):
                face = next_left_loop.face
                if face not in visited:
                    visited.add(face)
                else:
                    break
                mesh_loop.appendleft((next_left_loop.link_loop_next, next_left_loop.link_loop_prev))
                if not isclose(next_left_loop.edge.calc_face_angle(3.14), 0, abs_tol=0.17):
                    break
        if right_loop and isclose(right_loop.edge.calc_face_angle(3.14), 0, abs_tol=0.17):
            for next_right_loop in Geometry.mesh_loop_walk(right_loop):
                face = next_right_loop.face
                if face not in visited:
                    visited.add(face)
                else:
                    break
                mesh_loop.append((next_right_loop.link_loop_prev, next_right_loop.link_loop_next))
                if not isclose(next_right_loop.edge.calc_face_angle(3.14), 0, abs_tol=0.17):
                    break
        return mesh_loop


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
    def __init__(self, verts: list = None):
        self.verts = verts

    def get_bounding_verts(self) -> tuple[Vector, Vector]:  # min, max
        min_v = Vector((min(v.co.x for v in self.verts), min(v.co.y for v in self.verts),
                        min(v.co.z for v in self.verts)))
        max_v = Vector((max(v.co.x for v in self.verts), max(v.co.y for v in self.verts),
                        max(v.co.z for v in self.verts)))
        return min_v, max_v

    def get_bounding_center(self) -> Vector:
        min_v, max_v = self.get_bounding_verts()
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
    def connected_coplanar_faces(start_face: BMFace) -> CentredMeshGrid:
        def is_radial_face_valid(n_loop) -> bool:
            _current_face = n_loop.face
            _next_face = n_loop.link_loop_radial_next.face
            if _next_face == face or _next_face in visited:  # last condition does not protect entirely
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
                left_next = right_loop.link_loop_next.link_loop_radial_next.link_loop_next
                right_next = left_next.link_loop_next.link_loop_next
                next_faces.append(((left_next, right_next), pos + Vector((-1, 0))))
        gr.clean_grid()
        return gr


def update_tree_timer():
    if BuildingStyleTree.was_changes:
        update_trees = []
        for obj in bpy.data.objects:
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