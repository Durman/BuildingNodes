import inspect
import random
import sys
import traceback
from collections import namedtuple, defaultdict, deque
from enum import Enum, auto
from graphlib import TopologicalSorter
from itertools import count, chain, cycle
from math import isclose
from typing import Optional, Iterable, NamedTuple, Type, get_type_hints, Literal, Any

import bmesh
import bpy
from bmesh.types import BMEdge, BMFace, BMLoop, BMVert
from bpy.app.handlers import persistent
from bpy.types import NodeTree, Node, NodeSocket, Panel, Operator, PropertyGroup, Menu
import nodeitems_utils
from mathutils import Vector
from nodeitems_utils import NodeCategory, NodeItem


class FacadeTreeNames(PropertyGroup):
    identifier: bpy.props.StringProperty()
    user_name: bpy.props.StringProperty()


class BuildingGenerator(NodeTree):
    bl_idname = 'BuildingGenerator'
    bl_label = "Building Generator"
    bl_icon = 'NODETREE'
    was_changes = False  # flag to timer

    inst_col: bpy.props.PointerProperty(type=bpy.types.Collection, description="Keep all panels to be instanced")
    was_changed: bpy.props.BoolProperty(description="If True the tree should be reevaluated")
    facade_names: bpy.props.CollectionProperty(type=FacadeTreeNames)

    def update(self):
        BuildingGenerator.was_changes = True
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
            in_data = []
            for from_sock, to_sock in zip(prev_socks, node.inputs):
                if from_sock is not None:
                    in_data.append(sock_data[from_sock])
                elif hasattr(to_sock, 'value'):
                    def sock_value(build, *, _value=to_sock.value):
                        return _value
                    in_data.append(sock_value)
                else:
                    in_data.append(None)

            if node.bl_idname == FacadeInstanceNode.bl_idname:
                return node.execute(node.gen_input_mapping()(*in_data), base_bm, obj_facade_names)
            else:
                if hasattr(node, 'Props'):
                    props = node.Props(*[getattr(node, n) for n in node.Props._fields])
                else:
                    props = None
                res = node.execute(Inp(*in_data) if (Inp := node.gen_input_mapping()) is not None else None, props)
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
                if node.inputs[0].value is not None:
                    try:
                        self.inst_col.objects.link(node.inputs[0].value)
                    except RuntimeError:
                        pass  # Already was linked

        # let panels know their indexes
        obj_index = {obj: i for i, obj in enumerate(sorted(self.inst_col.objects, key=lambda o: o.name))}
        for node in self.nodes:
            if node.bl_idname == PanelNode.bl_idname and node.inputs[0].value:
                node.panel_index = obj_index[node.inputs[0].value]

        return self.inst_col

    def walk(self):
        node_graph = defaultdict(set)
        prev_sock = dict()
        for link in self.links:
            node_graph[link.to_node].add(link.from_node)
            prev_sock[link.to_socket] = link.from_socket
        for node in TopologicalSorter(node_graph).static_order():
            yield node, [prev_sock[s] if s in prev_sock else None for s in node.inputs]

    def update_facade_names(self):
        # todo make interface of all output nodes equal
        for node in self.nodes:
            if node.bl_idname == FacadeInstanceNode.bl_idname:
                self.facade_names.clear()
                for socket in node.inputs[1:]:
                    sock_names: FacadeTreeNames = self.facade_names.add()
                    sock_names.identifier = socket.identifier
                    sock_names.user_name = socket.user_name or socket.default_name

    def update_sockets(self):
        """Supports only adding sockets to the end of input output collections"""
        for node in self.nodes:
            for sock, template in zip(chain(node.inputs, [None]), node.input_template):
                if sock is None:
                    template.init(node, is_input=True)
            for sock, template in zip(chain(node.outputs, [None]), node.output_template):
                if sock is None:
                    template.init(node, is_input=False)

    def show_in_areas(self, is_to_show):
        for area in bpy.context.screen.areas:
            if area.ui_type == BuildingGenerator.bl_idname:
                area.spaces[0].node_tree = self if is_to_show else None


class BaseSocket:
    show_text = True
    user_name: bpy.props.StringProperty(description="Socket name given by user")  # todo tag redraw

    def update_value(self, context):
        self.id_data.update()  # https://developer.blender.org/T92635

    def draw(self, context, layout, node, text):
        if hasattr(self, 'value') and not self.is_output and not self.is_linked:
            col = layout.column()
            col.prop(self, 'value', text=(self.user_name or text or self.default_name) if self.show_text else '')
        else:
            layout.label(text=self.user_name or text or self.default_name)

    def draw_color(self, context, node):
        return self.color


class FacadeSocket(BaseSocket, NodeSocket):
    bl_idname = 'FacadeSocket'
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
    bl_idname = 'FloorSocket'
    bl_label = "Floor Socket"
    color = 0.35, 0.35, 1.0, 1.0
    default_name = 'Floor'


class PanelSocket(BaseSocket, NodeSocket):
    bl_idname = 'PanelSocket'
    bl_label = "Panel Socket"
    color = 0.0, 0.8, 0.8, 1.0
    default_name = 'Panel'


class FloatSocket(BaseSocket, NodeSocket):
    bl_idname = 'FloatSocket'
    bl_label = "Float Socket"
    color = 0.5, 0.5, 0.5, 1.0
    default_name = 'Float'
    value: bpy.props.FloatProperty(update=BaseSocket.update_value)


class ObjectSocket(BaseSocket, NodeSocket):
    bl_idname = 'ObjectSocket'
    bl_label = "Object Socket"
    default_name = 'Object'
    color = 1.0, 0.6, 0.45, 1.0
    show_text = False

    def poll_objects(self, obj):
        if obj.type != 'MESH':
            return False
        props: ObjectProperties = obj.building_props
        if props.facade_style == self.id_data:  # object can't be instanced inside itself
            return False
        scl_attr, wal_attr = obj.data.attributes.get('Scale'), obj.data.attributes.get('Wall index')
        if obj.name.split('.')[0] == 'Points' and scl_attr and wal_attr:  # most likely it's helper object
            return False
        return True

    value: bpy.props.PointerProperty(type=bpy.types.Object, update=BaseSocket.update_value, poll=poll_objects)


class IntSocket(BaseSocket, NodeSocket):
    bl_idname = 'IntSocket'
    bl_label = "Int Socket"
    color = 0.0, 0.6, 0.0, 1.0
    default_name = 'Integer'
    value: bpy.props.IntProperty(update=BaseSocket.update_value)


class StringSocket(BaseSocket, NodeSocket):
    bl_idname = 'StringSocket'
    bl_label = "String Socket"
    color = 0.4, 0.6, 0.8, 1.0
    default_name = 'String'
    value: bpy.props.StringProperty(update=BaseSocket.update_value)


class BoolSocket(BaseSocket, NodeSocket):
    bl_idname = 'BoolSocket'
    bl_label = "Bool Socket"
    default_name = 'Bool'
    color = 0.75, 0.55, 0.75, 1.0
    value: bpy.props.BoolProperty(update=BaseSocket.update_value)


class VectorSocket(BaseSocket, NodeSocket):
    bl_idname = 'VectorSocket'
    bl_label = "Vector Socket"
    default_name = 'Vector'
    color = 0.4, 0.3, 0.7, 1.0
    value: bpy.props.FloatVectorProperty(update=BaseSocket.update_value)


class Vector4Socket(BaseSocket, NodeSocket):
    bl_idname = 'Vector4Socket'
    bl_label = "Vector 4 Socket"
    default_name = 'Vector4'
    color = 0.4, 0.3, 0.7, 1.0
    value: bpy.props.FloatVectorProperty(update=BaseSocket.update_value, size=4)


class Categories(Enum):
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
                col.prop(sock, 'enabled', text=(sock.name or sock.default_name) + ' (connected)', emboss=False)
            else:
                col = self.layout.column()
                col.prop(sock, 'enabled', text=sock.name or sock.default_name)


class SocketTemplate(NamedTuple):
    type: NodeSocket
    name: str = ''
    enabled: bool = True
    display_shape: Literal['CIRCLE', 'SQUARE', 'DIAMOND', 'CIRCLE_DOT', 'SQUARE_DOT', 'DIAMOND_DOT'] = None
    value: Any = None

    def init(self, node: Node, is_input):
        node_sockets = node.inputs if is_input else node.outputs
        sock = node_sockets.new(self.type.bl_idname, self.name)
        if not self.enabled:
            sock.enabled = False
        if self.display_shape:
            sock.display_shape = self.display_shape
        if self.value is not None:
            sock.value = self.value


class BaseNode:
    category: Categories = None
    repeat_last_socket = False
    repeat_first_socket = False
    input_template: tuple[SocketTemplate] = []  # only for static sockets, cause it is used for checking sockets API
    output_template: tuple[SocketTemplate] = []  # only for static sockets, cause it is used for checking sockets API

    @classmethod
    def poll(cls, tree):
        return tree.bl_idname == BuildingGenerator.bl_idname

    def init(self, context):
        # update node colors
        if self.category is not None:
            self.use_custom_color = True
            self.color = self.category.color
        # create sockets
        for s_template in self.input_template:
            s_template.init(self, is_input=True)
        for s_template in self.output_template:
            s_template.init(self, is_input=False)

        self.node_init()

    def node_init(self):
        pass

    def update(self):
        # update sockets
        if self.repeat_last_socket:
            sock_id_name = self.inputs[-1].bl_idname
            if self.inputs[-1].is_linked:
                self.inputs.new(sock_id_name, "")
            for socket in list(self.inputs)[-2::-1]:
                if socket.bl_idname == self.inputs[-1].bl_idname and not socket.is_linked:
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
        input_names = []
        index = count()
        if self.repeat_last_socket or self.bl_idname == FacadeInstanceNode.bl_idname:
            for sock in self.inputs:
                inp_name = sock.name or sock.default_name + str(next(index))
                input_names.append(inp_name.lower().replace(' ', '_'))
        elif hasattr(self, 'Inputs'):
            return self.Inputs
        return namedtuple('Inputs', input_names) if input_names else None


class FacadeInstanceNode(BaseNode, Node):
    bl_idname = 'FacadeInstanceNode'
    bl_label = "Facade Instance"
    category = Categories.FACADE
    Inputs = namedtuple('Inputs', ['fill', 'facade0', 'facade1', 'facade2'])

    edit_sockets: bpy.props.BoolProperty(name='Edit')

    def node_init(self):
        self.inputs.new(FacadeSocket.bl_idname, "Fill")

    def draw_buttons(self, context, layout):
        layout.prop(self, 'edit_sockets', toggle=1)

    @staticmethod
    def execute(inputs: Inputs, base_bm: bmesh.types.BMesh, obj_facade_names: list[str]):
        build = Building()
        input_ind = {'': 0}
        for i, obj_f_name in enumerate(obj_facade_names, start=1):
            if obj_f_name != '':
                input_ind[obj_f_name] = i

        f_lay = base_bm.faces.layers.string.get('Facade name') or base_bm.faces.layers.string.new('Facade name')
        wall_lay = base_bm.faces.layers.int.get("Is wall") or base_bm.faces.layers.int.new("Is wall")

        for face in base_bm.faces:
            is_vertical = isclose(face.normal.dot(Vector((0, 0, 1))), 0, abs_tol=0.1)
            is_valid = is_vertical and len(face.verts) > 3 and not isclose(face.calc_area(), 0, abs_tol=0.1)
            facade_name = face[f_lay].decode()
            facade_func = inputs[ind] if (ind := input_ind.get(facade_name, 0)) < len(inputs) else inputs[0]
            if is_valid and facade_func:
                face[wall_lay] = 1
                build.cur_facade = Facade(face)
                facade_func(build)
            else:
                face[wall_lay] = 0
        return build.bm


class ObjectInputNode(BaseNode, Node):
    bl_idname = 'ObjectInputNode'
    bl_label = "Object Input"

    model: bpy.props.PointerProperty(type=bpy.types.Object)

    def node_init(self):
        self.outputs.new(ObjectSocket.bl_idname, "")

    def draw_buttons(self, context, layout):
        layout.prop(self, 'model')


class PanelNode(BaseNode, Node):
    bl_idname = 'PanelNode'
    bl_label = "Panel"
    category = Categories.PANEL
    Inputs = namedtuple('Inputs', ['object', 'scalable', 'scope_padding'])
    Props = namedtuple('Props', ['panel_index'])
    input_template = Inputs(
        SocketTemplate(ObjectSocket),
        SocketTemplate(BoolSocket, 'Scalable', enabled=False),
        SocketTemplate(Vector4Socket, 'Scope padding', enabled=False),
    )
    output_template = [SocketTemplate(PanelSocket)]

    mode: bpy.props.EnumProperty(items=[(i, i, '') for i in ['Object', 'Collection']])
    panel_index: bpy.props.IntProperty(description="Penal index in the collection")

    def draw_buttons(self, context, layout):
        row = layout.row(align=True)
        row.prop(self, "mode", expand=True)
        row.menu(ShowSocketsMenu.bl_idname, text='', icon='DOWNARROW_HLT')

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        def panel_gen(build: Building):
            # panel is expected to be in XY orientation
            obj = inputs.object(build)
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
            panel = Panel(props.panel_index, max_v - min_v)
            panel.set_scope_padding(inputs.scope_padding(build))  # for now it works only as scale
            return panel
        return panel_gen


class PanelAttributesNode(BaseNode, Node):
    bl_idname = 'PanelAttributesNode'
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
    bl_idname = 'SetPanelAttributeNode'
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


class PanelRandomizeNode(BaseNode, Node):
    bl_idname = 'PanelRandomizeNode'
    bl_label = "Panel Randomize"
    category = Categories.PANEL
    repeat_last_socket = True
    Inputs = namedtuple('Inputs', ['seed', 'panel0', 'panel1', 'panel2', 'panel3'])

    def node_init(self):
        self.inputs.new(IntSocket.bl_idname, "Seed").display_shape = 'DIAMOND_DOT'
        self.inputs.new(PanelSocket.bl_idname, "")
        self.outputs.new(PanelSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, params):
        random_streams = dict()

        def randomize_panels(build: Building):
            seed = int(inputs.seed(build))
            rand_stream = random_streams.get(seed)
            if rand_stream is None:
                rand_stream = random.Random(seed)
                random_streams[seed] = rand_stream
            panels = [inp(build) for inp in inputs[1: -1]]
            return rand_stream.choices(panels, weights=[p.probability for p in panels])[0]
        return randomize_panels


class PanelSwitchNode(BaseNode, Node):
    bl_idname = 'PanelSwitchNode'
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
    bl_idname = 'StackPanelsNode'
    bl_label = "Stack Panels Node"
    category = Categories.PANEL
    repeat_last_socket = True

    def node_init(self):
        self.inputs.new(PanelSocket.bl_idname, "")
        self.outputs.new(PanelSocket.bl_idname, "")


class FloorPatternNode(BaseNode, Node):
    bl_idname = 'FloorPatternNode'
    bl_label = "Floor Pattern"
    category = Categories.FLOOR
    Inputs = namedtuple('Inputs', ['height', 'left', 'fill', 'distribute', 'right'])

    def node_init(self):
        s = self.inputs.new(FloatSocket.bl_idname, "Height")
        s.value = 3
        s.display_shape = 'DIAMOND_DOT'
        self.inputs.new(PanelSocket.bl_idname, "Left")
        self.inputs.new(PanelSocket.bl_idname, "Fill")
        self.inputs.new(PanelSocket.bl_idname, "Distribute")
        self.inputs.new(PanelSocket.bl_idname, "Right")
        self.outputs.new(FloorSocket.bl_idname, "")

    @classmethod
    def execute(cls, inputs: Inputs, params):
        def floor_gen(build: Building, precompute=False):
            if precompute:
                build.cur_floor.height = inputs.height(build)
                return

            build.cur_floor.height = inputs.height(build)
            pan_stack = build.cur_floor.panels_stack
            if inputs.left:
                pan_stack.add_panel(build, inputs.left, 'LEFT')
            if inputs.right:
                pan_stack.add_panel(build, inputs.right, 'RIGHT')
            if not pan_stack.is_full(build):
                for i in range(10000):
                    pan_stack.add_panel(build, inputs.fill)
                    if pan_stack.is_full(build):
                        break

            pan_stack.update_location_scale(build)
        return floor_gen


class FloorAttributesNode(BaseNode, Node):
    bl_idname = 'FloorAttributesNode'
    bl_label = "Floor Attributes"
    category = Categories.FLOOR

    def node_init(self):
        self.outputs.new(FloatSocket.bl_idname, "Width").display_shape = 'DIAMOND'
        self.outputs.new(FloatSocket.bl_idname, "Height").display_shape = 'DIAMOND'
        self.outputs.new(IntSocket.bl_idname, "Number").display_shape = 'DIAMOND'
        self.outputs.new(FloatSocket.bl_idname, "Left corner angle").display_shape = 'DIAMOND'
        self.outputs.new(FloatSocket.bl_idname, "Right corner angle").display_shape = 'DIAMOND'
        self.outputs.new(FloatSocket.bl_idname, "Azimuth").display_shape = 'DIAMOND'

    @staticmethod
    def execute(inputs, props):
        def floor_width(build: Building):
            return build.cur_facade.width

        def floor_height(build: Building):
            return None

        def floor_index(build: Building):
            build.cur_floor.depth.add('floor_index')
            return build.cur_floor.index

        def left_corner_angle(build: Building):
            return build.cur_facade.left_wall_angle

        def right_corner_angle(build: Building):
            return build.cur_facade.right_wall_angle

        def azimuth(build: Building):
            return build.cur_facade.azimuth
        return floor_width, floor_height, floor_index, left_corner_angle, right_corner_angle, azimuth


class FloorSwitchNode(BaseNode, Node):
    bl_idname = 'FloorSwitchNode'
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
        def switch_floor(build, precompute=False):
            if inputs.bool(build):
                if inputs.true_floor is not None:
                    inputs.true_floor(build, precompute=precompute)
            else:
                if inputs.false_floor is not None:
                    inputs.false_floor(build, precompute=precompute)
        return switch_floor


class StackFloorsNode(BaseNode, Node):
    bl_idname = 'StackFloorsNode'
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
    bl_idname = 'FacadePatternNode'
    bl_label = "Facade Pattern"
    category = Categories.FACADE
    Inputs = namedtuple('Inputs', ['last', 'fill', 'distribute', 'first'])

    def node_init(self):
        self.inputs.new(FloorSocket.bl_idname, "Last")
        self.inputs.new(FloorSocket.bl_idname, "Fill")
        self.inputs.new(FloorSocket.bl_idname, "Distribute")
        self.inputs.new(FloorSocket.bl_idname, "First")
        self.outputs.new(FacadeSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, params):
        def facade_generator(build: Building):
            floors_stack = build.cur_facade.floors_stack
            is_fill_fixed = False
            if inputs.first:
                floors_stack.add_floor(build, inputs.first)
            if inputs.fill:
                for i in range(10000):
                    if inputs.last:
                        if floors_stack.will_be_last_floor(build, inputs.last):
                            floors_stack.add_floor(build, inputs.last)
                            break
                    else:
                        if floors_stack.is_full(build):
                            break

                    if not is_fill_fixed:
                        floor = floors_stack.add_floor(build, inputs.fill)
                        if 'floor_index' not in floor.depth:
                            is_fill_fixed = True
                    else:
                        floors_stack.repeat_last()
            floors_stack.instance_floors(build)
            return True

        return facade_generator

    @staticmethod
    def _execute(inputs: Inputs, params):
        def facade_generator(build: Building):
            facade = build.cur_facade
            facade.cur_floor_ind = 0
            vertices, flor_height = inputs.fill(build)
            flor_num = max(int(round(facade.height / flor_height)), 1)
            z_scale = facade.height / (flor_num * flor_height)
            z_step = Vector((0, 0, 1)) * (z_scale * flor_height)
            for v in vertices:
                v.co += z_step * 0.5
                v[build.scale_lay] *= Vector((1, z_scale, 1))
            for fi in range(1, flor_num):
                facade.cur_floor_ind = fi
                vertices, flor_height = inputs.fill(build)
                for v in vertices:
                    v.co += z_step * 0.5 + z_step * fi
                    v[build.scale_lay] *= Vector((1, z_scale, 1))
        return facade_generator


class SetFacadeAttributeNode(BaseNode, Node):
    bl_idname = 'SetFacadeAttributeNode'
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


class MathNode(BaseNode, Node):
    bl_idname = 'MathNode'
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
            row.active = props.facade_style is not None
            row.prop(props, 'show_in_edit_mode', text='', icon='EDITMODE_HLT')
            row.prop(props, 'realtime', text='', icon='RESTRICT_VIEW_OFF' if props.realtime else 'RESTRICT_VIEW_ON')
            row.prop(props, 'show_in_render', text='',
                     icon='RESTRICT_RENDER_OFF' if props.show_in_render else 'RESTRICT_RENDER_ON')
            col.template_ID(props, 'facade_style', new=AddNewFacadeStyleOperator.bl_idname,
                            unlink=UnlinkFacadeStyleOperator.bl_idname)

            col.prop(props, 'show_facade_names',
                     icon='DOWNARROW_HLT' if props.show_facade_names else 'RIGHTARROW', emboss=False)
            if props.show_facade_names and props.facade_style:
                col.use_property_split = True
                col.use_property_decorate = False
                for f_map in props.facade_names_mapping:
                    row = col.row(align=True)
                    row.prop(f_map, 'obj_facade_name', text=f_map.tree_facade_name)
                    if obj.mode == 'EDIT':
                        add_op = row.operator(EditFacadeAttributesOperator.bl_idname, text='', icon='ADD')
                        add_op.operation = 'add'
                        add_op.facade_name = f_map.obj_facade_name
                        remove_op = row.operator(EditFacadeAttributesOperator.bl_idname, text='', icon='REMOVE')
                        remove_op.operation = 'remove'
                        remove_op.facade_name = f_map.obj_facade_name
                if obj.mode == 'EDIT':
                    row = col.row(align=True)
                    add_op = row.operator(EditFacadeAttributesOperator.bl_idname, text='Add to fill facade', icon='ADD')
                    add_op.operation = 'add'
                    add_op.facade_name = ''
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
        obj.modifiers['Facade style']["Input_2_use_attribute"] = 1
        obj.modifiers['Facade style']["Input_2_attribute_name"] = "Normal"
        obj.modifiers['Facade style']["Input_3_use_attribute"] = 1
        obj.modifiers['Facade style']["Input_3_attribute_name"] = "Scale"
        obj.modifiers['Facade style']["Input_4_use_attribute"] = 1
        obj.modifiers['Facade style']["Input_4_attribute_name"] = "Is wall"
        obj.modifiers['Facade style']["Input_5_use_attribute"] = 1
        obj.modifiers['Facade style']["Input_5_attribute_name"] = "Wall index"


class FacadeNamesMapping(PropertyGroup):
    def update_obj_facade_name(self, context):
        # rename event
        prev_name_key = 'prev_name'
        if prev_name_key in self and self[prev_name_key] != '':
            bpy.ops.bn.edit_facade_attributes(
                operation='rename', facade_name=self[prev_name_key], new_facade_name=self.obj_facade_name)
        self[prev_name_key] = self.obj_facade_name

    tree_facade_identifier: bpy.props.StringProperty(description="Socket identifier")
    tree_facade_name: bpy.props.StringProperty()
    obj_facade_name: bpy.props.StringProperty(update=update_obj_facade_name)


class ObjectProperties(PropertyGroup):
    def is_building_tree(self, tree):
        return tree.bl_idname == BuildingGenerator.bl_idname

    def update_style(self, context):
        if self.facade_style is None:
            mod = self.get_modifier()
            if mod is not None:
                self.id_data.modifiers.remove(mod)
            self.error = ''
        else:
            self.update_mapping()
            try:
                self.facade_style.apply(self.id_data)
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
                self.facade_style.apply(self.id_data)

    def update_show_in_render(self, context):
        mod = self.get_modifier()
        if mod is not None:
            mod.show_render = self.show_in_render

    facade_style: bpy.props.PointerProperty(
        type=bpy.types.NodeTree, poll=is_building_tree, name="Facade Style", update=update_style)
    points: bpy.props.PointerProperty(type=bpy.types.Object)
    error: bpy.props.StringProperty()
    show_in_edit_mode: bpy.props.BoolProperty(
        default=True, description="Show facade style in edit mode", update=update_show_in_edit)
    realtime: bpy.props.BoolProperty(
        default=True, description='Display facade style in viewport', update=update_realtime)
    show_in_render: bpy.props.BoolProperty(
        default=True, description='Use facade style during render', update=update_show_in_render)
    show_facade_names: bpy.props.BoolProperty(name='Named facades', default=True)
    facade_names_mapping: bpy.props.CollectionProperty(type=FacadeNamesMapping)

    def apply_style(self):
        if self.id_data.mode == 'EDIT':
            can_be_updated = self.facade_style and self.realtime and self.show_in_edit_mode
        else:
            can_be_updated = self.facade_style and self.realtime
        if can_be_updated:
            self.facade_style.apply(self.id_data)

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
            modifier = obj.modifiers.new("Facade style", 'NODES')

        return GeometryTreeInterface(obj, modifier.node_group)

    def update_mapping(self):
        mapping = {m.tree_facade_identifier: m.obj_facade_name for m in self.facade_names_mapping}
        if self.facade_style:
            self.facade_names_mapping.clear()
            facade: FacadeTreeNames
            for facade in self.facade_style.facade_names:
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
        yield from zip((n.name for n in self.facade_style.facade_names), chain(self.id_data.face_maps, cycle([None])))


class AddNewFacadeStyleOperator(Operator):
    bl_idname = "bn.add_new_facade_style"
    bl_label = "Add new facade style"
    bl_description = "Add new facade style to the object"
    bl_options = {'INTERNAL', }

    @classmethod
    def poll(cls, context):
        return context.object is not None

    def execute(self, context):
        obj = context.object
        obj_props: ObjectProperties = obj.building_props
        tree = bpy.data.node_groups.new("FacadeStyle", BuildingGenerator.bl_idname)
        node1 = tree.nodes.new(PanelNode.bl_idname)
        node2 = tree.nodes.new(FloorPatternNode.bl_idname)
        node3 = tree.nodes.new(FacadePatternNode.bl_idname)
        node4 = tree.nodes.new(FacadeInstanceNode.bl_idname)
        tree.links.new(node2.inputs[2], node1.outputs[0])
        tree.links.new(node3.inputs[1], node2.outputs[0])
        tree.links.new(node4.inputs[0], node3.outputs[0])
        node2.location = Vector((200, 0))
        node3.location = Vector((400, 0))
        node4.location = Vector((600, 0))
        obj_props.facade_style = tree
        tree.show_in_areas(True)
        return {'FINISHED'}


class UnlinkFacadeStyleOperator(Operator):
    bl_idname = "bn.unlink_facade_style"
    bl_label = "Unlink facade style"
    bl_description = "Unlink facade style from the object"
    bl_options = {'INTERNAL', }

    @classmethod
    def poll(cls, context):
        return context.object is not None

    def execute(self, context):
        obj = context.object
        obj_props: ObjectProperties = obj.building_props
        obj_props.facade_style.show_in_areas(False)
        obj_props.facade_style = None
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
        socket = next(s for s in node.inputs if s.identifier == self.socket_identifier)
        if self.operation == 'add':
            node.inputs.new(socket.bl_idname, '')
            position = next(i for i, s in enumerate(node.inputs) if s.identifier == socket.identifier) + 1
            node.inputs.move(len(node.inputs) - 1, position)
        elif self.operation == 'delete':
            node.inputs.remove(socket)
        elif self.operation == 'rename':
            if self.new_socket_name.lower() == 'fill':
                self.report({'ERROR_INVALID_INPUT'}, f'"{self.new_socket_name}" socket name is forbidden')
                return {'CANCELLED'}
            socket.user_name = self.new_socket_name
        elif self.operation == 'move_up':
            current_index = next(i for i, s in enumerate(node.inputs) if s.identifier == socket.identifier)
            node.inputs.move(current_index, max([current_index - 1, 1]))
        elif self.operation == 'move_down':
            current_index = next(i for i, s in enumerate(node.inputs) if s.identifier == socket.identifier)
            node.inputs.move(current_index, current_index + 1)
        else:
            raise TypeError(f"It is not known how to handle the operation={self.operation}")
        tree.update_facade_names()
        for obj in bpy.data.objects:
            props: ObjectProperties = obj.building_props
            if props.facade_style and props.facade_style.bl_idname == BuildingGenerator.bl_idname:
                props.update_mapping()
        return {'FINISHED'}

    def invoke(self, context, event):
        self.tree_name = context.node.id_data.name
        self.node_name = context.node.name
        self.socket_identifier = context.socket.identifier
        self.old_socket_name = context.socket.user_name
        self.new_socket_name = context.socket.name
        wm = context.window_manager
        if self.operation == 'rename':
            return wm.invoke_props_dialog(self)
        else:
            return self.execute(context)

    def draw(self, context):
        self.layout.prop(self, 'new_socket_name')


class EditFacadeAttributesOperator(Operator):
    bl_idname = "bn.edit_facade_attributes"
    bl_label = "Edit facade attributes"
    bl_options = {'INTERNAL', }

    operation: bpy.props.EnumProperty(items=[(i, i, '') for i in ['add', 'remove', 'rename']])
    facade_name: bpy.props.StringProperty()
    new_facade_name: bpy.props.StringProperty(description='New facade name to rename')

    @classmethod
    def description(cls, context, properties):
        descriptions = {
            'rename': "Replace values with facade_name to new_facade_name",
            'add': f'Assign selected faces to "{properties.facade_name}" facade',
            'remove': f'Remove selected faces from "{properties.facade_name}" facade',
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
            f_lay = bm.faces.layers.string.get('Facade name')
            if f_lay is None:
                f_lay = bm.faces.layers.string.new('Facade name')
        if self.operation == 'add':
            for face in (f for f in bm.faces if f.select):
                face[f_lay] = self.facade_name.encode()
        elif self.operation == 'remove':
            for face in (f for f in bm.faces if f.select):
                if face[f_lay].decode() == self.facade_name:
                    face[f_lay] = ''.encode()
        elif self.operation == 'rename':
            if obj.mode == 'EDIT':
                for face in bm.faces:
                    if face[f_lay].decode() == self.facade_name:
                        face[f_lay] = self.new_facade_name.encode()
            else:
                attr = obj.data.attributes.get('Facade name')
                if attr is None:
                    attr = obj.data.attributes.new('Facade name', 'STRING', 'FACE')
                for face_attr in attr.data.values():
                    if face_attr.value == self.facade_name:
                        face_attr.value = self.new_facade_name
        try:
            obj.building_props.facade_style.apply(obj)
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
            # center = Vector((sum(v.x for v in points) / len(points), sum(v.y for v in points) / len(points),
            #                  sum(v.z for v in points) / len(points)))
            center = Geometry(points).get_bounding_center()
            obj.location += center
            for vert in bm.verts:
                vert.co -= center
        obj.data.update()
        for fac_obj in (o for o in bpy.data.objects if o.building_props.facade_style):
            props: ObjectProperties = fac_obj.building_props
            if obj in {panel for panel in props.facade_style.inst_col.objects}:
                try:
                    props.apply_style()
                except Exception:
                    traceback.print_exc()
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
        facade = build.cur_facade
        vec = build.bm.verts.new(self.location + Vector((0, 0, floor_level)))
        vec[build.norm_lay] = facade.normal
        vec[build.scale_lay] = (self.scale.x, self.scale.y * floor_scale, 1)
        vec[build.ind_lay] = self.obj_index


class PanelsStack:
    def __init__(self):
        self._left_panel = []
        self._panels = []
        self._right_panel = []
        self._stack_width = 0

    def add_panel(self, build, panel_f, p_type: Literal['LEFT', 'FILL', 'RIGHT'] = 'FILL'):
        build.cur_facade.cur_panel_ind = len(self._panels) if p_type == 'FILL' else 0
        panel: Panel = panel_f(build)
        if panel is not None:
            z_scale = build.cur_floor.height / panel.size.y
            panel.scale *= Vector((z_scale, z_scale))
            self._stack_width += panel.instance_size.x
            if p_type == 'FILL':
                self._panels.append(panel)
            elif p_type == 'LEFT':
                self._left_panel.append(panel)
            elif p_type == 'RIGHT':
                self._right_panel.append(panel)
            return panel

    def is_full(self, build):
        return self._stack_width > build.cur_facade.width

    def update_location_scale(self, build):
        facade = build.cur_facade
        xy_scale = build.cur_facade.width / self._stack_width
        xy_shift = 0
        for panel in self.all_panels:
            panel.scale *= Vector((xy_scale, 1))
            size = panel.instance_size.x
            xy_shift += size / 2
            panel.location = facade.start + facade.direction.normalized() * xy_shift
            xy_shift += size / 2

    @property
    def all_panels(self) -> Iterable[Panel]:
        return chain(self._left_panel, self._panels, self._right_panel)


class Floor:
    def __init__(self, index=None):
        self.index = index
        self.height = None
        self.z_level = None
        self.z_scale = None
        self.panels_stack: PanelsStack = PanelsStack()
        self.depth: set[Literal['floor_index']] = set()

    def instance_panels(self, build):
        for panel in self.panels_stack.all_panels:
            panel.instance(build, self.z_level, self.z_scale)


class FloorsStack:
    def __init__(self):
        self._floors = []
        self._current_height = 0
        self._last_ind = 0

    def add_floor(self, build, floor_f) -> Floor:
        floor: Floor = Floor(index=self._last_ind)
        build.cur_floor = floor
        floor_f(build)
        self._floors.append(floor)
        self._last_ind += 1
        self._current_height += floor.height
        return floor

    def repeat_last(self):
        self._floors.append(self._floors[-1])
        self._current_height += self._floors[-1].height
        self._last_ind += 1

    def will_be_last_floor(self, build, floor_f):
        floor: Floor = Floor(index=self._last_ind)
        build.cur_floor = floor
        floor_f(build, precompute=True)
        return build.cur_facade.height < (self._current_height + floor.height)

    def is_full(self, build):
        return build.cur_facade.height < self._current_height

    def instance_floors(self, build):
        z_scale = build.cur_facade.height / self._current_height
        real_floors_height = 0
        for floor in self._floors:
            height = floor.height * z_scale
            floor.z_level = real_floors_height + height / 2
            floor.z_scale = z_scale
            floor.instance_panels(build)
            real_floors_height += height


class Facade:
    def __init__(self, face):
        center = face.calc_center_median()
        dot_prod = [((v.co - center).cross(face.normal)) @ Vector((0, 0, 1)) for v in face.verts]
        right_low, right_up = sorted([v for v, prod in zip(face.verts, dot_prod) if prod < 0], key=lambda v: v.co.z)
        left_low, left_up = sorted([v for v, prod in zip(face.verts, dot_prod) if prod > 0], key=lambda v: v.co.z)
        left_edge, *_ = [e for e in left_low.link_edges if e.other_vert(left_up) == left_low]
        right_edge, *_ = [e for e in right_low.link_edges if e.other_vert(right_up) == right_low]
        xy_dir = (right_up.co - left_low.co) * Vector((1, 1, 0))
        xy_len = xy_dir.length
        z_dir = (left_low.co - right_up.co) * Vector((0, 0, 1))
        z_len = z_dir.length

        self.cur_floor_ind = None
        self.cur_panel_ind = None
        self.height = z_len
        self.width = xy_len
        self.start = left_low.co
        self.direction = xy_dir
        self.normal = face.normal

        self.left_wall_angle = left_edge.calc_face_angle()
        self.right_wall_angle = right_edge.calc_face_angle()
        self.azimuth = Building.calc_azimuth(self.normal)


class Building:
    def __init__(self):
        bm = bmesh.new()
        self.norm_lay = bm.verts.layers.float_vector.new("Normal")
        self.scale_lay = bm.verts.layers.float_vector.new("Scale")
        self.ind_lay = bm.verts.layers.int.new("Wall index")
        self.bm: bmesh.types.BMesh = bm
        self.cur_facade: Facade = None
        self.cur_floor: Floor = None

    @staticmethod
    def calc_azimuth(vec: Vector):
        vec = vec.normalized()
        north = Vector((0, 1, 0))
        is_right = vec.cross(north).normalized().z < 0
        return vec @ north + 3 if is_right else 1 - vec @ north


class Geometry:
    def __init__(self, verts: list):
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

def update_tree_timer():
    if BuildingGenerator.was_changes:
        update_trees = []
        for obj in bpy.data.objects:
            obj_props: ObjectProperties = obj.building_props
            if obj_props.facade_style and obj_props.facade_style.was_changed and obj_props.realtime:
                try:
                    obj_props.facade_style.apply(obj)
                except Exception as e:
                    traceback.print_exc()
                    obj_props.error = str(e)
                else:
                    obj_props.error = ''
                finally:
                    update_trees.append(obj_props.facade_style)
        for tree in update_trees:
            tree.was_changed = False
        BuildingGenerator.was_changes = False
    return 0.01


@persistent
def update_active_object(scene):
    obj = bpy.context.object

    # change active object event, update tree property of Building tree editors
    try:  # todo also changes of the tree editor type should tracked
        if (prev_obj := scene['active_obj']) != obj:
            scene['active_obj'] = obj
            if cur_tree := obj.building_props.facade_style:
                cur_tree.show_in_areas(True)
            elif prev_tree := prev_obj.building_props.facade_style:
                prev_tree.show_in_areas(False)
    except KeyError:
        scene['active_obj'] = obj

    # update active object
    if obj is None:
        return
    obj_props: ObjectProperties = obj.building_props
    can_be_updated = obj_props.facade_style is not None and obj_props.realtime
    if not can_be_updated:
        return

    if obj.mode == 'EDIT':
        obj['was_in_edit'] = True
        if obj_props.show_in_edit_mode:
            obj_props.facade_style.apply(obj)
    else:
        if 'was_in_edit' in obj:
            del obj['was_in_edit']
            obj_props.facade_style.apply(obj)


def get_node_categories():
    class Base:
        @classmethod
        def poll(cls, context):
            return context.space_data.tree_type == BuildingGenerator.bl_idname

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
    for tree in (t for t in bpy.data.node_groups if t.bl_idname == BuildingGenerator.bl_idname):
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
    for tree in (t for t in bpy.data.node_groups if t.bl_idname == BuildingGenerator.bl_idname):
        for node in tree.nodes:
            if node.category is not None:
                node.use_custom_color = True
                node.color = node.category.color


if __name__ == "__main__":
    unregister()
    register()
    _update_colors()
