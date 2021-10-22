import inspect
import random
import sys
import traceback
from collections import namedtuple, defaultdict
from enum import Enum, auto
from graphlib import TopologicalSorter
from itertools import count, chain
from math import isclose
from typing import Optional, Iterable, NamedTuple, Type

import bmesh
import bpy
from bpy.app.handlers import persistent
from bpy.types import NodeTree, Node, NodeSocket, Panel, Operator, PropertyGroup
import nodeitems_utils
from mathutils import Vector
from nodeitems_utils import NodeCategory, NodeItem


class BuildingGenerator(NodeTree):
    bl_idname = 'BuildingGenerator'
    bl_label = "Building Generator"
    bl_icon = 'NODETREE'
    was_changes = False  # flag to timer

    inst_col: bpy.props.PointerProperty(type=bpy.types.Collection, description="Keep all panels to be instanced")
    was_changed: bpy.props.BoolProperty(description="If True the tree should be reevaluated")

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
        points_bm = self.get_points(bm)
        points_bm.to_mesh(obj_props.points.data)
        points_bm.free()
        if obj.mode != 'EDIT':
            bm.to_mesh(obj.data)  # assign new attributes
            bm.free()
        gn_tree.set_points(obj_props.points)

        # set instances
        gn_tree.set_instances(self.inst_col)

    def get_points(self, base_bm):
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
                return node.execute(node.Inputs(*in_data), base_bm)
            else:
                if hasattr(node, 'Props'):
                    props = node.Props(*[getattr(node, n) for n in node.Props._fields])
                else:
                    props = None
                if node.repeat_last_socket:
                    res = node.execute(node.gen_input_mapping()(*in_data), props)
                else:
                    res = node.execute(node.Inputs(*in_data) if hasattr(node, 'Inputs') else None, props)
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


class BaseSocket:
    show_text = True

    def update_value(self, context):
        self.id_data.update()

    def draw(self, context, layout, node, text):
        if hasattr(self, 'value') and not self.is_output and not self.is_linked:
            col = layout.column()
            col.prop(self, 'value', text=(text or self.default_name) if self.show_text else '')
        else:
            layout.label(text=text or self.default_name)

    def draw_color(self, context, node):
        return self.color


class FacadeSocket(BaseSocket, NodeSocket):
    bl_idname = 'FacadeSocket'
    bl_label = "Facade Socket"
    color = 0.65, 0.25, 0.8, 1.0
    default_name = 'Facade'


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
    value: bpy.props.PointerProperty(type=bpy.types.Object, update=BaseSocket.update_value)


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
    default_name = 'Bool'
    color = 0.4, 0.3, 0.7, 1.0
    value: bpy.props.FloatVectorProperty(update=BaseSocket.update_value)


class Categories(Enum):
    PANEL = auto()
    FLOOR = auto()
    FACADE = auto()

    @property
    def color(self):
        colors = {
            Categories.PANEL: (0.3, 0.45, 0.5),
            Categories.FLOOR: (0.25, 0.25, 0.4),
            Categories.FACADE: (0.4, 0.25, 0.4),
        }
        return colors[self]


class BaseNode:
    category: Categories = None
    repeat_last_socket = False
    repeat_first_socket = False

    @classmethod
    def poll(cls, tree):
        return tree.bl_idname == 'BuildingGenerator'

    def init(self, context):
        if self.category is not None:
            self.use_custom_color = True
            self.color = self.category.color
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

    def gen_input_mapping(self) -> Type[NamedTuple]:
        input_names = []
        index = count()
        for sock in self.inputs:
            if sock.name:
                input_names.append(sock.name.lower())
            else:
                input_names.append(sock.default_name.lower() + str(next(index)))
        return namedtuple('Inputs', input_names)


class FacadeInstanceNode(BaseNode, Node):
    bl_idname = 'FacadeInstanceNode'
    bl_label = "Facade Instance"
    category = Categories.FACADE
    Inputs = namedtuple('Inputs', ['all', 'named'])

    def node_init(self):
        self.inputs.new(FacadeSocket.bl_idname, "All")
        self.inputs.new(FacadeSocket.bl_idname, "Named")

    @staticmethod
    def execute(inputs: Inputs, base_bm: bmesh.types.BMesh):
        build = Building(base_bm)
        for facade in build.facades():
            build.cur_facade = facade
            inputs.all(build)
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
    Inputs = namedtuple('Inputs', ['object', 'scalable'])
    Props = namedtuple('Props', ['panel_index'])

    mode: bpy.props.EnumProperty(items=[(i, i, '') for i in ['Object', 'Collection']])
    panel_index: bpy.props.IntProperty(description="Penal index in the collection")

    def node_init(self):
        self.inputs.new(ObjectSocket.bl_idname, "")
        self.inputs.new(BoolSocket.bl_idname, "Scalable")
        self.outputs.new(PanelSocket.bl_idname, "")

    def draw_buttons(self, context, layout):
        layout.prop(self, "mode", expand=True)

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        def panel_gen(build: Building):
            # panel is expected to be in XY orientation
            verts = inputs.object(build).data.vertices
            min_v = Vector((min(v.co.x for v in verts), min(v.co.y for v in verts)))
            max_v = Vector((max(v.co.x for v in verts), max(v.co.y for v in verts)))
            return Panel(props.panel_index, min_v, max_v)
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
        self.inputs.new(IntSocket.bl_idname, "Seed")
        self.inputs.new(PanelSocket.bl_idname, "")
        self.outputs.new(PanelSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, params):
        random_stream = random.Random(inputs.seed(None))

        def randomize_panels(build: Building):
            panels = [inp(build) for inp in inputs[1: -1]]
            return random_stream.choices(panels, weights=[p.probability for p in panels])[0]
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


class FlorePatternNode(BaseNode, Node):
    bl_idname = 'FlorePatternNode'
    bl_label = "Flore Pattern"
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
        def flore_gen(build: Building, precompute=False):
            if precompute:
                build.cur_flore.height = inputs.height(build)
                build.cur_flore.repeatable = False
                return

            panels = []
            panels_len = 0
            right_panel = None
            if inputs.left:
                build.cur_facade.cur_panel_ind = 0
                panel: Panel = inputs.left(build)
                if panel is not None:
                    z_scale = inputs.height(build) / panel.height
                    panels_len += panel.width * z_scale
                    panel.height_scale = z_scale
                    panels.append(panel)
            if inputs.right:
                build.cur_facade.cur_panel_ind = 0
                panel: Panel = inputs.right(build)
                if panel is not None:
                    z_scale = inputs.height(build) / panel.height
                    panels_len += panel.width * z_scale
                    panel.height_scale = z_scale
                    right_panel = panel
            if panels_len < build.cur_facade.width:
                for i in range(10000):
                    build.cur_facade.cur_panel_ind = i
                    panel: Panel = inputs.fill(build)
                    z_scale = inputs.height(build) / panel.height
                    panels_len += panel.width * z_scale
                    panel.height_scale = z_scale
                    panels.append(panel)
                    if panels_len > build.cur_facade.width:
                        break
            if right_panel:
                panels.append(right_panel)
            verts = []
            facade = build.cur_facade
            xy_scale = facade.width / panels_len
            xy_shift = 0
            zero_panel = Panel(0, Vector((0, 0)), Vector((0, 0)))
            for prev_pan, pan in zip(chain([zero_panel], panels), panels):
                prev_half_size = prev_pan.width * prev_pan.height_scale * xy_scale / 2
                half_size = pan.width * pan.height_scale * xy_scale / 2
                xy_shift += prev_half_size + half_size
                vec = build.bm.verts.new(facade.start + facade.direction.normalized() * xy_shift)
                vec[build.norm_lay] = facade.normal
                vec[build.scale_lay] = (pan.height_scale * xy_scale, pan.height_scale, 1)
                vec[build.ind_lay] = pan.index
                verts.append(vec)
            build.cur_flore.verts = verts
            build.cur_flore.height = inputs.height(build)
        return flore_gen


class FloreAttributesNode(BaseNode, Node):
    bl_idname = 'FloreAttributesNode'
    bl_label = "Flore Attributes"
    category = Categories.FLOOR

    def node_init(self):
        self.outputs.new(FloatSocket.bl_idname, "Width").display_shape = 'DIAMOND'
        self.outputs.new(FloatSocket.bl_idname, "Height").display_shape = 'DIAMOND'
        self.outputs.new(IntSocket.bl_idname, "Number").display_shape = 'DIAMOND'
        self.outputs.new(FloatSocket.bl_idname, "Left corner angle").display_shape = 'DIAMOND'
        self.outputs.new(FloatSocket.bl_idname, "Right corner angle").display_shape = 'DIAMOND'

    @staticmethod
    def execute(inputs, props):
        def flore_width(build: Building):
            return build.cur_facade.width

        def flore_height(build: Building):
            return None

        def flore_index(build: Building):
            return build.cur_flore.index

        def left_corner_angle(build: Building):
            return build.cur_facade.left_wall_angle

        def right_corner_angle(build: Building):
            return build.cur_facade.right_wall_angle
        return flore_width, flore_height, flore_index, left_corner_angle, right_corner_angle


class StackFloorsNode(BaseNode, Node):
    bl_idname = 'StackFloorsNode'
    bl_label = "Stack Floors"
    category = Categories.FACADE
    repeat_first_socket = True
    Inputs = namedtuple('Inputs', ['flore0', 'flore1', 'flore2', 'flore3'])

    def node_init(self):
        self.inputs.new(FloorSocket.bl_idname, "First flore")
        self.outputs.new(FacadeSocket.bl_idname, "")

    @staticmethod
    def execute(inputs: Inputs, params):
        def stack_flores(build: Building):
            pass
        return stack_flores


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
            facade = build.cur_facade
            flores_height = 0
            flore_fs = []
            cur_flore_ind = 0
            if inputs.first:
                floor: Flore = Flore(index=cur_flore_ind)
                cur_flore_ind += 1
                build.cur_flore = floor
                inputs.first(build, precompute=True)
                flores_height += floor.height
                flore_fs.append(inputs.first)
            if inputs.fill:
                for i in range(cur_flore_ind, 10000):
                    if inputs.last:
                        flore: Flore = Flore(index=cur_flore_ind)
                        build.cur_flore = flore
                        inputs.last(build, precompute=True)
                        if build.cur_facade.height < (flores_height + flore.height):
                            flores_height += flore.height
                            flore_fs.append(inputs.last)
                            cur_flore_ind += 1
                            break
                        else:
                            pass  # last flore can't be added yet
                    else:
                        if build.cur_facade.height < flores_height:
                            break
                    flore: Flore = Flore(index=cur_flore_ind)
                    cur_flore_ind += 1
                    build.cur_flore = flore
                    inputs.fill(build, precompute=True)
                    flores_height += flore.height
                    flore_fs.append(inputs.fill)

            z_scale = facade.height / flores_height
            flores_height = 0
            for fi, flore_f in enumerate(flore_fs):
                flore: Flore = Flore(index=fi)
                build.cur_flore = flore
                flore_f(build)
                height = flore.height * z_scale
                for v in flore.verts:
                    v.co += Vector((0, 0, flores_height + height / 2))
                    v[build.scale_lay] *= Vector((1, z_scale, 1))
                flores_height += height
        return facade_generator

    @staticmethod
    def _execute(inputs: Inputs, params):
        def facade_generator(build: Building):
            facade = build.cur_facade
            facade.cur_flore_ind = 0
            vertices, flor_height = inputs.fill(build)
            flor_num = max(int(round(facade.height / flor_height)), 1)
            z_scale = facade.height / (flor_num * flor_height)
            z_step = Vector((0, 0, 1)) * (z_scale * flor_height)
            for v in vertices:
                v.co += z_step * 0.5
                v[build.scale_lay] *= Vector((1, z_scale, 1))
            for fi in range(1, flor_num):
                facade.cur_flore_ind = fi
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
    Inputs = namedtuple('Inputs', ['val1', 'val2'])
    Props = namedtuple('Props', ['mode'])

    mode: bpy.props.EnumProperty(
        items=[(i.lower(), i, '') for i in ['Add', 'Multiply', 'Grater_than', 'Less_than', 'Remainder']])

    def node_init(self):
        self.inputs.new(FloatSocket.bl_idname, "").display_shape = 'DIAMOND_DOT'
        self.inputs.new(FloatSocket.bl_idname, "").display_shape = 'DIAMOND_DOT'
        self.outputs.new(FloatSocket.bl_idname, "").display_shape = 'DIAMOND_DOT'

    def draw_buttons(self, context, layout):
        layout.prop(self, "mode", text='')

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        funcs = {
            'add': lambda v1, v2: v1 + v2,
            'multiply': lambda v1, v2: v1 * v2,
            'grater_than': lambda v1, v2: v1 > v2,
            'less_than': lambda v1, v2: v1 < v2,
            'remainder': lambda v1, v2: v1 % v2,
        }

        def math(build):
            return funcs[props.mode](inputs.val1(build), inputs.val2(build))
        return math


class ObjectPanel(Panel):
    bl_idname = "VIEW3D_PT_ObjectPanel"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "Building nodes"
    bl_label = "Active object"

    def draw(self, context):
        col = self.layout.column()
        obj = context.object
        if obj.building_props.error:
            col.label(text=obj.building_props.error, icon='ERROR')
        if obj:
            col.prop(obj.building_props, 'facade_style')
        else:
            col.label(text='Select object')


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
            try:
                self.facade_style.apply(self.id_data)
            except Exception as e:
                self.error = str(e)
                raise
            else:
                self.error = ''

    facade_style: bpy.props.PointerProperty(
        type=bpy.types.NodeTree, poll=is_building_tree, name="Facade Style", update=update_style)
    points: bpy.props.PointerProperty(type=bpy.types.Object)
    error: bpy.props.StringProperty()

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


classes = []
for name, member in inspect.getmembers(sys.modules[__name__]):
    is_module_cls = inspect.isclass(member) and member.__module__ == __name__
    if is_module_cls:
        if any(base_cls in member.__bases__ for base_cls
               in [NodeTree, NodeSocket, Node, Panel, Operator, PropertyGroup]):
            classes.append(member)


class AllNodes(NodeCategory):
    @classmethod
    def poll(cls, context):
        return context.space_data.tree_type == BuildingGenerator.bl_idname


node_categories = [
    AllNodes('ALL_NODES', "All nodes", items=[NodeItem(cls.bl_idname) for cls in classes if BaseNode in cls.__bases__])
]


class Facade:
    def __init__(self, face, index):
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

        # self.vertices: bmesh.types.BMVertSeq = vertices
        # self.index = index
        self.cur_flore_ind = None
        self.cur_panel_ind = None
        self.height = z_len
        self.width = xy_len
        self.start = left_low.co
        self.direction = xy_dir
        self.normal = face.normal
        self.left_wall_angle = left_edge.calc_face_angle()
        self.right_wall_angle = right_edge.calc_face_angle()


class Building:
    def __init__(self, base_bm):
        bm = bmesh.new()
        self.norm_lay = bm.verts.layers.float_vector.new("Normal")
        self.scale_lay = bm.verts.layers.float_vector.new("Scale")
        self.ind_lay = bm.verts.layers.int.new("Wall index")
        self.bm: bmesh.types.BMesh = bm
        self.base_bm = base_bm
        self.cur_facade: Facade = None
        self.cur_flore: Flore = None

    def facades(self) -> Iterable[Facade]:
        wall_lay = self.base_bm.faces.layers.int.get("Is wall")
        if wall_lay is None:
            wall_lay = self.base_bm.faces.layers.int.new("Is wall")

        for fi, face in enumerate(self.base_bm.faces):
            if isclose(face.normal.dot(Vector((0, 0, 1))), 0, abs_tol=0.1):
                face[wall_lay] = 1
                yield Facade(face, fi)
            else:
                face[wall_lay] = 0


class Flore:
    def __init__(self, index=None):
        self.verts: list[bmesh.types.BMVert] = None
        self.index = index
        self.height = None
        self.repeatable = False


class Panel:
    def __init__(self, index: int, min_vector: Vector, max_vector: Vector):
        # panel is expected to be in XY orientation
        vec_size = max_vector - min_vector
        self.width = vec_size.x
        self.height = vec_size.y
        self.index = index
        self.probability = 1
        self.width_scale = 1
        self.height_scale = 1


def update_tree_timer():
    if BuildingGenerator.was_changes:
        update_trees = []
        for obj in bpy.data.objects:
            obj_props: ObjectProperties = obj.building_props
            if obj_props.facade_style and obj_props.facade_style.was_changed:
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
    if bpy.context.object is None or bpy.context.object.mode != 'EDIT':
        return
    obj_props: ObjectProperties = bpy.context.object.building_props
    if obj_props.facade_style is None:
        return
    obj_props.facade_style.apply(bpy.context.object)


def register():
    for cls in classes:
        bpy.utils.register_class(cls)

    nodeitems_utils.register_node_categories('CUSTOM_NODES', node_categories)
    bpy.types.Object.building_props = bpy.props.PointerProperty(type=ObjectProperties)
    bpy.app.handlers.depsgraph_update_post.append(update_active_object)
    bpy.app.handlers.load_post.append(update_tree_timer)  # this is hack to store function somewhere
    bpy.app.timers.register(update_tree_timer, persistent=True)


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

    for cls in classes[:]:
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
