# Building Nodes add-on for Blender for procedural building modeling
# Copyright (C) 2021 Soluyanov Sergey | sv@soluyanov.ru
# License - GPLv3


import bisect
import inspect
import random
import sys
import traceback
from abc import ABC, abstractmethod
from cProfile import Profile
from collections import namedtuple, defaultdict
from contextlib import contextmanager
from enum import Enum, auto
from functools import wraps, cmp_to_key
from graphlib import TopologicalSorter
from itertools import count, chain, cycle, repeat, accumulate, dropwhile
from math import isclose, inf
from pathlib import Path
from pstats import Stats
from typing import Optional, Iterable, NamedTuple, Type, get_type_hints, Literal, Any, Union, overload, Generic, \
    TypeVar, Iterator

import bmesh
import bpy
import numpy as np
from bmesh.types import BMFace, BMLoop, BMVert, BMesh
from bpy.app.handlers import persistent
from bpy.props import StringProperty, BoolProperty, EnumProperty
from bpy.types import NodeTree, Node, NodeSocket, Panel, Operator, PropertyGroup, Menu, AddonPreferences
import nodeitems_utils
from mathutils import Vector
from nodeitems_utils import NodeCategory, NodeItem


bl_info = {
    "name": "Building Nodes",
    "author": "Soluyanov Sergey",
    "version": (1, 0, 1),
    "blender": (3, 0, 0),
    "location": "Property panel -> Building nodes panel and Building style tree editor",
    "description": "Tool for procedural building modeling",
    "warning": "",
    "doc_url": "https://durman.github.io/BuildingNodesDocs/",
    "tracker_url": "https://github.com/Durman/BuildingNodesDocs/discussions",
    "category": "Object",
}


FACE_STYLE_LAYER_NAME = "BnStyleName"  # should be unchanged between versions


def profile(fun=None, *, sort: Literal['time', 'cumulative'] = 'time', length=10, file: Path = None):
    if fun is None:
        return lambda f: profile(f, sort=sort, length=length, file=file)

    @wraps(fun)
    def inner(*args, **kwargs):
        with Profile() as pr:
            res = fun(*args, **kwargs)
            if file is not None:
                print(f"Save into file: {file}")
                pr.dump_stats(file)
            else:
                Stats(pr).strip_dirs().sort_stats(sort).print_stats(length)
        return res
    return inner


class BuildingStyleTree(NodeTree):
    bl_idname = 'bn_BuildingStyleTree'
    bl_label = "Building Style Editor"
    bl_icon = 'HOME'
    was_changes = False  # flag to timer

    inst_col: bpy.props.PointerProperty(type=bpy.types.Collection, description="Keep all panels to be instanced")  # todo should be set to None during copying
    was_changed: bpy.props.BoolProperty(description="If True the tree should be reevaluated")

    def update(self):
        BuildingStyleTree.was_changes = True
        self.was_changed = True
        self.check_reroutes_sockets()

    def check_reroutes_sockets(self):
        if not any(n.bl_idname == 'NodeReroute' for n in self.nodes):
            return

        # analytical part, it's impossible to use Tree structure and modify the tree
        Req = namedtuple('Req', ['left_s', 'type', 'shape', 'reroute'])
        socket_job: dict[NodeSocket, Req] = dict()
        for node, left_ss in self.walk():  # walk is sorted in case if reroute nodes are going one after other
            if node.bl_idname == 'NodeReroute' and left_ss and left_ss[0] is not None:
                left_s, *_ = left_ss
                if left_s in socket_job:
                    s_type = socket_job[left_s].type
                    s_shape = socket_job[left_s].shape
                else:
                    s_type = left_s.bl_idname
                    s_shape = left_s.display_shape
                if s_type != node.inputs[0].bl_idname or s_shape != node.inputs[0].display_shape:
                    socket_job[node.outputs[0]] = Req(left_s, s_type, s_shape, node)

        # regenerating sockets
        for props in reversed(socket_job.values()):
            # handle input socket
            in_s = props.reroute.inputs.new(props.type, props.left_s.name)
            in_s.display_shape = props.shape
            self.links.new(in_s, props.left_s)
            props.reroute.inputs.remove(props.reroute.inputs[0])

            # handle output sockets
            out_s = props.reroute.outputs.new(props.type, props.left_s.name)
            out_s.display_shape = props.shape
            for right_s in (l.to_socket for l in props.reroute.outputs[0].links):
                self.links.new(right_s, out_s)
            props.reroute.outputs.remove(props.reroute.outputs[0])

    def apply(self, obj):
        obj_props: ObjectProperties = obj.building_props
        gn_tree = obj_props.get_gn_tree()

        # set position and attributes
        if obj_props.points is None or obj_props.points['owner_name'] != obj.name:
            obj_props.points = bpy.data.objects.new('Points', bpy.data.meshes.new('Points'))
            obj_props.points['owner_name'] = obj.name
        if obj.mode == 'EDIT':
            bm = bmesh.from_edit_mesh(obj.data)
        else:
            bm = bmesh.new()
            bm.from_mesh(obj.data)
        bm.faces.ensure_lookup_table()
        points_bm = self.get_points(bm)
        if points_bm:
            points_bm.to_mesh(obj_props.points.data)
            points_bm.free()
        if obj.mode != 'EDIT':
            bm.to_mesh(obj.data)  # assign new attributes
            bm.free()
        gn_tree.set_points(obj_props.points)

        # set instances
        gn_tree.set_instances(self.inst_col)

    # @profile(sort='cumulative', file=Path.home() / 'desktop' / 'stats')
    def get_points(self, base_bm):
        self.store_instances()
        sock_data = dict()
        for node, prev_socks in self.walk():

            # grab data from previous nodes
            in_data = dict()
            for from_sock, to_sock in zip(prev_socks, node.inputs):
                if from_sock is not None:
                    in_data[to_sock.py_identifier] = sock_data[from_sock]
                elif hasattr(to_sock, 'value'):
                    def sock_value(build, *, _value=to_sock.value):
                        return _value
                    in_data[to_sock.py_identifier] = sock_value
                else:
                    in_data[to_sock.py_identifier] = None

            is_last_node = node.bl_idname == BuildingStyleNode.bl_idname
            # collect properties
            if node.bl_idname == 'NodeReroute':
                pass
            elif is_last_node:
                props = base_bm
            elif node.props_template:
                props = node.props_template
            elif hasattr(node, 'Props'):
                props = node.Props(*[getattr(node, n) for n in node.Props._fields])
            else:
                props = None

            # find inputs mapping
            if node.bl_idname == 'NodeReroute':
                pass
            elif node.input_template:  # this says that sockets have appropriate identifiers
                mapping = node.gen_input_mapping()
                input_data = mapping(*[in_data[key] for key in mapping._fields])  # key words
            else:  # positional
                input_data = (Inp := node.gen_input_mapping()) and Inp(*in_data.values())

            if node.bl_idname == 'NodeReroute':
                res = in_data[node.inputs[0].identifier.replace('.', '')]
            else:
                res = node.execute(input_data, props)

            if is_last_node:
                return res
            if not isinstance(res, tuple):
                res = (res, )
            for i, data in enumerate(res):
                if hasattr(node, 'Outputs'):
                    out_sock = node.get_socket(node.Outputs._fields[i], is_input=False)
                else:
                    out_sock = node.outputs[i]
                sock_data[out_sock] = data

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
        obj_index = {obj: i for i, obj
                     in enumerate(sorted(self.inst_col.objects, key=lambda o: cmp_to_key(bl_sort_str)(o.name)))}
        for node in self.nodes:
            if node.bl_idname == PanelNode.bl_idname and node.inputs[0].value:
                node.panel_index = obj_index[node.inputs[0].value]

        return self.inst_col

    def walk(self) -> Iterable[tuple[Node, list[Optional[NodeSocket]]]]:
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
            prev_nodes.extend(prev_node for s in list(node.inputs)[::-1] if (prev_node := nodes.get(s)) is not None)

    def update_sockets(self):
        """ Supports (only for nodes with template attributes):
        - adding sockets from a template which identifier was not found in a sockets collection
        - marking sockets as deprecated which identifiers are not found in a template
        """
        for node in (n for n in self.nodes if n.bl_idname not in {'NodeReroute', 'NodeFrame', 'NodeUndefined'}):
            if node.input_template:
                socks = {s.identifier: s for s in node.inputs}
                if node.repeat_last_socket:
                    sock_keys = node.input_template._fields[:-1]
                    sock_templates = node.input_template[:-1]
                else:
                    sock_keys = node.input_template._fields
                    sock_templates = node.input_template
                for pos, (key, template) in enumerate(zip(sock_keys, sock_templates)):
                    if key not in socks:
                        template.init(node, is_input=True, identifier=key)
                        node.inputs.move(len(node.inputs) - 1, pos)
                for key, sock in socks.items():
                    if sock.bl_idname == 'NodeSocketUndefined':
                        node.inputs.remove(sock)
                        continue
                    is_deprecated = not hasattr(node.input_template, key)
                    if is_deprecated and node.repeat_last_socket:
                        if sock.bl_idname == node.input_template[-1].type.bl_idname:
                            if sock.bl_idname == node.inputs[-1].bl_idname:
                                is_deprecated = False
                    sock.is_deprecated = is_deprecated
                    if is_deprecated:
                        sock.enabled = True
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
    default_shape = 'CIRCLE'

    def update_is_to_show(self, context):
        self.enabled = self.is_to_show
        # self.update_value(context)

    user_name: bpy.props.StringProperty(description="Socket name given by user")  # todo tag redraw
    is_deprecated: bpy.props.BoolProperty(description="In case the socket is not used by a node any more")
    is_to_show: bpy.props.BoolProperty(
        default=True, description="To display the socket in node interface", update=update_is_to_show)
    update_ref: StringProperty(description="Path to the update function for value property")

    def update_value(self, context):
        if self.update_ref:
            eval(self.update_ref)(self, context)
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

        elif self.is_output and self.node.main_prop:
            row = layout.row(align=True)
            sock = self.node.get_socket(self.node.main_prop, is_input=True)
            if sock.enabled:
                row.label(text=self.user_name or text or self.default_name)
            else:
                row.prop(sock, 'value', text='')
            if self.node.settings_viewer:
                row.alignment = 'RIGHT'
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

    @property
    def py_identifier(self):
        return self.identifier.replace('.', '')


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
    default_shape = 'DIAMOND_DOT'
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
    default_shape = 'DIAMOND_DOT'
    default_name = 'Integer'
    value: bpy.props.IntProperty(update=BaseSocket.update_value)


class StringSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_StringSocket'
    bl_label = "String Socket"
    color = 0.4, 0.6, 0.8, 1.0
    default_shape = 'DIAMOND_DOT'
    default_name = 'String'
    value: bpy.props.StringProperty(update=BaseSocket.update_value)


class BoolSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_BoolSocket'
    bl_label = "Bool Socket"
    default_shape = 'DIAMOND_DOT'
    default_name = 'Bool'
    color = 0.75, 0.55, 0.75, 1.0
    value: bpy.props.BoolProperty(update=BaseSocket.update_value)


class VectorSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_VectorSocket'
    bl_label = "Vector Socket"
    default_shape = 'DIAMOND_DOT'
    default_name = 'Vector'
    color = 0.4, 0.3, 0.7, 1.0
    value: bpy.props.FloatVectorProperty(update=BaseSocket.update_value)


class EnumSocket(BaseSocket, NodeSocket):
    bl_idname = 'bn_EnumSocket'
    bl_lable = "Enum Socket"
    default_shape = 'DIAMOND_DOT'
    default_name = "Enum"
    color = 0, 0.3, 0, 1

    def eval_items(self, context):
        try:
            return eval(self.items_ref)
        except (NameError, AttributeError):
            return [('ERROR', 'ERROR', '')]

    value: EnumProperty(items=eval_items, update=BaseSocket.update_value)
    items_ref: StringProperty(description="Path to the items")


class InputSocket(BaseSocket, NodeSocket):
    """Generic socket"""
    bl_idname = 'bn_InputSocket'
    bl_lable = "Input Socket"
    default_shape = 'DIAMOND_DOT'
    default_name = "Input"
    color = 0.5, 0.5, 0.5, 1.0


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


class SocketTemplate(NamedTuple):
    type: NodeSocket
    name: str = ''
    enabled: bool = True
    display_shape: Literal['CIRCLE', 'SQUARE', 'DIAMOND', 'CIRCLE_DOT', 'SQUARE_DOT', 'DIAMOND_DOT'] = None
    default_value: Any = None
    items_ref: str = None
    update_ref: str = None

    def init(self, node: Node, is_input, identifier=None):
        node_sockets = node.inputs if is_input else node.outputs
        sock = node_sockets.new(self.type.bl_idname, self.name, identifier=identifier or '')
        sock.display_shape = self.display_shape or sock.default_shape
        if not self.enabled:
            sock.is_to_show = False
        if self.default_value is not None:
            sock.value = self.default_value
        if self.type == EnumSocket:
            sock.items_ref = self.items_ref
        if self.update_ref:
            sock.update_ref = self.update_ref


class NodeSettingsOperator:
    bl_label = "Node settings"
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

        if node.panel_props:
            panel_names = []
            for search_node in node.id_data.walk_back(node):
                if search_node.bl_idname == PanelNode.bl_idname:
                    panel_names.append(search_node.name)
            node['panel_names'] = panel_names

        if node.floor_props:
            panel_names = []
            for search_node in node.id_data.walk_back(node):
                if search_node.bl_idname == FloorNode.bl_idname:
                    panel_names.append(search_node.name)
            node['floor_names'] = panel_names

        wm = context.window_manager
        return wm.invoke_props_dialog(self, width=200)

    def draw(self, context):
        self.draw_all(self.layout, self.node)

    @staticmethod
    def draw_all(layout, node):  # should be used in Property panel
        box = layout.box()
        NodeSettingsOperator.draw_sockets(box, node)
        if node.panel_props:
            box = layout.box()
            NodeSettingsOperator.draw_remote_props(box, node, 'PANEL', node.panel_props)
        if node.floor_props:
            box = layout.box()
            NodeSettingsOperator.draw_remote_props(box, node, 'FLOOR', node.floor_props)

    @staticmethod
    def draw_sockets(layout, node):
        # grid = layout.grid_flow(row_major=True, columns=2)
        col = layout.column()
        col.alignment = 'RIGHT'
        row = col.row()
        row.label(text='Node properties value')
        row = row.row(align=True)
        row.alignment = 'RIGHT'
        row.label(text='Show')
        for sock in node.inputs:
            if not sock.is_linked and hasattr(sock, 'value'):
                row = col.row()
                row.prop(sock, 'value', text=sock.user_name or sock.name or sock.default_name)
                row.prop(sock, 'is_to_show', text='')

    @staticmethod
    def draw_remote_props(layout, node, props_type: Literal['PANEL', 'FLOOR'], sock_identifiers: list):
        node_names_key = 'panel_names' if props_type == 'PANEL' else 'floor_names'
        tree = node.id_data
        if node_names_key not in node or not node[node_names_key]:
            layout.label(text="Remote props was not found")
        else:
            remote_nodes = [tree.nodes[n] for n in node[node_names_key]]
            for identifier in sock_identifiers:
                col = layout.column(align=True, heading=identifier)
                # col.use_property_split = True
                # col.use_property_decorate = False
                for remote_node in remote_nodes:
                    socket = remote_node.get_socket(identifier, is_input=True)
                    node_label = remote_node.draw_label() if hasattr(remote_node, 'draw_label') else remote_node.bl_label
                    row = col.row()
                    row.prop(socket, 'value', text=f"{node_label}")


class DefaultNodeSettings(NodeSettingsOperator, Operator):
    bl_idname = "bn.default_node_settings"


class BaseNode:
    category: Categories = None
    repeat_last_socket = False
    input_template: tuple[SocketTemplate] = []  # only for static sockets, cause it is used for checking sockets API
    output_template: tuple[SocketTemplate] = []  # only for static sockets, cause it is used for checking sockets API
    props_template: tuple = []
    settings_viewer = None
    main_prop = None  # name of the input socket to show its value in first output socket
    panel_props: list[str] = []  # list of panel remote properties to show
    floor_props: list[str] = []  # list of floor remote properties to show

    @classmethod
    def poll(cls, tree):
        return tree.bl_idname == BuildingStyleTree.bl_idname

    def init(self, context):
        # update node colors
        self['version'] = bl_info['version']
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
            self.settings_viewer.draw_sockets(layout, self)

    def update(self):
        # update sockets
        links = {l.to_socket: l for l in self.id_data.links}
        if self.repeat_last_socket:
            sock_id_name = self.inputs[-1].bl_idname
            if sock_id_name == self.input_template[-1].type.bl_idname:
                if self.inputs[-1].is_linked:
                    identifier = self.input_template._fields[-1] if self.input_template else ''
                    self.input_template[-1].init(self, True, identifier)
                for low_sock, up_sock in zip(list(self.inputs)[::-1], list(self.inputs)[-2::-1]):
                    if up_sock in links or up_sock.bl_idname != sock_id_name:
                        break
                    if low_sock.bl_idname == sock_id_name and low_sock not in links:
                        self.inputs.remove(low_sock)

        self.node_update()

    def node_update(self):
        pass

    @staticmethod
    def execute(inputs, props):
        pass

    def gen_input_mapping(self) -> Optional[Type[NamedTuple]]:
        if self.input_template:  # this says that sockets have appropriate identifiers
            pos_identifiers = []
            key_identifiers = self.Inputs._fields
            if self.repeat_last_socket:  # there are extra socket not presented in the template
                for sock in reversed(self.inputs):
                    if sock.bl_idname == self.inputs[-1].bl_idname:
                        pos_identifiers.append(sock.py_identifier)
                    else:
                        break
                pos_identifiers.reverse()
                key_identifiers = key_identifiers[:-1]
            return namedtuple('Inputs', chain(key_identifiers, pos_identifiers))  # key words
        elif self.repeat_last_socket:
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
            for base, grid in build.facades:
                facade: Facade = inputs.facade(base)
                floors_stack = facade.floors_stack
                if floors_stack:
                    floors_stack.is_full = isclose(base.size.y - floors_stack.width, 0, abs_tol=0.001)
                    for floor in floors_stack:
                        floor.panels_stack.is_full = isclose(base.size.x - floor.panels_stack.width, 0, abs_tol=0.001)
                    facade.do_instance(build, grid)
        return build.bm


class PanelNode(BaseNode, Node):
    bl_idname = 'bn_PanelNode'
    bl_label = "Panel"
    category = Categories.PANEL
    settings_viewer = DefaultNodeSettings
    Inputs = namedtuple('Inputs', ['object', 'scalable', 'probability'])
    Props = namedtuple('Props', ['panel_index'])
    input_template = Inputs(
        SocketTemplate(ObjectSocket, enabled=False),
        SocketTemplate(BoolSocket, 'Scalable', enabled=False, default_value=True),
        SocketTemplate(FloatSocket, 'Probability', enabled=False, default_value=1),
    )
    Outputs = namedtuple('Outputs', ['panel'])
    output_template = Outputs(SocketTemplate(PanelSocket))
    main_prop = 'object'

    panel_index: bpy.props.IntProperty(description="Penal index in the collection")

    def draw_label(self):
        obj_socket = self.get_socket('object', is_input=True)
        return obj_socket.value and obj_socket.value.name or self.bl_label

    @staticmethod
    def execute(inputs: Inputs, props: Props):
        size_v_catch = None

        def panel_gen(facade: BaseFacade):
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
            panel.is_scalable = inputs.scalable(facade)
            return panel
        return panel_gen


class PanelAttributesNode(BaseNode, Node):
    bl_idname = 'bn_PanelAttributesNode'
    bl_label = "Panel Attributes"
    category = Categories.PANEL
    Outputs = namedtuple('Outputs', ['index'])
    output_template = Outputs(SocketTemplate(IntSocket, 'Index'))

    @staticmethod
    def execute(inputs, props):
        def panel_index(facade: BaseFacade):
            return facade.cur_panel_ind
        return panel_index


class PanelRandomizeNode(BaseNode, Node):
    bl_idname = 'bn_PanelRandomizeNode'
    bl_label = "Panel Randomize"
    category = Categories.PANEL
    repeat_last_socket = True
    settings_viewer = DefaultNodeSettings
    Inputs = namedtuple('Inputs', ['seed', 'panel'])
    input_template = Inputs(SocketTemplate(IntSocket, 'Seed'), SocketTemplate(PanelSocket))
    Outputs = namedtuple('Outputs', ['panel'])
    output_template = Outputs(SocketTemplate(PanelSocket))
    panel_props = ['probability']

    @staticmethod
    def execute(inputs: Inputs, params):
        random_streams = dict()
        last_facade = None

        def randomize_panels(facade: BaseFacade):
            nonlocal last_facade
            if facade != last_facade:
                random_streams.clear()
                last_facade = facade
            stream = random_streams.get(facade.cur_floor)
            if stream is None:
                stream = random.Random(int(inputs.seed(facade)) + facade.index)
                random_streams[facade.cur_floor] = stream
            panels = [p for inp in inputs[1: -1] if inp and (p := inp(facade)) is not None]
            return stream.choices(panels, weights=[p.probability for p in panels])[0]
        return randomize_panels


class MirrorPanelNode(BaseNode, Node):
    bl_idname = 'bn_MirrorPanelNode'
    bl_label = 'Mirror Panel'
    category = Categories.PANEL
    settings_viewer = DefaultNodeSettings
    Inputs = namedtuple('Inputs', ['panel', 'mirror_x', 'mirror_y'])
    input_template = Inputs(
        SocketTemplate(PanelSocket),
        SocketTemplate(BoolSocket, 'Mirror along X', False, display_shape='DIAMOND_DOT', default_value=True),
        SocketTemplate(BoolSocket, 'Mirror along Y', False, display_shape='DIAMOND_DOT'),
    )
    Outputs = namedtuple('Outputs', ['panel'])
    output_template = Outputs(SocketTemplate(PanelSocket))

    def draw_label(self):
        x = 'X' if self.get_socket('mirror_x', True).value else ''
        y = 'Y' if self.get_socket('mirror_y', True).value else ''
        if x or y:
            return f"{self.bl_label} - [{x}{' ' if x and y else ''}{y}]"
        return f"{self.bl_label}"

    @staticmethod
    def execute(inputs: Inputs, props):
        def mirror_panel(facade: BaseFacade):
            panel = inputs.panel(facade)
            if panel:
                if inputs.mirror_x(facade):
                    panel.mirror_x = True
                if inputs.mirror_y(facade):
                    panel.mirror_y = True
            return panel
        return mirror_panel


class JoinPanelsNode(BaseNode, Node):
    bl_idname = 'bn_JoinPanelsNode'
    bl_label = 'Join Panels'
    category = Categories.PANEL
    repeat_last_socket = True
    settings_viewer = DefaultNodeSettings
    Inputs = namedtuple('Inputs', ['align', 'panel'])
    input_template = Inputs(
        SocketTemplate(EnumSocket, 'Align', False, items_ref="JoinPanelsNode.align_items"),
        SocketTemplate(PanelSocket),
    )
    Outputs = namedtuple('Outputs', ['panel'])
    output_template = Outputs(SocketTemplate(PanelSocket))
    align_items = [(i, i.capitalize(), '') for i in ['RIGHT', 'TOP', 'LEFT', 'BOTTOM']]

    @staticmethod
    def execute(inputs: Inputs, props):
        def join_panels(facade: BaseFacade):
            shell = PanelShell()
            for _, panel_f in dropwhile(lambda inp: inp[0] != 'panel', zip(inputs._fields, inputs)):
                if panel_f is None:
                    continue
                panel = panel_f(facade)
                if not panel:
                    continue

                align = inputs.align(facade)
                if shell.size == Vector((0, 0)):
                    shell.add_panel(panel, Vector((0, 0)))
                elif align == 'RIGHT':
                    shell.add_panel(panel, Vector((shell.size.x / 2 + panel.size.x / 2, 0)))
                elif align == 'TOP':
                    shell.add_panel(panel, Vector((0, shell.size.y / 2 + panel.size.y / 2)))
                elif align == 'LEFT':
                    shell.add_panel(panel, Vector((-shell.size.x / 2 + -panel.size.x / 2, 0)))
                elif align == 'BOTTOM':
                    shell.add_panel(panel, Vector((0, -shell.size.y / 2 + -panel.size.y / 2)))
                else:
                    raise TypeError

            if shell.has_sub_panels():
                return shell
        return join_panels


class FloorNode(BaseNode, Node):
    bl_idname = 'bn_FloorNode'
    bl_label = "Floor"
    category = Categories.FLOOR
    settings_viewer = DefaultNodeSettings
    Inputs = namedtuple('Inputs', ['height', 'length', 'scalable', 'is_ground', 'left', 'fill', 'right'])
    input_template = Inputs(
        SocketTemplate(FloatSocket, 'Height', False, 'DIAMOND_DOT'),
        SocketTemplate(FloatSocket, 'Length', False, 'DIAMOND_DOT'),
        SocketTemplate(BoolSocket, 'Scalable', False, 'DIAMOND_DOT', True),
        SocketTemplate(BoolSocket, 'Is ground', False, 'DIAMOND_DOT', True),
        SocketTemplate(PanelSocket, 'Left'),
        SocketTemplate(PanelSocket, 'Fill'),
        SocketTemplate(PanelSocket, 'Right'),
    )
    Outputs = namedtuple('Outputs', ['floor'])
    output_template = Outputs(SocketTemplate(FloorSocket))
    panel_props = ['scalable']

    @staticmethod
    def execute(inputs: Inputs, props):
        catch = None

        def floor_gen(base: BaseFacade):
            floor = base.get_floor(base.request_size.x if (l := inputs.length(base)) <= 0 else l)
            floor.is_scalable = inputs.scalable(base)
            floor.is_ground = inputs.is_ground(base)

            if base.read_props:
                return [floor]

            def get_panel(func, counter) -> Optional[Panel]:
                if func:
                    for fail_ind, try_ind in enumerate(counter):
                        if fail_ind > 10:
                            break
                        base.cur_panel_ind = try_ind
                        _panel = func(base)
                        if _panel:
                            return _panel

            pan_stack = floor.panels_stack
            if panel := get_panel(inputs.left, count()):
                pan_stack.append(panel, throw_error=False)
            if last_panel := get_panel(inputs.right, count()):
                pan_stack.append(last_panel, throw_error=False)
            if not pan_stack.is_full:
                fill_count = count()
                for _ in range(10000):
                    panel = get_panel(inputs.fill, fill_count)
                    if panel is None:
                        break
                    if isclose(panel.size.x, 0, abs_tol=0.001):
                        raise RuntimeError(f"The width of some panel is too small")
                    try:
                        if last_panel:
                            pan_stack.insert(-1, panel)
                        else:
                            pan_stack.append(panel)
                    except IndexError:
                        break

            facade = Facade(base.request_size.y)
            if pan_stack:
                floor.height = max((p.size.y for p in pan_stack), default=0) if (h := inputs.height(base)) <= 0 else h
                if floor.panels_stack.is_full:
                    pan_stack.fit_scale()
                facade.floors_stack.append(floor, throw_error=False)
            return facade

        return floor_gen


class FloorAttributesNode(BaseNode, Node):
    bl_idname = 'bn_FloorAttributesNode'
    bl_label = "Floor Attributes"
    category = Categories.FLOOR
    Outputs = namedtuple('Outputs', ['index'])
    output_template = Outputs(
        SocketTemplate(IntSocket, 'Index', display_shape='DIAMOND'),
    )

    @staticmethod
    def execute(inputs, props):
        def floor_index(facade: BaseFacade):
            facade.depth.add('floor_index')
            return facade.cur_floor_ind

        return floor_index


class JoinFloorsNode(BaseNode, Node):
    bl_idname = 'bn_JoinFloorsNode'
    bl_label = 'Join Floors'
    category = Categories.FLOOR
    repeat_last_socket = True
    Inputs = namedtuple('Inputs', ['match_mode', 'direction', 'floor'])
    input_template = Inputs(
        SocketTemplate(EnumSocket, 'Match mode', False, items_ref='JoinFloorsNode.mode_items'),
        SocketTemplate(EnumSocket, 'Direction', False, items_ref='JoinFloorsNode.direction_items'),
        SocketTemplate(FloorSocket),
    )
    Outputs = namedtuple('Outputs', ['floor'])
    output_template = Outputs(SocketTemplate(FloorSocket))
    mode_items = [(i, i.capitalize(), '') for i in ['NONE', 'REPEAT', 'CYCLE']]
    direction_items = [(i, i.capitalize(), '') for i in ['VERTICAL', 'HORIZONTAL']]
    settings_viewer = DefaultNodeSettings

    @staticmethod
    def execute(inputs: Inputs, props):
        def join_floors(base: BaseFacade):
            facade = Facade(base.request_size.y)
            fac_funcs = list(filter(bool, reversed(inputs[inputs._fields.index('floor'): -1])))
            mode = inputs.match_mode(base)
            iter_funcs = {'NONE': iter, 'REPEAT': lambda a: chain(a, repeat(a[-1], 1000)), 'CYCLE': cycle}
            direction = inputs.direction(base)

            for fac_func in iter_funcs[mode](fac_funcs if direction == 'VERTICAL' else fac_funcs[::-1]):
                cur_len = facade.floors_stack and facade.floors_stack[0].panels_stack.width or 0
                cur_size = Vector((0, facade.floors_stack.width)) if direction == 'VERTICAL' else Vector((cur_len, 0))
                with base.size_context(base.request_size - cur_size):
                    sub_f: Facade = fac_func(base)
                if not sub_f.floors_stack:
                    break
                try:
                    if direction == 'VERTICAL':
                        facade.join_along_y(sub_f)
                    else:
                        facade.join_along_x(sub_f, base.request_size.x)
                except IndexError:
                    break

            if facade.floors_stack.is_full:
                facade.floors_stack.fit_scale()
            return facade
        return join_floors


class JoinFacadesNode(BaseNode, Node):
    bl_idname = "bn_JoinFacadesNode"
    bl_label = "Join Facades"
    category = Categories.FACADE
    repeat_last_socket = True
    Inputs = namedtuple('Inputs', ['match_mode', 'direction',  'facade'])
    input_template = Inputs(
        SocketTemplate(EnumSocket, 'Match mode', False, items_ref='JoinFacadesNode.match_mode_items'),
        SocketTemplate(EnumSocket, 'Direction', False, items_ref='JoinFacadesNode.direction_items'),
        SocketTemplate(FacadeSocket),
    )
    Outputs = namedtuple('Outputs', ['facade'])
    output_template = Outputs(SocketTemplate(FacadeSocket))
    match_mode_items = [(i, i.capitalize(), '') for i in ['NONE', 'REPEAT', 'CYCLE']]
    direction_items = [(i, i.capitalize(), '') for i in ['VERTICAL', 'HORIZONTAL']]
    settings_viewer = DefaultNodeSettings

    @staticmethod
    def execute(inputs: Inputs, props):
        def join_facades(base: BaseFacade):
            facade = Facade(base.request_size.y)
            fac_funcs = list(filter(bool, reversed(inputs[inputs._fields.index('facade'): -1])))
            mode = inputs.match_mode(base)
            iter_funcs = {'NONE': iter, 'REPEAT': lambda a: chain(a, repeat(a[-1], 1000)), 'CYCLE': cycle}
            direction = inputs.direction(base)
            is_empty = {f: False for f in fac_funcs}

            for fac_func in iter_funcs[mode](fac_funcs if direction == 'VERTICAL' else fac_funcs[::-1]):
                cur_len = facade.floors_stack and facade.floors_stack[0].panels_stack.width or 0
                cur_size = Vector((0, facade.floors_stack.width)) if direction == 'VERTICAL' else Vector((cur_len, 0))

                # facade always returns at list one floor even if the height of a base facade is 0
                if direction == 'VERTICAL' and isclose(base.request_size.y - cur_size.y, 0, abs_tol=0.001):
                    break
                with base.size_context(base.request_size - cur_size):
                    sub_f: Facade = fac_func(base)

                # break if all facades are empty
                if not sub_f.floors_stack:
                    is_empty[fac_func] = True
                    if all(is_empty.values()):
                        break
                try:
                    if direction == 'VERTICAL':
                        facade.join_along_y(sub_f)
                    else:
                        facade.join_along_x(sub_f, base.request_size.x)
                except IndexError:
                    break

            if facade.floors_stack.is_full:
                facade.floors_stack.fit_scale()
            return facade
        return join_facades


class FacadeNode(BaseNode, Node):
    bl_idname = 'bn_FacadeNode'
    bl_label = "Facade"
    category = Categories.FACADE
    settings_viewer = DefaultNodeSettings
    Inputs = namedtuple('Inputs', ['height', 'length', 'last', 'fill', 'first'])
    input_template = Inputs(
        SocketTemplate(FloatSocket, 'Height', False, 'DIAMOND_DOT'),
        SocketTemplate(FloatSocket, 'Length', False, 'DIAMOND_DOT'),
        SocketTemplate(FloorSocket, 'Last'),
        SocketTemplate(FloorSocket, 'Fill'),
        SocketTemplate(FloorSocket, 'First'),
    )
    Outputs = namedtuple('Outputs', ['facade'])
    output_template = Outputs(SocketTemplate(FacadeSocket))
    floor_props = ['scalable', 'is_ground']

    @staticmethod
    def execute(inputs: Inputs, params):
        def facade_generator(base: BaseFacade):
            use_height = base.request_size.y > (height := inputs.height(base)) > 0
            request_size = Vector((length if(length := inputs.length(base)) > 0 else base.request_size.x,
                                   height if use_height else base.request_size.y))
            if base.read_props:
                return

            def get_floors(func, counter) -> Optional[Facade]:
                _floors = None
                if func:
                    for fail_ind, try_ind in enumerate(counter):
                        if fail_ind > 10:
                            break
                        base.cur_floor_ind = try_ind
                        _floors = func(base)
                        if _floors:
                            break
                return _floors

            with base.size_context(request_size):
                facade = Facade(request_size.y)
                if first_floor := get_floors(inputs.first, count()):
                    if first_floor.floors_stack:
                        first = first_floor.floors_stack[0]
                        if not first.is_ground or (first.is_ground and isclose(base.level, 0, abs_tol=0.001)):
                            facade.join_along_y(first_floor, throw_error=False)
                if last_floor := get_floors(inputs.last, count()):
                    for floor in last_floor.floors_stack:
                        floor.is_last = True
                    facade.join_along_y(last_floor, throw_error=False)
                # fill floors
                if not facade.floors_stack.is_full:
                    fill_count = count()
                    for i in range(1000):
                        if not (fill_floor := get_floors(inputs.fill, fill_count)) or not fill_floor.floors_stack:
                            break
                        if any(isclose(floor.height, 0, abs_tol=0.001) for floor in fill_floor.floors_stack):
                            raise SizeError(f"The height of some panel is too small")
                        try:
                            if last_floor:
                                facade.floors_stack.insert(-len(last_floor.floors_stack), list(fill_floor.floors_stack))
                            else:
                                facade.join_along_y(fill_floor)
                        except IndexError:
                            break

            if facade.floors_stack.is_full:
                facade.floors_stack.fit_scale()
            return facade

        return facade_generator


class FacadeAttributesNode(BaseNode, Node):
    bl_idname = 'bn_FacadeAttributesNode'
    bl_label = 'Facade Attributes'
    category = Categories.FACADE
    Outputs = namedtuple('Outputs', ['height', 'length', 'left_angle', 'right_angle', 'mat_id', 'facade_index'])
    output_template = Outputs(
        SocketTemplate(FloatSocket, 'Height', display_shape='DIAMOND'),
        SocketTemplate(FloatSocket, 'Length', display_shape='DIAMOND'),
        SocketTemplate(FloatSocket, 'Left corner angle', display_shape='DIAMOND'),
        SocketTemplate(FloatSocket, 'Right corner angle', display_shape='DIAMOND'),
        SocketTemplate(IntSocket, 'Material index', display_shape='DIAMOND'),
        SocketTemplate(IntSocket, 'Index', display_shape='DIAMOND'),
    )

    @staticmethod
    def execute(inputs, props):
        def facade_height(facade: BaseFacade):
            return facade.size.y

        def facade_length(facade: BaseFacade):
            return facade.size.x

        def left_corner_angle(facade: BaseFacade):
            return facade.left_wall_angle

        def right_corner_angle(facade: BaseFacade):
            return facade.right_wall_angle

        def material_id(facade: BaseFacade):
            return facade.material_index

        def facade_index(facade: BaseFacade):
            return facade.index
        return facade_height, facade_length, left_corner_angle, right_corner_angle, material_id, facade_index


class MathNode(BaseNode, Node):
    bl_idname = 'bn_MathNode'
    bl_label = "Math"
    Inputs = namedtuple('Inputs', ['operation', 'val1', 'val2'])
    input_template = Inputs(
        SocketTemplate(EnumSocket, 'Operation', False, items_ref='MathNode.operation_items'),
        SocketTemplate(FloatSocket, display_shape='DIAMOND_DOT'),
        SocketTemplate(FloatSocket, display_shape='DIAMOND_DOT'),
    )
    operation_items = [
        ('add', 'Add', '', 0),
        ('subtract', 'Subtract', '', 1),
        ('multiply', 'Multiply', '', 2),
        ('divide', 'Divide', '', 3),
        ('remainder', 'Reminder', '', 4),
    ]
    Outputs = namedtuple('Outputs', ['value'])
    output_template = Outputs(SocketTemplate(FloatSocket, display_shape='DIAMOND_DOT'))
    main_prop = 'operation'
    settings_viewer = DefaultNodeSettings

    @staticmethod
    def execute(inputs: Inputs, props):
        funcs = {
            'add': lambda v1, v2: v1 + v2,
            'subtract': lambda v1, v2: v1 - v2,
            'multiply': lambda v1, v2: v1 * v2,
            'divide': lambda v1, v2: v1 / v2,
            'remainder': lambda v1, v2: v1 % v2,
        }

        def math(facade):
            return funcs[inputs.operation(facade)](inputs.val1(facade), inputs.val2(facade))
        return math


class BooleanMathNode(BaseNode, Node):
    bl_idname = "bn_BooleanMathNode"
    bl_label = "Boolean Math"
    Inputs = namedtuple('Inputs', ['operation', 'val1', 'val2'])
    input_template = Inputs(
        SocketTemplate(EnumSocket, 'Operation', False, items_ref='BooleanMathNode.operation_items',
                       update_ref='BooleanMathNode.update_operation'),
        SocketTemplate(BoolSocket, display_shape='DIAMOND_DOT'),
        SocketTemplate(BoolSocket, display_shape='DIAMOND_DOT'),
    )
    Outputs = namedtuple('Outputs', ['value'])
    output_template = Outputs(SocketTemplate(BoolSocket, display_shape='DIAMOND_DOT'))
    operation_items = [(i, i.capitalize().replace('_', ' '), '') for i in ['and', 'or', 'not']]
    main_prop = 'operation'
    settings_viewer = DefaultNodeSettings

    def update_operation(self: NodeSocket, context):
        self.node.get_socket('val2', True).is_to_show = self.value != 'not'

    @staticmethod
    def execute(inputs: Inputs, props):
        funcs = {
            'and': lambda v1, v2: bool(v1) and bool(v2),
            'or': lambda v1, v2: bool(v1) or bool(v2),
            'not': lambda v1, _: not bool(v1),
        }

        def boolean_math(facade: BaseFacade):
            return funcs[inputs.operation(facade)](inputs.val1(facade), inputs.val2(facade))
        return boolean_math


class IntegerValueNode(BaseNode, Node):
    bl_idname = "bn_IntegerValueNode"
    bl_label = "Integer"
    Inputs = namedtuple('Inputs', ['value'])
    input_template = Inputs(SocketTemplate(IntSocket, enabled=False, display_shape='DIAMOND_DOT'))
    Outputs = namedtuple('Outputs', ['value'])
    output_template = Outputs(SocketTemplate(IntSocket, display_shape='DIAMOND_DOT'))
    main_prop = 'value'
    settings_viewer = DefaultNodeSettings

    @staticmethod
    def execute(inputs: Inputs, props):
        def get_integer(facade: BaseFacade):
            return inputs.value(facade)
        return get_integer


class FloatValueNode(BaseNode, Node):
    bl_idname = "bn_FloatValueNode"
    bl_label = "Float"
    Inputs = namedtuple('Inputs', ['value'])
    input_template = Inputs(SocketTemplate(FloatSocket, enabled=False, display_shape='DIAMOND_DOT'))
    Outputs = namedtuple('Outputs', ['value'])
    output_template = Outputs(SocketTemplate(FloatSocket, display_shape='DIAMOND_DOT'))
    main_prop = 'value'
    settings_viewer = DefaultNodeSettings

    @staticmethod
    def execute(inputs: Inputs, props):
        def get_float(facade: BaseFacade):
            return inputs.value(facade)
        return get_float


class SelectInputNode(BaseNode, Node):
    bl_idname = "bn_SelectInputNode"
    bl_label = "Select Input"
    repeat_last_socket = True
    Inputs = namedtuple('Inputs', ['match_mode', 'index', 'input'])
    mode_items = [(i, i.capitalize(), '') for i in ['NONE', 'REPEAT', 'CYCLE']]
    input_template = Inputs(
        SocketTemplate(EnumSocket, 'Match mode', False, items_ref="SelectInputNode.mode_items"),
        SocketTemplate(IntSocket, 'Index'),
        SocketTemplate(InputSocket),
    )
    Outputs = namedtuple('Outputs', ['input'])
    output_template = Outputs(SocketTemplate(InputSocket))
    settings_viewer = DefaultNodeSettings

    @staticmethod
    def execute(inputs: Inputs, props):
        def get_input(facade: BaseFacade):
            func_ind = inputs._fields.index('input')
            input_funcs = {i: f for i, f in enumerate(inputs[func_ind:-1])}
            mode = inputs.match_mode(facade)
            if mode == 'NONE':
                index = inputs.index(facade)
            elif mode == 'REPEAT':
                index = min(len(input_funcs) - 1, inputs.index(facade))
            elif mode == 'CYCLE':
                index = inputs.index(facade) % len(input_funcs)
            else:
                raise TypeError(f"Unknown mode {mode}")
            input_f = input_funcs.get(int(index))
            if input_f:
                return input_f(facade)
        return get_input


class ComparisonMathNode(BaseNode, Node):
    bl_idname = "bn_ComparisonMathNode"
    bl_label = "Comparison Math"
    Inputs = namedtuple('Inputs', ['operation', 'value1', 'value2', 'tolerance'])
    input_template = Inputs(
        SocketTemplate(EnumSocket, 'Operation', False, items_ref='ComparisonMathNode.operation_items',
                       update_ref='ComparisonMathNode.update_mode'),
        SocketTemplate(FloatSocket, display_shape='DIAMOND_DOT'),
        SocketTemplate(FloatSocket, display_shape='DIAMOND_DOT'),
        SocketTemplate(FloatSocket, 'Tolerance', enabled=False, display_shape='DIAMOND_DOT', default_value=0.01),
    )
    Outputs = namedtuple('Outputs', ['value'])
    output_template = Outputs(SocketTemplate(BoolSocket, display_shape='DIAMOND_DOT'))

    def update_mode(self: NodeSocket, context):
        self.node.get_socket('tolerance', True).is_to_show = self.value == 'is_close'

    operation_items = [(i, i.capitalize().replace('_', ' '), '') for i in [
        'equal', 'is_close', 'not_equal', 'grater_than', 'grater_or_equal', 'less_than', 'less_or_equal']]
    main_prop = 'operation'
    settings_viewer = DefaultNodeSettings

    @staticmethod
    def execute(inputs: Inputs, props):
        funcs = {
            'equal': lambda v1, v2, v3: v1 == v2,
            'is_close': lambda v1, v2, v3: isclose(v1, v2, abs_tol=v3),
            'not_equal': lambda v1, v2, v3: v1 != v2,
            'grater_than': lambda v1, v2, _: v1 > v2,
            'grater_or_equal': lambda v1, v2, _: v1 >= v2,
            'less_than': lambda v1, v2, _: v1 < v2,
            'less_or_equal': lambda v1, v2, _: v1 <= v2,
        }

        def compare_values(facade: BaseFacade):
            return funcs[inputs.operation(facade)](inputs.value1(facade), inputs.value2(facade), inputs.tolerance(facade))
        return compare_values


class StyleOperationsMenu(Menu):
    bl_idname = "OBJECT_MT_style_operations"
    bl_label = "Style operations"

    def draw(self, context):
        lay = self.layout
        lay.operator_enum(ApplyBuildingStyleOperator.bl_idname, "mode")
        lay.separator()
        lay.operator(LinkBuildingStyleOperator.bl_idname, text="Link style to selected")
        lay.operator(SelectByStyleOperator.bl_idname, text="Select with the same style")


class ObjectPanel(Panel):
    bl_idname = "VIEW3D_PT_ObjectPanel"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "Building nodes"
    bl_label = "Building properties"

    def draw(self, context):
        col = self.layout.column()
        obj = context.object
        if obj:
            if obj.building_props.error:
                col.label(text=obj.building_props.error, icon='ERROR')
            props: ObjectProperties = obj.building_props
            row = col.row(align=True)
            row1 = row.row(align=True, heading="Building style:")
            row1.active = props.building_style is not None
            row1.prop(props, 'show_in_edit_mode', text='', icon='EDITMODE_HLT')
            row1.prop(props, 'realtime', text='', icon='RESTRICT_VIEW_OFF' if props.realtime else 'RESTRICT_VIEW_ON')
            row1.prop(props, 'show_in_render', text='',
                     icon='RESTRICT_RENDER_OFF' if props.show_in_render else 'RESTRICT_RENDER_ON')
            row2 = row.row(align=True)
            row2.menu(StyleOperationsMenu.bl_idname, text='', icon='DOWNARROW_HLT')
            col.template_ID(props, 'building_style', new=AddNewBuildingStyleOperator.bl_idname,
                            unlink=UnlinkBuildingStyleOperator.bl_idname)
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


class GeometryTreeInterface:
    VERSION = "0.11"
    VERSION_KEY = 'bn_version'

    def __init__(self, mod):
        self._mod = mod

        # bad tree
        if self.VERSION_KEY not in mod.node_group:
            if len(mod.node_group.nodes) > 2:
                raise ValueError(f'Given tree={mod.node_group} was created by user - changes are forbidden')
            else:
                self._arrange_tree(mod.node_group, mod.id_data)
                mod.node_group[self.VERSION_KEY] = self.VERSION
                self.update_modifier_interface()

        # old version
        elif mod.node_group[self.VERSION_KEY] != self.VERSION:
            self._arrange_tree(mod.node_group, mod.id_data)
            mod.node_group[self.VERSION_KEY] = self.VERSION
            self.update_modifier_interface()

    def set_points(self, obj: bpy.types.Object):
        self._mod[self._mod.node_group.inputs['Object'].identifier] = obj

    def set_instances(self, col: bpy.types.Collection):
        self._mod[self._mod.node_group.inputs['Collection'].identifier] = col

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
        tree.links.new(obj_n.inputs[0], in_n.outputs[5])  # <- points  "Input_6"
        tree.links.new(col_n.inputs[0], in_n.outputs[6])  # <- panels  "Input_7"
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

    def update_modifier_interface(self):
        self._mod[f"{self._mod.node_group.inputs['Vector'].identifier}_use_attribute"] = 1
        self._mod[f"{self._mod.node_group.inputs['Vector'].identifier}_attribute_name"] = "Normal"
        self._mod[f"{self._mod.node_group.inputs['Scale'].identifier}_use_attribute"] = 1
        self._mod[f"{self._mod.node_group.inputs['Scale'].identifier}_attribute_name"] = "Scale"
        self._mod[f"{self._mod.node_group.inputs['Selection'].identifier}_use_attribute"] = 1
        self._mod[f"{self._mod.node_group.inputs['Selection'].identifier}_attribute_name"] = "Is wall"
        self._mod[f"{self._mod.node_group.inputs['Instance Index'].identifier}_use_attribute"] = 1
        self._mod[f"{self._mod.node_group.inputs['Instance Index'].identifier}_attribute_name"] = "Wall index"


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
            try:
                self.building_style.apply(self.id_data)
            except Exception as e:
                self.error = repr(e)
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
    points: bpy.props.PointerProperty(type=bpy.types.Object)
    error: bpy.props.StringProperty()
    show_in_edit_mode: bpy.props.BoolProperty(
        default=True, description="Show building style in edit mode", update=update_show_in_edit)
    realtime: bpy.props.BoolProperty(
        default=True, description='Display building style in viewport', update=update_realtime)
    show_in_render: bpy.props.BoolProperty(
        default=True, description='Use building style during render', update=update_show_in_render)

    def apply_style(self):
        if self.id_data.mode == 'EDIT':
            can_be_updated = self.building_style and self.realtime and self.show_in_edit_mode
        else:
            can_be_updated = self.building_style and self.realtime
        if can_be_updated:
            try:
                self.building_style.apply(self.id_data)
            except Exception as e:
                self.error = repr(e)
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
            redundant_tree = modifier.node_group
            modifier.node_group = self._get_hostage_tree()
            bpy.data.node_groups.remove(redundant_tree)
            interface = GeometryTreeInterface(modifier)
            interface.update_modifier_interface()
            return interface
        else:
            return GeometryTreeInterface(modifier)

    def _get_hostage_tree(self):
        for tree in bpy.data.node_groups:
            if GeometryTreeInterface.VERSION_KEY in tree\
                    and GeometryTreeInterface.VERSION == tree[GeometryTreeInterface.VERSION_KEY]:
                return tree
        new_tree = bpy.data.node_groups.new('Hostage tree', 'GeometryNodeTree')
        return new_tree


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
        node2: Node = tree.nodes.new(FloorNode.bl_idname)
        node3: Node = tree.nodes.new(FacadeNode.bl_idname)
        node4: Node = tree.nodes.new(BuildingStyleNode.bl_idname)
        tree.links.new(node2.get_socket('fill', is_input=True), node1.outputs[0])
        tree.links.new(node3.get_socket('fill', is_input=True), node2.outputs[0])
        tree.links.new(node4.get_socket('facade', is_input=True), node3.outputs[0])
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
            center = Geometry.get_bounding_center([v.co for v in points])
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


class LinkBuildingStyleOperator(Operator):
    bl_idname = "bn.link_building_style"
    bl_label = "Link Building Style"
    bl_options = {"REGISTER", "UNDO"}

    @classmethod
    def description(cls, context, properties):
        return f'Add style="{context.object.building_props.building_style.name}" to selected objects'

    @classmethod
    def poll(cls, context):
        return bool(context.object)

    def execute(self, context):
        selected = context.selected_objects
        active = context.object
        style_tree = active.building_props.building_style
        for obj in selected:
            if obj != active:
                obj.building_props.building_style = style_tree
        return {'FINISHED'}


class SelectByStyleOperator(Operator):
    bl_idname = "bn.select_by_style"
    bl_label = "Select by style"
    bl_options = {"REGISTER", "UNDO"}

    @classmethod
    def description(cls, context, properties):
        return f'Select all objects with style="{context.object.building_props.building_style.name}"'

    @classmethod
    def poll(cls, context):
        if context.object and context.object.building_props.building_style:
            return True
        else:
            cls.poll_message_set("Active object doesn't have building style")
            return False

    def execute(self, context):
        active = context.object
        current_style = active.building_props.building_style
        for obj in context.scene.objects:
            if obj.building_props.building_style == current_style and obj.visible_get():
                obj.select_set(True)
        return {'FINISHED'}


class ApplyBuildingStyleOperator(Operator):
    bl_idname = "bn.apply_building_style"
    bl_label = "Apply Building Style"
    bl_options = {"REGISTER", "UNDO"}
    modes = [
        ("TO_ACTIVE", "Apply style (to active)", "Apply building style of active object"),
        ("TO_SELECTED", "Apply style (to selected)", "Apply building style of all selected objects"),
        ("CURRENT_TO_ALL", "Apply current style (to all)", "Apply style of visible objects with style equal to active object style"),
    ]

    mode: EnumProperty(items=modes)

    @classmethod
    def description(cls, context, properties):
        for mode in cls.modes:
            if mode[0] == properties.mode:
                return mode[2]

    @classmethod
    def poll(cls, context):
        if context.object and context.object.building_props.building_style:
            return True
        else:
            cls.poll_message_set("Active object doesn't have building style")
            return False

    def execute(self, context):
        if self.mode == 'TO_ACTIVE':
            self.apply_to_selected(context, context.object)
        elif self.mode == 'TO_SELECTED':
            for obj in context.selected_objects:
                if obj.type == 'MESH':
                    self.apply_to_selected(context, obj)
        elif self.mode == 'CURRENT_TO_ALL':
            current_style = context.object.building_props.building_style
            for obj in context.scene.objects:
                if obj.building_props.building_style == current_style and obj.visible_get():
                    self.apply_to_selected(context, obj)
        else:
            raise TypeError(f"Unknown({self.mode}) mode is given")
        return {'FINISHED'}

    @staticmethod
    def apply_to_selected(context, obj):
        bpy.ops.object.select_all(action='DESELECT')
        obj.select_set(True)
        context.view_layer.objects.active = None
        bpy.ops.object.duplicates_make_real()  # it's not always work if the object is active
        context.view_layer.objects.active = obj
        for mod in obj.modifiers:
            bpy.ops.object.modifier_apply(modifier=mod.name)
        obj.building_props.building_style = None

        # join
        obj.select_set(True)
        bpy.ops.object.join()


classes = dict()
for name, member in inspect.getmembers(sys.modules[__name__]):
    is_module_cls = inspect.isclass(member) and member.__module__ == __name__
    if is_module_cls:
        if any(base_cls in member.__bases__ for base_cls
               in [NodeTree, NodeSocket, Node, Panel, Operator, PropertyGroup, Menu, AddonPreferences]):
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

    def __add__(self, other: float) -> 'DistSlice':
        return DistSlice(self.start, None if self.stop is None else self.stop + other)

    def __iadd__(self, other: float) -> 'DistSlice':
        self.stop = None if self.stop is None else self.stop + other
        return self

    def __sub__(self, other: float) -> 'DistSlice':
        return DistSlice(self.start, None if self.stop is None else self.stop - other)

    def __isub__(self, other: float) -> 'DistSlice':
        if self.stop is not None:
            self.stop = self.stop - other
        return self

    def __eq__(self, other: 'DistSlice'):
        if isinstance(other, DistSlice):
            return self.start == other.start and self.stop == other.stop
        return NotImplemented

    def __repr__(self):
        start = self.start.__format__('.2f') if self.start is not None else None
        stop = self.stop.__format__('.2f') if self.stop is not None else None
        return f"<DistSlice({start}, {stop})>"


class Shape(ABC):
    is_scalable: bool

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
        self.is_scalable = True
        self.mirror_x = False
        self.mirror_y = False

    def copy(self):
        panel = Panel(self.obj_index, self.size.copy())
        panel.scale = self.scale.copy()
        panel.probability = self.probability
        panel.is_scalable = self.is_scalable
        panel.mirror_x = self.mirror_x
        panel.mirror_y = self.mirror_y
        return panel

    @property
    def stack_size(self):
        return self.size.x * self.scale.x

    def scale_along_stack(self, factor: float):
        self.scale *= Vector((factor, 1))

    def set_scope_padding(self, padding):
        self.size.x += padding[0] + padding[2]
        self.size.y += padding[1] + padding[3]

    def do_instance(self, build: 'Building', location: Vector, scale: Vector, normal: Vector, direction):
        mirror_vec = Vector((-1 if self.mirror_x else 1, -1 if self.mirror_y else 1))
        vec = build.bm.verts.new(location)
        vec[build.norm_lay] = normal
        vec[build.scale_lay] = (*(self.scale * mirror_vec * scale), 1)
        vec[build.ind_lay] = self.obj_index

    def __repr__(self):
        return f"<Panel:{self.obj_index}>"


class PanelShell(Shape):
    def __init__(self):
        self._sub_panels: list[Panel] = []
        self._sub_positions: list[Vector] = []
        self.size: Vector = Vector((0, 0))
        self.scale: Vector = Vector((1, 1))

        # user attributes
        self.mirror_x = False
        self.mirror_y = False

    def copy(self):
        shell = PanelShell()
        shell._sub_panels = [p.copy() for p in self._sub_panels]
        shell._sub_positions = [v.copy() for v in self._sub_positions]
        shell.size = self.size.copy()
        shell.scale = self.scale.copy()
        shell.mirror_x = self.mirror_x
        shell.mirror_y = self.mirror_y
        return shell

    @property
    def probability(self):
        return sum(p.probability for p in self._sub_panels) / len(self._sub_panels)

    @property
    def is_scalable(self):
        if self._sub_panels:
            return any(p.is_scalable for p in self._sub_panels)
        else:
            return True

    def add_panel(self, panel: Panel, position: Vector):
        self._sub_panels.append(panel)
        self._sub_positions.append(position)
        shell_corners = [Vector((-self.size.x / 2, -self.size.y / 2)), Vector((self.size.x / 2, self.size.y / 2))]
        # todo take into account scale of the panel?
        panel_corners = [Vector((-panel.size.x / 2, -panel.size.y / 2)), Vector((panel.size.x / 2, panel.size.y / 2))]
        panel_corners = [c + position for c in panel_corners]
        min_v, max_v = Geometry.get_bounding_verts(shell_corners + panel_corners)
        new_center = Geometry.get_bounding_center([min_v, max_v])
        self._sub_positions = [p - new_center for p in self._sub_positions]
        self.size = max_v - min_v

    @property
    def stack_size(self):
        return self.size.x * self.scale.x

    def scale_along_stack(self, factor: float):
        self.scale *= Vector((factor, 1))

    def do_instance(self, build: 'Building', location: Vector, scale: Vector, normal: Vector, direction):
        mirror_vec = Vector((-1 if self.mirror_x else 1, -1 if self.mirror_y else 1))
        for panel, sub_loc in zip(self._sub_panels, self._sub_positions):
            sub_loc *= self.scale * scale * mirror_vec
            sub_loc_3d = direction * sub_loc.x + Vector((0, 0, sub_loc.y))
            panel.do_instance(build, location + sub_loc_3d, scale * self.scale * mirror_vec, normal, direction)

    def has_sub_panels(self) -> bool:
        return bool(self._sub_panels)

    def __repr__(self):
        indexes = ','.join([str(p.obj_index) for p in self._sub_panels])
        return f"<PanelShell:{indexes}>"


class Floor(Shape):
    def __init__(self, index, length):
        self.index = index
        self.z_scale = 1
        self.panels_stack: ShapesStack[Panel] = ShapesStack(length)

        # user attributes
        self.height = None
        self.is_scalable = True
        self.is_ground = True

        # util props
        self.is_last = False

    def copy(self, copy_panels=True):
        floor = Floor(self.index, self.panels_stack.max_width)
        floor.z_scale = self.z_scale
        floor.height = self.height
        floor.is_scalable = self.is_scalable
        floor.is_ground = self.is_ground
        floor.is_last = self.is_last
        if copy_panels:
            floor.panels_stack = self.panels_stack.copy()
        return floor

    @property
    def stack_size(self):
        return self.height * self.z_scale

    @property
    def is_ledge(self):
        return isclose(self.panels_stack[0].size.y, 0, abs_tol=0.001) if self.panels_stack else False

    def scale_along_stack(self, factor: float):
        self.z_scale *= factor

    def do_instance(self, build: 'Building', start: Vector, direction: Vector, normal: Vector, cell: 'GridCell',
                    z_factor):
        """    +--+--+--+   3D
        start  *  │  │  │
               +--+--+--+--------→ direction
        """
        xy_shift = 0
        panels = cell.pick_panels(self)
        width = sum(p.stack_size for p in panels)
        scalable_width = sum(p.stack_size for p in panels if p.is_scalable)
        panels_range = cell.x_range

        if panels and panels[-1] == self.panels_stack[-1]:
            """
              +-------+-----------+ - - - +
              │+---------+        │       │
              │+---------+        │       │
              +-------+-----------+ - - - +
               ←  panels →
                      ←    cell   →←empty →
              ←            facade         →
            """
            if cell.x_range.stop > self.panels_stack.width:
                panels_range -= cell.x_range.stop - self.panels_stack.width

        xy_factor = (panels_range.length - (width - scalable_width)) / scalable_width
        for panel in panels:
            p_xy_factor = xy_factor if panel.is_scalable else 1
            size_x = panel.stack_size * p_xy_factor
            z_scale = self.stack_size / panel.size.y * z_factor if not isclose(panel.size.y, 0, abs_tol=0.001) else 1
            xy_shift += size_x / 2
            panel.do_instance(build, start + direction * xy_shift, Vector((p_xy_factor, z_scale)), normal, direction)
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
        self.is_full = False

    def copy(self):
        stack = ShapesStack(self.max_width)
        stack._shapes = [shape.copy() for shape in self._shapes]
        stack._cum_width = self._cum_width.copy()
        return stack

    def append(self, shape: Shape, throw_error=True):
        if self.can_be_added(shape.stack_size):
            self._cum_width.append(self._cum_width[-1] + (shape and shape.stack_size or 0))
            self._shapes.append(shape)
        else:
            self.is_full = True
            if throw_error:
                raise IndexError("Given shape is too big or shape stuck is full")

    def extend(self, shapes: list[Shape], throw_error=True):
        if self.can_be_added(sum(s.stack_size for s in shapes)):
            self._cum_width.extend(self._cum_width[-1] + s.stack_size for s in shapes)
            self._shapes.extend(shapes)
        else:
            self.is_full = True
            if throw_error:
                raise IndexError("Given shapes are too big or shape stuck is full")

    def insert(self, index: int, shape: Union[Shape, list[Shape]]):
        if isinstance(shape, list):
            if self.can_be_added(sum(s.stack_size for s in shape)):
                self[index: index] = shape
                return
        else:
            if self.can_be_added(shape.stack_size):
                self[index: index] = [shape]
                return

        self.is_full = True
        raise IndexError("Given shape is too big or shape stuck is full")

    def replace(self, shapes: list[Shape], position: DistSlice) -> list[Shape]:
        replace_ind = self._range_to_indexes(position)
        removed_panels = self[replace_ind]
        self[replace_ind] = shapes
        return removed_panels

    @property
    def width(self):
        return self._cum_width[-1]

    def calc_scalable_width(self):
        return sum(s.stack_size for s in self._shapes if s.is_scalable)

    def fit_scale(self):
        scalable_width = self.calc_scalable_width()
        if not scalable_width:
            return
        scale = (self.max_width - (self.width - scalable_width)) / scalable_width
        for shape in (s for s in self._shapes if s.is_scalable):
            shape.scale_along_stack(scale)
        self._cum_width = list(accumulate((p.stack_size for p in self._shapes), initial=0))

    def can_be_added(self, size: float) -> bool:
        """               │←-→│ the scale distance if the shape will be added
        +-------+------+------+-----
        │ *     │ *    │  new │
                          │
                          │
                       │←→│     the scale distance if the shape won't be added
        +-------+------+------  in this case the panel should not be added
        │ *     │ *    │
        """
        # stack always should has at list one non flat item
        if not any(not isclose(s.stack_size, 0, abs_tol=0.001) for s in self._shapes):
            return True
        # shape with 0 size always can be added
        if size == 0:
            return True
        cur_scale_dist = self.max_width - self.width
        if cur_scale_dist < 0:
            return False
        new_scale_dist = self.width + size - self.max_width
        if new_scale_dist < 0:
            return True
        if new_scale_dist > self.calc_scalable_width():
            return False
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
            right_shape_ind = bisect.bisect(self._cum_width, dist_range.stop + 0.00001) - 1  # ...01 fix precision
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
    def __getitem__(self, key: float) -> ShapeType: ...
    @overload
    def __getitem__(self, key: slice) -> list[ShapeType]: ...
    @overload
    def __getitem__(self, key: DistSlice) -> list[ShapeType]: ...

    def __getitem__(self, key):
        if isinstance(key, (int, slice)):
            return self._shapes[key]
        if isinstance(key, DistSlice):
            return self._shapes[self._range_to_indexes(key)]
        if isinstance(key, float):
            position = bisect.bisect(self._cum_width, key) - 1
            return self._shapes[position]
        raise TypeError

    @overload
    def __setitem__(self, key: int, shape: Shape): ...
    @overload
    def __setitem__(self, key: slice, shape: list[Shape]): ...

    def __setitem__(self, key, shape):
        if isinstance(key, int):
            index = key
            old_panel_size = self._cum_width[index + 1] - self._cum_width[index]
            new_panel_size = shape.stack_size
            impact_size = new_panel_size - old_panel_size
            self._shapes[index] = shape
            self._cum_width = [self._cum_width[:index + 1]] + [old_s + impact_size for old_s in
                                                               self._cum_width[index + 1:]]
        elif isinstance(key, slice):
            shapes = shape
            start = key.start if key.start is not None else 0
            stop = key.stop if key.stop is not None else len(self._shapes)
            old_shapes_size = sum(s - s_prev for s, s_prev in zip(
                self._cum_width[start + 1: stop + 1], self._cum_width[start: stop]))
            size = sum(s.stack_size for s in shapes)
            impact_size = size - old_shapes_size
            self._shapes[start: stop] = shapes
            self._cum_width[start + 1: stop + 1] = [self._cum_width[start] + size]
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
    def __init__(self, height: float):
        self.floors_stack: ShapesStack[Floor] = ShapesStack(height)

    @property
    def last_floors(self) -> list[Floor]:
        last_fs = []
        for floor in reversed(self.floors_stack):
            if floor.is_last:
                last_fs.append(floor.copy(self))
            else:
                break
        last_fs.reverse()
        return last_fs

    def join_along_x(self, facade: 'Facade', length):
        is_floor_full = False
        for i, sub_floor in enumerate(facade.floors_stack):
            # generate base floor
            try:
                floor = self.floors_stack[i]
            except IndexError:
                floor = sub_floor.copy(copy_panels=False)
                floor.panels_stack.max_width = length
                self.floors_stack.append(floor, throw_error=False)
            # add empty panels if facades has different number of floors
            if i > 0 and not is_floor_full:
                empty_dist = self.floors_stack[0].panels_stack.width \
                             - (floor.panels_stack.width + sub_floor.panels_stack.width)
                if not isclose(empty_dist, 0, abs_tol=0.001):
                    shell = PanelShell()
                    shell.size = Vector((empty_dist, floor.height))
                    floor.panels_stack.append(shell)
            # fill base floor
            try:
                floor.panels_stack.extend(list(sub_floor.panels_stack))
            except IndexError:
                is_floor_full = True
                break
        # extend last facade with empty floors
        for i, floor in enumerate(self.floors_stack):
            if i > 0:
                empty_dist = self.floors_stack[0].panels_stack.width - floor.panels_stack.width
                if not isclose(empty_dist, 0, abs_tol=0.001):
                    shell = PanelShell()
                    shell.size = Vector((empty_dist, floor.height))
                    floor.panels_stack.append(shell)
        # scale panels
        if is_floor_full:
            for f in self.floors_stack:
                f.panels_stack.fit_scale()
            raise IndexError

    def join_along_y(self, facade: 'Facade', throw_error=True):
        self.floors_stack.extend(list(facade.floors_stack), throw_error=throw_error)

    def do_instance(self, build: 'Building', grid: 'CentredMeshGrid'):
        """     ↑ direction 3D
                +------------+
                │  floor     │
        start   *------------+-----→ Panels direction
        """
        used_faces = set()
        for cell in grid:
            if all(fi in used_faces for fi in cell.face_indexes):
                continue
            elif any(fi in used_faces for fi in cell.face_indexes):
                raise RuntimeError("Some polygon was already handled")

            cell = cell.fit_to_shape(self.floors_stack)
            if cell is None:
                continue
            used_faces.update(cell.face_indexes)
            floors = cell.pick_floors(self.floors_stack)

            # fix range in case if facade does not cover ful height
            current_range = cell.y_range
            is_top = floors[-1] == self.floors_stack[-1]
            if is_top:
                if cell.y_range.stop > self.floors_stack.width:
                    current_range -= cell.y_range.stop - self.floors_stack.width

            height = sum(f.stack_size for f in floors)
            scalable_height = sum(f.stack_size for f in floors if f.is_scalable)
            z_factor = (current_range.length - (height - scalable_height)) / scalable_height

            # replace top floors if necessary
            fixed_floors = None
            if cell.is_top and not is_top:
                last_fs = self.last_floors
                if last_fs:
                    fixed_floors: ShapesStack[floors] = ShapesStack(current_range.length)
                    fixed_floors.extend([f.copy(build.cur_facade) for f in floors])
                    fixed_floors.fit_scale()
                    last_fs_height = sum(f.stack_size for f in last_fs)
                    fixed_floors.replace(last_fs, DistSlice(current_range.stop - current_range.start - last_fs_height, current_range.stop - current_range.start))
                    fixed_floors.fit_scale()

            face = build._base_bm.faces[cell.face_indexes[0]]
            start, max_l = Geometry.get_bounding_loops(face)
            direction = Vector((0, 0, 1))
            panels_direction = ((max_l.vert.co - start.vert.co) * Vector((1, 1, 0))).normalized()
            z_shift = 0
            for floor in fixed_floors or floors:
                f_z_factor = z_factor if floor.is_scalable and not fixed_floors else 1
                size = floor.stack_size * f_z_factor
                z_shift += size / 2
                floor.do_instance(build, start.vert.co + direction * z_shift, panels_direction, face.normal,
                                  cell, f_z_factor)
                z_shift += size / 2

    def __repr__(self):
        floors = '\n'.join([repr(floor) for floor in self.floors_stack[::-1]])
        return f"<Facade: \n{floors}>"


class BaseFacade:
    def __init__(self, index, size: Vector, mat_index: int, level: float):
        self.index = index
        self.cur_floor: Floor = None
        self.cur_floor_ind = 0  # it's not always the last index in the floors stack
        self.cur_panel_ind = None  # it's not always the last index in the panels stack
        self.read_props = False
        self.size: Vector = size
        self.level = level

        self.depth: set[Literal['floor_index']] = set()

        self.material_index = mat_index
        self.left_wall_angle = None
        self.right_wall_angle = None

        # util props
        self.request_size = size

    def get_floor(self, width=None) -> Floor:
        floor = Floor(self.index, width or self.size.x)
        self.cur_floor = floor
        return floor

    @contextmanager
    def reading_props(self):
        current_state = self.read_props
        try:
            self.read_props = True
            yield None
        finally:
            self.read_props = current_state

    @contextmanager
    def size_context(self, size: Vector = None):
        last_size = self.request_size.copy()
        if size:
            self.request_size = size
        yield None
        self.request_size = last_size


class Building:
    def __init__(self, base_bm):
        bm = bmesh.new()
        self.norm_lay = bm.verts.layers.float_vector.new("Normal")
        self.scale_lay = bm.verts.layers.float_vector.new("Scale")
        self.ind_lay = bm.verts.layers.int.new("Wall index")
        self.bm: BMesh = bm

        self.cur_facade: BaseFacade = None

        self._base_bm: BMesh = base_bm

    @property
    def facades(self) -> Iterable[tuple[BaseFacade, 'CentredMeshGrid']]:
        wall_lay = self._base_bm.faces.layers.int.get("Is wall") or self._base_bm.faces.layers.int.new("Is wall")
        crease_lay = self._base_bm.edges.layers.crease.active
        min_build_v, _ = Geometry.get_bounding_verts([v.co for v in self._base_bm.verts])

        visited = set()
        fac_ind = count()
        for face in self._base_bm.faces:
            if face in visited:
                continue
            is_vertical = isclose(face.normal.dot(Vector((0, 0, 1))), 0, abs_tol=0.1)
            is_valid = is_vertical and len(face.verts) > 3 and not isclose(face.calc_area(), 0, abs_tol=0.1)
            if is_valid:

                facade_grid = Geometry.connected_coplanar_faces(face, crease_lay)
                first_cell = next(iter(facade_grid))
                min_facade_v, _ = Geometry.get_bounding_verts([v.co for v in self._base_bm.faces[first_cell.face_indexes[0]].verts])
                facade = BaseFacade(next(fac_ind), facade_grid.size, face.material_index, min_facade_v.z - min_build_v.z)
                left_ind, right_ind = facade_grid.corner_cells()
                left_loop, _ = Geometry.get_bounding_loops(self._base_bm.faces[left_ind])
                facade.left_wall_angle = left_loop.link_loop_prev.edge.calc_face_angle(3.14)
                _, right_loop = Geometry.get_bounding_loops(self._base_bm.faces[right_ind])
                facade.right_wall_angle = right_loop.link_loop_prev.edge.calc_face_angle(3.14)
                self.cur_facade = facade
                yield facade, facade_grid

                for cell in facade_grid:
                    _face = self._base_bm.faces[cell.face_indexes[0]]
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


class GridCell:
    """
    >>> gr = CentredMeshGrid()
    >>> gr.add(Vector((0, 0)), Vector((1., 1.)), 0)
    >>> gr.add(Vector((1, 0)), Vector((2., 1.)), 1)
    >>> gr.add(Vector((0, 1)), Vector((1., 2.)), 2)
    >>> gr.add(Vector((1, 1)), Vector((2., 2.)), 3)
    >>> gr.add(Vector((1, 2)), Vector((2., 2.)), 4)
    >>> gr.clean_grid()
    >>> gr
    array([[-1,  4],
           [ 2,  3],
           [ 0,  1]])
    >>> first_cell = next(iter(gr))
    >>> first_cell
    array([[0]])
    >>> first_cell.x_range
    <DistSlice(0.00, 1.00)>
    >>> first_cell.is_right
    False
    >>> first_cell.is_top
    False
    >>> first_cell.face_indexes
    [0]
    >>> joined_cell = first_cell.join_up()
    >>> joined_cell
    array([[0],
           [2]])
    >>> joined_cell.join_up()
    Traceback (most recent call last):
        ...
    RuntimeError: Up row can't be appended
    >>> joined_cell = joined_cell.join_right()
    >>> joined_cell
    array([[0, 1],
           [2, 3]])
    >>> joined_cell.x_range
    <DistSlice(0.00, 3.00)>
    >>> joined_cell.y_range
    <DistSlice(0.00, 3.00)>
    >>> joined_cell.is_top
    False
    >>> joined_cell.is_right
    True
    >>> joined_cell.face_indexes
    [0, 1, 2, 3]
    >>> visited_cells = set(gr)
    >>> visited_cells.update(gr)
    >>> len(visited_cells)
    5
    """
    def __init__(self, grid, row_range: slice, col_range: slice):
        if -1 in grid.cell_data[row_range, col_range]:
            raise TypeError(f"There are empty cells in given range ({grid.cell_data[row_range, col_range]})")

        self._grid: CentredMeshGrid = grid
        self._row_range: slice = row_range
        self._col_range: slice = col_range

    @property
    def x_range(self) -> DistSlice:
        return DistSlice(self._grid.cum_size_x[self._col_range.start], self._grid.cum_size_x[self._col_range.stop])

    @property
    def y_range(self) -> DistSlice:
        return DistSlice(self._grid.cum_size_y[self._row_range.start], self._grid.cum_size_y[self._row_range.stop])

    @property
    def is_top(self) -> bool:
        is_last_row = len(self._grid.cell_data) == self._row_range.stop
        widest_cell_i = max((i for i in range(self._col_range.start, self._col_range.stop)),
                            key=lambda i: self._grid.size_x[i])
        return is_last_row or self._grid.cell_data[self._row_range.stop, widest_cell_i] == -1

    @property
    def is_right(self) -> bool:
        is_last_column = len(self._grid.cell_data[0]) == self._col_range.stop
        return is_last_column or -1 in self._grid.cell_data[self._row_range, self._col_range.stop]

    @property
    def face_indexes(self) -> list[int]:
        return self._grid.cell_data[self._row_range, self._col_range].flatten().tolist()

    def join_up(self) -> 'GridCell':
        if not self.is_top:
            try:
                new_row_range = slice(self._row_range.start, self._row_range.stop+1)
                return GridCell(self._grid, new_row_range, self._col_range)
            except TypeError:
                pass
        raise RuntimeError(f"Up row can't be appended")

    def join_right(self) -> 'GridCell':
        if not self.is_right:
            try:
                new_col_range = slice(self._col_range.start, self._col_range.stop+1)
                return GridCell(self._grid, self._row_range, new_col_range)
            except TypeError:
                pass
        raise RuntimeError(f"Right column can't be appended")

    def fit_to_shape(self, floors: ShapesStack[Floor]) -> Optional['GridCell']:

        # join along Y
        joined_cell = None
        floors_in_range = None
        nothing_to_join = False
        last_normal_floor = next(f for f in reversed(floors) if not f.is_ledge)
        for _ in range(1000):
            try:
                if joined_cell is None:
                    joined_cell = self
                else:
                    joined_cell = joined_cell.join_up()
            except RuntimeError:
                nothing_to_join = True

            floors_in_range = floors[joined_cell.y_range]
            # if last cell is too short to fit a floor
            if nothing_to_join and not floors_in_range:
                floors_in_range = joined_cell.pick_floors(floors)
                if not floors_in_range:
                    return None
                break

            # the floor row is too small
            if not nothing_to_join and not floors_in_range:
                continue

            # check if there is unused top rows
            if not nothing_to_join and floors_in_range[-1] == last_normal_floor:
                continue

            break

        # join along X
        nothing_to_join = False
        start_cell = joined_cell
        joined_cell = None
        for _ in range(1000):
            try:
                if joined_cell is None:
                    joined_cell = start_cell
                else:
                    joined_cell = joined_cell.join_right()
            except RuntimeError:
                nothing_to_join = True

            panels = [f.panels_stack[joined_cell.x_range] for f in floors_in_range]
            if nothing_to_join and not all(panels):
                panels = [joined_cell.pick_panels(f) for f in floors_in_range]
                if not all(panels):
                    return None
                break

            # the column is too small
            if not nothing_to_join and not all(panels):
                continue

            # check if there is unused right columns
            if not nothing_to_join and any([ps[-1] == f.panels_stack[-1] for ps, f in zip(panels, floors_in_range)]):
                continue

            break
        return joined_cell

    def pick_floors(self, floors: ShapesStack[Floor]) -> list[Floor]:
        f_in_range = floors[self.y_range]
        if not f_in_range:
            try:
                f_in_range.append(floors[self.y_range.start + self.y_range.length / 2])
            except IndexError:
                pass
        return f_in_range

    def pick_panels(self, floor: Floor) -> list[Panel]:
        panels = floor.panels_stack[self.x_range]
        if not panels:
            try:
                panels.append(floor.panels_stack[self.x_range.start + self.x_range.length / 2])
            except IndexError:
                pass
        return panels

    def __eq__(self, other: 'GridCell'):
        if isinstance(other, GridCell):
            return id(self._grid) == id(other._grid) and self._row_range == other._row_range \
                   and self._col_range == other._col_range
        return NotImplemented

    def __hash__(self):
        return hash((self._grid, self._row_range.start, self._row_range.stop, self._col_range.start, self._col_range.stop))

    def __repr__(self):
        return repr(self._grid.cell_data[self._row_range, self._col_range])


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
    >>> gr.cell_data
    array([[ 0,  1],
           [ 2, -1]])
    >>> gr.size_x
    array([1., 2.])
    >>> gr.size_y
    array([1., 3.])
    >>> [fi.face_indexes[0] for fi in gr]
    [0, 1, 2]
    """

    def __init__(self):
        self.cell_data: np.array[int] = np.full((100, 100), -1)
        self.size_x = np.full(100, -1.0)
        self.size_y = np.full(100, -1.0)

        self._center_row = 50
        self._center_col = 50

        self.cum_size_x = None
        self.cum_size_y = None

    def add(self, cord: Vector, size: Vector, face_ind: int):
        if self.cum_size_x is not None:
            raise RuntimeError("Can't add new items to initialized grid")
        grid_pos = self._to_ind(cord)
        self.cell_data[grid_pos] = face_ind
        self.size_x[grid_pos[1]] = size.x
        self.size_y[grid_pos[0]] = size.y

    def clean_grid(self):
        self.size_x = self.size_x[np.any(self.cell_data != -1, 0)]
        self.size_y = self.size_y[np.any(self.cell_data != -1, 1)]
        self.cell_data = self.cell_data[..., np.any(self.cell_data != -1, 0)][np.any(self.cell_data != -1, 1), ...]
        self.cum_size_x = list(accumulate(self.size_x, initial=0))
        self.cum_size_y = list(accumulate(self.size_y, initial=0))

    @property
    def size(self) -> Vector:
        return Vector((np.sum(self.size_x[self.size_x > 0]), np.sum(self.size_y[self.size_y > 0])))

    def corner_cells(self) -> tuple[int, int]:
        left = next(fi[0] for fi in self.cell_data if fi[0] != -1)
        right = next(fi[-1] for fi in self.cell_data if fi[-1] != -1)
        return left, right

    def _to_ind(self, coord: Vector) -> tuple[int, int]:
        return self._center_row + int(coord.y), self._center_col + int(coord.x)

    def __iter__(self) -> Iterator[GridCell]:
        return self._walk_cells()

    def __repr__(self):
        return repr(self.cell_data[::-1])

    def _walk_cells(self):
        for i_row in range(len(self.cell_data)):
            for i_col in range(len(self.cell_data[0])):
                if self.cell_data[i_row, i_col] != -1:
                    yield GridCell(self, slice(i_row, i_row+1), slice(i_col, i_col+1))


class Geometry:
    @staticmethod
    def get_bounding_verts(verts: list[Vector]) -> tuple[Vector, Vector]:  # min, max
        dim = len(verts[0])
        if dim == 3:
            min_v = Vector((min(v.x for v in verts), min(v.y for v in verts), min(v.z for v in verts)))
            max_v = Vector((max(v.x for v in verts), max(v.y for v in verts), max(v.z for v in verts)))
        elif dim == 2:
            min_v = Vector((min(v.x for v in verts), min(v.y for v in verts)))
            max_v = Vector((max(v.x for v in verts), max(v.y for v in verts)))
        else:
            raise TypeError(f"Vectors of size 2 or 3 are expected, size:{dim} is given")
        return min_v, max_v

    @staticmethod
    def get_bounding_center(verts: list[Vector]) -> Vector:
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


class SizeError(Exception):
    """When an element is to small to perform operation"""


def bl_sort_str(str1: str, str2: str) -> int:
    """BLender sorts objects names differently compare to the sorted Python function
    https://developer.blender.org/diffusion/B/browse/master/source/blender/blenlib/intern/string.c;5f59bf00444bf310d0ad0dd20039839912af5122$882

    >>> sorted(['Obj.2', 'Obj 3', 'Obj.1', 'Obj 4', 'Obj', 'obj'], key=cmp_to_key(bl_sort_str))
    ['Obj', 'Obj.1', 'Obj.2', 'Obj 3', 'Obj 4', 'obj']
    """
    for c1, c2 in zip(str1, str2):
        if c1 == c2:
            continue
        elif c1 == '.':
            return -1
        elif c2 == '.':
            return 1
        elif c1 < c2:
            return -1
        elif c1 > c2:
            return 1

    if len(str1) > len(str2):
        return 1
    elif len(str1) < len(str2):
        return -1
    else:
        return 0


def transfer_data_menu(self, context):
    self.layout.operator(LinkBuildingStyleOperator.bl_idname, icon='HOME')


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
                    obj_props.error = repr(e)
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


@persistent
def update_file(scene):
    for tree in (t for t in bpy.data.node_groups if t.bl_idname == BuildingStyleTree.bl_idname):
        try:
            tree.update_sockets()
        except Exception:
            traceback.print_exc()


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
    bpy.app.handlers.load_post.append(transfer_data_menu)  # this is hack to store function somewhere
    bpy.types.VIEW3D_MT_make_links.append(transfer_data_menu)
    if __name__ == "__main__":
        update_file(None)
    else:
        bpy.app.handlers.load_post.append(update_file)
    print("Building Nodes: initialized")


def unregister():
    try:
        fun_ind = [f.__name__ for f in bpy.app.handlers.load_post].index(update_file.__name__)
        fun = bpy.app.handlers.load_post[fun_ind]
    except ValueError:
        pass
    else:
        bpy.app.handlers.load_post.remove(fun)
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
    try:
        fun_ind = [f.__name__ for f in bpy.app.handlers.load_post].index(transfer_data_menu.__name__)
        fun = bpy.app.handlers.load_post[fun_ind]
    except ValueError:
        pass
    else:
        bpy.app.handlers.load_post.remove(fun)
        bpy.types.VIEW3D_MT_make_links.remove(fun)

    for cls in reversed(classes):
        real_cls = cls.__base__.bl_rna_get_subclass_py(cls.__name__)
        if real_cls is not None:  # in case it was not registered yet
            bpy.utils.unregister_class(real_cls)


def _update_colors():
    for tree in (t for t in bpy.data.node_groups if t.bl_idname == BuildingStyleTree.bl_idname):
        for node in (n for n in tree.nodes if n.bl_idname not in {'NodeReroute', 'NodeFrame', 'NodeUndefined'}):
            if node.category is not None:
                node.use_custom_color = True
                node.color = node.category.color


if __name__ == "__main__":
    unregister()
    register()
    _update_colors()
