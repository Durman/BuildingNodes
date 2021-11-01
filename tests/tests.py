import os
import subprocess
import sys
from itertools import count
from math import isclose

import bmesh
import bpy
from bmesh.types import BMesh
from mathutils import Vector

if __package__ is None:
    # when this file is run directly it does not know root path to use import from above folders
    from pathlib import Path
    sys.path.append(str(Path(__file__).parent.parent))

import main

try:
    import pytest
except ImportError:
    environ_copy = dict(os.environ)
    environ_copy["PYTHONNOUSERSITE"] = "1"

    subprocess.run([sys.executable, "-m", "pip", "install", 'pytest'], check=True, env=environ_copy)
    import pytest


@pytest.fixture
def object_to_mesh():
    bms = []

    def _object_to_mesh(obj_name) -> BMesh:
        obj = bpy.data.objects[obj_name]
        new_bm = bmesh.new()
        new_bm.from_mesh(obj.data)
        bms.append(new_bm)
        return new_bm
    yield _object_to_mesh
    for bm in bms:
        bm.free()


@pytest.fixture
def mark_facade_loops():
    def _mark_facade_loops(bm):
        build = main.Building(min(v.co.z for v in bm.verts))
        ind_lay = bm.faces.layers.int.get('Facade index') or bm.faces.layers.int.new('Facade index')
        loop_layer = bm.loops.layers.int
        bound_lay = (lay := loop_layer.get('Is bound')) and loop_layer.remove(lay) or loop_layer.new('Is bound')
        facade_ind = count(1)
        visited = set()
        for face in bm.faces:
            if face in visited:
                continue
            is_vertical = isclose(face.normal.dot(Vector((0, 0, 1))), 0, abs_tol=0.1)
            is_valid = is_vertical and len(face.verts) > 3 and not isclose(face.calc_area(), 0, abs_tol=0.1)
            if is_valid:
                next_fac_ind = next(facade_ind)
                for face_bound_loops in build.get_floor_polygons(face):
                    face = face_bound_loops[0].face
                    visited.add(face)
                    face[ind_lay] = next_fac_ind
                    face_bound_loops[0][bound_lay] = 1
                    face_bound_loops[1][bound_lay] = 2
        return ind_lay, bound_lay
    return _mark_facade_loops


def test_walking_loops(object_to_mesh, mark_facade_loops):
    standard_bm = object_to_mesh('Mark bounding loops')
    bm = object_to_mesh('Mark bounding loops')
    face_lay, loop_lay = mark_facade_loops(bm)
    st_face_lay = standard_bm.faces.layers.int.get(face_lay.name)
    st_loop_lay = standard_bm.loops.layers.int.get(loop_lay.name)
    for face, st_face in zip(bm.faces, standard_bm.faces):
        assert face[face_lay] == st_face[st_face_lay]
        for loop, st_loop in zip(face.loops, st_face.loops):
            assert loop[loop_lay] == st_loop[st_loop_lay]


pytest.main(['tests.py'])
