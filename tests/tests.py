import os
import subprocess
import sys
from pathlib import Path

import bmesh
import bpy
from bmesh.types import BMesh
from mathutils import Vector

if __package__ is None:
    # when this file is run directly it does not know root path to use import from above folders
    sys.path.append(str(Path(__file__).parent.parent))

import __init__ as m

try:
    import pytest
except ImportError:
    environ_copy = dict(os.environ)
    environ_copy["PYTHONNOUSERSITE"] = "1"

    subprocess.run([sys.executable, "-m", "pip", "install", 'pytest'], check=True, env=environ_copy)
    import pytest


IS_TESTING = True  # if is False the tests will update the test file with new data
WALK_TEST_OBJ = 'Walk test'


@pytest.fixture
def object_to_mesh():
    bms: list[tuple[str, BMesh]] = []

    def _object_to_mesh(obj_name) -> BMesh:
        obj = bpy.data.objects[obj_name]
        new_bm = bmesh.new()
        new_bm.from_mesh(obj.data)
        bms.append((obj_name, new_bm))
        new_bm.faces.ensure_lookup_table()
        return new_bm
    yield _object_to_mesh
    if not IS_TESTING:
        for name, bm in bms:
            obj = bpy.data.objects[name]
            bm.to_mesh(obj.data)
    for _, bm in bms:
        bm.free()


class TestGeometry:
    def test_connected_coplanar_faces(self, object_to_mesh):
        bm = object_to_mesh(WALK_TEST_OBJ)
        isl_lay = bm.faces.layers.int.get('Facade ind') or bm.faces.layers.int.new('Facade ind')
        order_lay = bm.faces.layers.int.get('Order') or bm.faces.layers.int.new('Order')
        island_i = 1
        visited = set()
        for face in bm.faces:
            if face in visited:
                continue
            facade_greed = m.Geometry.connected_coplanar_faces(face)
            order_i = 0
            for cell in facade_greed:
                facade_face = bm.faces[cell.face_indexes[0]]
                visited.add(facade_face)
                if IS_TESTING:
                    assert facade_face[isl_lay] == island_i
                    assert facade_face[order_lay] == order_i
                else:
                    facade_face[isl_lay] = island_i
                    facade_face[order_lay] = order_i
                order_i += 1
            island_i += 1


@pytest.fixture
def simple_floor():
    """  ←-3-→←-3→←-3→

         +---+---+---+  +
         │ 0 │ 1 │ 2 │  3
         +---+---+---+  +
    """
    floor = m.Floor(0, length=9)
    floor.height = 3
    for i in range(3):
        panel = m.Panel(i, size=Vector((3, 3)))
        floor.panels_stack.append(panel)
    return floor


@pytest.fixture
def simple_facade(simple_floor: m.Floor):
    """  ←-3-→←-3→←-3→

         +---+---+---+  +
         │   │   │   │  3
         +---+---+---+  +
         │   │   │   │  3
         +---+---+---+  +
    """
    facade = m.Facade(height=6)
    try:
        while True:
            facade.floors_stack.append(simple_floor.copy())
    except IndexError:
        pass
    return facade


@pytest.fixture
def facade_grid():
    """  ←1→←-4-→←-4-→

         +-+----+       +
         │3│ 4  │       3
         +-+----+----+  +
         │0│ 1  │ 2  │  3
         +-+----+----+  +
    """
    gr = m.CentredMeshGrid()
    gr.add(Vector((0, 0)), Vector((1., 3.)), 0)
    gr.add(Vector((1, 0)), Vector((4., 3.)), 1)
    gr.add(Vector((2, 0)), Vector((4., 3.)), 2)
    gr.add(Vector((0, 1)), Vector((1., 3.)), 3)
    gr.add(Vector((1, 1)), Vector((4., 3.)), 4)
    gr.clean_grid()
    return gr


@pytest.fixture
def facade_grid2():
    """  ←1→←---7--→←1→

           +-------+-+  +
           │   3   │4│  3
         +-+-------+-+  +
         │0│   1   │2│  3
         +-+-------+-+  +
    """
    gr = m.CentredMeshGrid()
    gr.add(Vector((0, 0)), Vector((1., 3.)), 0)
    gr.add(Vector((1, 0)), Vector((7., 3.)), 1)
    gr.add(Vector((2, 0)), Vector((1., 3.)), 2)
    gr.add(Vector((1, 1)), Vector((7., 3.)), 3)
    gr.add(Vector((2, 1)), Vector((1., 3.)), 4)
    gr.clean_grid()
    return gr


class TestMeshGrid:
    def test_cell_join(self, facade_grid: m.CentredMeshGrid, simple_facade: m.Facade):
        c0, c1, c2, c3, c4, *_ = facade_grid  # type: m.GridCell
        joined_cell = c0.fit_to_shape(simple_facade.floors_stack)
        assert joined_cell.x_range == m.DistSlice(0, 5)
        assert set(joined_cell.face_indexes) == {0, 1}
        joined_cell = c2.fit_to_shape(simple_facade.floors_stack)
        assert joined_cell.x_range == m.DistSlice(5, 9)
        assert set(joined_cell.face_indexes) == {2}
        joined_cell = c3.fit_to_shape(simple_facade.floors_stack)
        assert joined_cell.x_range == m.DistSlice(0, 5)
        assert set(joined_cell.face_indexes) == {3, 4}

    def test_cell_join2(self, facade_grid2: m.CentredMeshGrid, simple_facade: m.Facade):
        c0, c1, c2, c3, c4, *_ = facade_grid2  # type: m.GridCell
        joined_cell = c0.fit_to_shape(simple_facade.floors_stack)
        assert joined_cell.x_range == m.DistSlice(0, 9)
        assert set(joined_cell.face_indexes) == {0, 1, 2}
        assert joined_cell.is_top == False
        joined_cell = c3.fit_to_shape(simple_facade.floors_stack)
        assert joined_cell.x_range == m.DistSlice(1, 9)
        assert set(joined_cell.face_indexes) == {3, 4}
        assert joined_cell.is_top == True


class TestShapesStack:
    def test_get_shape(self, simple_floor: m.Floor):
        assert simple_floor.panels_stack[1.5].obj_index == 0
        assert simple_floor.panels_stack[3.0].obj_index == 1
        assert simple_floor.panels_stack[3.5].obj_index == 1
        with pytest.raises(IndexError):
            simple_floor.panels_stack[9.0].obj_index


if __name__ == '__main__':
    pytest.main(['tests.py', '-s', '--pdb'])  # without -s pdb does not work =D
    pytest.main([str(Path(__file__).parent.parent), '--doctest-modules'])
