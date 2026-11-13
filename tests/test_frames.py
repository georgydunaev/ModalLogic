#!/usr/bin/env python3
"""Unit tests for composable Kripke frame classes, accessibility relation mixins, and automated correspondence checkers."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.semantics import KripkeFrame
from modallogic.frames import (
    FrameProperty,
    ReflexiveFrameMixin,
    TransitiveFrameMixin,
    SymmetricFrameMixin,
    SerialFrameMixin,
    EuclideanFrameMixin,
    ConfluentFrameMixin,
    DirectedFrameMixin,
    WellFoundedFrameMixin,
    ConverseWellFoundedFrameMixin,
    ComposableFrame,
    KFrame,
    KDFrame,
    TFrame,
    KBFrame,
    K4Frame,
    K45Frame,
    KD45Frame,
    S4Frame,
    S5Frame,
    GLFrame,
    ConfluentFrame,
    DirectedFrame,
    create_frame,
)
from modallogic.correspondence import (
    check_confluence,
    check_directedness,
    check_well_foundedness,
    correspondence_theorem_c4,
    verify_frame_correspondence,
    AutomatedCorrespondenceChecker,
)


class TestComposableFramesAndCorrespondence(unittest.TestCase):
    def test_property_mixins_direct_check(self):
        # Reflexive mixin
        class DummyReflexive(ReflexiveFrameMixin, KripkeFrame):
            pass

        f_refl = DummyReflexive(["w0", "w1"], [("w0", "w0"), ("w1", "w1")])
        sat, witness = f_refl.check_reflexive_property()
        self.assertTrue(sat)
        self.assertIsNone(witness)

        f_non_refl = DummyReflexive(["w0", "w1"], [("w0", "w0")])
        sat_fail, witness_fail = f_non_refl.check_reflexive_property()
        self.assertFalse(sat_fail)
        self.assertEqual(witness_fail, "w1")

        # Transitive mixin
        class DummyTransitive(TransitiveFrameMixin, KripkeFrame):
            pass

        f_trans = DummyTransitive(["w0", "w1", "w2"], [("w0", "w1"), ("w1", "w2"), ("w0", "w2")])
        self.assertTrue(f_trans.check_transitive_property()[0])

        f_non_trans = DummyTransitive(["w0", "w1", "w2"], [("w0", "w1"), ("w1", "w2")])
        self.assertFalse(f_non_trans.check_transitive_property()[0])

        # Symmetric mixin
        class DummySymmetric(SymmetricFrameMixin, KripkeFrame):
            pass

        f_sym = DummySymmetric(["w0", "w1"], [("w0", "w1"), ("w1", "w0")])
        self.assertTrue(f_sym.check_symmetric_property()[0])

        # Serial mixin
        class DummySerial(SerialFrameMixin, KripkeFrame):
            pass

        f_ser = DummySerial(["w0"], [("w0", "w0")])
        self.assertTrue(f_ser.check_serial_property()[0])

        # Euclidean mixin
        class DummyEuclidean(EuclideanFrameMixin, KripkeFrame):
            pass

        f_eucl = DummyEuclidean(["w0", "w1"], [("w0", "w0"), ("w0", "w1"), ("w1", "w0"), ("w1", "w1")])
        self.assertTrue(f_eucl.check_euclidean_property()[0])

        # Confluent mixin
        class DummyConfluent(ConfluentFrameMixin, KripkeFrame):
            pass

        f_conf = DummyConfluent(
            ["w0", "w1", "w2", "w3"],
            [("w0", "w1"), ("w0", "w2"), ("w1", "w3"), ("w2", "w3"), ("w3", "w3")],
        )
        self.assertTrue(f_conf.check_confluent_property()[0])

        # Well-founded mixin
        class DummyWellFounded(WellFoundedFrameMixin, KripkeFrame):
            pass

        f_wf = DummyWellFounded(["w0", "w1"], [("w0", "w1")])
        self.assertTrue(f_wf.check_well_founded_property()[0])

    def test_s4_composable_frame_validation(self):
        # Valid S4 frame (reflexive and transitive)
        f_s4 = S4Frame(
            worlds=["w0", "w1"],
            relation=[("w0", "w0"), ("w1", "w1"), ("w0", "w1")],
            validate=True,
        )
        self.assertTrue(f_s4.is_valid_frame())
        report = f_s4.validation_report()
        self.assertTrue(report["is_valid"])
        self.assertIn("reflexive", report["satisfied"])
        self.assertIn("transitive", report["satisfied"])

        # Invalid S4 frame missing reflexivity should raise ValueError when validate=True
        with self.assertRaises(ValueError):
            S4Frame(
                worlds=["w0", "w1"],
                relation=[("w0", "w1")],
                validate=True,
            )

    def test_s5_composable_frame_validation(self):
        # Equivalence relation
        f_s5 = S5Frame(
            worlds=["w0", "w1"],
            relation=[("w0", "w0"), ("w1", "w1"), ("w0", "w1"), ("w1", "w0")],
            validate=True,
        )
        self.assertTrue(f_s5.is_valid_frame())

        # Preorder that is not symmetric fails S5 validation
        with self.assertRaises(ValueError):
            S5Frame(
                worlds=["w0", "w1"],
                relation=[("w0", "w0"), ("w1", "w1"), ("w0", "w1")],
                validate=True,
            )

    def test_gl_composable_frame_validation(self):
        # Strict finite DAG (transitive and converse well-founded)
        f_gl = GLFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
            validate=True,
        )
        self.assertTrue(f_gl.is_valid_frame())

        # Reflexive loop violates converse well-foundedness
        with self.assertRaises(ValueError):
            GLFrame(
                worlds=["w0"],
                relation=[("w0", "w0")],
                validate=True,
            )

    def test_kd45_and_k4_composable_frames(self):
        # KD45: serial, transitive, euclidean
        f_kd45 = KD45Frame(
            worlds=["w0", "w1"],
            relation=[("w0", "w1"), ("w1", "w1")],
            validate=True,
        )
        self.assertTrue(f_kd45.is_valid_frame())

        # K4: transitive
        f_k4 = K4Frame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
            validate=True,
        )
        self.assertTrue(f_k4.is_valid_frame())

    def test_confluent_frame_and_checkers(self):
        # Diamond / Church-Rosser confluence: w0 sees w1 and w2; both see w3 (with loop at w3)
        f_conf = ConfluentFrame(
            worlds=["w0", "w1", "w2", "w3"],
            relation=[("w0", "w1"), ("w0", "w2"), ("w1", "w3"), ("w2", "w3"), ("w3", "w3")],
            validate=True,
        )
        self.assertTrue(f_conf.is_valid_frame())

        is_conf, witness = check_confluence(f_conf)
        self.assertTrue(is_conf)
        self.assertIsNone(witness)

        # Non-confluent fork: w0 sees w1 and w2, but they have no common successor
        f_fork = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w0", "w2")],
        )
        is_conf_f, witness_f = check_confluence(f_fork)
        self.assertFalse(is_conf_f)
        self.assertEqual(witness_f[0], "w0")

    def test_c4_correspondence_theorem(self):
        # Confluent frame validates C4 (<>[]p -> []<>p)
        f_conf = KripkeFrame(
            worlds=["w0", "w1", "w2", "w3"],
            relation=[("w0", "w1"), ("w0", "w2"), ("w1", "w3"), ("w2", "w3"), ("w3", "w3")],
        )
        res_conf = correspondence_theorem_c4(f_conf)
        self.assertTrue(res_conf["is_property_satisfied"])
        self.assertTrue(res_conf["is_axiom_valid"])
        self.assertTrue(verify_frame_correspondence(f_conf, "C4"))

        # Non-confluent fork falsifies C4
        f_fork = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w0", "w2")],
        )
        res_fork = correspondence_theorem_c4(f_fork)
        self.assertFalse(res_fork["is_property_satisfied"])
        self.assertFalse(res_fork["is_axiom_valid"])
        self.assertIsNotNone(res_fork["countermodel"])
        # Check that countermodel falsifies C4 at counterworld
        cm = res_fork["countermodel"]
        cw = res_fork["counterworld"]
        ax = res_fork["axiom"]
        self.assertFalse(cm.satisfies(cw, ax))
        self.assertTrue(verify_frame_correspondence(f_fork, "C4"))

    def test_automated_correspondence_checker(self):
        f_s4 = S4Frame(
            worlds=["w0", "w1"],
            relation=[("w0", "w0"), ("w1", "w1"), ("w0", "w1")],
        )
        rep_s4 = AutomatedCorrespondenceChecker.verify_system(f_s4, "S4")
        self.assertTrue(rep_s4["is_valid"])

        rep_s5 = AutomatedCorrespondenceChecker.verify_system(f_s4, "S5")
        self.assertFalse(rep_s5["is_valid"])
        self.assertIn("5", rep_s5["failed_axioms"])

        # GL system check
        f_gl = GLFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        rep_gl = AutomatedCorrespondenceChecker.verify_system(f_gl, "GL")
        self.assertTrue(rep_gl["is_valid"])

    def test_create_frame_factory(self):
        f = create_frame("S4", ["w0"], [("w0", "w0")], validate=True)
        self.assertIsInstance(f, S4Frame)

        f_gl = create_frame("GL", ["w0", "w1"], [("w0", "w1")], validate=True)
        self.assertIsInstance(f_gl, GLFrame)


if __name__ == "__main__":
    unittest.main()
