#!/usr/bin/env python3
"""Negative controls for accepting a scoped Lean audit log."""
import unittest

from check_requirement_audit import audit_log


class AuditLogControls(unittest.TestCase):
    def test_allowed_dependencies_and_axiom_free_declaration(self):
        log = "'a' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        log += "'b' does not depend on any axioms\n"
        self.assertEqual(set(audit_log(log, {"a", "b"})), {"a", "b"})

    def test_missing_declaration_is_rejected(self):
        with self.assertRaises(RuntimeError):
            audit_log("'a' depends on axioms: [propext]", {"a", "b"})

    def test_duplicate_declaration_is_rejected(self):
        with self.assertRaises(RuntimeError):
            audit_log("'a' depends on axioms: [propext]\n" * 2, {"a"})

    def test_unexpected_declaration_is_rejected(self):
        with self.assertRaises(RuntimeError):
            audit_log("'other' depends on axioms: [propext]", {"a"})

    def test_sorry_and_extra_axioms_are_rejected(self):
        for axiom in ("sorryAx", "Unproved.PhysicalBridge"):
            with self.subTest(axiom=axiom), self.assertRaises(RuntimeError):
                audit_log(f"'a' depends on axioms: [propext, {axiom}]", {"a"})


if __name__ == "__main__":
    unittest.main()
