#!/usr/bin/env python3
"""Status-contract tests, not mathematical proof acceptance."""
import copy
import unittest
from verify_existence import native_accepted, PIN


class AcceptanceContract(unittest.TestCase):
    def setUp(self):
        self.good = {
            "status": "EXISTENCE_ONLY_KERNEL_PROOF_ACCEPTED",
            "admitted_target": PIN["target"],
            "existence_only_kernel_certificate": True,
            "kernel_verification_status": "passed_declared_existence_only_target",
            "verified_theorem": "Fixture.proof",
        }

    def test_full_native_contract_required(self):
        # Synthetic unit-test fixture only, not a real Lean proof receipt.
        self.assertTrue(native_accepted(self.good, 0, "Fixture.proof"))
        for key in self.good:
            report = copy.deepcopy(self.good)
            del report[key]
            self.assertFalse(native_accepted(report, 0, "Fixture.proof"), key)

    def test_nonzero_process_exit_rejected(self):
        self.assertFalse(native_accepted(self.good, 1, "Fixture.proof"))
        self.assertFalse(native_accepted(self.good, 2, "Fixture.proof"))

    def test_missing_or_different_theorem_rejected(self):
        self.assertFalse(native_accepted(self.good, 0, None))
        self.assertFalse(native_accepted(self.good, 0, "Other.proof"))

    def test_support_success_is_not_existence(self):
        report = {"status": "PROOF_NOT_SUBMITTED", "supplementary_lemmas_verified": True,
                  "existence_only_kernel_certificate": False}
        self.assertFalse(native_accepted(report, 2, None))

    def test_conditional_proof_receipt_rejected(self):
        report = dict(self.good, status="PROOF_REJECTED",
                      existence_only_kernel_certificate=False)
        self.assertFalse(native_accepted(report, 1, "Fixture.proof"))

    def test_source_translation_and_matching_universes_are_not_native_acceptance(self):
        report = dict(self.good, status="INCOMPATIBLE_PROOF_SIGNATURE",
                      source_translation_verified=True,
                      spacetime_transport_verified=True,
                      existence_only_kernel_certificate=False)
        self.assertFalse(native_accepted(report, 2, "Fixture.proof"))
        self.assertFalse(native_accepted(report, 0, "Fixture.proof"))


if __name__ == "__main__":
    unittest.main()
