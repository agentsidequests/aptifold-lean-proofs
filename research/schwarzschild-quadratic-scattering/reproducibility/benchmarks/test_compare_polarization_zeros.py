"""Exercise the released enclosures and realistic comparison failures."""

from copy import deepcopy
import unittest

from compare_polarization_zeros import ROOT_FIELDS, archived_record, compare_records


class PolarizationReplayTests(unittest.TestCase):
    def setUp(self):
        self.reference = archived_record("fine")
        self.candidate = deepcopy(self.reference)

    def compare_fine(self):
        return compare_records(self.candidate, "fine", self.reference, "fine")

    def test_saved_coarse_and_fine_agree(self):
        compare_records(self.reference, "fine", archived_record("coarse"), "coarse")

    def test_root_order_can_change(self):
        for field in ROOT_FIELDS:
            self.candidate[field].reverse()
        self.assertEqual(self.compare_fine(), (1, 0))

    def test_both_coordinates_must_match_the_same_permutation(self):
        self.candidate[ROOT_FIELDS[0]].reverse()
        with self.assertRaisesRegex(ValueError, "one-to-one overlap"):
            self.compare_fine()

    def test_duplicate_root_is_rejected(self):
        for field in ROOT_FIELDS:
            self.candidate[field][0] = self.candidate[field][1]
        with self.assertRaisesRegex(ValueError, "one-to-one overlap"):
            self.compare_fine()

    def test_fine_precision_cannot_be_replaced_by_coarse_precision(self):
        self.candidate[ROOT_FIELDS[0]][0]["real"] = "[1.294793416342738 +/- 1e-12]"
        with self.assertRaisesRegex(ValueError, "fine radius limit"):
            self.compare_fine()

    def test_shifted_root_is_rejected_even_when_narrow(self):
        self.candidate[ROOT_FIELDS[0]][0]["real"] = "1.294793417342738"
        with self.assertRaisesRegex(ValueError, "one-to-one overlap"):
            self.compare_fine()

    def test_wrong_frequency_is_rejected(self):
        self.candidate["parent_frequency"] = "3/8"
        with self.assertRaisesRegex(ValueError, "parent_frequency"):
            self.compare_fine()


if __name__ == "__main__":
    unittest.main()
