#!/usr/bin/env python3
"""Focused inexpensive tests for the retained exact certificate lane."""

from __future__ import annotations

import json
import unittest
from fractions import Fraction

import Script0002 as part_a
import Script0003 as part_b
import Script0001


class ExactCertificateTests(unittest.TestCase):
    def test_preserved_certificate_hashes(self) -> None:
        self.assertEqual(Script0001.sha256(Script0001.ROOT / "Script0002.py"), "dfe758c0fbf01f54729c5369065364a759699475ae8ab1d58bac51a36b686083")
        self.assertEqual(Script0001.sha256(Script0001.ROOT / "Script0003.py"), "882fbfe18990c418270553b2536c5dc9272b83207c5972abd1bc2af780b6d5b2")

    def test_constants_and_support_separation(self) -> None:
        self.assertEqual(part_a.A, Fraction(1, 250))
        self.assertEqual(part_a.ETA, Fraction(1, 100000))
        self.assertEqual(part_b.T, Fraction(1, 10000))
        self.assertEqual(part_b.RHO, Fraction(1, 10**12))
        for e, f in zip(part_a.ELLS, part_a.FS):
            self.assertTrue(abs(e - part_b.LA) > part_a.ETA + part_b.RHO or abs(f - part_b.FA) > part_a.ETA + part_b.RHO)
            self.assertTrue(abs(e - part_b.LB) > part_a.ETA + part_b.RHO or abs(f - part_b.FB) > part_a.ETA + part_b.RHO)

    def test_packet_floor_is_strictly_above_claimed_floor(self) -> None:
        floor = Fraction(27) * part_b.T**2 * part_b.RHO**2 / 131072
        self.assertGreater(floor, Fraction(1, 10**36))

    def test_retained_artifact_schema_and_source_manifest(self) -> None:
        document = json.loads(Script0001.ARTIFACT.read_text())
        Script0001.validate_schema(document)
        for relative, digest in document["source_manifest"].items():
            self.assertEqual(Script0001.sha256(Script0001.ROOT / relative), digest)


if __name__ == "__main__":
    unittest.main()
