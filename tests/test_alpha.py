#!/usr/bin/env python3
"""Verification tests for Alpha (00.v)."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestAlpha(unittest.TestCase):
    def test_coq_file_exists(self):
        vfile = os.path.join(ROOT, "00.v")
        self.assertTrue(os.path.isfile(vfile))
        self.assertGreater(os.path.getsize(vfile), 0)


if __name__ == "__main__":
    unittest.main()
