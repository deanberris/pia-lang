"""Runs a unittest module's tests under Bazel's test sharding.

Bazel sets TEST_TOTAL_SHARDS and TEST_SHARD_INDEX when a test has
`shard_count`; each shard runs every n-th test, in a stable order.
"""
import os
import sys
import unittest


def main(module):
    suite = unittest.defaultTestLoader.loadTestsFromModule(module)
    tests = []

    def flatten(s):
        for t in s:
            if isinstance(t, unittest.TestSuite):
                flatten(t)
            else:
                tests.append(t)

    flatten(suite)
    tests.sort(key=lambda t: t.id())
    total = int(os.environ.get("TEST_TOTAL_SHARDS", "1"))
    index = int(os.environ.get("TEST_SHARD_INDEX", "0"))
    if "TEST_SHARD_STATUS_FILE" in os.environ:
        open(os.environ["TEST_SHARD_STATUS_FILE"], "w").close()
    mine = unittest.TestSuite(t for i, t in enumerate(tests) if i % total == index)
    result = unittest.TextTestRunner(verbosity=2).run(mine)
    sys.exit(0 if result.wasSuccessful() else 1)
