#!/usr/bin/env python3
"""Small falsifiable tests for full-build measurement and graph analysis."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from analyze_build_profile import analyze
from profile_build import now


class BuildProfileTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'processes').mkdir()
        self.build = self.root / 'build'
        (self.build / 'lib/lean').mkdir(parents=True)
        self.result = dict(start=10., end=19., wall_seconds=9., user_seconds=8.,
                           system_seconds=1., exit_code=0)
        self.write_result()

    def tearDown(self):
        self.temp.cleanup()

    def write_result(self):
        (self.root / 'result.json').write_text(json.dumps(self.result))

    def module(self, name, start, end, imports=()):
        row = dict(kind='lean', module=name, start=start, end=end,
                   wall_seconds=end-start, user_seconds=1., system_seconds=0., exit_code=0)
        (self.root / 'processes' / (name + '.json')).write_text(json.dumps(row))
        (self.build / 'lib/lean' / (name + '.ilean')).write_text(json.dumps(
            dict(directImports=[[n, True, False, False] for n in imports])))

    def test_actual_waiting_and_weighted_path_are_distinct(self):
        self.module('A', 11., 13.)
        self.module('B', 13., 17., ['A'])
        self.module('C', 15., 16., ['A'])
        self.module('D', 18., 19., ['B', 'C'])
        d = analyze(self.root, self.build)
        self.assertEqual(d['observed_terminal_path'], ['A', 'B', 'D'])
        self.assertEqual(d['weighted_path'], (7., ['A', 'B', 'D']))
        rows = {r['module']: r for r in d['modules']}
        self.assertEqual(rows['D']['launch_gap_seconds'], 1.)
        self.assertEqual(rows['A']['descendants'], 3)
        self.assertEqual(d['peak_compilers'], 2)
        self.assertAlmostEqual(sum(d['compiler_occupancy_seconds'].values()), 9.)

    def test_cache_hit_is_not_a_compile_profile(self):
        with self.assertRaisesRegex(ValueError, 'cache hit'):
            analyze(self.root, self.build)

    def test_failure_is_not_a_speedup(self):
        self.result['exit_code'] = 1
        self.write_result()
        with self.assertRaisesRegex(ValueError, 'failed builds'):
            analyze(self.root, self.build)

    def test_inconsistent_timestamps_are_rejected(self):
        self.module('A', 11., 15.)
        self.module('B', 14., 17., ['A'])
        with self.assertRaisesRegex(ValueError, 'inconsistent timestamps'):
            analyze(self.root, self.build)

    def test_failed_child_is_rejected_even_with_successful_parent(self):
        self.module('A', 11., 13.)
        path = self.root / 'processes/A.json'
        row = json.loads(path.read_text())
        row['exit_code'] = 1
        path.write_text(json.dumps(row))
        with self.assertRaisesRegex(ValueError, 'failed compiler'):
            analyze(self.root, self.build)

    def test_duplicate_module_is_rejected(self):
        self.module('A', 11., 13.)
        original = self.root / 'processes/A.json'
        (self.root / 'processes/duplicate.json').write_bytes(original.read_bytes())
        with self.assertRaisesRegex(ValueError, 'duplicate module'):
            analyze(self.root, self.build)

    def test_missing_plugin_is_rejected_before_replay(self):
        output = self.root / 'replay'
        result = subprocess.run(
            [sys.executable, str(Path(__file__).with_name('profile_compile.py')),
             'ToMathlib.General', '--output', str(output),
             '--plugin', str(self.root / 'missing.so')],
            capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn('every --plugin', result.stderr)
        self.assertFalse(output.exists())

    def test_start_records_are_not_completed_compiles(self):
        self.module('A', 11., 13.)
        (self.root / 'processes/123.start.json').write_text('{}')
        self.assertEqual(analyze(self.root, self.build)['module_count'], 1)

    def test_clock_epoch_is_shared_across_processes(self):
        before = now()
        env = os.environ.copy()
        if env.get('PYTHONPYCACHEPREFIX'):
            env['PYTHONPYCACHEPREFIX'] = str(Path(env['PYTHONPYCACHEPREFIX']).resolve())
        child = float(subprocess.check_output(
            [sys.executable, '-c', 'from profile_build import now; print(now())'],
            cwd=Path(__file__).parent, env=env, text=True))
        self.assertLessEqual(before, child)
        self.assertLessEqual(child, now())


if __name__ == '__main__':
    unittest.main()
