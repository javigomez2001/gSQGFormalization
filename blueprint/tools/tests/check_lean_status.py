#!/usr/bin/env python3
"""Exercise the real compiled extractor on private sorrys, cut points, and axioms.

Run from the project root: python3 blueprint/tools/tests/check_lean_status.py
This builds only a tiny temporary fixture and never writes to the project's .lake.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile

PROJECT = Path(__file__).resolve().parents[3]
FIXTURE = '''import Lean
namespace GSQG
private theorem fixtureHelper : True := by sorry
theorem fixtureHiddenSorry : True := fixtureHelper
theorem fixturePending : True := by sorry
theorem fixtureWrapper : True := fixturePending
theorem fixtureDone : True := True.intro
axiom fixtureCustom : True
theorem fixtureUsesCustom : True := fixtureCustom
end GSQG
'''


def main():
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=PROJECT, text=True).strip()
    search_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                          cwd=PROJECT, text=True).strip()
    with tempfile.TemporaryDirectory(prefix='gsqg-extractor-test-') as temp:
        temp = Path(temp)
        src = temp / 'StatusFixture.lean'
        src.write_text(FIXTURE)
        env = {**os.environ, 'LEAN_PATH': str(temp) + os.pathsep + search_path}
        subprocess.run([lean, '-R', str(temp), '-o', str(temp / 'StatusFixture.olean'), str(src)],
                       env=env, check=True, capture_output=True, text=True)
        names = ['fixtureHiddenSorry', 'fixturePending', 'fixtureWrapper', 'fixtureDone', 'fixtureUsesCustom']
        bp = temp / 'blueprint.json'
        bp.write_text(json.dumps({'nodes': [{'lean': ['GSQG.' + n]} for n in names]}))
        out = temp / 'status.json'
        subprocess.run([lean, '--run', str(PROJECT / 'blueprint/tools/LeanStatus.lean'),
                        'StatusFixture', str(bp), str(out)], env=env, check=True)
        status = json.loads(out.read_text())
        assert status['GSQG.fixtureHiddenSorry']['sorry'] is True
        assert status['GSQG.fixtureHiddenSorry']['local_sorry'] is True
        assert status['GSQG.fixtureWrapper']['sorry'] is True
        assert status['GSQG.fixtureWrapper']['local_sorry'] is False
        assert status['GSQG.fixtureWrapper']['blueprint_deps'] == ['GSQG.fixturePending']
        assert status['GSQG.fixtureDone']['sorry'] is False
        assert status['GSQG.fixtureDone']['axioms'] == []
        assert status['GSQG.fixtureUsesCustom']['axioms'] == ['GSQG.fixtureCustom']
    print('Compiled Lean status regressions passed.')


if __name__ == '__main__':
    main()
