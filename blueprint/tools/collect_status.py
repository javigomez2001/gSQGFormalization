#!/usr/bin/env python3
"""Compile the root import, collect statuses, and stamp the exact input snapshot.

Usage: collect_status.py [--source] [--project PROJECT] [MODULE ...]
--project supports a writable build copy; its input fingerprint must match this project.
"""
import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from build_site import load_blueprint
from status_common import PROJECT, report, source_fingerprint, write_json


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source', action='store_true')
    ap.add_argument('--project', type=Path, default=PROJECT)
    ap.add_argument('--out', type=Path, default=PROJECT / 'blueprint/site')
    ap.add_argument('modules', nargs='*')
    args = ap.parse_args()
    before = source_fingerprint()
    if source_fingerprint(args.project) != before:
        raise SystemExit('Build copy differs from current project inputs; report not changed.')
    nodes, _ = load_blueprint()
    with tempfile.TemporaryDirectory(prefix='gsqg-status-') as temp:
        temp = Path(temp)
        bp, raw = temp / 'blueprint.json', temp / 'status.json'
        write_json(bp, {'nodes': nodes})
        if args.source:
            subprocess.run([sys.executable, str(PROJECT / 'blueprint/tools/source_status.py'),
                            str(bp), str(raw)], check=True)
            result = json.loads(raw.read_text())
            output = PROJECT / 'blueprint/build/source_status.json'
        else:
            # Always build GSQG: a successful chapter build alone cannot refresh Main's .olean.
            subprocess.run(['lake', 'build', *args.modules, 'GSQG'], cwd=args.project, check=True)
            subprocess.run(['lake', 'env', 'lean', '--run',
                            'blueprint/tools/LeanStatus.lean', 'GSQG', str(bp), str(raw)],
                           cwd=args.project, check=True)
            result = report(json.loads(raw.read_text()), 'lean', before)
            output = PROJECT / 'blueprint/build/lean_status.json'
        if source_fingerprint() != before or source_fingerprint(args.project) != before:
            raise SystemExit('Sources changed during checking; previous report retained. Run again.')
        write_json(output, result)
    subprocess.run([sys.executable, str(PROJECT / 'blueprint/tools/build_site.py'),
                    '--lean-status', str(output), '--out', str(args.out)], check=True)


if __name__ == '__main__':
    main()
