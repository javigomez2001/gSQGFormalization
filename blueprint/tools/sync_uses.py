#!/usr/bin/env python3
"""Synchronize proof references with uses, reading current sources rather than cached JSON.

Forward references are allowed (assemblies need them); cycles are reported, never added.
Usage: sync_uses.py [--apply] [--check]
"""
import argparse
import re
from pathlib import Path

from build_site import ROOT, load_blueprint, mask_comments, strip_comments, command_args, split_list


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    nodes, _ = load_blueprint()
    labels = {n['id'] for n in nodes}
    deps = {n['id']: set(n['uses']) | set(n['proof_uses']) for n in nodes}

    def depends_on(a, b):
        seen, todo = set(), [a]
        while todo:
            x = todo.pop()
            if x == b:
                return True
            if x not in seen:
                seen.add(x)
                todo.extend(deps.get(x, ()))
        return False

    total, skipped = 0, []
    for filename in sorted({n['file'] for n in nodes}):
        path = ROOT / filename
        text = path.read_text()
        own_nodes = [n for n in nodes if n['file'] == filename]
        edits = []
        for match in re.finditer(r'\\begin\{proof\}(?:\[[^\]]*\])?(.*?)\\end\{proof\}', mask_comments(text), re.S):
            line = text.count('\n', 0, match.start()) + 1
            previous = [n for n in own_nodes if n['line'] <= line]
            if not previous:
                continue
            node = max(previous, key=lambda n: n['line'])
            body = strip_comments(match.group(1))
            uses = set(split_list(command_args(body, 'uses')))
            cited = set(split_list(command_args(body, '(?:[cC]ref|ref)')))
            missing = []
            for target in sorted(cited & labels - uses - set(node['uses']) - {node['id']}):
                if depends_on(target, node['id']):
                    skipped.append((node['id'], target))
                    continue
                missing.append(target)
                deps[node['id']].add(target)
            if missing:
                total += len(missing)
                print(f"{path.name}: {node['id']}: + {', '.join(missing)}")
                # Insert separately: do not edit commented-out macros or misidentify equation labels.
                edits.append((match.start(1), '\n  \\uses{' + ', '.join(missing) + '}'))
        if args.apply:
            for pos, value in reversed(edits):
                text = text[:pos] + value + text[pos:]
            if edits:
                path.write_text(text)
    print(f'{total} missing proof dependencies; {len(skipped)} cyclic references require review')
    for source, target in skipped:
        print(f'  cycle prevented: {source} -> {target}')
    return int(args.check and bool(total or skipped))


if __name__ == '__main__':
    raise SystemExit(main())
