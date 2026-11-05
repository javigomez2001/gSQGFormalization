#!/usr/bin/env python3
"""Check the actual plasTeX graph against dashboard dependency reachability.

The graph may be transitively reduced, so compare ancestor sets rather than direct edges.
Usage: check_rendered_graph.py [--data blueprint.json] [--graph dep_graph_document.html]
No Lean execution or rendering is performed by this check.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import re

PROJECT = Path(__file__).resolve().parents[3]


def ancestors(graph, node):
    seen, todo = set(), list(graph.get(node, ()))
    while todo:
        predecessor = todo.pop()
        if predecessor not in seen:
            seen.add(predecessor)
            todo.extend(graph.get(predecessor, ()))
    return seen


def check(data, rendered):
    match = re.search(r'\.renderDot\(`(.*?)`\)', rendered, re.S)
    if match is None:
        raise ValueError('No rendered DOT graph found in the HTML.')
    dot = match.group(1)
    edges = set(re.findall(r'"([^"]+)"\s*->\s*"([^"]+)"', dot))
    actual = defaultdict(set)
    for source, target in edges:
        actual[target].add(source)
    graph_nodes = set(re.findall(r'"([^"]+)"\s*\[', dot))
    expected = {n['id']: set(n['uses'] + n['proof_uses'] +
                            (n.get('lean_uses', []) if data['lean_checked'] else []))
                for n in data['nodes']}
    if graph_nodes != set(expected):
        raise ValueError(f'Graph nodes differ: missing={sorted(set(expected) - graph_nodes)}, '
                         f'extra={sorted(graph_nodes - set(expected))}')
    failures = []
    for node in expected:
        want, got = ancestors(expected, node), ancestors(actual, node)
        if want != got:
            failures.append((node, sorted(want - got), sorted(got - want)))
    if failures:
        examples = '; '.join(f'{node}: missing {missing[:8]}, extra {extra[:8]}'
                             for node, missing, extra in failures[:6])
        raise ValueError(f'{len(failures)} nodes have incorrect rendered dependency reachability. {examples}')
    return len(expected), len(edges), len(ancestors(actual, data.get('main_path_root', 'thm:main')))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=PROJECT / 'blueprint/site/data/blueprint.json')
    parser.add_argument('--graph', type=Path, default=PROJECT / 'blueprint/site/blueprint/dep_graph_document.html')
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    nodes, edges, main_ancestors = check(data, args.graph.read_text())
    print(f'Rendered graph matches all {nodes} nodes ({edges} edges after reduction); '
          f'all {main_ancestors} ancestors of {data.get("main_path_root", "thm:main")} are present.')


if __name__ == '__main__':
    main()
