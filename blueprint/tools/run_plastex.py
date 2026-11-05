"""Run plasTeX with an iterative ancestor search in plastexdepgraph.

The upstream `DepGraph.ancestors` recurses once per predecessor through `map`, which hits
Python's C recursion limit on large blueprints (and never terminates on a cycle). This
wrapper replaces it with an equivalent breadth-first search and reports any cycle found.
Usage: run_plastex.py [plastex arguments...]
"""
import sys

from plastexdepgraph.Packages import depgraph


def ancestors(self, node):
    if node not in self.nodes:
        return set()
    if node in self._ancestors:
        return self._ancestors[node]
    seen, todo = set(), list(self.predecessors(node))
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        if n in self._ancestors:
            seen |= self._ancestors[n]
        else:
            todo.extend(self.predecessors(n))
    if node in seen:
        print(f"run_plastex: dependency cycle through {getattr(node, 'id', node)}", file=sys.stderr)
    return self._ancestors.setdefault(node, seen)


depgraph.DepGraph.ancestors = ancestors

from plasTeX.client import plastex  # noqa: E402

sys.argv[0] = "plastex"
sys.exit(plastex())
