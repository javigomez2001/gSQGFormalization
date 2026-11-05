#!/usr/bin/env python3
"""Apply verified status to a *copy* of the LaTeX sources for leanblueprint.

The dashboard and the rendered dependency graph must use the same evidence.
Never write generated leanok markers into the maintained blueprint sources.
"""
import json
import re
import sys
from pathlib import Path

from build_site import NODE_ENVS, mask_comments, read_group, split_list


def coalesce_uses(text):
    r"""Emit one active \uses per statement/proof, as required by plastexdepgraph.

    Its callback replaces the environment's dependency list rather than appending.
    Keep statement and proof scopes separate, and retain comments from removed macros.
    """
    masked = mask_comments(text)
    envs = '|'.join((*NODE_ENVS, 'proof'))
    tokens = re.compile(r'\\(begin|end)\{(' + envs + r')\}|\\uses\s*\{')
    stack, groups = [], []
    for match in tokens.finditer(masked):
        action, env = match.groups()
        if action == 'begin':
            stack.append((env, []))
        elif action == 'end':
            if stack and stack[-1][0] == env:
                groups.append(stack.pop()[1])
        elif stack:
            content, end = read_group(masked, match.end() - 1)
            stack[-1][1].append((match.start(), end, split_list([content])))
    edits = []
    for uses in groups:
        if len(uses) < 2:
            continue
        names = list(dict.fromkeys(name for _, _, labels in uses for name in labels))
        for i, (start, end, _) in enumerate(uses):
            comments = ''.join(m.group() + '\n' for m in re.finditer(r'(?<!\\)%[^\n]*', text[start:end]))
            replacement = ('\\uses{' + ', '.join(names) + '}' if i == 0 else '')
            if comments:
                replacement += '\n' + comments
            edits.append((start, end, replacement))
    for start, end, replacement in sorted(edits, reverse=True):
        text = text[:start] + replacement + text[end:]
    return text


def annotate(data, source):
    by_file = {}
    for node in data['nodes']:
        by_file.setdefault(node['file'].removeprefix('src/'), []).append(node)
    for filename, nodes in by_file.items():
        path = source / filename
        text = path.read_text()
        edits = []
        for node in nodes:
            start = sum(len(line) for line in text.splitlines(keepends=True)[:node['line'] - 1])
            end = text.index('\\end{' + node['kind'] + '}', start)
            if data['lean_checked'] and node.get('lean_checked', False) and node['stated'] and (
                    node['kind'] != 'definition' or node['proved']):
                edits.append((end, '\\leanok\n'))
            # Definitions have no proof environment; lemma proofs get their own marker.
            if data['lean_checked'] and node.get('lean_checked', False) and node['proved'] and node['has_proof']:
                proof = text.index('\\begin{proof}', end)
                proof_end = text.index('\\end{proof}', proof)
                edits.append((proof_end, '\\leanok\n'))
            missing = node.get('uncovered_lean_uses', [])
            if data['lean_checked'] and missing:
                dep_at = text.index('\\end{proof}', end) if node['has_proof'] else end
                edits.append((dep_at, '\\uses{' + ', '.join(missing) + '}\n'))
        for pos, value in sorted(edits, reverse=True):
            text = text[:pos] + value + text[pos:]
        if not data['lean_checked']:
            text = re.sub(r'\\(?:leanok|mathlibok)\b', '', text)
        path.write_text(coalesce_uses(text))
    if data['lean_checked']:
        provenance = ('Statuses checked against the current Lean build. Proof completion is relative '
                      'to the displayed dependencies; see the dashboard for transitive axiom checks.')
    elif data.get('has_compiled_snapshot'):
        provenance = ('This graph has not been checked against the current Lean build. '
                      'The dashboard shows the dated results of the saved compiled build separately.')
    else:
        provenance = ('Unverified snapshot: no current compiled proof status is asserted in this graph. '
                      'See the dashboard for source inventory and freshness details.')
    content = source / 'content.tex'
    content.write_text('\\noindent ' + provenance + '\n\n' + content.read_text())


if __name__ == '__main__':
    annotate(json.loads(Path(sys.argv[1]).read_text()), Path(sys.argv[2]))
