#!/usr/bin/env python3
"""Unverified source inventory; never evidence of a kernel-checked proof.

Usage: source_status.py blueprint.json output.json [--root PROJECT]
Generated declarations and external names remain unknown until checked by Lean.
"""
import argparse
import re
from pathlib import Path

from status_common import PROJECT, report, source_fingerprint, write_json

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom|opaque)\s+([^\s:({\[]+)", re.M)
IDENT = re.compile(r"[^\W\d][\w'.]*", re.UNICODE)
SCOPE = re.compile(r"^(namespace|section|end)\b(?:[ \t]+([^\s/-]+))?", re.M)


def strip_comments(src):
    """Mask nested Lean comments and strings, preserving offsets and line numbers."""
    out, i, depth = list(src), 0, 0
    while i < len(src):
        if src.startswith('/-', i):
            depth += 1
            out[i:i + 2] = '  '
            i += 2
        elif depth and src.startswith('-/', i):
            depth -= 1
            out[i:i + 2] = '  '
            i += 2
        elif depth:
            if src[i] != '\n':
                out[i] = ' '
            i += 1
        elif src.startswith('--', i):
            end = src.find('\n', i)
            end = len(src) if end < 0 else end
            out[i:end] = ' ' * (end - i)
            i = end
        elif src[i] == '"':
            out[i] = ' '
            i += 1
            while i < len(src):
                c = src[i]
                if c != '\n':
                    out[i] = ' '
                i += 1
                if c == '\\' and i < len(src):
                    out[i] = ' '
                    i += 1
                elif c == '"':
                    break
        else:
            i += 1
    return ''.join(out)


def declarations(root):
    bodies = {}
    for path in sorted((root / 'GSQG').rglob('*.lean')):
        src = strip_comments(path.read_text(encoding='utf-8'))
        matches = list(DECL.finditer(src))
        scopes = iter(SCOPE.finditer(src))
        scope, stack = next(scopes, None), []
        for i, match in enumerate(matches):
            while scope and scope.start() < match.start():
                kind, name = scope.groups()
                if kind == 'end':
                    if stack:
                        stack.pop()
                else:
                    stack.append(name if kind == 'namespace' else None)
                scope = next(scopes, None)
            name = match.group(2)
            namespace = '.'.join(s for s in stack if s)
            if name.startswith('_root_.'):
                name = name[7:]
            elif namespace:
                name = namespace + '.' + name
            end = matches[i + 1].start() if i + 1 < len(matches) else len(src)
            body = src[match.end():end]
            key = name if name not in bodies else f'{name}@{path.relative_to(root)}:{i}'
            bodies[key] = (name, body, match.group(1))
    return bodies


def scan(root, names):
    bodies = declarations(root)
    bp = set(names)
    aliases = {}
    for key, (name, _, _) in bodies.items():
        parts = name.split('.')
        for i in range(len(parts)):
            aliases.setdefault('.'.join(parts[i:]), set()).add(key)
    refs, direct = {}, {}
    for key, (_, body, kind) in bodies.items():
        toks = set(IDENT.findall(body))
        direct[key] = bool({'sorry', 'sorryAx', 'admit'} & toks) or kind == 'axiom'
        refs[key] = set().union(*(aliases.get(t, set()) for t in toks)) - {key}

    def reach(start, through_bp):
        todo, seen = list(start), set()
        while todo:
            key = todo.pop()
            if key in seen:
                continue
            seen.add(key)
            if direct[key]:
                return True
            todo.extend(r for r in refs[key] if through_bp or bodies[r][0] not in bp)
        return False

    result = {}
    for name in sorted(bp):
        keys = {k for k, (n, _, _) in bodies.items() if n == name}
        result[name] = {
            'exists': True if keys else None,
            'sorry': reach(keys, True) if keys else None,
            'local_sorry': reach(keys, False) if keys else None,
            'source_only': True,
        }
    return result


def main():
    import json
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('blueprint', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--root', type=Path, default=PROJECT)
    args = ap.parse_args()
    before = source_fingerprint(args.root)
    names = [l for n in json.loads(args.blueprint.read_text())['nodes'] for l in n['lean']]
    result = scan(args.root, names)
    if before != source_fingerprint(args.root):
        raise SystemExit('Sources changed during scan; previous report retained. Run again.')
    write_json(args.output, report(result, 'source', before, args.root))
    print(f'{len(result)} unique blueprint names: {sum(s["exists"] is True for s in result.values())} '
          'found in sources (unverified; generated/external declarations may be unknown)')


if __name__ == '__main__':
    main()
