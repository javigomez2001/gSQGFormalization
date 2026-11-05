#!/usr/bin/env python3
"""Build the formalization progress dashboard from the blueprint chapters.

Usage:
    python3 tools/build_site.py [--lean-status lean_status.json] [--out site]

Parses every src/chapters/*.tex file for leanblueprint nodes (definition,
lemma, proposition, theorem, corollary), extracts \\label, \\lean, \\uses,
\\leanok, \\mathlibok, \\notready, and the "% MATHLIB-GAP" comments,
computes leanblueprint-style statuses, and writes
site/data/blueprint.json, which site/index.html renders.

If --lean-status is given (JSON: {"GSQG.foo": {"exists": true, "sorry": false}}),
the Lean status overrides the \\leanok markers, in the spirit of LeanArchitect.
"""
import argparse
import datetime
import html
import json
import re
from pathlib import Path

from status_common import source_fingerprint, unpack_status, write_json

ROOT = Path(__file__).resolve().parent.parent
NODE_ENVS = ("definition", "lemma", "proposition", "theorem", "corollary")
KIND_SHORT = {"definition": "def", "lemma": "lem", "proposition": "prop",
              "theorem": "thm", "corollary": "cor"}


def strip_comments(text):
    """Remove LaTeX comments (unescaped % to end of line)."""
    return re.sub(r"(?<!\\)%.*", "", text)


def mask_comments(text):
    """Keep source offsets while making commented-out environments invisible."""
    return re.sub(r"(?<!\\)%[^\n]*", lambda m: " " * len(m.group()), text)


def comments(text):
    return [m.group(1).strip() for m in re.finditer(r"(?<!\\)%(.*)", text)]


def read_group(text, i, open_ch="{", close_ch="}"):
    """Given text[i] == open_ch, return (content, index after closing)."""
    assert text[i] == open_ch
    depth, j = 0, i
    while j < len(text):
        c = text[j]
        if c == "\\":
            j += 2
            continue
        if c == open_ch:
            depth += 1
        elif c == close_ch:
            depth -= 1
            if depth == 0:
                return text[i + 1:j], j + 1
        j += 1
    return text[i + 1:], len(text)


def command_args(text, name):
    out = []
    for m in re.finditer(r"\\" + name + r"\s*\{", text):
        content, _ = read_group(text, m.end() - 1)
        out.append(content)
    return out


def split_list(args):
    return [x.strip() for a in args for x in a.split(",") if x.strip()]


def to_html(body):
    """Light LaTeX-to-HTML conversion; math is left for KaTeX."""
    t = strip_comments(body)
    for cmd in ("label", "lean", "uses", "proves"):
        t = re.sub(r"\\" + cmd + r"\s*\{[^{}]*\}", "", t)
    t = re.sub(r"\\(leanok|mathlibok|notready)\b", "", t)
    t = html.escape(t, quote=False)
    t = re.sub(r"\\(?:[cC]ref|ref|eqref)\{([^{}]*)\}",
               lambda m: ", ".join(f'<a class="xref" data-ref="{r.strip()}">{r.strip()}</a>'
                                   for r in m.group(1).split(",")), t)
    for cmd, tag in (("emph", "em"), ("textit", "em"), ("textbf", "strong"), ("texttt", "code")):
        t = re.sub(r"\\" + cmd + r"\{([^{}]*)\}", rf"<{tag}>\1</{tag}>", t)
    t = re.sub(r"\\begin\{(enumerate|itemize)\}(\[[^\]]*\])?", r"<ul>", t)
    t = re.sub(r"\\end\{(enumerate|itemize)\}", r"</ul>", t)
    t = re.sub(r"\\item\s*(\[([^\]]*)\])?", lambda m: f"<li>{(m.group(2) or '') + ' ' if m.group(2) else ''}", t)
    t = re.sub(r"\\(par|medskip|smallskip|bigskip|noindent)\b", "<br>", t)
    # Apostrophes are derivative primes in math. Do not apply global prose-quote
    # substitutions: these would turn f'' and f''' into invalid mathematical text.
    t = t.replace("~", " ")
    t = re.sub(r"\n\s*\n", "<br><br>", t)
    return t.strip()


def find_env_end(text, env, start):
    m = re.compile(r"\\end\{" + env + r"\}").search(text, start)
    return (m.start(), m.end()) if m else (len(text), len(text))


def parse_chapter(path, chapter_titles):
    raw = path.read_text(encoding="utf-8")
    body_text = raw
    parse_text = mask_comments(body_text)
    chap_num = path.name.split("_")[0]
    nodes = []
    pat = re.compile(r"\\begin\{(" + "|".join(NODE_ENVS) + r")\}")
    pos = 0
    sections = [(m.start(), m.group(1)) for m in re.finditer(r"\\section\*?\{([^{}]*)\}", parse_text)]
    while True:
        m = pat.search(parse_text, pos)
        if not m:
            break
        # skip matches inside comments
        line_start = body_text.rfind("\n", 0, m.start()) + 1
        if "%" in body_text[line_start:m.start()].replace("\\%", ""):
            pos = m.end()
            continue
        env = m.group(1)
        i = m.end()
        title = ""
        while i < len(body_text) and body_text[i] in " \t":
            i += 1
        if i < len(body_text) and body_text[i] == "[":
            title, i = read_group(body_text, i, "[", "]")
        end_s, end_e = find_env_end(parse_text, env, i)
        stmt = body_text[i:end_s]
        # proof directly following (allow whitespace / comment lines)
        rest = parse_text[end_e:]
        pm = re.match(r"(?:\s|(?<!\\)%[^\n]*\n)*\\begin\{proof\}(\[[^\]]*\])?", rest)
        proof, after = "", end_e
        if pm:
            ps = end_e + pm.end()
            pe_s, pe_e = find_env_end(parse_text, "proof", ps)
            proof, after = body_text[ps:pe_s], pe_e
        before = body_text[max(0, line_start - 400):line_start]
        before_lines = before.splitlines()[-4:]
        # comments between the previous node and this one (MATHLIB-GAP annotations)
        pre_comments = " ".join(l for l in before_lines if l.strip().startswith("%"))
        labels = command_args(strip_comments(stmt), "label")
        if not labels:
            pos = after
            continue
        label = labels[0]
        sec = ""
        for s_pos, s_name in sections:
            if s_pos < m.start():
                sec = s_name
        stmt_clean = strip_comments(stmt)
        proof_clean = strip_comments(proof)
        node = {
            "id": label,
            "kind": env,
            "title": title.strip(),
            "chapter": chap_num,
            "section": sec,
            "lean": split_list(command_args(stmt_clean, "lean")),
            "uses": split_list(command_args(stmt_clean, "uses")),
            "proof_uses": split_list(command_args(proof_clean, "uses")),
            "stmt_leanok": bool(re.search(r"\\leanok\b", stmt_clean)),
            "proof_leanok": bool(re.search(r"\\leanok\b", proof_clean)),
            "mathlibok": bool(re.search(r"\\mathlibok\b", stmt_clean)),
            "notready": bool(re.search(r"\\notready\b", stmt_clean)),
            "mathlib_gap": "MATHLIB-GAP" in pre_comments or "MATHLIB-GAP" in stmt,
            "has_proof": bool(pm),
            "statement_html": to_html(stmt),
            "proof_html": to_html(proof),
            "line": raw.count("\n", 0, m.start()) + 1,
            "file": f"src/chapters/{path.name}",
        }
        nodes.append(node)
        pos = after
    return nodes


def node_dependencies(n):
    return list(dict.fromkeys(n["uses"] + n["proof_uses"] + n.get("lean_uses", [])))


def compute_status(nodes, lean_status, verified=False, compiled_snapshot=False):
    by_id = {n["id"]: n for n in nodes}
    owners = {}
    for n in nodes:
        for decl in n["lean"]:
            owners.setdefault(decl, set()).add(n["id"])
    for n in nodes:
        n["lean_uses"] = []
        n["fully_proved"] = False
        n["snapshot_stated"] = False
        n["snapshot_proved"] = False
        n["snapshot_fully_proved"] = False
        n["blueprint_only"] = False
        n["missing_lean_names"] = []
        n["unexpected_axioms"] = []
        if lean_status is not None and n["lean"]:
            st = [lean_status.get(d) for d in n["lean"]]
            n["missing_lean_names"] = [d for d, s in zip(n["lean"], st)
                                       if not s or s.get('exists') is not True]
            exists = all(s and s.get("exists") is True for s in st)
            n["unexpected_axioms"] = sorted({a for s in st if s for a in s.get("axioms", [])
                if a not in {"propext", "Classical.choice", "Quot.sound", "sorryAx"}})
            sorry_free = exists and not n["unexpected_axioms"] and all(
                s.get("local_sorry", s.get("sorry")) is False for s in st)
            n["stated"] = exists
            n["proved"] = sorry_free
            snapshot_checked = (verified or compiled_snapshot) and exists and all(not s.get('source_only') and
                isinstance(s.get('axioms'), list) for s in st)
            checked = verified and snapshot_checked
            n["lean_checked"] = checked
            if verified and not checked:
                n["proved"] = False
            n["fully_proved"] = checked and not n["unexpected_axioms"] and all(
                s.get("sorry") is False for s in st)
            n["snapshot_stated"] = snapshot_checked
            n["snapshot_proved"] = snapshot_checked and sorry_free
            n["snapshot_fully_proved"] = snapshot_checked and not n["unexpected_axioms"] and all(
                s.get("sorry") is False for s in st)
            n["blueprint_only"] = compiled_snapshot and not exists
            n["lean_uses"] = sorted({owner for s in st if s for d in s.get("blueprint_deps", [])
                                    for owner in owners.get(d, ()) if owner != n["id"]})
        else:
            n["stated"] = n["stmt_leanok"] or n["mathlibok"]
            n["proved"] = n["mathlibok"] or (n["stmt_leanok"] and
                                             (n["proof_leanok"] or (n["kind"] == "definition"
                                                                    and n["stmt_leanok"])))
            n["lean_checked"] = False
            if compiled_snapshot:
                n["blueprint_only"] = True
                n["stated"] = False
                n["proved"] = False
    missing = set()
    for n in nodes:
        for d in node_dependencies(n):
            if d not in by_id:
                missing.add(d)
    memo = {}

    def fully(nid, stack=()):
        if nid in memo:
            return memo[nid]
        n = by_id.get(nid)
        if n is None or nid in stack:
            return False
        ok = n["proved"] and all(fully(d, stack + (nid,)) for d in node_dependencies(n))
        memo[nid] = ok
        return ok

    for n in nodes:
        deps_s = [by_id[d] for d in n["uses"] if d in by_id]
        deps_p = [by_id[d] for d in node_dependencies(n) if d in by_id]
        dangling = [d for d in node_dependencies(n) if d not in by_id]
        n["dangling"] = dangling
        n["ready_to_state"] = not n["notready"] and all(d["stated"] for d in deps_s) and not any(
            d not in by_id for d in n['uses'])
        n["graph_fully_proved"] = fully(n["id"])
        if n["mathlibok"] and n["fully_proved"]:
            status = "mathlib"
        elif n["fully_proved"]:
            status = "fully_proved"
        elif compiled_snapshot and n["snapshot_fully_proved"]:
            status = "snapshot_fully_proved"
        elif n["proved"]:
            status = "proved"
        elif n["stated"] and all(d["proved"]
                                 for d in deps_p) and not dangling:
            status = "can_prove"
        elif n["stated"]:
            status = "stated"
        elif n["notready"]:
            status = "not_ready"
        elif n["blueprint_only"]:
            status = "blueprint_only"
        elif all(d["stated"] for d in deps_s) and not [d for d in n["uses"] if d not in by_id]:
            status = "can_state"
        else:
            status = "blocked"
        n["status"] = status
    return sorted(missing)


def critical_ancestors(nodes, root):
    by_id = {n["id"]: n for n in nodes}
    seen, todo = set(), [root]
    while todo:
        x = todo.pop()
        if x in seen or x not in by_id:
            continue
        seen.add(x)
        todo.extend(node_dependencies(by_id[x]))
    return seen


def select_main_path(nodes, target=None):
    """The primary theorem shown on the dashboard (Theorem 1.1 by default)."""
    root = target or 'thm:main'
    node = next((n for n in nodes if n['id'] == root), None)
    if node is None and target:
        raise ValueError(f'Unknown target node: {root}')
    label = (node.get('title') if node else None) or root
    return root, label, critical_ancestors(nodes, root)


def uncovered_lean_dependencies(nodes):
    """Only flag compiled dependencies not already represented through blueprint \\uses."""
    declared = {n['id']: n['uses'] + n['proof_uses'] for n in nodes}
    gaps = []
    for n in nodes:
        seen, todo = set(), list(declared[n['id']])
        while todo:
            d = todo.pop()
            if d not in seen:
                seen.add(d)
                todo.extend(declared.get(d, ()))
        missing = sorted(set(n.get('lean_uses', ())) - seen)
        n['uncovered_lean_uses'] = missing
        if missing:
            gaps.append({'node': n['id'], 'dependencies': missing})
    return gaps


def load_blueprint():
    content = (ROOT / "src" / "content.tex").read_text(encoding="utf-8")
    chapter_titles = {}
    for m in re.finditer(r"\\chapter\{(.*?)\}\\input\{chapters/(\d+)_", content):
        chapter_titles[m.group(2)] = m.group(1)

    nodes = []
    paths = [ROOT / "src" / (name + ".tex") for name in
             command_args(strip_comments(content), "input")]
    for path in paths:
        nodes.extend(parse_chapter(path, chapter_titles))
    return nodes, chapter_titles


def dependency_cycles(nodes):
    """Strongly connected components, including self loops, in the displayed graph."""
    graph = {n['id']: node_dependencies(n) for n in nodes}
    index, low, stack, active, cycles = {}, {}, [], set(), []

    def visit(v):
        index[v] = low[v] = len(index)
        stack.append(v)
        active.add(v)
        for w in graph[v]:
            if w not in graph:
                continue
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in active:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            component = []
            while True:
                w = stack.pop()
                active.remove(w)
                component.append(w)
                if w == v:
                    break
            if len(component) > 1 or v in graph[v]:
                cycles.append(sorted(component))
    for v in graph:
        if v not in index:
            visit(v)
    return sorted(cycles)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean-status", type=Path)
    ap.add_argument("--no-status", action="store_true", help="Parse only, for collecting Lean names")
    ap.add_argument("--out", type=Path, default=ROOT / "site")
    ap.add_argument("--target", default=None,
                    help="Primary theorem for the dashboard's path view (default: thm:main)")
    args = ap.parse_args()
    nodes, chapter_titles = load_blueprint()

    lean_status = None
    metadata = {"source": "markers"}
    status_path = args.lean_status
    if status_path is None and not args.no_status:
        for candidate in (ROOT / 'build/lean_status.json', ROOT / 'build/source_status.json'):
            if candidate.exists():
                status_path = candidate
                break
    if status_path is not None and not args.no_status:
        lean_status, metadata = unpack_status(json.loads(status_path.read_text()))
    fresh = metadata.get('source_fingerprint') == source_fingerprint()
    verified = metadata['source'] == 'lean' and fresh
    compiled_snapshot = metadata['source'] == 'lean' and bool(metadata.get('checked_at'))
    metadata = {**metadata, 'fresh': fresh}

    # duplicate labels
    seen, dups = set(), set()
    for n in nodes:
        if n["id"] in seen:
            dups.add(n["id"])
        seen.add(n["id"])

    missing = compute_status(nodes, lean_status, verified, compiled_snapshot)
    main_path_root, main_path_label, on_path = select_main_path(nodes, args.target)
    for n in nodes:
        n["on_main_path"] = n["id"] in on_path

    chapters = []
    chapter_files = {p.name.split("_")[0]: p for p in (ROOT / "src" / "chapters").glob("*.tex")}
    for num in sorted(chapter_titles):
        # skip chapters without blueprint nodes
        f = chapter_files.get(num)
        if f and not any(n["chapter"] == num for n in nodes) and not re.search(
                r"\\begin\{(" + "|".join(NODE_ENVS) + r")\}", f.read_text(encoding="utf-8")):
            continue
        chapters.append({
            "num": num,
            "title": chapter_titles.get(num, ""),
            "written": any(n["chapter"] == num for n in nodes),
        })

    data = {
        "generated": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "lean_checked": verified,
        "source_current": verified,
        "has_compiled_snapshot": compiled_snapshot,
        "source_scan": metadata['source'] == 'source',
        "provenance": metadata,
        "main_path_root": main_path_root,
        "main_path_label": main_path_label,
        "artifacts": {"html": (ROOT / 'site/blueprint/index.html').exists(),
                      "pdf": (ROOT / 'site/blueprint.pdf').exists()},
        "chapters": chapters,
        "nodes": nodes,
        "missing_labels": missing,
        "duplicate_labels": sorted(dups),
        "dependency_cycles": dependency_cycles(nodes),
        "undeclared_lean_dependencies": uncovered_lean_dependencies(nodes),
        "unexpected_axioms": [
            {"node": n['id'], "axioms": n['unexpected_axioms']} for n in nodes if n['unexpected_axioms']],
    }
    if compiled_snapshot:
        records = list(lean_status.values())
        acceptable = lambda s: s.get('exists') is True and isinstance(s.get('axioms'), list) and not s.get('source_only') and all(
            a in {'propext', 'Classical.choice', 'Quot.sound', 'sorryAx'} for a in s['axioms'])
        data['snapshot_summary'] = {
            'checked_at': metadata.get('checked_at'),
            'declarations': len(records),
            'existing_declarations': sum(s.get('exists') is True for s in records),
            'locally_complete_declarations': sum(acceptable(s) and s.get('local_sorry') is False for s in records),
            'fully_proved_declarations': sum(acceptable(s) and s.get('sorry') is False for s in records),
        }
    artifact_record = ROOT / 'site/data/artifacts.json'
    if artifact_record.exists():
        rendered = json.loads(artifact_record.read_text())
        data['artifacts']['current'] = (
            rendered.get('source_fingerprint') == source_fingerprint() and
            rendered.get('status_checked_at') == metadata.get('checked_at') and
            rendered.get('lean_checked') == verified)
        data['artifacts']['rendered_at'] = rendered.get('rendered_at')
    else:
        data['artifacts']['current'] = False
    out = args.out / "data"
    out.mkdir(parents=True, exist_ok=True)
    write_json(out / "blueprint.json", data)
    # also as JS so index.html works from file:// without a server
    (out / "blueprint.js").write_text("window.BLUEPRINT = " + json.dumps(data, ensure_ascii=False) + ";\n",
                                      encoding="utf-8")
    counts = {}
    for n in nodes:
        counts[n["status"]] = counts.get(n["status"], 0) + 1
    print(f"{len(nodes)} nodes from {sum(c['written'] for c in chapters)} chapters; status {counts}")
    print(f"{len(missing)} labels referenced but not defined; {len(dups)} duplicate labels")


if __name__ == "__main__":
    main()
