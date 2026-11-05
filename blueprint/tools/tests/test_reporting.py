"""Regression checks for proof evidence, source parsing, and failure-safe publication."""
import copy
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import build_site
import collect_status
import render_status
import source_status
import status_common


def node(nid, lean=None, **kwargs):
    return dict(id=nid, lean=lean or ['GSQG.' + nid.split(':')[-1]], uses=[], proof_uses=[],
                kind='lemma', stmt_leanok=False, proof_leanok=False, mathlibok=False,
                notready=False, **kwargs)


def checked(sorry=False, local=False, deps=(), axioms=()):
    return dict(exists=True, sorry=sorry, local_sorry=local,
                blueprint_deps=list(deps), axioms=list(axioms))


class EvidenceTests(unittest.TestCase):
    def test_primary_target_can_be_selected_and_defaults_to_front_theorem(self):
        front, bridge, patch = node('thm:main'), node('lem:patch_bridge'), node('thm:c13_patch_main')
        front['title'], patch['title'] = 'Front theorem', '2D patch theorem'
        patch['proof_uses'] = ['thm:main', 'lem:patch_bridge']
        nodes = [front, bridge, patch]
        root, label, path = build_site.select_main_path(nodes, 'thm:c13_patch_main')
        self.assertEqual((root, label), ('thm:c13_patch_main', '2D patch theorem'))
        self.assertEqual(path, {'thm:main', 'lem:patch_bridge', 'thm:c13_patch_main'})
        root, label, path = build_site.select_main_path(nodes)
        self.assertEqual((root, label, path), ('thm:main', 'Front theorem', {'thm:main'}))
        with self.assertRaisesRegex(ValueError, 'Unknown target node'):
            build_site.select_main_path(nodes, 'thm:typo')

    def test_blueprint_split_keeps_saved_results_without_new_certification(self):
        old, planned = node('lem:old'), node('lem:planned')
        old['proof_uses'] = ['lem:planned']
        status = {'GSQG.old': checked()}
        build_site.compute_status([old, planned], status, verified=False, compiled_snapshot=True)
        self.assertFalse(old['lean_checked'])
        self.assertFalse(old['fully_proved'])
        self.assertTrue(old['snapshot_fully_proved'])
        self.assertEqual(old['status'], 'snapshot_fully_proved')
        self.assertFalse(planned['stated'])
        self.assertFalse(planned['proved'])
        self.assertFalse(planned['snapshot_fully_proved'])
        self.assertTrue(planned['blueprint_only'])
        self.assertEqual(planned['status'], 'blueprint_only')
        self.assertEqual(planned['missing_lean_names'], ['GSQG.planned'])

    def test_source_approximation_does_not_become_historical_compiled_evidence(self):
        n = node('lem:a')
        s = {**checked(), 'source_only': True}
        build_site.compute_status([n], {'GSQG.a': s}, compiled_snapshot=True)
        self.assertFalse(n['snapshot_stated'])
        self.assertFalse(n['snapshot_proved'])
        self.assertFalse(n['snapshot_fully_proved'])

    def test_omitted_dependency_cannot_give_false_full_proof(self):
        nodes = [node('lem:a'), node('lem:b')]
        status = {'GSQG.a': checked(sorry=True, deps=['GSQG.b']),
                  'GSQG.b': checked(sorry=True, local=True)}
        build_site.compute_status(nodes, status, verified=True)
        self.assertEqual(nodes[0]['status'], 'proved')
        self.assertFalse(nodes[0]['fully_proved'])
        self.assertEqual(nodes[0]['lean_uses'], ['lem:b'])
        self.assertEqual(build_site.critical_ancestors(nodes, 'lem:a'), {'lem:a', 'lem:b'})

    def test_unused_planned_dependency_does_not_undercount(self):
        nodes = [node('lem:a'), node('lem:b')]
        nodes[0]['proof_uses'] = ['lem:b']
        status = {'GSQG.a': checked(), 'GSQG.b': checked(True, True)}
        build_site.compute_status(nodes, status, verified=True)
        self.assertTrue(nodes[0]['fully_proved'])
        self.assertFalse(nodes[0]['graph_fully_proved'])

    def test_all_registered_declarations_must_exist(self):
        nodes = [node('lem:a', ['GSQG.a', 'GSQG.missing'])]
        build_site.compute_status(nodes, {'GSQG.a': checked()}, verified=True)
        self.assertFalse(nodes[0]['stated'])
        self.assertFalse(nodes[0]['fully_proved'])

    def test_mathlib_markers_do_not_override_missing_declarations(self):
        n = node('lem:mathlib', ['Missing.mathlib_lemma'])
        n['mathlibok'] = True
        build_site.compute_status([n], {}, verified=True)
        self.assertFalse(n['stated'])
        self.assertNotEqual(n['status'], 'mathlib')

    def test_source_stale_legacy_reports_are_never_fully_proved(self):
        for verified, source_only, axioms in [(False, False, []), (True, True, []), (True, False, None)]:
            with self.subTest(verified=verified, source_only=source_only, axioms=axioms):
                n = node('lem:a')
                s = dict(exists=True, sorry=False, local_sorry=False, source_only=source_only)
                if axioms is not None:
                    s['axioms'] = axioms
                build_site.compute_status([n], {'GSQG.a': s}, verified=verified)
                self.assertFalse(n['fully_proved'])

    def test_nonstandard_axioms_are_not_accepted_as_proofs(self):
        n = node('lem:a')
        build_site.compute_status([n], {'GSQG.a': checked(axioms=['GSQG.customAxiom'])}, True)
        self.assertFalse(n['proved'])
        self.assertFalse(n['fully_proved'])
        self.assertEqual(n['unexpected_axioms'], ['GSQG.customAxiom'])

    def test_cycles_are_reported_without_infinite_recursion(self):
        nodes = [node('lem:a'), node('lem:b')]
        status = {'GSQG.a': checked(deps=['GSQG.b']), 'GSQG.b': checked(deps=['GSQG.a'])}
        build_site.compute_status(nodes, status, True)
        self.assertEqual(build_site.dependency_cycles(nodes), [['lem:a', 'lem:b']])
        self.assertTrue(all(n['fully_proved'] for n in nodes))

    def test_transitively_represented_dependencies_are_not_reported_as_gaps(self):
        a, b, c = node('lem:a'), node('lem:b'), node('lem:c')
        a['proof_uses'] = ['lem:b']
        b['proof_uses'] = ['lem:c']
        a['lean_uses'] = ['lem:c']
        self.assertEqual(build_site.uncovered_lean_dependencies([a,b,c]), [])

    def test_definition_with_sorry_is_not_a_finished_dependency(self):
        a, b = node('def:a'), node('lem:b')
        a['kind'] = 'definition'
        b['uses'] = ['def:a']
        build_site.compute_status([a,b], {'GSQG.a': checked(True, True), 'GSQG.b': checked(True, True)}, True)
        self.assertEqual(b['status'], 'stated')


class MetadataTests(unittest.TestCase):
    def test_current_paper_map_covers_the_manuscript_numbering(self):
        # The maintained manuscript uses one theorem counter, reset by section.
        root = status_common.PROJECT
        paper = build_site.strip_comments((root / 'paper/gsqg_Nov26.tex').read_text())
        paper = paper[paper.index(r'\begin{document}'):]
        kinds = 'theorem|lemma|proposition|definition|remark|corollary|notation|convention|example'
        events = re.finditer(r'\\appendix|\\section\{([^}]+)\}|\\begin\{(' + kinds + r')\}', paper)
        appendix, section, number, expected = False, 0, 0, set()
        for event in events:
            if event.group() == r'\appendix':
                appendix, section = True, 0
            elif event.group(1):
                section, number = section + 1, 0
            else:
                number += 1
                prefix = chr(64 + section) if appendix else str(section)
                expected.add((event.group(2).capitalize(), f'{prefix}.{number}'))
        text = (root / 'docs/PAPER_MAP.md').read_text()
        rows = re.findall(r'^\| (Theorem|Lemma|Proposition|Definition|Remark|Corollary|Notation|Convention|Example) '
                          r'([\dAB]+\.\d+)\b', text.split('## Beyond the paper')[0], re.M)
        self.assertEqual(len(rows), len(set(rows)), 'Duplicate paper-map entries')
        self.assertEqual(set(rows), expected)
        for line in text.splitlines():
            if line.startswith('|'):
                self.assertEqual(len(re.split(r'(?<!\\)\|', line)), 5,
                                 'Unescaped vertical bar in paper-map table: ' + line)


class SourceTests(unittest.TestCase):
    def test_comments_strings_and_namespace_scopes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'GSQG').mkdir()
            (root / 'GSQG/Example.lean').write_text('''namespace GSQG
/- ignored /- nested -/ theorem fake : False := sorry -/
namespace Lib
section
private theorem helper : True := by sorry
theorem usesHelper : True := helper
end
end Lib
def text := "sorry /- not a comment -/"
theorem done : True := True.intro
end GSQG
''')
            result = source_status.scan(root, ['GSQG.Lib.usesHelper', 'GSQG.done', 'GSQG.fake',
                                              'GSQG.text', 'Missing.Mathlib', 'GSQG.done.field'])
            self.assertTrue(result['GSQG.Lib.usesHelper']['local_sorry'])
            self.assertFalse(result['GSQG.done']['local_sorry'])
            self.assertFalse(result['GSQG.text']['local_sorry'])
            for name in ['GSQG.fake', 'Missing.Mathlib', 'GSQG.done.field']:
                self.assertIsNone(result[name]['exists'])
            self.assertTrue(all(s['source_only'] for s in result.values()))

    def test_blueprint_boundary_is_local_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'GSQG').mkdir()
            (root / 'GSQG/Example.lean').write_text('''namespace GSQG
theorem unfinished : True := by sorry
theorem wrapper : True := unfinished
end GSQG
''')
            result = source_status.scan(root, ['GSQG.unfinished', 'GSQG.wrapper'])
            self.assertFalse(result['GSQG.wrapper']['local_sorry'])
            self.assertTrue(result['GSQG.wrapper']['sorry'])

    def test_latex_commented_labels_and_environments_ignored(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / '01_example.tex'
            p.write_text(r'''% \begin{lemma}\label{lem:fake}\end{lemma}
\begin{lemma}
% \label{lem:wrong}
\label{lem:actual}\lean{GSQG.actual}
% \end{lemma}
Text.
\end{lemma}
\begin{proof}
% \end{proof}
\uses{lem:dependency}
Done.
\end{proof}
''')
            nodes = build_site.parse_chapter(p, {})
            self.assertEqual([n['id'] for n in nodes], ['lem:actual'])
            self.assertEqual(nodes[0]['proof_uses'], ['lem:dependency'])

    def test_fingerprint_changes_with_proof_statement_or_toolchain(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for file in ['GSQG.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                         'GSQG/A.lean', 'blueprint/src/chapters/01_example.tex', 'blueprint/tools/LeanStatus.lean']:
                p = root / file
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(file)
            for file in ['GSQG/A.lean', 'blueprint/src/chapters/01_example.tex', 'lean-toolchain']:
                before = status_common.source_fingerprint(root)
                with (root / file).open('a') as stream:
                    stream.write('changed')
                self.assertNotEqual(before, status_common.source_fingerprint(root))


class RenderTests(unittest.TestCase):
    def test_multiple_uses_are_coalesced_per_environment_without_losing_comments(self):
        text = r'''\begin{lemma}
\uses{def:a, % a comment inside the argument
 def:b}
% \uses{def:ignored}
\uses{def:c, def:a}
Statement.
\end{lemma}
\begin{proof}
\uses{lem:p}
% Preserve this explanation.
\uses{lem:q, lem:p}
Proof.
\end{proof}
'''
        result = render_status.coalesce_uses(text)
        active = build_site.strip_comments(result)
        statement, proof = active.split(r'\begin{proof}')
        self.assertEqual(build_site.command_args(statement, 'uses'), ['def:a, def:b, def:c'])
        self.assertEqual(build_site.command_args(proof, 'uses'), ['lem:p, lem:q'])
        self.assertIn('% a comment inside the argument', result)
        self.assertIn(r'% \uses{def:ignored}', result)
        self.assertIn('% Preserve this explanation.', result)

    def test_dashboard_preserves_double_and_triple_derivative_primes(self):
        text = "$f''(y)$ and $f'''(y)$, with $g^{(3)}(y)$ unchanged."
        rendered = build_site.to_html(text)
        self.assertIn("$f''(y)$", rendered)
        self.assertIn("$f'''(y)$", rendered)
        self.assertNotIn('\u201d', rendered)

    def test_compiled_statement_and_proof_markers_are_separate(self):
        for proved, expected in [(False, 1), (True, 2)]:
            with self.subTest(proved=proved), tempfile.TemporaryDirectory() as tmp:
                source = Path(tmp)
                (source / 'chapters').mkdir()
                (source / 'content.tex').write_text('content')
                path = source / 'chapters/01_example.tex'
                path.write_text('\\begin{lemma}\\label{lem:a}\nText.\n\\end{lemma}\n'
                                '\\begin{proof}\nProof.\n\\end{proof}\n')
                data = {'lean_checked': True, 'nodes': [dict(id='lem:a', file='src/chapters/01_example.tex',
                        line=1, kind='lemma', stated=True, lean_checked=True, proved=proved,
                        has_proof=True, uses=[], proof_uses=[], uncovered_lean_uses=['lem:b'])]}
                render_status.annotate(data, source)
                self.assertEqual(path.read_text().count('\\leanok'), expected)
                self.assertIn('\\uses{lem:b}', path.read_text())

    def test_render_copy_does_not_assert_unverified_markers(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp)
            (source / 'chapters').mkdir()
            (source / 'content.tex').write_text('content')
            path = source / 'chapters/01_example.tex'
            path.write_text('\\begin{lemma}\\label{lem:a}\\leanok\\mathlibok\nText.\n\\end{lemma}\n')
            data = {'lean_checked': False, 'nodes': [dict(id='lem:a', file='src/chapters/01_example.tex',
                    line=1, kind='lemma', stated=True, proved=True, has_proof=False, uses=[], proof_uses=[])]}
            render_status.annotate(data, source)
            self.assertNotIn('\\leanok', path.read_text())
            self.assertNotIn('\\mathlibok', path.read_text())

    def test_full_build_failure_retains_previous_site(self):
        for stage in ['pdf', 'html']:
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                bp = root / 'blueprint'
                (bp / 'tools').mkdir(parents=True)
                (bp / 'src').mkdir()
                (bp / 'site/data').mkdir(parents=True)
                (bp / 'site/blueprint').mkdir()
                (bp / 'site/index.html').write_text('dashboard')
                (bp / 'site/data/blueprint.json').write_text('old data')
                (bp / 'site/blueprint/index.html').write_text('old html')
                shutil.copy2(TOOLS.parent / 'build.sh', bp / 'build.sh')
                (bp / 'tools/status_common.py').write_text("def source_fingerprint(): return 'unchanged'\n")
                (bp / 'tools/build_site.py').write_text("""import pathlib,sys
out=pathlib.Path(sys.argv[sys.argv.index('--out')+1])
(out/'data').mkdir(parents=True,exist_ok=True)
(out/'data/blueprint.json').write_text('{"nodes":[]}')
""")
                (bp / 'tools/render_status.py').write_text('')
                (root / 'bin').mkdir()
                failing = root / 'bin/latexmk'
                failing.write_text('#!/bin/sh\nexit 17\n')
                failing.chmod(0o755)
                venv = root / 'venv/bin'
                venv.mkdir(parents=True)
                (venv / 'plastex').write_text('#!/bin/sh\nexit 23\n')
                (venv / 'plastex').chmod(0o755)
                env = {**os.environ, 'PATH': str(root / 'bin') + ':' + os.environ['PATH'],
                       'BLUEPRINT_VENV': str(root / 'venv'), 'BLUEPRINT_SKIP_PDF': '1' if stage == 'html' else '0'}
                result = subprocess.run(['bash', str(bp / 'build.sh')], env=env, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual((bp / 'site/data/blueprint.json').read_text(), 'old data')
                self.assertEqual((bp / 'site/blueprint/index.html').read_text(), 'old html')
                self.assertFalse(list((bp / 'build').glob('site-stage.*')))

    def test_failed_lean_build_does_not_write_status_or_scan_old_objects(self):
        with mock.patch.object(sys, 'argv', ['collect_status.py']), \
             mock.patch.object(collect_status, 'source_fingerprint', return_value='same'), \
             mock.patch.object(collect_status, 'load_blueprint', return_value=([], {})), \
             mock.patch.object(collect_status, 'write_json') as writer, \
             mock.patch.object(collect_status.subprocess, 'run', side_effect=subprocess.CalledProcessError(1, 'lake')) as run:
            with self.assertRaises(subprocess.CalledProcessError):
                collect_status.main()
            self.assertEqual(run.call_count, 1)
            self.assertIn('GSQG', run.call_args.args[0])
            self.assertEqual(writer.call_count, 1)  # temporary blueprint names only

    def test_source_change_during_check_discards_new_report(self):
        def run(command, **kwargs):
            if '--run' in command:
                Path(command[-1]).write_text('{}')
        with mock.patch.object(sys, 'argv', ['collect_status.py']), \
             mock.patch.object(collect_status, 'source_fingerprint', side_effect=['before','before','after']), \
             mock.patch.object(collect_status, 'load_blueprint', return_value=([], {})), \
             mock.patch.object(collect_status, 'write_json', wraps=status_common.write_json) as writer, \
             mock.patch.object(collect_status.subprocess, 'run', side_effect=run):
            with self.assertRaisesRegex(SystemExit, 'Sources changed'):
                collect_status.main()
            self.assertEqual(writer.call_count, 1)


if __name__ == '__main__':
    unittest.main()
