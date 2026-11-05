#!/usr/bin/env bash
# Build in staging; publish only after every requested check and renderer succeeds.
# WITH_LEAN=1 rebuilds Lean; otherwise retain a cached report with visible freshness.
# BLUEPRINT_SKIP_PDF=1 explicitly omits the PDF (e.g. on a host without TeX).
set -euo pipefail
cd "$(dirname "$0")"
BLUEPRINT_ENV="${BLUEPRINT_VENV:-$HOME/.venvs/gsqg-blueprint}"
TOOLS="$(pwd)/tools"
mkdir -p build
stage=$(mktemp -d "$(pwd)/build/site-stage.XXXXXX")
trap 'rm -rf "$stage"' EXIT
python3 - <<'PY' > "$stage/fingerprint"
import sys
sys.path.insert(0, 'tools')
from status_common import source_fingerprint
print(source_fingerprint())
PY
mkdir -p "$stage/site"
cp -r src "$stage/src"
cp site/index.html "$stage/site/index.html"
if [ "${WITH_LEAN:-0}" = 1 ]; then
  lean_args=()
  if [ -n "${LEAN_PROJECT:-}" ]; then lean_args+=(--project "$LEAN_PROJECT"); fi
  python3 tools/collect_status.py "${lean_args[@]}" --out "$stage/site"
  LEAN_STATUS="$(pwd)/build/lean_status.json"
fi
status_args=()
if [ -n "${LEAN_STATUS:-}" ]; then status_args+=(--lean-status "$LEAN_STATUS"); fi
python3 tools/build_site.py "${status_args[@]}" --out "$stage/site"
python3 tools/render_status.py "$stage/site/data/blueprint.json" "$stage/src"
if [ "${BLUEPRINT_SKIP_PDF:-0}" != 1 ]; then
  if ! (cd "$stage/src" && latexmk -pdf -interaction=nonstopmode -halt-on-error print.tex > latexmk.log 2>&1); then
    cp "$stage/src/latexmk.log" build/latexmk.log
    echo "PDF build failed; site retained. See blueprint/build/latexmk.log" >&2
    exit 1
  fi
  cp "$stage/src/print.pdf" "$stage/site/blueprint.pdf"
  if [ -f "$stage/src/print.bbl" ]; then cp "$stage/src/print.bbl" "$stage/src/web.bbl"; fi
fi
if ! (cd "$stage/src" && "$BLUEPRINT_ENV/bin/python3" "$TOOLS/run_plastex.py" -c plastex.cfg web.tex > ../site/plastex.log 2>&1); then
  cp "$stage/site/plastex.log" build/plastex.log
  echo "plasTeX failed; site retained. See blueprint/build/plastex.log" >&2
  exit 1
fi
# The renderer wrote ../site/blueprint relative to the copied source tree.
python3 - "$stage" <<'PY'
import datetime, json, sys
from pathlib import Path
sys.path.insert(0, 'tools')
from status_common import source_fingerprint, write_json
stage = Path(sys.argv[1])
if source_fingerprint() != (stage / 'fingerprint').read_text().strip():
    raise SystemExit('Sources changed during rendering; previous site retained. Run again.')
path = stage / 'site/data/blueprint.json'
data = json.loads(path.read_text())
rendered_at = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
data['artifacts'] = {'html': (stage / 'site/blueprint/index.html').exists(),
                     'pdf': (stage / 'site/blueprint.pdf').exists(),
                     'current': True, 'rendered_at': rendered_at}
write_json(stage / 'site/data/artifacts.json', {
    'source_fingerprint': source_fingerprint(),
    'status_checked_at': data['provenance'].get('checked_at'),
    'lean_checked': data['lean_checked'], 'rendered_at': rendered_at})
write_json(path, data)
(path.parent / 'blueprint.js').write_text('window.BLUEPRINT = ' + json.dumps(data, ensure_ascii=False) + ';\n')
PY
cp -r "$stage/site/data" site/
rm -rf site/blueprint
cp -r "$stage/site/blueprint" site/
cp "$stage/site/plastex.log" site/
if [ -f "$stage/site/blueprint.pdf" ]; then cp "$stage/site/blueprint.pdf" site/; else rm -f site/blueprint.pdf; fi
python3 - <<'PY'
import json
from pathlib import Path
nodes = json.loads(Path('site/data/blueprint.json').read_text())['nodes']
names = sorted({name for n in nodes for name in n['lean']})
Path('lean_decls').write_text('\n'.join(names) + '\n')
PY
echo "Site built in $(pwd)/site"
