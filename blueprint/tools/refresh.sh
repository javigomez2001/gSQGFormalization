#!/usr/bin/env bash
# Fast unverified inventory by default; --lean always builds the complete root import.
# Optional writable copy: --lean --project /tmp/gsqg-check [GSQG.<Module> ...]
set -euo pipefail
cd "$(dirname "$0")/../.."
case "${1:-}" in
  --lean) shift; exec python3 blueprint/tools/collect_status.py "$@" ;;
  --source) shift; exec python3 blueprint/tools/collect_status.py --source "$@" ;;
  "") exec python3 blueprint/tools/collect_status.py --source ;;
  *) echo "Usage: $0 [--source | --lean [--project DIR] [MODULE ...]]" >&2; exit 2 ;;
esac
