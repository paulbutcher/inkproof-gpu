#!/usr/bin/env bash
# Prints the public API of Inkproof.Gpu, one line per declaration; CI compares it with API.lock.
# Regenerate with: scripts/api-lock.sh > API.lock
set -euo pipefail
cd "$(dirname "$0")/../test"
lake build InkproofGpu inkproof-tools/api-lock >&2
lake env "$(lake query inkproof-tools/api-lock 2>/dev/null)" Inkproof.Gpu
