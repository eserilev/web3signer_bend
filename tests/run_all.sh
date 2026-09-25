#!/bin/sh
# Builds each test binary and runs each test suite.
#
#   tests/run_all.sh <consensus-spec-tests/tests dir>
#
# Set BEND to the bend binary if it is not on PATH, and LIGHTHOUSE to a
# Lighthouse checkout if it is not at ../lighthouse.
set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
vectors=${1:?usage: tests/run_all.sh <consensus-spec-tests/tests dir>}
bend=${BEND:-bend}
export BEND_NO_TELEMETRY=1

mkdir -p "$root/build/tests"
for name in ssz_cli laws_cli json_cli request_cli store_cli; do
  "$bend" "$root/tests/$name.bend" -o "$root/build/tests/$name" >/dev/null
done
# Programs with foreign effects need scripts/build.sh.
BEND="$bend" "$root/scripts/build.sh" "$root/tests/keys_cli.bend" "$root/build/tests/keys_cli"
BEND="$bend" "$root/scripts/build.sh" "$root/main.bend" "$root/build/bulkhead"
BEND="$bend" "$root/spike/phase0/build.sh" >/dev/null

echo "== ssz";      "$root/tests/run_ssz.py" "$vectors"
echo "== laws";     "$root/tests/run_laws.py" 2000
echo "== json";     "$root/tests/run_json.py"
echo "== requests"; "$root/tests/run_requests.py"
echo "== store";    "$root/tests/run_store.py" 2000
echo "== keys";     "$root/tests/run_keys.py" "${LIGHTHOUSE:-$root/../lighthouse}"
echo "== server";   "$root/tests/run_server.py"
echo "== proofs"
"$bend" "$root/PROOF.bend" 2>&1 | head -1 || true
