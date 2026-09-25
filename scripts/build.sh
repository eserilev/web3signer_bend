#!/bin/sh
# Builds a Bend program that uses the foreign effects of src/ffi.bend.
#
#   scripts/build.sh <file.bend> <output binary>
#
# `bend x.bend -o bin` compiles in a temp dir with fixed flags, so it cannot
# find blst, OpenSSL or ICU. This script has Bend write the C file, then runs
# clang with Bend's own flags plus the include paths and libraries.
# Set BEND and CC to choose the tools.
set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
src=$1
out=$2
bend=${BEND:-bend}
cc=${CC:-clang}
blst="$root/build/blst"

if [ ! -f "$blst/libblst.a" ]; then
  mkdir -p "$blst"
  (cd "$blst" && CC="$cc" sh "$root/vendor/blst/build.sh" >/dev/null)
fi

mkdir -p "$(dirname "$out")"
BEND_NO_TELEMETRY=1 "$bend" "$src" -o "$out.c" >/dev/null
"$cc" -std=c11 -O3 -I "$root/vendor/blst/bindings" -I "$root/src/ffi" "$out.c" \
  "$blst/libblst.a" -lcrypto -licuuc -lpthread -lm -o "$out"
