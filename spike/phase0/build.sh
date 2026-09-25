#!/bin/sh
# Builds the phase 0 spike. Bend emits C, then clang links it with blst.
#
# `bend x.bend -o bin` compiles in a temp dir with fixed flags, so it cannot
# find blst. `bend x.bend -o x.c` writes the C file here instead, and this
# script adds the blst include path and library to Bend's own flags.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
out="$root/build/phase0"
blst="$root/build/blst"
bend=${BEND:-bend}
cc=${CC:-clang}

if [ ! -f "$blst/libblst.a" ]; then
  mkdir -p "$blst"
  (cd "$blst" && CC="$cc" sh "$root/vendor/blst/build.sh")
fi

mkdir -p "$out"
BEND_NO_TELEMETRY=1 "$bend" "$here/main.bend" -o "$out/sign.c"
"$cc" -std=c11 -O3 -I "$root/vendor/blst/bindings" "$out/sign.c" \
  "$blst/libblst.a" -lpthread -lm -o "$out/sign"
echo "built $out/sign"
