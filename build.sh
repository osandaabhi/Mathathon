#!/usr/bin/env bash
# Build the T5 formalization.  Lean 4 + a prebuilt Mathlib must be on PATH;
# LEAN_PATH already points at Mathlib's oleans in this VM.
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD:${LEAN_PATH}"
mods=("$@")
if [ ${#mods[@]} -eq 0 ]; then mods=(Basic Moments Convex NodeBounds Constants PsiConvex TangentData Jm32 ChordData Main); fi
for m in "${mods[@]}"; do
  echo "== checking MathathonT5/$m.lean"
  lean -o "MathathonT5/$m.olean" "MathathonT5/$m.lean"
done
echo "== all modules checked"
