#!/bin/zsh
# STALE (2026-07-30 audit): reads/writes the MONOLITHIC aggregator form that the X0
# modularization replaced with per-benchmark leaves. Running gen_covers.sh would
# OVERWRITE RelCertifier/Instances/BenchCovers.lean and destroy the 40-leaf layout.
# Repoint at the leaves before any use.
# Regenerate RelCertifier/Instances/BenchCovers.lean from the tool's cover search.
set -e
cd "$(dirname $0)/.."
lake build relcert > /dev/null
OUT=RelCertifier/Instances/BenchCovers.lean
cat > $OUT << 'HDR'
/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Tool-emitted covers (do not edit — `relcert --emit-cover`, drift-checked)

One `CoverEmitE` literal per certified benchmark: the search's successful cover
(λ, budget, certificate flags, admissible starts, strata orders, pruned edges).
Regenerate: `scripts/gen_covers.sh`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

HDR
for d in benchmarks/suite_uniform/*/; do
  b=$(basename $d)
  [ "$b" = "shield_unreachable" ] && continue
  echo "/-- \`$b\` (emitted). -/" >> $OUT
  ./.lake/build/bin/relcert --emit-cover $d/input.txt ${b}_cover >> $OUT
  echo "" >> $OUT
done
echo "end RelCertifier" >> $OUT
echo "regenerated $OUT"
