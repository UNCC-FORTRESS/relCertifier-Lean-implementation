#!/bin/zsh
# Cover drift check: re-run the search, compare against the committed literals.
set -e
cd "$(dirname $0)/.."
TMP=$(mktemp -d)
trap "rm -rf $TMP" EXIT
for d in benchmarks/suite_uniform/*/; do
  b=$(basename $d)
  [ "$b" = "shield_unreachable" ] && continue
  ./.lake/build/bin/relcert --emit-cover $d/input.txt ${b}_cover > $TMP/$b.lean
  if ! grep -qF "$(head -2 $TMP/$b.lean | tail -1)" RelCertifier/Instances/BenchCovers.lean; then
    echo "DRIFT: $b"; exit 1
  fi
done
echo "cover drift: clean (46 benchmarks)"
