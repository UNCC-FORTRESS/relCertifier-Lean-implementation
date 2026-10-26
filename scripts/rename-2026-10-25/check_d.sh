#!/bin/zsh
# (c)+(d): exes build, then every README step-2..5 check; one log per step under $L/d/.
cd "$(dirname $0)/../.."
L=${1:-/tmp/rename-checks}
mkdir -p $L
lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts > $L/exes.log 2>&1; echo "exes exit $?"
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt > $L/quick.log 2>&1; echo "quick exit $?"
for d in benchmarks/suite_v2/*/; do
  printf '%s\t%s\n' "$(basename "$d")" "$PWD/${d}input.txt"
done > /tmp/bench-paths-v2.tsv
BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test > $L/test.log 2>&1; echo "test exit $?"
./.lake/build/bin/relcert-bridge-verdicts > $L/bridge.log 2>&1; echo "bridge exit $?"
./.lake/build/bin/relcert-refute-verdicts > $L/refute.log 2>&1; echo "refute exit $?"
lake build $(ls RelCertifier/InstancesV2/Refute/*.lean | sed 's|/|.|g; s|\.lean$||') > $L/refute_build.log 2>&1; echo "refute build exit $?"
./.lake/build/bin/relcert-progress-verdicts > $L/progress.log 2>&1; echo "progress exit $?"
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms" > $L/battery.log; echo "battery done"
lake build RelCertifier.InstancesV2.AxiomCheck 2>&1 | grep -A3 "depends on axioms" > $L/axiomcheck.log; echo "axiomcheck done"
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt > $L/negative.log 2>&1; echo "negative exit $?"
