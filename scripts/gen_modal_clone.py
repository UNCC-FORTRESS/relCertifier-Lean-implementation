#!/usr/bin/env python3
"""Generate modal Theorem 3 instances for benchmarks whose RIGHT system is
byte-identical to a proven template's (same modes, guards, evolves, dynamics)
and whose LEFT window family has the same shape (same mode count, k = 1, λ = 1).
The instance then differs only in the benchmark identity: the IR it cites, the
namespace, and the final theorem name — the invariant enters through the opaque
lowering pipeline and needs no per-benchmark proof text.

Usage: gen_modal_clone.py <template.lean> <template_bench> <target_bench> <out.lean>
"""
import sys, re

tmpl, tb, nb, out = sys.argv[1:5]
s = open(tmpl).read()

def camel(b):
    return ''.join(w.capitalize() for w in b.split('_')) + 'Modal'

s = s.replace(f'import RelCertifier.Instances.BenchIR.{tb}',
              f'import RelCertifier.Instances.BenchIR.{nb}')
s = s.replace(f'namespace {camel(tb)}', f'namespace {camel(nb)}')
s = s.replace(f'end {camel(tb)}', f'end {camel(nb)}')
s = s.replace(f'{tb}_IR', f'{nb}_IR')
s = s.replace(f'{tb}_modal', f'{nb}_modal')
s = s.replace(f'`{tb}`', f'`{nb}`')
# header note
s = s.replace('# T3-3 GATE —', f'# T3-6 (GENERATED from {tb} — identical right system) —')
open(out, 'w').write(s)
print(f'{out} generated')
