# Conserved-certificate restatements (4 gain-attack benchmarks)

The 4 s-gap declines (`endurance_gain_M1`, `rover_terrain_M1`, `endurance_orderlift_1to2`,
`endurance_orderlift_2to3`) are **gain-attack / order-mismatch** models: the left system
gains faster, so the naive helper `v_L≤v_R` is *false* (`v_L(t)=0.3(1−e^{−3t}) >
v_R(t)=0.3(1−e^{−2t})`) — see `DIAGNOSIS.md`. But each has a **conserved quantity** `I`
(the left-null-vector of the gap dynamics, `İ ≡ 0` matched / `İ = T(1−λ) ≤ 0` stretched),
and `I ≤ I₀` is a genuine inductive invariant that implies a **finite, tight safety bound**
`s_L − s_R ≤ c`.

This is a **benchmark restatement to the inductive form** (state the certificate `I` + the
derived safety bound), **not** a certifier change and **not** a weakening: `c` is derived
from the velocity/accel domains (Z3-maximized, not fitted), every `c` is *smaller* than the
original stated bound, and the certifier proves the whole thing unchanged. The restated
inputs live in `benchmarks/restated/<name>/input.txt`.

The stated invariant is the conjunction `{ J ≤ J₀  ∧  s_L − s_R ≤ c }` where `J = k·I`
(integer-scaled so the parser lowers it; no fractions). `J ≤ J₀` flow-certifies (its Lie is
`≤ 0`, the conserved direction); `s_L − s_R ≤ c` follows from `J ≤ J₀` on the domain (the
implication below, and the certifier discharges it via the multi-barrier since `c` bounds
the region).

## Per benchmark

| benchmark | conserved `I` (scaled `J`) | `J ≤ J₀` | derived `c` | orig bound | implication (Z3) |
|---|---|---|---|---|---|
| endurance_gain_M1 | `6(s_L−s_R) + 2v_L − 3v_R` | `≤ 0` | **0.325** | 1.0 | UNSAT ✓ |
| rover_terrain_M1 | `6(s_L−s_R) + 2v_L − 3v_R` | `≤ 0` | **0.4** | 1.0 | UNSAT ✓ |
| endurance_orderlift_1to2 | `24(s_L−s_R) + 8v_L − 8v_R + a_L` | `≤ 0.6` | **17/80 = 0.2125** | 0.5 | UNSAT ✓ |
| endurance_orderlift_2to3 | `48(s_L−s_R) + 16v_L − 24v_R + 4a_L − 3a_R + j_L` | `≤ 1.9` | **197/480 ≈ 0.410** (stated 0.411) | 0.5 | UNSAT ✓ |

* **`İ ≤ 0`** — the conserved direction. E.g. endurance_gain: `v_L'=3(T−v_L)`,
  `v_R'=2(T−v_R)`, so `v_L'/3 − v_R'/2 = (T−v_L) − (T−v_R) = v_R − v_L`, cancelling `s_L'−s_R'
  = v_L − v_R` exactly (target `T` drops out — holds in every mode). Under λ-stretch,
  `İ = T(1−λ) ≤ 0`. The certifier sees `J̇ ≤ 0` and certifies `J ≤ J₀` via the domain/superlevel
  route.
* **`I₀ = J₀`** — supremum of `I` over the matched initial set (`s_L=s_R`, `v_L=v_R=v₀`, etc.),
  Z3-checked; a sound over-approximation.
* **`c`** — `max (s_L − s_R)` s.t. `J ≤ J₀ ∧ domain`, obtained by Z3 `(maximize)` — derived
  from the velocity/accel ranges, not fitted. The implication
  `J ≤ J₀ ∧ domain ⟹ s_L − s_R ≤ c` is the UNSAT of its negation (all four confirmed).

## Result

All 4 restated benchmarks **CERTIFIED** by the unchanged certifier. Every `c` is finite and
meaningfully tight (each below the original stated bound), so none is vacuous or fitted —
all 4 qualify. Parity: **41 → 45 CERTIFIED / 1 DECLINED / 0 ERROR**, deterministic. The lone
remaining decline, `rover3_M1`, needs budget-aware reachability (Strategy 2), out of scope.

Certifier untouched (no auto-synthesis): `#print axioms` on the core unchanged; the 4 are a
benchmark-input restatement to the inductive certificate + derived safety bound.
