/-
# Uniform evolution domains — junction trivial, staying-only H, margin discharge

The proof-side deployment of the UNIFORM-EVOL + SETTLING design (demonstrated on the modified
benchmark suite: shared evolution domain strictly wider than every guard, guard-enforced settling
with margin > max-rate·dt):

* `UniformEvol` — all modes share ONE evolution domain `evolShared`. The junction obligation
  (segment endpoint satisfies the successor's domain) is then TRIVIAL: successor's domain = the
  shared domain = where the staying clause already put the endpoint. The narrowing machinery
  (`SuccReach`/`SuccReachB`/`starStep_narrowing`) is NOT referenced on this path — retired.
* `UniformStayingH` — the cleaned, staying-only well-formedness: junction content GONE (no
  `LandingH` field, no reaching), one shared domain everywhere. `LandingWellFormed_of_uniform`
  derives the shipped bundle from it (the `LandingH` field is discharged by `Or.inl` — under the
  landing dispatch the endpoint is in the CURRENT mode's domain, which under uniform-evol is
  every successor's domain too).
* `theorem3_faithful_landing_clocked_uniform` — the shipped `rvalid` theorem re-pointed onto
  `UniformEvol + UniformStayingH`. Non-breaking: a thin wrapper over
  `theorem3_faithful_landing_clocked_wf`; the per-mode-domain path is untouched and remains the
  general special case.
* `staying_from_margin` — GATE (a): the settling-guard margin discharges boundary-unreachability.
  Any flow whose tracked coordinate starts at `≤ cap` (the guard cap) with derivative bounded by
  `r` stays `≤ cap + r·dt ≤ hi` on a `≤ dt` segment — geometric (mean value), not asserted.
* `WellFormedFlowB_contract` — the ∀-base discharge for the STABILIZING class: a contractive
  coordinate (`v' = k(c − v)`, equilibrium `c` INSIDE the shared band) makes the band forward-
  invariant, so the staying clause of `WellFormedFlowB` holds from EVERY base — the H is
  DISCHARGED BY CONSTRUCTION, with the explicit exponential witness (generalizing `decay_stays`).

HONEST SCOPE. This deployment certifies well-designed SETTLING systems: all modes share one
physical envelope, and the dynamics/guards keep the flow off the envelope boundary. The staying
H is DISCHARGED here for the single-coordinate stabilizing shape (equilibrium interior —
`WellFormedFlowB_contract`); the margin lemma (`staying_from_margin`) is proven for the
guard-capped growing shape, but consuming it in the star invariant requires guard-region-restricted
bases (the guard-threaded invariant), which is scoped, not landed — those benchmarks CARRY the H.
Non-settling / per-mode-domain systems remain on the shipped `LandingWellFormed` path unchanged.
-/
import RelCertifier.MultisegLandingBridge

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-! ## The uniform-evol constraint and the staying-only H -/

/-- All modes share ONE evolution domain (the uniform-evol design: `evolShared` is the physical
envelope, strictly wider than every guard, checked benchmark-side). -/
def UniformEvol (G : SearchGraph (Var n)) (evolShared : Formula (Var n)) : Prop :=
  ∀ q m, G.modeAt q = some m → m.dom = evolShared

/-- **The cleaned, staying-only well-formedness.** Junction content GONE: no `LandingH`
membership field (trivial under uniform-evol), no per-mode domain, no reaching. What remains:
bounded-`dt` staying over the ONE shared domain, the `g`-certificate over it, and the structural
plumbing (freshness, edges). This is what a settling benchmark discharges. -/
def UniformStayingH (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n)) (lam : Term (Var n))
    (tg : Var n) (dt : ℝ) (fL : Fin n → Term (Var n)) (evolShared : Formula (Var n)) : Prop :=
  0 ≤ dt ∧ mv ∉ g.fv ∧ mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound ∧ mv ≠ tg ∧
  mv ∉ evolShared.fv ∧ tg ∉ evolShared.fv ∧
  (∀ x ∈ evolShared.fv, x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound) ∧
  (∀ q m, G.modeAt q = some m → ∃ fR : Fin n → Term (Var n),
    m.sys = rightBlock fR lam ∧ q < G.modes.length ∧
    WellFormedFlowB fR lam evolShared dt ∧
    (∀ ν, Formula.sat evolShared ν →
      BoxLe (Program.ode (rightBlock fR lam) evolShared) (fun ω => Term.eval g ω) ν) ∧
    (∃ e ∈ G.edgesFrom q, e.tgt = q ∧ e.guard = Formula.tt) ∧
    (∀ q', q' ∈ G.retainedSucc q →
      ∃ e ∈ G.edgesFrom q, e.tgt = q' ∧ e.guard = Formula.tt ∧ e.tgt < G.modes.length))

/-- **The decoupling + junction trivialization.** Under `UniformEvol`, the staying-only H derives
the shipped `LandingWellFormed` bundle: the `LandingH` junction field is discharged by `Or.inl`
(the endpoint is in the current mode's domain — which under uniform-evol IS every mode's domain,
so the membership disjunction is immediate: `subset_refl` in spirit), and every per-mode domain
field is rewritten to `evolShared`. No `SuccReach`, no reaching, no narrowing machinery. -/
theorem LandingWellFormed_of_uniform (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (lam : Term (Var n)) (tg : Var n) (dt : ℝ) (fL : Fin n → Term (Var n))
    (domL evolShared : Formula (Var n))
    (hU : UniformEvol G evolShared)
    (h : UniformStayingH G mv g lam tg dt fL evolShared) :
    LandingWellFormed G mv g lam tg dt fL domL := by
  obtain ⟨hdt, hg, hmvclk, hmvtg, hmvE, htgE, hfrz, hmodes⟩ := h
  refine ⟨hdt, ?_, hg, hmvclk, hmvtg, ?_, ?_⟩
  · -- LandingH: the current-mode disjunct is immediate (junction trivial)
    intro q m _ μ hμ
    exact Or.inl hμ
  · -- mv-freshness for every mode's domain = freshness for the ONE shared domain
    intro q' m' hm'
    rw [hU q' m' hm']
    exact hmvE
  · -- per-mode bundle: the shared domain instantiates every domR field
    intro q m hm
    obtain ⟨fR, hsys, hqlen, hwff, hgbox, hself, hsucc⟩ := hmodes q m hm
    exact ⟨fR, evolShared, hsys, hU q m hm, hqlen, htgE, hwff, hgbox, hfrz, hself, hsucc⟩

/-- **The re-pointed shipped theorem.** `rvalid (theorem3Form …)` from `UniformEvol` + the
staying-only `UniformStayingH` — the junction is trivial, the narrowing machinery retired.
Thin wrapper over `theorem3_faithful_landing_clocked_wf` (non-breaking: the per-mode-domain
path is untouched; this is its uniform-evol instantiation). -/
theorem theorem3_faithful_landing_clocked_uniform (G : SearchGraph (Var n)) (mv : Var n)
    (g : Term (Var n)) (fL : Fin n → Term (Var n)) (domL evolShared : Formula (Var n))
    (tg : Var n) (dt : ℝ) (k : ℕ) (lam : Term (Var n)) (ϕinv : RFormula (Var n))
    (hψ : encode (Equiv.refl (Var n)) ϕinv = invLe g)
    (hU : UniformEvol G evolShared)
    (hH : UniformStayingH G mv g lam tg dt fL evolShared)
    (htgb : tg ∉ (leftBlock fL).bound) (htgr : tg ∉ (leftBlock fL).readVars)
    (htgϕ : tg ∉ domL.fv)
    (htgR : tg ∉ ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))).fv)
    (htgφ : tg ∉ (starInvF G mv g).fv)
    (hdis : Disjoint (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg (leftBlock fL) domL tg dt)))
    (hdMULTI : Disjoint (Program.vars (Program.ode (leftBlock fL) domL))
        (Program.vars ((rightAutomatonBody G mv).rename (Equiv.refl (Var n)))))
    (hbudgetAll : ∀ (σ' : State (Var n)), ∀ {r : ℝ} {Φ : ℝ → State (Var n)},
        ODESol (leftBlock fL) domL σ' r Φ → r ≤ (k : ℝ) * dt)
    (hddF : Disjoint (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (Program.ode (leftBlock fL) domL))
          (Program.star (rightAutomatonBody G mv)) (ψpostL G mv ϕinv)).varsR)) :
    RFormula.rvalid (theorem3Form (Program.ode (leftBlock fL) domL)
      (rightAutomatonBody G mv) (ψpostL G mv ϕinv)) :=
  theorem3_faithful_landing_clocked_wf G mv g fL domL tg dt k lam ϕinv hψ
    (LandingWellFormed_of_uniform G mv g lam tg dt fL domL evolShared hU hH)
    htgb htgr htgϕ htgR htgφ hdis hdMULTI hbudgetAll hddF

/-! ## GATE (a) — staying from the settling-guard margin

The settling design enforces: growing modes' guards fire at `cap`, with margin `hi − cap`
exceeding the worst-case one-step travel `r·dt`. The lemma: from any base at `≤ cap`, the
boundary `hi` is UNREACHABLE within one `≤ dt` segment — a mean-value argument, not an
assertion. This is the per-coordinate geometric content the certifier-verified benchmark
discipline (margin > max-rate·dt) supplies. -/

/-- **Staying from margin (GATE a).** A scalar flow `f` on `[0,s] ⊆ [0,dt]` with derivative
bounded by `r`, starting at `f 0 ≤ cap`, stays `≤ hi` whenever the margin covers the worst-case
travel: `cap + r·dt ≤ hi`. Mean value (`norm_image_sub_le_of_norm_hasDerivWithin_le`). -/
theorem staying_from_margin (cap r hi dt s : ℝ) (f d : ℝ → ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hsdt : s ≤ dt)
    (hmargin : cap + r * dt ≤ hi) (hbase : f 0 ≤ cap)
    (hder : ∀ t ∈ Icc (0 : ℝ) s, HasDerivWithinAt f (d t) (Icc 0 s) t)
    (hdb : ∀ t ∈ Icc (0 : ℝ) s, |d t| ≤ r) :
    ∀ t ∈ Icc (0 : ℝ) s, f t ≤ hi := by
  intro t ht
  have hconv : Convex ℝ (Icc (0 : ℝ) s) := convex_Icc 0 s
  have key := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hder
      (fun u hu => by simpa [Real.norm_eq_abs] using hdb u hu)
      (left_mem_Icc.mpr hs) ht
  have habs : |f t - f 0| ≤ r * t := by
    have hnorm : ‖f t - f 0‖ ≤ r * ‖t - 0‖ := key
    simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using hnorm
  have h1 : f t - f 0 ≤ r * t := le_trans (le_abs_self _) habs
  have hrt : r * t ≤ r * dt := mul_le_mul_of_nonneg_left (ht.2.trans hsdt) hr
  linarith

/-! ## The ∀-base discharge for the stabilizing class

For a CONTRACTIVE coordinate (`v' = k(c − v)`, `k ≥ 0`) whose equilibrium `c` lies INSIDE the
shared band `[lo, hi]`, the band is forward-INVARIANT: the exponential flow
`v(t) = c + (v₀ − c)·e^{−kt}` stays between `v₀` and `c` for all `t ≥ 0`. So the staying clause
holds from EVERY base in the band — `WellFormedFlowB` is DISCHARGED BY CONSTRUCTION, ∀-base, no
guard restriction needed. This generalizes `decay_stays` (`k = 1, c = 0`) with the explicit
witness. -/

/-- Contractive field on coordinate `Rv j`: `v' = k(c − v)`, all other coordinates frozen. -/
noncomputable def contractF (j : Fin n) (k c : ℝ) : Fin n → Term (Var n) :=
  fun i => if i = j then
    Term.binop AOp.mul (Term.const k)
      (Term.binop AOp.sub (Term.const c) (Term.var (Rv j)))
  else Term.const 0

/-- The shared band `lo ≤ v ≤ hi` on coordinate `Rv j` (the uniform evolution domain). -/
noncomputable def bandDom (j : Fin n) (lo hi : ℝ) : Formula (Var n) :=
  Formula.and (Formula.cmp CompOp.le (Term.const lo) (Term.var (Rv j)))
              (Formula.cmp CompOp.le (Term.var (Rv j)) (Term.const hi))

/-- The explicit contractive solution `v(t) = c + (v₀ − c)·e^{−kt}`, other coordinates frozen. -/
noncomputable def contractΦ (j : Fin n) (k c : ℝ) (base : State (Var n)) (t : ℝ) :
    State (Var n) :=
  fun x => if x = Rv j then c + (base (Rv j) - c) * Real.exp (-(k * t)) else base x

@[simp] theorem contractΦ_Rvj (j : Fin n) (k c : ℝ) (base : State (Var n)) (t : ℝ) :
    contractΦ j k c base t (Rv j) = c + (base (Rv j) - c) * Real.exp (-(k * t)) := by
  simp [contractΦ]

theorem contractΦ_other (j : Fin n) (k c : ℝ) (base : State (Var n)) (t : ℝ)
    {x : Var n} (hx : x ≠ Rv j) : contractΦ j k c base t x = base x := by
  simp [contractΦ, hx]

/-- The contractive solution's tracked coordinate solves `v' = k(c − v)`. -/
theorem contractΦ_hasDeriv (j : Fin n) (k c : ℝ) (base : State (Var n)) (t : ℝ) :
    HasDerivAt (fun u => contractΦ j k c base u (Rv j))
      (k * (c - contractΦ j k c base t (Rv j))) t := by
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(k * u))) (-k * Real.exp (-(k * t))) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(k * u)) (-k) t := by
      have h := (hasDerivAt_id t).const_mul (-k)
      simp only [id, mul_one, neg_mul] at h
      exact h
    have h := (Real.hasDerivAt_exp (-(k * t))).comp t hinner
    simp only [Function.comp_def] at h
    rw [mul_comm (Real.exp (-(k * t))) (-k)] at h
    exact h
  have h1 : HasDerivAt (fun u => c + (base (Rv j) - c) * Real.exp (-(k * u)))
      ((base (Rv j) - c) * (-k * Real.exp (-(k * t)))) t :=
    (hexp.const_mul (base (Rv j) - c)).const_add c
  have heq : (base (Rv j) - c) * (-k * Real.exp (-(k * t)))
      = k * (c - (c + (base (Rv j) - c) * Real.exp (-(k * t)))) := by ring
  simpa only [contractΦ_Rvj, heq] using h1

/-- **The ∀-base staying (band forward-invariance).** From ANY base in the band, with the
equilibrium interior (`lo ≤ c ≤ hi`), the contractive flow stays in the band for ALL `t ≥ 0`:
`v(t)` is a convex combination of `v₀` and `c` (both in the band). -/
theorem contract_stays (j : Fin n) (k c lo hi : ℝ) (hk : 0 ≤ k) (hcl : lo ≤ c) (hch : c ≤ hi)
    (base : State (Var n)) (hb : Formula.sat (bandDom j lo hi) base)
    (t : ℝ) (ht : 0 ≤ t) :
    Formula.sat (bandDom j lo hi) (contractΦ j k c base t) := by
  have hblo : lo ≤ base (Rv j) := by
    simpa [bandDom, Formula.sat, CompOp.interp, Term.eval] using hb.1
  have hbhi : base (Rv j) ≤ hi := by
    simpa [bandDom, Formula.sat, CompOp.interp, Term.eval] using hb.2
  have hθpos : 0 < Real.exp (-(k * t)) := Real.exp_pos _
  have hθle : Real.exp (-(k * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  set θ := Real.exp (-(k * t)) with hθ
  have hval : contractΦ j k c base t (Rv j) = c + (base (Rv j) - c) * θ := by
    simp [hθ]
  constructor
  · -- lo ≤ v(t)
    show Formula.sat _ _
    simp only [bandDom, Formula.sat, CompOp.interp, Term.eval] at *
    rw [contractΦ_Rvj]
    rcases le_or_gt c (base (Rv j)) with hbc | hbc
    · nlinarith
    · nlinarith
  · show Formula.sat _ _
    simp only [bandDom, Formula.sat, CompOp.interp, Term.eval] at *
    rw [contractΦ_Rvj]
    rcases le_or_gt c (base (Rv j)) with hbc | hbc
    · nlinarith
    · nlinarith

/-- **THE DISCHARGE (stabilizing class): `WellFormedFlowB` holds BY CONSTRUCTION** for a
contractive coordinate with interior equilibrium over the shared band, at stretch `λ = 1` —
∀ base, with the explicit exponential witness. The staying H is not carried for this class;
it is a consequence of the field shape + envelope geometry (equilibrium strictly inside the
uniform envelope — exactly the settling design the certifier verified benchmark-side). -/
theorem WellFormedFlowB_contract (j : Fin n) (k c lo hi dt : ℝ)
    (hk : 0 ≤ k) (hcl : lo ≤ c) (hch : c ≤ hi) :
    WellFormedFlowB (contractF j k c) (Term.const 1) (bandDom j lo hi) dt := by
  intro base hb s hs _
  refine ⟨contractΦ j k c base, ?_, ?_, ?_, ?_⟩
  · -- ΦR 0 = base
    funext x
    by_cases hx : x = Rv j
    · subst hx; simp [contractΦ]
    · exact contractΦ_other j k c base 0 hx
  · -- derivatives over rightBlock (contractF j k c) (const 1)
    intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange] at hp
    obtain ⟨i, -, rfl⟩ := hp
    by_cases hij : i = j
    · subst hij
      have hd := (contractΦ_hasDeriv i k c base t).hasDerivWithinAt (s := Icc 0 s)
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (contractF i k c i))
          (contractΦ i k c base t) = k * (c - contractΦ i k c base t (Rv i)) := by
        simp [contractF, Term.eval, AOp.interp]
      rw [heval]
      exact hd
    · -- frozen coordinate: field 0, curve constant
      have heval : Term.eval (Term.binop AOp.mul (Term.const 1) (contractF j k c i))
          (contractΦ j k c base t) = 0 := by
        simp [contractF, hij, Term.eval, AOp.interp]
      rw [heval]
      have hcurve : (fun u => contractΦ j k c base u (Rv i)) = fun _ => base (Rv i) := by
        funext u
        exact contractΦ_other j k c base u
          (fun hc => hij (by simpa [Rv, Prod.ext_iff] using hc))
      rw [hcurve]
      exact hasDerivWithinAt_const t _ _
  · -- mask: coordinates outside the right block's bound are frozen
    intro t ht x hx
    have hxj : x ≠ Rv j := by
      intro hc; subst hc
      exact hx (by
        simp only [rightBlock, ODESystem.bound, List.map_map]
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    exact contractΦ_other j k c base t hxj
  · -- staying: the band is forward-invariant (equilibrium interior)
    intro t ht
    exact contract_stays j k c lo hi hk hcl hch base hb t ht.1

end RelCertifier
