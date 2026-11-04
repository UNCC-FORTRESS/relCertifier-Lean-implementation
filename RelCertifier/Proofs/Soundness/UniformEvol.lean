/-
# Uniform evolution domains: trivial junction, staying-only hypothesis, margin discharge

Lemmas for models whose right modes all share one evolution domain, the form every benchmark
declares (Appendix B.2, *Domains*):

* `UniformEvol`: all modes share one evolution domain `evolShared`. The junction obligation
  (a segment's endpoint satisfies the successor's domain) is then trivial: the successor's
  domain is the shared domain, where the staying clause already puts the endpoint. The
  narrowing machinery (`SuccReach`/`SuccReachB`/`starStep_narrowing`) is not used here.
* `UniformStayingH`: the staying-only well-formedness hypothesis over the shared domain (no
  `LandingH` field, no reaching). `LandingWellFormed_of_uniform` derives the
  `LandingWellFormed` bundle from it (its `LandingH` field holds by `Or.inl`: the endpoint is in
  the current mode's domain, which is every successor's domain).
* `theorem3_faithful_landing_clocked_uniform`: the `rvalid` statement of
  `theorem3_faithful_landing_clocked_wf` from `UniformEvol` and `UniformStayingH`, a thin
  wrapper; the per-mode-domain statement is unchanged.
* `staying_from_margin`: a scalar flow starting at `≤ cap` with derivative bounded by `r`
  stays `≤ cap + r·dt ≤ hi` on a segment of length `≤ dt` (mean value theorem).
* `WellFormedFlowB_contract`: for a contractive coordinate (`v' = k(c − v)`, equilibrium `c`
  inside the shared band) the band is forward invariant, so the staying clause of
  `WellFormedFlowB` holds from every base, with the explicit exponential witness
  (generalizing `decay_stays`).

Scope: the staying hypothesis is discharged here for the single-coordinate contractive shape
(`WellFormedFlowB_contract`). `staying_from_margin` covers the guard-capped growing shape, but
using it in the star invariant needs bases restricted to the guard region (the guard-threaded
invariant, `GuardThreaded.lean`); models outside both shapes carry the hypothesis.
-/
import RelCertifier.Proofs.Flow.MultisegLandingBridge

namespace RelCertifier
open DL DLCalTiming DLRel Function Set

variable {n : ℕ}

/-! ## The uniform-evol constraint and the staying-only hypothesis -/

/-- Every mode of `G` has the evolution domain `evolShared`: `G.modeAt q = some m → m.dom =
evolShared` (one evolution domain per system, Appendix B.2). -/
def UniformEvol (G : SearchGraph (Var n)) (evolShared : Formula (Var n)) : Prop :=
  ∀ q m, G.modeAt q = some m → m.dom = evolShared

/-- **Staying-only well-formedness over a shared domain.** `0 ≤ dt`, freshness of the mode
variable `mv` and the clock `tg`, and for every mode `q`: a right block `rightBlock fR lam`
with `WellFormedFlowB fR lam evolShared dt` (bounded-`dt` staying), the box `g ≤ 0` along
its flow from every state of `evolShared`, an unguarded self-edge, and an unguarded edge to
every retained successor. No `LandingH` field, no per-mode domain, no reaching. -/
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

/-- **Junction trivialization.** Under `UniformEvol`, `UniformStayingH` implies the
`LandingWellFormed` bundle: its `LandingH` junction field holds by `Or.inl` (the endpoint is in
the current mode's domain, which under `UniformEvol` is every mode's domain), and every per-mode
domain field is instantiated by `evolShared`. No `SuccReach`, no reaching. -/
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

/-- **The single-left-flow ∀∃ invariance under a shared domain.** `rvalid (theorem3Form …)`
for the left flow `leftBlock fL` under `domL`, the right automaton of `G`, and the
one-component invariant `g ≤ 0` (`hψ`), from `UniformEvol`, `UniformStayingH`, the left
budget `r ≤ k·dt` and the freshness and disjointness side conditions. A thin wrapper over
`theorem3_faithful_landing_clocked_wf` through `LandingWellFormed_of_uniform`. -/
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

/-! ## Staying from the settling-guard margin

In a settling model, a growing mode's guard fires at `cap`, with margin `hi − cap` exceeding
the worst-case one-step travel `r·dt`. From any base at `≤ cap`, the boundary `hi` is then
unreachable within one segment of length `≤ dt`, by the mean value theorem. -/

/-- **Staying from margin.** A scalar flow `f` on `[0,s] ⊆ [0,dt]` with derivative
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
shared band `[lo, hi]`, the band is forward invariant: the exponential flow
`v(t) = c + (v₀ − c)·e^{−kt}` stays between `v₀` and `c` for all `t ≥ 0`. So the staying clause
holds from every base in the band, and `WellFormedFlowB` holds with no guard restriction.
This generalizes `decay_stays` (`k = 1, c = 0`) with the explicit witness. -/

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

/-- **`WellFormedFlowB` for a contractive coordinate.** For the field `contractF j k c` with
`k ≥ 0` and equilibrium `lo ≤ c ≤ hi`, at rate `λ = 1`, `WellFormedFlowB` holds over the band
`lo ≤ v ≤ hi` from every base, with the explicit exponential witness: the staying hypothesis
is a consequence of the field shape and the equilibrium lying inside the band. -/
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
