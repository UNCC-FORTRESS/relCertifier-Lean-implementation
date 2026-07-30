"""λ/k assembly tail for multiF instances (single λ, single k, in-place dispatch)."""
import sys
sys.path.insert(0, '/private/tmp/claude-503/-Users-jxiang1-Develop/fcb60004-278e-482c-8a81-5509a4c43a3d/scratchpad')
from gen_multif import gen


def tail_lk(spec):
    S = spec['suf']; N = spec['n']; LAM = spec['lam']; K = spec['kw']
    NS = spec['ns']; THM = spec['thm']; BENCH = spec['bench']; ng = len(spec['gs'])
    P1 = "Program.ode (rightBlock (fR%s m) (Term.const 1)) domR%s" % (S, S)
    seglist = ", ".join(["(q, mode%s q, edge%s q q)" % (S, S)] * K)
    piecelist = ",\n        ".join([P1] * K)
    rfls = " | ".join(["rfl"] * K)
    rfl3 = " | ".join(["rfl"] * 3)
    rflg = " | ".join(["rfl"] * ng)
    if K == 1:
        chain = "  · simp"
    else:
        chain = "  · exact " + "".join(["(hstep _ _ _ rfl "] * (K - 1)) + "(by simp)" + ")" * (K - 1)
    resp = "\n".join(
        "    · have := respond%s %d q (by norm_num) hq3 dt hdt (hv %d q (by norm_num) hq3) hσ\n"
        "      simpa [mode%s] using this" % (S, i, i, S) for i in range(3))
    T = []
    A = T.append
    A("""
/-! ## The route verdicts (stratified-DC at the cover's λ) -/

def Verd{S} (l m : ℕ) : Prop :=
  ∀ i (hi : i < (g{S} :: gs{S}).length),
    z3solve (flowQuery ⟨(g{S} :: gs{S})[i], fL{S} l, fR{S} m, Term.const ({LAM}),
      strataDomHost (Formula.and domL{S} domR{S}) ((g{S} :: gs{S}).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(g{S} :: gs{S})[i], fL{S} l, fR{S} m, Term.const ({LAM}),
      strataDomHost (Formula.and domL{S} domR{S}) ((g{S} :: gs{S}).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(g{S} :: gs{S})[i], fL{S} l, fR{S} m, Term.const ({LAM}),
      strataDomHost (Formula.and domL{S} domR{S}) ((g{S} :: gs{S}).take i)⟩) = Verdict.unsat

/-! ## The coupling at λ, and its λ = 1 transport (L7) -/

theorem couple{S} (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : Verd{S} l m) :
    ∀ σ', Formula.sat (Formula.and (FM g{S} gs{S}) env{S}) σ' → σ' tg{S} = 0 →
      faModalB (Equiv.refl (Var {N}))
        (Program.ode (DLCalTiming.clk tg{S} (leftBlock (fL{S} l))) domL{S})
        (Program.ode (rightBlock (fR{S} m) (Term.const ({LAM}))) domR{S})
        (Formula.and (FM g{S} gs{S}) env{S}) tg{S} dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tg{S} (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tg{S}
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fL{S} l) (fR{S} m) (Term.const ({LAM}))
    (Formula.and domL{S} domR{S}) (g{S} :: gs{S}) hv
  have hboxes : ∀ g' ∈ g{S} :: gs{S}, Formula.sat (Formula.box (Program.ode
      (leftBlock (fL{S} l) ++ rightBlock (fR{S} m) (Term.const ({LAM})))
      (Formula.and domL{S} domR{S})) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' hg'
    intro g hg
    exact (sat_FM_iff g{S} gs{S} σ').mp hσ'.1 g hg
  have hbase := segment_faModalB_from_certB_list g{S} gs{S} (fL{S} l) (fR{S} m)
    (Term.const ({LAM})) domL{S} domR{S} tg{S} dt
    (LR_blocks_disjoint _ _ _ (hfL{S} l hl) (hfR{S} m hm) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomL{S} hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomR{S} hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL{S} l) _ h
      exact aux_ne_Lv a{S} i hi)
    (fun h => aux_notin_range_Lv a{S} (leftBlock_readVars_sub (fL{S} l) (hfL{S} l hl) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fR{S} m) (Term.const ({LAM})) _ h
      exact aux_ne_Rv a{S} i hi)
    (fun h => aux_notin_range_Rv a{S} (rightBlock_readVars_sub (fR{S} m)
      (Term.const ({LAM})) (hfR{S} m hm) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv a{S} (rightBlock_boundSet_sub (fR{S} m)
      (Term.const ({LAM})) h))
    (fun h => aux_notin_range_Lv a{S} (hdomL{S} h))
    (fun h => aux_notin_range_Rv a{S} (hdomR{S} h))
    htgg hboxes
    (es{S} l m hl hm dt hdt σ' hσ')
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domL{S} ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domR{S} μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domL{S} μ := by
    rwa [(Formula.coincidence domL{S} (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomL{S} hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fR{S} m) (Term.const ({LAM})) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domL{S} μ ↔ Formula.sat domL{S} ν)]
  exact ⟨hdomLμ, hdomRμ⟩

theorem couple1{S} (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : Verd{S} l m) :
    ∀ σ, Formula.sat (Formula.and (FM g{S} gs{S}) env{S}) σ →
      faModalB (Equiv.refl (Var {N}))
        (Program.ode (DLCalTiming.clk tg{S} (leftBlock (fL{S} l))) domL{S})
        ({P1}) (Formula.and (FM g{S} gs{S}) env{S}) tg{S} dt
        (Function.update σ tg{S} 0) := by
  intro σ hσ
  have htgφ : tg{S} ∉ (Formula.and (FM g{S} gs{S}) env{S}).fv := by
    intro h
    rcases h with h | h
    · exact htgF{S} h
    · exact htgenv{S} h
  have hupdφ : Formula.sat (Formula.and (FM g{S} gs{S}) env{S})
      (Function.update σ tg{S} 0) := by
    rwa [(Formula.coincidence (Formula.and (FM g{S} gs{S}) env{S}) (fun v hv' =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv')) _ _) :
        Formula.sat (Formula.and (FM g{S} gs{S}) env{S}) _ ↔ _)]
  refine faModalB_monoQ ?_ (couple{S} l m hl hm dt hdt hv
    (Function.update σ tg{S} 0) hupdφ (Function.update_self _ _ _))
  intro ν μ hsem
  exact sem_rightBlock_reparam ({LAM}) 1 (by norm_num) one_pos hsem

/-! ## The window response ({K} pieces at the in-place mode) -/

theorem respond{S} (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : Verd{S} l m) {{σ : State (Var {N})}}
    (hσ : Formula.sat (Formula.and (FM g{S} gs{S}) env{S}) σ) :
    Formula.sat (faModal (Equiv.refl (Var {N}))
      (windowSeg (leftBlock (fL{S} l)) domL{S} tg{S} dt {K})
      (bigSeq [{piecelist}])
      (Formula.and (FM g{S} gs{S}) env{S})) σ := by
  have hfa := Hmulti_windowRF_prefixed (fL{S} l) domL{S} (FM g{S} gs{S}) env{S}
    a{S} dt {K} htgF{S} htgenv{S} [] (by simp) (fun σ' hσ' => hσ'.2.1) (by simp)
    (hfL{S} l hl) hdomL{S}
    (List.replicate {K} ({P1})) (by simp) (by norm_num)
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ, Program.rename_refl]
      exact hdisH_progR (⟨fR{S} m, Term.const 1, domR{S}⟩ : RepoHop {N})
        (hfR{S} m hm) (by simp [Term.fv]) hdomR{S} (hfL{S} l hl) hdomL{S})
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact couple1{S} l m hl hm dt hdt hv σ' hσ')
    hσ
  simpa [List.replicate] using hfa

/-! ## The step provider — every window certifies every mode, so the response
stays in place -/

theorem Hmulti{S} (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : ∀ l m : ℕ, l < 3 → m < 3 → Verd{S} l m) :
    ∀ P ∈ leftProgs{S} dt, ∀ (q : ℕ), q < Gr{S}.modes.length → ∀ σ, σ mv{S} = (q : ℝ) →
      Formula.sat (Formula.and (FM g{S} gs{S}) env{S}) σ →
      ∃ segs : List (ℕ × RMode (Var {N}) × REdge (Var {N})),
        (∀ s ∈ segs, Gr{S}.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr{S}.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var {N})) P
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FM g{S} gs{S}) env{S})) σ := by
  intro P hP q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [Gr{S}] using hq
  have hself : Gr{S}.modeAt q = some (mode{S} q) ∧ edge{S} q q ∈ Gr{S}.edgesFrom q := by
    refine ⟨Gr{S}_modeAt q hq3, edge{S}_mem q q ?_⟩
    interval_cases q <;> simp [Gr{S}]
  have hstep : ∀ (a b : ℕ × RMode (Var {N}) × REdge (Var {N})) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var {N}) × REdge (Var {N})) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  simp only [leftProgs{S}, leftData{S}, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  refine ⟨[{seglist}], ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with {rfls} <;> exact hself
{chain}
  · exact fun s hs => by rw [hhead1 _ _ _ hs]
  · rcases hP with {rfl3}
{resp}

/-- **`{BENCH}`, modal Theorem 3** (λ = {LAM}, k = {K}). -/
theorem {THM} (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : ∀ l m : ℕ, l < 3 → m < 3 → Verd{S} l m) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs{S} dt))
      (rightAutomatonBody Gr{S} mv{S})
      (RFormula.and (RFormula.and (canonInvM g{S} gs{S}) (envLR domL{S} domR{S}))
        (mvValidR mv{S} Gr{S}.modes.length))) := by
  refine theorem3_faithful_multiF_LR Gr{S} mv{S} (FM g{S} gs{S}) domL{S} domR{S}
    (leftProgs{S} dt) (canonInvM g{S} gs{S}) (encode_canonInvM g{S} gs{S}) ?_ ?_ ?_
  · exact hdis_multi Gr{S} 0 1 dt leftData{S} (by decide) htt{S} hRv{S} hL{S}
  · exact hstep_assembled_multiF Gr{S} mv{S} (FM g{S} gs{S}) env{S} (leftProgs{S} dt)
      hmvF{S} hmvenv{S} hfresh{S} htt{S} hlt{S} (hframes{S} dt)
      (Hmulti{S} dt hdt hv)
  · exact hddF_multiE Gr{S} 0 1 dt leftData{S} (canonInvM g{S} gs{S}) domL{S} domR{S}
      (by decide) htt{S} hRv{S} hL{S}
      (canonInvM_varsL g{S} gs{S} (by
        intro g' hg'
        simp only [g{S}, gs{S}, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with {rflg} <;> exact hgAt _))
      (canonInvM_varsR g{S} gs{S}) hdomL{S} hdomR{S}

end {NS}
end RelCertifier
""".format(S=S, N=N, LAM=LAM, K=K, NS=NS, THM=THM, BENCH=BENCH, P1=P1,
           piecelist=piecelist, seglist=seglist, rfls=rfls, rfl3=rfl3, rflg=rflg,
           chain=chain, resp=resp))
    return "".join(T)


def gen_lk(spec):
    spec = dict(spec)
    spec['no_tail'] = True
    body = gen(spec)
    body = body.replace("import RelCertifier.Proofs.Encoding.RepoPrefixR",
        "import RelCertifier.Proofs.Encoding.RepoPrefixR\n"
        "import RelCertifier.Proofs.Encoding.Reparam\n"
        "import RelCertifier.Proofs.Encoding.WindowRF")
    return body + tail_lk(spec)
