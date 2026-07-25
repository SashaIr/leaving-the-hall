import RequestProject.Psi.Area

namespace Psi

/-! ### Rise-composition (`lem:comp`): algebra of `muVec` and geometry of `cc`/`northRuns`

The proof of `phi_riseComp` follows the same recursion as `phi_area`.  On the
algebra side, `tauOf_descent` gives
`τ = (c+h) :: (τ' .map (·+c))` with `c = a+1+b`, and `muVec_tauOf_descent` turns
this into `μ(τ) = (c+h) :: muVecAux τ' h`.  On the geometry side the reconstructed
path contracts (`cc`) to `U^{a+1+b+h}` followed by `cc ρ'`, so
`northRuns (cc Φ) = (c+h) :: northRuns (cc ρ')`; and `riseComp_split` shows
`northRuns (cc ρ') = ppart(g₀-h) ++ (northRuns (cc π')).tail`.  The two tails are
matched through the induction hypothesis and `muVecAux_head_shift`. -/

/-- The one–element (or empty) list `[n]` if `n > 0`, else `[]`; this is the
shape of each `if`-branch in `muVecAux`/`northRunsAux`. -/
def ppart (n : ℕ) : List ℕ := if n > 0 then [n] else []

/-- Number of leading North (`true`) steps. -/
def leadN : List Bool → ℕ
  | true :: r => leadN r + 1
  | _ => 0

/-- Drop the leading North run and the single East step that terminates it. -/
def afterLeadRun : List Bool → List Bool
  | true :: r => afterLeadRun r
  | false :: r => r
  | [] => []

theorem muVecAux_map_add (M : List ℕ) (q c : ℕ) :
    muVecAux (M.map (· + c)) (q + c) = muVecAux M q := by
  induction M generalizing q with
  | nil => simp [muVecAux]
  | cons x xs ih =>
    simp only [List.map_cons, muVecAux]
    rw [show x + c - (q + c) = x - q from by omega, ih x]

theorem muVecAux_head_shift (L : List ℕ) (hpt : ℕ) (hL : 0 < L.headD 0) :
    muVecAux L hpt = ppart (L.headD 0 - hpt) ++ (muVec L).tail := by
  cases L with
  | nil => simp at hL
  | cons x xs =>
    simp only [List.headD_cons] at hL
    have hmv : muVec (x :: xs) = x :: muVecAux xs x := by
      simp only [muVec, muVecAux, Nat.sub_zero]; rw [if_pos hL, List.singleton_append]
    rw [hmv]
    simp [muVecAux, ppart]

theorem desComp_head_pos (word : List Bool) (hw : word ≠ []) :
    0 < (desComp word).headD 0 := by
  have gen : ∀ (word : List Bool) (cur : ℕ), word ≠ [] → 0 < (desCompAux word cur).headD 0 := by
    intro word
    induction word with
    | nil => intro cur h; exact absurd rfl h
    | cons a t iht =>
      intro cur _
      cases t with
      | nil => simp [desCompAux]
      | cons b rest =>
        simp only [desCompAux]
        split
        · simp
        · exact iht (cur + 1) (by simp)
  exact gen word 0 hw

theorem tauOf_head_pos (w : List Bool) (av : List ℕ) (hv : IsValid w av) :
    0 < (tauOf w av).headD 0 := by
  obtain ⟨hlen, -, -⟩ := hv
  obtain ⟨g0, gs, hg⟩ := List.exists_cons_of_ne_nil (desComp_ne_nil (false :: w))
  have hg0 : 0 < g0 := by
    have := desComp_head_pos (false :: w) (by simp)
    rw [hg] at this; simpa using this
  have hav : av ≠ [] := by
    intro h; subst h; rw [hg] at hlen; simp at hlen
  obtain ⟨a0, as, ha⟩ := List.exists_cons_of_ne_nil hav
  rw [tauOf, hg, deltaOf_cons, ha]
  simp only [List.zipWith_cons_cons, List.headD_cons]
  omega

theorem muVec_tauOf_descent {w : List Bool} (hnd : noDescent w = false) (ha : ℕ)
    (av' : List ℕ) :
    muVec (tauOf w (ha :: av'))
      = ((cLead0 w + 1 + cLead1 (w.drop (cLead0 w))) + ha)
        :: muVecAux (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av') ha := by
  rw [tauOf_descent hnd]
  simp only [muVec, muVecAux, Nat.sub_zero]
  rw [if_pos (by omega), List.singleton_append]
  congr 1
  rw [show cLead0 w + 1 + cLead1 (w.drop (cLead0 w)) + ha
        = ha + (cLead0 w + 1 + cLead1 (w.drop (cLead0 w))) from by omega, muVecAux_map_add]

theorem northRunsAux_split (J : List Bool) (c : ℕ) :
    northRunsAux J c = ppart (c + leadN J) ++ northRuns (afterLeadRun J) := by
  induction J generalizing c with
  | nil => simp [northRunsAux, leadN, afterLeadRun, northRuns, ppart]
  | cons a r ih =>
    cases a with
    | true => simp only [northRunsAux, leadN, afterLeadRun]; rw [ih (c + 1)]; congr 2; omega
    | false => simp only [northRunsAux, leadN, afterLeadRun, northRuns, ppart, add_zero]

theorem northRunsAux_replicate_true (n : ℕ) (X : List Bool) (c : ℕ) :
    northRunsAux (List.replicate n true ++ X) c = northRunsAux X (c + n) := by
  induction n generalizing c with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [northRunsAux]
    rw [ih (c + 1)]; congr 1; omega

theorem northRunsAux_pos (Y : List Bool) (c : ℕ) : ∀ x ∈ northRunsAux Y c, 0 < x := by
  induction Y generalizing c with
  | nil =>
    intro x hx; simp only [northRunsAux] at hx; split at hx <;> simp_all
  | cons a r ih =>
    cases a with
    | true => intro x hx; simp only [northRunsAux] at hx; exact ih (c + 1) x hx
    | false =>
      intro x hx; simp only [northRunsAux, List.mem_append] at hx
      rcases hx with h1 | h2
      · split at h1 <;> simp_all
      · exact ih 0 x h2

theorem northRunsAux_zero_eq (J : List Bool) (hpt : ℕ) :
    northRunsAux J 0
      = ppart ((northRunsAux J hpt).headD 0 - hpt) ++ (northRunsAux J hpt).tail := by
  rw [northRunsAux_split J 0, northRunsAux_split J hpt]
  rcases Nat.eq_zero_or_pos (hpt + leadN J) with h0 | hpos
  · have hh : hpt = 0 := by omega
    have hl : leadN J = 0 := by omega
    subst hh
    rw [hl]
    simp only [Nat.zero_add, ppart, Nat.lt_irrefl, if_false, List.nil_append, Nat.sub_zero]
    cases hBc : northRuns (afterLeadRun J) with
    | nil => simp
    | cons bb bs =>
      have hbpos : 0 < bb := by
        have hmem : bb ∈ northRuns (afterLeadRun J) := by rw [hBc]; simp
        exact northRunsAux_pos (afterLeadRun J) 0 bb hmem
      simp [hbpos]
  · have hpp : ppart (hpt + leadN J) = [hpt + leadN J] := by simp only [ppart, hpos, if_true]
    rw [hpp]
    simp only [List.headD_cons, List.cons_append, List.tail_cons]
    rw [show hpt + leadN J - hpt = leadN J from by omega, Nat.zero_add, List.nil_append]

theorem cc_append_replicate_true (n : ℕ) (X : List Bool) :
    cc (List.replicate n true ++ X) = List.replicate n true ++ cc X := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    show true :: cc (List.replicate m true ++ X) = List.replicate (m + 1) true ++ cc X
    rw [ih, List.replicate_succ, List.cons_append]

theorem cc_replicate_false (n : ℕ) : cc (List.replicate n false) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hstep : cc (List.replicate (m + 1) false) = false :: cc (List.replicate m false) := by
      cases m with
      | zero => rfl
      | succ p => rfl
    rw [hstep, ih, List.replicate_succ]

theorem cc_fUD_cons_true (a : ℕ) (q : List Bool) :
    cc (fUD a ++ true :: q) = List.replicate (a + 1) true ++ cc q := by
  induction a with
  | zero => simp [fUD, cc]
  | succ m ih =>
    rw [fUD_succ, List.append_assoc, List.cons_append]
    show true :: cc (false :: (fUD m ++ true :: q)) = List.replicate (m + 1 + 1) true ++ cc q
    have hcc : cc (false :: (fUD m ++ true :: q)) = cc (fUD m ++ true :: q) := by
      cases m with
      | zero => simp [fUD, cc]
      | succ p => rw [fUD_succ]; rfl
    rw [hcc, ih]
    conv_rhs => rw [List.replicate_succ, List.cons_append]

/-- Contracting `ρ ++ Z` when `ρ` has no `DD`: all of `ρ`'s East steps are
contracted, contributing `numN ρ` North steps; a trailing East step of `ρ` is
folded into `Z` as a leading `false`. -/
theorem cc_noDD_append_gen (rho Z : List Bool) (hrho : hasDD rho = false) :
    cc (rho ++ Z)
      = List.replicate (numN rho) true ++ (if stEast rho false then cc (false :: Z) else cc Z) := by
  induction rho with
  | nil => simp [numN, stEast]
  | cons a r ih =>
    cases a with
    | true =>
      have hr : hasDD r = false := by simpa [hasDD] using hrho
      have hnn : numN (true :: r) = numN r + 1 := by simp [numN]
      have hse : stEast (true :: r) false = stEast r false := by simp [stEast]
      rw [List.cons_append, cc, ih hr, hnn, hse, List.replicate_succ, List.cons_append]
    | false =>
      cases r with
      | nil =>
        have hnn : numN ([false] : List Bool) = 0 := by simp [numN]
        have hse : stEast ([false] : List Bool) false = true := by simp [stEast]
        rw [hnn, hse]
        simp only [List.replicate_zero, List.nil_append, if_true]
        rw [List.singleton_append]
      | cons b r' =>
        cases b with
        | false => simp [hasDD] at hrho
        | true =>
          have hr : hasDD (true :: r') = false := by simpa [hasDD] using hrho
          have hnn : numN (false :: true :: r') = numN (true :: r') := by
            simp [numN]
          have hse : stEast (false :: true :: r') false = stEast (true :: r') false := by
            simp [stEast]
          have hcc : cc (false :: true :: r' ++ Z) = cc ((true :: r') ++ Z) := rfl
          rw [hcc, hnn, hse, ih hr]

theorem northRuns_cc_cons_false (X : List Bool) :
    northRuns (cc (false :: X)) = northRuns (cc X) := by
  cases X with
  | nil => rfl
  | cons b xs =>
    cases b with
    | true => rfl
    | false =>
      show northRuns (false :: cc (false :: xs)) = northRuns (cc (false :: xs))
      simp [northRuns, northRunsAux]

theorem northRuns_cc_replicate_false (n : ℕ) (X : List Bool) :
    northRuns (cc (List.replicate n false ++ X)) = northRuns (cc X) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, northRuns_cc_cons_false, ih]

theorem northRuns_replicate_true_replicate_false (m n : ℕ) (hm : 0 < m) :
    northRuns (List.replicate m true ++ List.replicate n false) = [m] := by
  rw [northRuns, northRunsAux_replicate_true, Nat.zero_add]
  have htail : ∀ p : ℕ, northRunsAux (List.replicate p false) 0 = [] := by
    intro p; induction p with
    | zero => rfl
    | succ q ih =>
        rw [List.replicate_succ]
        simp only [northRunsAux, Nat.lt_irrefl, if_false, List.nil_append]
        exact ih
  cases n with
  | zero => simp only [List.replicate_zero]; simp [northRunsAux, hm]
  | succ p =>
    rw [List.replicate_succ]
    simp only [northRunsAux]
    rw [if_pos hm, htail p, List.append_nil]

/-- Contracting `ρ ++ Z` when `ρ` has no `DD` and `Z` starts with a North step:
every East step of `ρ` is contracted, leaving `numN ρ` North steps in front of
`cc Z`. -/
theorem cc_noDD_append_true (rho Z : List Bool) (hrho : hasDD rho = false)
    (hZ : Z.head? = some true) :
    cc (rho ++ Z) = List.replicate (numN rho) true ++ cc Z := by
  cases Z with
  | nil => simp at hZ
  | cons z zs =>
    cases z with
    | false => simp at hZ
    | true =>
      rw [cc_noDD_append_gen rho (true :: zs) hrho]
      have hif : (if stEast rho false then cc (false :: true :: zs) else cc (true :: zs))
          = cc (true :: zs) := by split <;> rfl
      rw [hif]

/-- Key geometric identity: the rise composition of `cc ρ'` is obtained from that
of `cc (ρ ++ ρ')` by cutting `numN ρ` off the first run. -/
theorem riseComp_split (rho rho' : List Bool) (hrho : hasDD rho = false) :
    northRuns (cc rho')
      = ppart ((northRuns (cc (rho ++ rho'))).headD 0 - numN rho)
        ++ (northRuns (cc (rho ++ rho'))).tail := by
  set T := (if stEast rho false then cc (false :: rho') else cc rho') with hT
  have h1 : northRuns (cc (rho ++ rho')) = northRunsAux T (numN rho) := by
    rw [northRuns, cc_noDD_append_gen rho rho' hrho, northRunsAux_replicate_true, Nat.zero_add,
      ← hT]
  have hTAIL : northRuns T = northRuns (cc rho') := by
    rw [hT]
    by_cases hs : stEast rho false = true
    · rw [if_pos hs, northRuns_cc_cons_false]
    · rw [if_neg hs]
  rw [h1, ← northRunsAux_zero_eq T (numN rho)]
  exact hTAIL.symm

/-- The head of `muVec L` is the head of `L` (when positive). -/
theorem muVec_headD (L : List ℕ) (hL : 0 < L.headD 0) :
    (muVec L).headD 0 = L.headD 0 := by
  cases L with
  | nil => simp at hL
  | cons x xs =>
    simp only [List.headD_cons] at hL
    have hmv : muVec (x :: xs) = x :: muVecAux xs x := by
      simp only [muVec, muVecAux, Nat.sub_zero]; rw [if_pos hL, List.singleton_append]
    rw [hmv]; simp

/-- Geometry of the reconstructed path: contracting and taking rise runs yields a
first run of length `a+1+b+h` followed by the runs of `cc ρ'`. -/
theorem riseComp_recon (a b hh : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false) (hnumN : numN rho = hh) :
    northRuns (cc ((List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho'))
      = (a + 1 + b + hh) :: northRuns (cc rho') := by
  set Z := List.replicate b true ++ List.replicate (b + 1) false ++ rho' with hZdef
  have hZhead : Z.head? = some true := by
    rw [hZdef]; cases b with | zero => omega | succ m => simp [List.replicate_succ]
  have hpath : (List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho'
      = fUD a ++ true :: (rho ++ Z) := by
    rw [hZdef, fUD]; simp [List.append_assoc]
  have hccZ : cc Z = List.replicate b true ++ cc (List.replicate (b + 1) false ++ rho') := by
    rw [hZdef, List.append_assoc, cc_append_replicate_true]
  have hcc2 : cc (List.replicate (b + 1) false ++ rho')
      = false :: cc (List.replicate b false ++ rho') := by
    obtain ⟨p, rfl⟩ : ∃ p, b = p + 1 := ⟨b - 1, by omega⟩
    rfl
  rw [hpath, cc_fUD_cons_true, cc_noDD_append_true rho Z hnoDD hZhead, hnumN, hccZ, hcc2,
    northRuns, northRunsAux_replicate_true, northRunsAux_replicate_true,
    northRunsAux_replicate_true]
  simp only [northRunsAux]
  rw [if_pos (by omega), List.singleton_append,
    show 0 + (a + 1) + hh + b = a + 1 + b + hh from by omega]
  congr 1
  rw [← northRuns, northRuns_cc_replicate_false]

/-- Rise-composition preservation (`lem:comp`): `μ(c(π)) = μ(τ)`. -/
theorem phi_riseComp (w : List Bool) (av : List ℕ) (h : IsValid w av) :
    northRuns (cc (phiPath w av)) = muVec (tauOf w av) := by
  revert h
  fun_induction phiPath w av with
  | case1 w av hnd =>
      intro hv
      have hnd' : noDescent w = true := by simpa using hnd
      -- base path `= fUD l ++ true :: (replicate k true ++ replicate (k+1) false)`
      set l := (w.filter (· = false)).length with hl
      set k := (w.filter id).length with hk
      have hlk : l + k = w.length := by rw [hl, hk]; exact len_filter_split w
      have hpath : (List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
            ++ List.replicate (k + 1) false
          = fUD l ++ true :: (List.replicate k true ++ List.replicate (k + 1) false) := by
        rw [fUD, List.replicate_succ]; simp [List.append_assoc]
      rw [hpath, cc_fUD_cons_true, cc_append_replicate_true, cc_replicate_false,
        ← List.append_assoc, ← List.replicate_add]
      rw [northRuns_replicate_true_replicate_false _ _ (by omega)]
      -- muVec side
      rw [tauOf, desComp_noDescent hnd']
      have hlen : av.length = 1 := by
        have := hv.1; rw [desComp_noDescent hnd'] at this; simpa using this
      obtain ⟨a0, rfl⟩ : ∃ a0, av = [a0] := by
        cases av with
        | nil => simp at hlen
        | cons x xs => cases xs with
          | nil => exact ⟨x, rfl⟩
          | cons _ _ => simp at hlen
      have ha0 : a0 = 0 := by
        have := hv.2.2
        rw [tauOf, desComp_noDescent hnd'] at this
        simp only [deltaOf, deltaAux, zero_add, List.zipWith_cons_cons, List.zipWith_nil_right,
          List.getLast?_singleton, Option.some.injEq] at this
        omega
      subst ha0
      simp only [deltaOf, deltaAux, zero_add, List.zipWith_cons_cons, List.zipWith_nil_right,
        add_zero, muVec, muVecAux, List.append_nil]
      have : 0 < w.length + 1 := by omega
      rw [if_pos (by omega)]
      congr 1
      omega
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      intro hv
      have hnd' : noDescent w = false := by simpa using hnd
      have ivt : IsValid w' av' := isValid_tail w av hv hnd'
      have hb : 1 ≤ b := (noDescent_false_decomp hnd').2
      have hpiD : IsDyck pi := phi_isDyck w' av'
      have hpine : pi ≠ [] := phiPath_ne_nil w' av'
      have happ : rho ++ rho' = pi := by
        have := splitAtRow_append pi hh; rw [hsplit] at this; simpa using this
      have hle := isValid_head_le w av hv hnd'
      have hnoDD : hasDD rho = false := by
        have := phi_split_noDD w' av' ivt hh hle
        rw [hsplit] at this; simpa using this
      have hbound : hh ≤ numN pi := le_trans hle (tau_headD_le_numN w' av' ivt)
      have hnumN : numN rho = hh := by
        have := split_numN pi hh hbound; rw [hsplit] at this; simpa using this
      rw [riseComp_recon a b hh rho rho' hb hnoDD hnumN]
      -- algebra of τ
      have hL : 0 < (tauOf w' av').headD 0 := tauOf_head_pos w' av' ivt
      have hIH : northRuns (cc pi) = muVec (tauOf w' av') := ihrec ivt
      have hav : av = hh :: av' := isValid_av_cons w av hv hnd'
      have hmu : muVec (tauOf w av) = (a + 1 + b + hh) :: muVecAux (tauOf w' av') hh := by
        rw [hav]; exact muVec_tauOf_descent hnd' hh av'
      rw [hmu]
      -- match the two `cons`es
      refine congrArg (List.cons _) ?_
      -- tail: `northRuns (cc rho') = muVecAux (tauOf w' av') hh`
      rw [muVecAux_head_shift (tauOf w' av') hh hL]
      have hsplitG := riseComp_split rho rho' hnoDD
      rw [happ, hIH, muVec_headD (tauOf w' av') hL, hnumN] at hsplitG
      rw [hsplitG]


end Psi
