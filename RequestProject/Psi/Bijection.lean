import RequestProject.Psi.Inverse

namespace Psi

/-! ### Well-definedness of `Ψ`

The remaining ingredient is that `Ψ` of a nonempty Dyck path is a valid datum.
We prove this together with a geometric identity for the first coordinate of the
height vector `τ = tauOf (Ψ π)`: `τ₁` equals the number of North steps of `π`
before its first `DD` (two consecutive East steps).  This identity is exactly
what couples the recursion: it converts the chain inequality needed to build
validity for `π` into the combinatorial fact `numN ρ ≤ numNBeforeDD (ρ ++ ρ')`. -/

/-- North steps in the maximal prefix free of `DD` (two consecutive East steps).
This equals the first coordinate `τ₁` of the height vector `tauOf (Ψ π)`. -/
def numNBeforeDD : List Bool → ℕ
  | [] => 0
  | true :: r => numNBeforeDD r + 1
  | false :: false :: _ => 0
  | false :: r => numNBeforeDD r

theorem numNBeforeDD_cons_true (r : List Bool) :
    numNBeforeDD (true :: r) = numNBeforeDD r + 1 := rfl

/-- A `DD`-free prefix `ρ` contributes all its North steps before the first `DD`
of `ρ ++ ρ'`. -/
theorem numN_le_numNBeforeDD_append (ρ ρ' : List Bool) (hρDD : hasDD ρ = false) :
    numN ρ ≤ numNBeforeDD (ρ ++ ρ') := by
  induction ρ with
  | nil => simp [numN]
  | cons x xs ih =>
    cases x with
    | true =>
      have hxs : hasDD xs = false := by rw [hasDD_cons] at hρDD; exact (Bool.or_eq_false_iff.mp hρDD).2
      simp only [List.cons_append, numNBeforeDD_cons_true, numN_cons_true]
      have := ih hxs; omega
    | false =>
      rw [numN_cons_false, List.cons_append]
      cases xs with
      | nil => simp [numN]
      | cons y ys =>
        cases y with
        | false => simp [hasDD] at hρDD
        | true =>
          have hxs : hasDD (true :: ys) = false := by
            rw [hasDD_cons] at hρDD; exact (Bool.or_eq_false_iff.mp hρDD).2
          show numN (true :: ys) ≤ numNBeforeDD (false :: true :: (ys ++ ρ'))
          have hrec : numNBeforeDD (false :: true :: (ys ++ ρ'))
              = numNBeforeDD (true :: (ys ++ ρ')) := rfl
          rw [hrec]
          have := ih hxs
          simpa using this

/-- If `s` is `DD`-free and the junction to `t` is not a `DD`, the `DD`-count of
`s ++ t` splits: all of `s` is traversed. -/
theorem numNBeforeDD_append (s t : List Bool) (hs : hasDD s = false)
    (hbnd : ¬ (s.getLast? = some false ∧ t.head? = some false)) :
    numNBeforeDD (s ++ t) = numN s + numNBeforeDD t := by
  induction s with
  | nil => simp [numN]
  | cons x xs ih =>
    cases x with
    | true =>
      have hxs : hasDD xs = false := by rw [hasDD_cons] at hs; exact (Bool.or_eq_false_iff.mp hs).2
      have hbnd' : ¬ (xs.getLast? = some false ∧ t.head? = some false) := by
        cases xs with
        | nil => rintro ⟨h1, _⟩; simp at h1
        | cons z zs => rw [List.getLast?_cons_cons] at hbnd; exact hbnd
      simp only [List.cons_append, numNBeforeDD_cons_true, numN_cons_true]
      rw [ih hxs hbnd']; omega
    | false =>
      have hxs : hasDD xs = false := by rw [hasDD_cons] at hs; exact (Bool.or_eq_false_iff.mp hs).2
      rw [numN_cons_false, List.cons_append]
      cases xs with
      | nil =>
        have ht : t.head? ≠ some false := by intro hc; exact hbnd ⟨by simp, hc⟩
        cases t with
        | nil => simp [numNBeforeDD, numN]
        | cons z zs =>
          have hz : z = true := by cases z with | true => rfl | false => simp at ht
          subst hz; simp [numNBeforeDD, numN]
      | cons y ys =>
        have hy : y = true := by cases y with | true => rfl | false => simp [hasDD] at hs
        subst hy
        have hbnd' : ¬ ((true :: ys).getLast? = some false ∧ t.head? = some false) := by
          rw [List.getLast?_cons_cons] at hbnd; exact hbnd
        show numNBeforeDD (false :: true :: (ys ++ t)) = numN (true :: ys) + numNBeforeDD t
        have hrec : numNBeforeDD (false :: true :: (ys ++ t))
            = numNBeforeDD (true :: (ys ++ t)) := rfl
        rw [hrec]
        have := ih hxs hbnd'
        simpa using this

/-- `(UD)^m` is `DD`-free with `m` North steps. -/
theorem numNBeforeDD_fUD (m : ℕ) :
    numNBeforeDD ((List.replicate m [true, false]).flatten) = m := by
  induction m with
  | zero => simp [numNBeforeDD]
  | succ k ih =>
    have hstep : (List.replicate (k+1) [true, false]).flatten
        = true :: false :: (List.replicate k [true, false]).flatten := by
      rw [List.replicate_succ, List.flatten_cons]; rfl
    rw [hstep]
    cases k with
    | zero => rfl
    | succ j =>
      have hstep2 : (List.replicate (j+1) [true, false]).flatten
          = true :: false :: (List.replicate j [true, false]).flatten := by
        rw [List.replicate_succ, List.flatten_cons]; rfl
      show numNBeforeDD (true :: false :: (List.replicate (j+1) [true, false]).flatten) = j + 1 + 1
      rw [hstep2]
      show numNBeforeDD (false :: true :: false :: (List.replicate j [true, false]).flatten) + 1
          = j + 1 + 1
      have hrfl : numNBeforeDD (false :: true :: false :: (List.replicate j [true, false]).flatten)
          = numNBeforeDD (true :: false :: (List.replicate j [true, false]).flatten) := rfl
      rw [hrfl, ← hstep2, ih]

/-- `numNBeforeDD` of the base reconstructed path `(UD)^a U^{b+1} D^{b+1}`. -/
theorem numNBeforeDD_base_step (a b : ℕ) :
    numNBeforeDD ((List.replicate a [true, false]).flatten
        ++ List.replicate (b + 1) true ++ List.replicate (b + 1) false)
      = a + b + 1 := by
  rw [show (List.replicate a [true, false]).flatten = fUD a from rfl, List.append_assoc]
  have hb1 : ((List.replicate (b+1) true ++ List.replicate (b+1) false)).head? = some true := by
    rw [List.replicate_succ]; simp
  have hbnd : ¬ ((fUD a).getLast? = some false ∧
      (List.replicate (b+1) true ++ List.replicate (b+1) false).head? = some false) := by
    rintro ⟨_, h2⟩; rw [hb1] at h2; simp at h2
  rw [numNBeforeDD_append _ _ (hasDD_fUD a) hbnd, numN_fUD]
  have hgl : (List.replicate (b+1) true).getLast? = some true := by
    rw [List.getLast?_replicate]; simp
  have hbnd2 : ¬ ((List.replicate (b+1) true).getLast? = some false ∧
      (List.replicate (b+1) false).head? = some false) := by
    rintro ⟨h1, _⟩; rw [hgl] at h1; simp at h1
  rw [numNBeforeDD_append _ _ (hasDD_replicate_true (b+1)) hbnd2, numN_replicate_true]
  have hfalse : numNBeforeDD (List.replicate (b+1) false) = 0 := by
    cases b with
    | zero => simp [numNBeforeDD]
    | succ k => rw [List.replicate_succ, List.replicate_succ]; rfl
  rw [hfalse]; omega

/-- `numNBeforeDD` of the recursive reconstructed path
`(UD)^a U ρ U^b D^{b+1} ρ'`: the first `DD` sits in the pyramid `D^{b+1}`. -/
theorem numNBeforeDD_reconstruct (a b : ℕ) (ρ ρ' : List Bool) (hb : 1 ≤ b)
    (hρDD : hasDD ρ = false) :
    numNBeforeDD ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
      = a + 1 + numN ρ + b := by
  rw [show (List.replicate a [true, false]).flatten = fUD a from rfl]
  set s := fUD a ++ [true] ++ ρ ++ List.replicate b true with hsdef
  have hwhole : fUD a ++ [true] ++ ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
      = s ++ (List.replicate (b + 1) false ++ ρ') := by rw [hsdef]; simp [List.append_assoc]
  rw [hwhole]
  have hs1 : hasDD (fUD a ++ [true]) = false :=
    hasDD_append_false (fUD a) [true] (hasDD_fUD a) rfl (fun _ => by simp)
  have hs2 : hasDD (fUD a ++ [true] ++ ρ) = false := by
    apply hasDD_append_false _ ρ hs1 hρDD
    intro h; rw [stEast_append] at h; simp [stEast] at h
  have hs : hasDD s = false := by
    rw [hsdef]
    apply hasDD_append_false _ (List.replicate b true) hs2 (hasDD_replicate_true b)
    intro _
    obtain ⟨b', rfl⟩ : ∃ b', b = b'+1 := ⟨b-1, by omega⟩
    rw [List.replicate_succ]; simp
  have hsgl : s.getLast? = some true := by
    rw [hsdef]
    obtain ⟨b', rfl⟩ : ∃ b', b = b'+1 := ⟨b-1, by omega⟩
    rw [List.getLast?_append]; simp [List.getLast?_replicate]
  have hbnd : ¬ (s.getLast? = some false ∧
      (List.replicate (b+1) false ++ ρ').head? = some false) := by
    rintro ⟨h1, _⟩; rw [hsgl] at h1; simp at h1
  rw [numNBeforeDD_append s _ hs hbnd]
  have h0 : numNBeforeDD (List.replicate (b+1) false ++ ρ') = 0 := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b'+1 := ⟨b-1, by omega⟩
    rw [show b'+1+1 = b'+2 from rfl, List.replicate_succ, List.replicate_succ, List.cons_append,
      List.cons_append]; rfl
  have hns : numN s = a + 1 + numN ρ + b := by
    rw [hsdef, numN_append, numN_append, numN_append, numN_fUD, numN_replicate_true,
      show numN ([true] : List Bool) = 1 from rfl]
  rw [h0, hns]; omega

/-- Adding a constant preserves a `≤`-chain (forward direction). -/
theorem isChain_map_add (l : List ℕ) (c : ℕ) (h : l.IsChain (· ≤ ·)) :
    (l.map (· + c)).IsChain (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons x xs ih => cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.isChain_cons_cons] at h
      simp only [List.map_cons]
      rw [List.isChain_cons_cons]
      exact ⟨by omega, by have := ih h.2; simpa using this⟩

/-- Validity of the base datum `(0^a, [0])`. -/
theorem isValid_zeros (a : ℕ) : IsValid (List.replicate a false) [0] := by
  have hnd : noDescent (List.replicate a false) = true := by simpa using noDescent_sorted a 0
  refine ⟨?_, ?_, ?_⟩
  · rw [desComp_noDescent hnd]; simp
  · rw [tauOf, desComp_noDescent hnd]; simp [deltaOf, deltaAux]
  · rw [tauOf, desComp_noDescent hnd]; simp [deltaOf, deltaAux, List.length_replicate]

/-- Validity of the base datum `(0^a 1^b, [0])`. -/
theorem isValid_zeros_ones (a b : ℕ) :
    IsValid (List.replicate a false ++ List.replicate b true) [0] := by
  have hnd : noDescent (List.replicate a false ++ List.replicate b true) = true :=
    noDescent_sorted a b
  refine ⟨?_, ?_, ?_⟩
  · rw [desComp_noDescent hnd]; simp
  · rw [tauOf, desComp_noDescent hnd]; simp [deltaOf, deltaAux]
  · rw [tauOf, desComp_noDescent hnd]
    simp [deltaOf, deltaAux, List.length_append, List.length_replicate]

/-- Reverse construction of validity: prepend the block `0^a 1^b 0` to a valid
datum, with a head area `h` bounded by the first height coordinate. -/
theorem isValid_cons (a b : ℕ) (w' : List Bool) (av' : List ℕ) (hb : 1 ≤ b)
    (hv : IsValid w' av') (h : ℕ) (hh : h ≤ (tauOf w' av').headD 0) :
    IsValid (List.replicate a false ++ List.replicate b true ++ [false] ++ w') (h :: av') := by
  obtain ⟨hlen, hchain, hlast⟩ := hv
  set wb := List.replicate a false ++ List.replicate b true ++ [false] ++ w' with hwbdef
  have hwform : wb = List.replicate a false ++ List.replicate b true ++ false :: w' := by
    rw [hwbdef]; simp [List.append_assoc]
  have hnd : noDescent wb = false := by rw [hwform]; exact noDescent_block a b w' hb
  have hcl0 : cLead0 wb = a := by rw [hwform]; exact cLead0_block a b w' hb
  have hdropa : wb.drop (cLead0 wb) = List.replicate b true ++ false :: w' := by
    rw [hcl0, hwform]; exact drop_a_block a b w'
  have hcl1 : cLead1 (wb.drop (cLead0 wb)) = b := by rw [hdropa]; exact cLead1_block b w'
  have hdropb : (wb.drop (cLead0 wb)).drop (cLead1 (wb.drop (cLead0 wb)) + 1) = w' := by
    rw [hcl1, hdropa]; exact drop_block b w'
  set c := cLead0 wb + 1 + cLead1 (wb.drop (cLead0 wb)) with hcdef
  have htau : tauOf wb (h :: av') = (c + h) :: (tauOf w' av').map (· + c) := by
    rw [tauOf_descent hnd, hdropb]
  have htau_ne : tauOf w' av' ≠ [] := by
    have hpos : 0 < (tauOf w' av').length := by
      rw [tauOf, List.length_zipWith, deltaOf_length, hlen, min_self]
      exact List.length_pos_of_ne_nil (desComp_ne_nil _)
    exact List.ne_nil_of_length_pos hpos
  have hwblen : wb.length = a + b + 1 + w'.length := by
    rw [hwbdef]; simp [List.length_append, List.length_replicate, List.append_assoc]; omega
  have hc_eq : c = a + 1 + b := by rw [hcdef, hcl1, hcl0]
  refine ⟨?_, ?_, ?_⟩
  · rw [desComp_descent hnd, hdropb]; simp only [List.length_cons]; omega
  · rw [htau]
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil htau_ne
    rw [hx]; simp only [List.map_cons]
    rw [List.isChain_cons_cons]
    refine ⟨?_, ?_⟩
    · have hxhd : (tauOf w' av').headD 0 = x := by rw [hx]; rfl
      omega
    · have := isChain_map_add (tauOf w' av') c hchain
      rw [hx] at this; simpa using this
  · rw [htau]
    have hM : (tauOf w' av').map (· + c) ≠ [] := by simpa using htau_ne
    obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hM
    rw [hz]; rw [List.getLast?_cons_cons, ← hz, List.getLast?_map, hlast]
    simp only [Option.map_some]
    congr 1
    rw [hwblen, hc_eq]; omega

/-- The `some`-branch of the well-definedness induction: `Ψ π` is valid and its
first height coordinate is `numNBeforeDD π`. -/
theorem psi_valid_head_some (n : ℕ)
    (IH : ∀ m, m < n → ∀ π : List Bool, π.length = m → IsDyck π → π ≠ [] →
      IsValid (psiPath π).1 (psiPath π).2 ∧
        (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π)
    (π : List Bool) (hlen : π.length = n) (hd : IsDyck π) (hne : π ≠ []) (i : ℕ)
    (hfd : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    IsValid (psiPath π).1 (psiPath π).2 ∧
      (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π := by
  set a := cUD π with hadef
  set rest := π.drop (2 * a + 1) with hrestdef
  have hstart : rest.head? = some true := dyck_rest_head π i hd hne hfd
  set p := ((rest.take i).reverse.takeWhile id).length with hpdef
  set L := ((rest.drop i).takeWhile (· = false)).length with hLdef
  set b := min p (L - 1) with hbdef
  set ρ := rest.take (i - b) with hρdef
  set ρ' := rest.drop (i + b + 1) with hρ'def
  obtain ⟨hstruct, hρDD, hmax, hb1, hne0⟩ :=
    psi_rest_struct rest i p L b hfd hstart hpdef hLdef hbdef
  simp only [← hρdef, ← hρ'def] at hstruct hρDD hmax hne0
  have hπ : π = (List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ' := by
    have hl := dyck_leading π hd hne
    rw [← hadef, ← hrestdef, hstruct] at hl
    rw [hl]; simp [List.append_assoc]
  have hρU : ρ = [] ∨ ρ.head? = some true := by
    rcases Nat.eq_zero_or_pos (numN ρ) with h0 | hpos
    · left; exact hne0 h0
    · right
      have hlt : 0 < ρ.length := by
        by_contra hc; push_neg at hc
        rw [Nat.le_zero, List.length_eq_zero_iff] at hc; rw [hc] at hpos; simp [numN] at hpos
      have hh : ρ.head? = rest.head? := by
        rw [hρdef, List.head?_take, if_neg (by intro hz; rw [hρdef, hz] at hlt; simp at hlt)]
      rw [hh, hstart]
  have hresD : IsDyck (ρ ++ ρ') := dyck_residual π b ρ ρ' hd hne hstruct hρDD hρU
  by_cases hemp : ρ ++ ρ' = []
  · obtain ⟨hρe, hρ'e⟩ := List.append_eq_nil_iff.mp hemp
    have hbase : π = (List.replicate a [true, false]).flatten
        ++ List.replicate (b + 1) true ++ List.replicate (b + 1) false := by
      rw [hπ, hρe, hρ'e]; simp [List.replicate_succ, List.append_assoc]
    have hpsi : psiPath π = (List.replicate a false ++ List.replicate b true, [0]) := by
      rw [hbase]; exact psiPath_base a b
    refine ⟨?_, ?_⟩
    · rw [hpsi]; exact isValid_zeros_ones a b
    · have h1 : (psiPath π).1 = List.replicate a false ++ List.replicate b true := by rw [hpsi]
      have h2 : (psiPath π).2 = [0] := by rw [hpsi]
      rw [h1, h2]
      have hrhs : numNBeforeDD π = a + b + 1 := by rw [hbase, numNBeforeDD_base_step]
      rw [hrhs]
      have hnd : noDescent (List.replicate a false ++ List.replicate b true) = true :=
        noDescent_sorted a b
      rw [tauOf, desComp_noDescent hnd]
      simp only [deltaOf, deltaAux, zero_add, List.zipWith_cons_cons, List.zipWith_nil_left,
        List.headD_cons, add_zero, List.length_append, List.length_replicate]
  · have hpsi : psiPath π = (List.replicate a false ++ List.replicate b true ++ [false]
          ++ (psiPath (ρ ++ ρ')).1, numN ρ :: (psiPath (ρ ++ ρ')).2) := by
      rw [hπ]; exact psiPath_step a b ρ ρ' hb1 hρU hρDD hmax hemp
    have hreslen : (ρ ++ ρ').length < n := by
      rw [← hlen]; conv_rhs => rw [hπ]
      simp only [List.length_append, List.length_cons, List.length_replicate, fUD_len,
        List.length_nil]; omega
    obtain ⟨hvalid', hhead'⟩ := IH (ρ ++ ρ').length hreslen (ρ ++ ρ') rfl hresD hemp
    set w' := (psiPath (ρ ++ ρ')).1 with hw'def
    set av' := (psiPath (ρ ++ ρ')).2 with hav'def
    have hbound : numN ρ ≤ (tauOf w' av').headD 0 := by
      rw [hhead']; exact numN_le_numNBeforeDD_append ρ ρ' hρDD
    refine ⟨?_, ?_⟩
    · rw [hpsi]
      exact isValid_cons a b w' av' hb1 hvalid' (numN ρ) hbound
    · have h1 : (psiPath π).1 = List.replicate a false ++ List.replicate b true ++ false :: w' := by
        rw [hpsi]; simp [List.append_assoc]
      have h2 : (psiPath π).2 = numN ρ :: av' := by rw [hpsi]
      have hrhs : numNBeforeDD π = a + 1 + numN ρ + b := by
        rw [hπ]; exact numNBeforeDD_reconstruct a b ρ ρ' hb1 hρDD
      rw [h1, h2, tauOf_descent (noDescent_block a b w' hb1), hrhs]
      simp only [List.headD_cons]
      rw [cLead0_block a b w' hb1, drop_a_block a b w', cLead1_block b w']
      omega

/-- Well-definedness (`lem:well-defined`): `Ψ` of a nonempty Dyck path is valid
data, and the first height coordinate is `numNBeforeDD π`. -/
theorem psi_valid_head (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    IsValid (psiPath π).1 (psiPath π).2 ∧
      (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π := by
  suffices H : ∀ n, ∀ π : List Bool, π.length = n → IsDyck π → π ≠ [] →
      IsValid (psiPath π).1 (psiPath π).2 ∧
        (tauOf (psiPath π).1 (psiPath π).2).headD 0 = numNBeforeDD π by
    exact H π.length π rfl hd hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro π hlen hd hne
    rcases hfd : firstDDidx (π.drop (2 * cUD π + 1)) with _ | i
    · have hrf : π.drop (2 * cUD π + 1) = [false] := dyck_none_rest π hd hne hfd
      have hpsi : psiPath π = (List.replicate (cUD π) false, [0]) := by rw [psiPath.eq_1, hfd]
      refine ⟨?_, ?_⟩
      · rw [hpsi]; exact isValid_zeros (cUD π)
      · have h1 : (psiPath π).1 = List.replicate (cUD π) false := by rw [hpsi]
        have h2 : (psiPath π).2 = [0] := by rw [hpsi]
        rw [h1, h2]
        have hrhs : numNBeforeDD π = cUD π + 1 := by
          have hπfud : π = (List.replicate (cUD π + 1) [true, false]).flatten := by
            conv_lhs => rw [dyck_leading π hd hne, hrf]
            rw [List.replicate_succ']; simp
          conv_lhs => rw [hπfud, numNBeforeDD_fUD]
        rw [hrhs]
        have hnd : noDescent (List.replicate (cUD π) false) = true := by
          simpa using noDescent_sorted (cUD π) 0
        rw [tauOf, desComp_noDescent hnd]
        simp only [deltaOf, deltaAux, zero_add, List.zipWith_cons_cons, List.zipWith_nil_left,
          List.headD_cons, add_zero, List.length_replicate]
    · exact psi_valid_head_some n IH π hlen hd hne i hfd

/-- Well-definedness (`lem:well-defined`): `Ψ` of a nonempty Dyck path is valid
data. -/
theorem psi_isValid (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    IsValid (psiPath π).1 (psiPath π).2 :=
  (psi_valid_head π hd hne).1

/-- `Ψ` maps the codomain into the domain: it sends a Dyck path of size `n` to a
valid datum `(w, av)` with `|w| + 1 = n`. -/
theorem psi_mapsTo (n : ℕ) (hn : 1 ≤ n) :
    Set.MapsTo psiPath (Cod n) (Dom n) := by
  rintro π ⟨hd, hsize⟩
  have hne : π ≠ [] := by rintro rfl; simp only [List.length_nil] at hsize; omega
  refine ⟨?_, psi_isValid π hd hne⟩
  have hround := phi_psi π hd hne
  have hs := phi_size (psiPath π).1 (psiPath π).2
  rw [hround, hsize] at hs
  omega

/-- **The bijection** (`the main theorem`): `Φ = phiPath` is a bijection between
valid data of size `n` and decorated Dyck paths of size `n`, with explicit
inverse `Ψ = psiPath`. -/
theorem phi_bijOn (n : ℕ) (hn : 1 ≤ n) :
    Set.BijOn (fun p : List Bool × List ℕ => phiPath p.1 p.2) (Dom n) (Cod n) := by
  refine Set.InvOn.bijOn ⟨?_, ?_⟩ (phi_mapsTo n) (psi_mapsTo n hn)
  · rintro ⟨w, av⟩ ⟨_, hv⟩
    exact psi_phi w av hv
  · intro π hπ
    refine phi_psi π hπ.1 ?_
    intro hnil; rw [hnil] at hπ; simp only [Cod, Set.mem_setOf_eq, List.length_nil] at hπ; omega


end Psi
