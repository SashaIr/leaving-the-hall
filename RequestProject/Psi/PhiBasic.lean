import RequestProject.Psi.PathLemmas

namespace Psi

/-! ## Properties of `Φ = phiPath` (hence of the bijection `Ψ`)

The forward bijection `Ψ` is the inverse of `phiPath`; each statement below is the
corresponding property of `Ψ` read through that inverse. -/

/-- `Φ` produces a genuine Dyck path (`lem:well-defined`, path side).  No validity
of the area vector is needed. -/
theorem phi_isDyck (w : List Bool) (av : List ℕ) :
    IsDyck (phiPath w av) := by
  fun_induction phiPath w av with
  | case1 w av hnd => exact isDyck_base _ _
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      have hpi : IsDyck pi := ihrec
      have happ : rho ++ rho' = pi := by
        have := splitAtRow_append pi hh; rw [hsplit] at this; simpa using this
      rw [IsDyck, isDyckAux_iff] at hpi
      obtain ⟨hval, hend⟩ := hpi
      rw [← happ, validFrom_append] at hval
      rw [← happ, runHeight_append] at hend
      obtain ⟨hvalρ, hvalρ'⟩ := hval
      exact isDyck_sandwich a b rho rho' hvalρ hvalρ' hend

/-- `#0(w) + #1(w) = |w|`. -/
theorem len_filter_split (w : List Bool) :
    (w.filter (· = false)).length + (w.filter id).length = w.length := by
  induction w with
  | nil => simp
  | cons a t ih => cases a <;> (simp_all; omega)

/-- `Φ` produces a path of the expected size `2n`, `n = |w| + 1` (no validity of
the area vector is needed). -/
theorem phi_size (w : List Bool) (av : List ℕ) :
    (phiPath w av).length = 2 * (w.length + 1) := by
  fun_induction phiPath w av with
  | case1 w av h =>
      have hs := len_filter_split w
      simp only [List.length_append, List.length_flatten, List.map_replicate,
        List.length_replicate, List.sum_replicate, smul_eq_mul, List.length_cons,
        List.length_nil]
      omega
  | case2 w av h a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      have hnd : noDescent w = false := by simpa using h
      have hdec : w = List.replicate a false ++ List.replicate b true ++ false :: w' :=
        (noDescent_false_decomp hnd).1
      have hlen := congrArg List.length hdec
      simp only [List.length_append, List.length_replicate, List.length_cons] at hlen
      have hsp : rho.length + rho'.length = pi.length := by
        have hh2 := splitAtRow_length pi hh
        rw [hsplit] at hh2; simpa using hh2
      have hpi : pi.length = 2 * (w'.length + 1) := ihrec
      simp only [List.length_append, List.length_flatten, List.map_replicate,
        List.length_replicate, List.sum_replicate, smul_eq_mul, List.length_cons,
        List.length_nil]
      omega

/-- The produced path has exactly `#0(w)` valleys: `w ∈ W(0^l, 1^k)` with `l` the
number of valleys. -/
theorem phi_numValleys (w : List Bool) (av : List ℕ) :
    numValleys (phiPath w av) = (w.filter (· = false)).length := by
  fun_induction phiPath w av with
  | case1 w av hnd => exact numValleys_base _ _
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      have hnd' : noDescent w = false := by simpa using hnd
      have hdec : w = List.replicate a false ++ List.replicate b true ++ false :: w' :=
        (noDescent_false_decomp hnd').1
      have hb1 : 1 ≤ b := (noDescent_false_decomp hnd').2
      have hpiD : IsDyck pi := phi_isDyck w' av'
      have hpine : pi ≠ [] := phiPath_ne_nil w' av'
      have happ : rho ++ rho' = pi := by
        have := splitAtRow_append pi hh; rw [hsplit] at this; simpa using this
      have hbd : stEast rho false = false → rho'.head? = some true := by
        intro hsr
        by_cases hr0 : rho = []
        · have hpp : rho' = pi := by rw [hr0, List.nil_append] at happ; exact happ
          rw [hpp]; exact dyck_head pi hpiD hpine
        · have hfst : (splitAtRow pi hh).1 ≠ [] := by rw [hsplit]; exact hr0
          have hst : stEast (splitAtRow pi hh).1 false = false := by rw [hsplit]; exact hsr
          rcases sar_bound_pos pi hh hfst hst with h1 | h2
          · exfalso
            have hr'0 : rho' = [] := by rw [hsplit] at h1; exact h1
            have hrp : rho = pi := by rw [hr'0, List.append_nil] at happ; exact happ
            rw [hrp, dyck_stEast pi hpiD hpine] at hsr
            exact Bool.noConfusion hsr
          · rw [hsplit] at h2; exact h2
      rw [show (List.replicate a [true, false]).flatten ++ [true] ++ rho ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho' = fUD a ++ [true] ++ rho ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho' from rfl]
      rw [numValleys_construction a b rho rho' hb1 hbd, happ, ihrec]
      conv_rhs => rw [hdec]
      simp only [List.filter_append, List.length_append, filterF_replicate_false,
        filterF_replicate_true, List.filter_cons, decide_true, if_true, List.length_cons]
      omega

/-! ### Rise count (`w ∈ W(0^l,1^k)`, rise side) -/

theorem numN_append (p q : List Bool) : numN (p ++ q) = numN p + numN q := by
  unfold numN; rw [List.filter_append, List.length_append]
theorem numN_replicate_true (n : Nat) : numN (List.replicate n true) = n := by
  induction n with
  | zero => simp [numN]
  | succ m ih => rw [List.replicate_succ]; unfold numN at ih ⊢; simp [List.filter_cons, ih]
theorem numN_replicate_false (n : Nat) : numN (List.replicate n false) = 0 := by
  induction n with
  | zero => simp [numN]
  | succ m ih => rw [List.replicate_succ]; unfold numN at ih ⊢; simp [List.filter_cons, ih]
theorem numN_fUD (a : Nat) : numN (fUD a) = a := by
  induction a with
  | zero => simp [fUD, numN]
  | succ a ih =>
      rw [fUD_succ, numN_append, ih, show numN [true, false] = 1 from rfl]; omega
theorem numN_single_true : numN [true] = 1 := rfl
theorem numN_cons (a : Bool) (t : List Bool) :
    numN (a :: t) = (if a = true then 1 else 0) + numN t := by
  cases a with
  | false => simp [numN]
  | true => simp [numN, List.filter_cons]; omega
theorem numN_count (p : List Bool) (le sn : Bool) :
    numN p = countRises p le sn + countValleys p le
      + (if le = false ∧ sn = false ∧ p.head? = some true then 1 else 0) := by
  induction p generalizing le sn with
  | nil => simp [numN, countRises, countValleys]
  | cons a t ih =>
      rw [numN_cons]
      cases a with
      | true =>
          rw [ih false true]
          cases le <;> cases sn <;>
            simp [countRises, countValleys] <;> omega
      | false =>
          rw [ih true sn]
          cases le <;> cases sn <;>
            simp [countRises, countValleys]
theorem count_split (p : List Bool) (h : p.head? = some true) :
    numRises p + numValleys p + 1 = numN p := by
  have h2 := numN_count p false false
  simp only [h, and_true, if_true] at h2
  simp only [numRises, numValleys]
  omega
theorem numN_flatten_pair (l : Nat) :
    numN ((List.replicate l [true, false]).flatten) = l := numN_fUD l
theorem numN_phiPath (w : List Bool) (av : List ℕ) : numN (phiPath w av) = w.length + 1 := by
  fun_induction phiPath w av with
  | case1 w av hnd =>
      simp only [numN_append, numN_flatten_pair, numN_replicate_true, numN_replicate_false,
        add_zero]
      have := len_filter_split w
      omega
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      have hdec : w = List.replicate a false ++ List.replicate b true ++ false :: w' :=
        (noDescent_false_decomp (by simpa using hnd)).1
      have happ : rho ++ rho' = pi := by
        have := splitAtRow_append pi hh; rw [hsplit] at this; simpa using this
      have hsum : numN rho + numN rho' = w'.length + 1 := by
        rw [← numN_append, happ, ihrec]
      have hwlen : w.length = a + b + 1 + w'.length := by
        rw [hdec]; simp [List.length_append]; omega
      rw [show (List.replicate a [true, false]).flatten = fUD a from rfl,
          numN_append, numN_append, numN_append, numN_append, numN_append, numN_fUD,
          numN_single_true, numN_replicate_true, numN_replicate_false]
      omega
theorem phi_numRises (w : List Bool) (av : List ℕ) :
    numRises (phiPath w av) = (w.filter id).length := by
  have hd := phi_isDyck w av
  have hne := phiPath_ne_nil w av
  have hh : (phiPath w av).head? = some true := dyck_head _ hd hne
  have hcs := count_split (phiPath w av) hh
  have hnv := phi_numValleys w av
  have hnn := numN_phiPath w av
  have hlen := len_filter_split w
  rw [hnv, hnn] at hcs
  omega


end Psi
