import RequestProject.Psi.Defs

namespace Psi

/-! ## Structural lemmas -/

/-- `splitAtRow` splits a path into two pieces that concatenate back to it. -/
theorem splitAtRow_append (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1 ++ (splitAtRow p h).2 = p := by
  fun_induction splitAtRow p h <;> simp_all

/-- `splitAtRow` preserves the total length. -/
theorem splitAtRow_length (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1.length + (splitAtRow p h).2.length = p.length := by
  have := splitAtRow_append p h
  have : ((splitAtRow p h).1 ++ (splitAtRow p h).2).length = p.length := by rw [this]
  simpa using this

theorem cLead0_take (w : List Bool) :
    w.take (cLead0 w) = List.replicate (cLead0 w) false := by
  fun_induction cLead0 w with
  | case1 r ih =>
      rw [show 1 + cLead0 r = cLead0 r + 1 from by omega, List.take_succ_cons,
        List.replicate_succ, ih]
  | case2 t h => simp

theorem cLead1_take (w : List Bool) :
    w.take (cLead1 w) = List.replicate (cLead1 w) true := by
  fun_induction cLead1 w with
  | case1 r ih =>
      rw [show 1 + cLead1 r = cLead1 r + 1 from by omega, List.take_succ_cons,
        List.replicate_succ, ih]
  | case2 t h => simp

theorem cLead0_drop (w : List Bool) : (w.drop (cLead0 w)).head? ≠ some false := by
  fun_induction cLead0 w with
  | case1 r ih =>
      rw [show 1 + cLead0 r = cLead0 r + 1 from by omega, List.drop_succ_cons]; exact ih
  | case2 t h =>
      cases t with
      | nil => simp
      | cons a t' => cases a with
        | false => exact (h t' rfl).elim
        | true => simp

theorem cLead1_drop (w : List Bool) : (w.drop (cLead1 w)).head? ≠ some true := by
  fun_induction cLead1 w with
  | case1 r ih =>
      rw [show 1 + cLead1 r = cLead1 r + 1 from by omega, List.drop_succ_cons]; exact ih
  | case2 t h =>
      cases t with
      | nil => simp
      | cons a t' => cases a with
        | true => exact (h t' rfl).elim
        | false => simp

theorem noDescent_cons_false (rest : List Bool) :
    noDescent (false :: rest) = noDescent rest := by
  cases rest with | nil => simp [noDescent] | cons y ys => simp [noDescent]

theorem noDescent_repl_true (b : ℕ) : noDescent (List.replicate b true) = true := by
  induction b with
  | zero => simp [noDescent]
  | succ b ih =>
      rw [List.replicate_succ]
      cases b with
      | zero => simp [noDescent]
      | succ c => rw [List.replicate_succ] at ih ⊢; simp only [noDescent] at ih ⊢; simp_all

theorem noDescent_sorted (a b : ℕ) :
    noDescent (List.replicate a false ++ List.replicate b true) = true := by
  induction a with
  | zero => simpa using noDescent_repl_true b
  | succ a ih => rw [List.replicate_succ, List.cons_append, noDescent_cons_false]; exact ih

/-- When `w` has a descent, it decomposes as `0^a 1^b 0 w'` with `b ≥ 1`, where
`a`, `b`, `w'` are exactly the quantities used by `phiPath`. -/
theorem noDescent_false_decomp {w : List Bool} (hw : noDescent w = false) :
    w = List.replicate (cLead0 w) false
          ++ List.replicate (cLead1 (w.drop (cLead0 w))) true
          ++ false :: (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)
        ∧ 1 ≤ cLead1 (w.drop (cLead0 w)) := by
  set a := cLead0 w with ha
  set v := w.drop a with hv
  set b := cLead1 v with hb
  have hwv : w = List.replicate a false ++ v := by
    conv_lhs => rw [← List.take_append_drop a w]
    rw [cLead0_take w]
  have hvb : v = List.replicate b true ++ v.drop b := by
    conv_lhs => rw [← List.take_append_drop b v]
    rw [cLead1_take v]
  have hv_head : v.head? ≠ some false := by have := cLead0_drop w; rwa [← hv] at this
  have hvd_head : (v.drop b).head? ≠ some true := cLead1_drop v
  clear_value a v b
  cases hd : v.drop b with
  | nil =>
    exfalso
    have hvr : v = List.replicate b true := by rw [hvb, hd, List.append_nil]
    rw [hwv, hvr, noDescent_sorted] at hw
    exact absurd hw (by simp)
  | cons c cs =>
    have hc : c = false := by
      rcases c with _ | _
      · rfl
      · exact absurd (by rw [hd]; rfl) hvd_head
    subst hc
    have hcs : v.drop (b + 1) = cs := by
      have hx : v.drop (b + 1) = (v.drop b).drop 1 := by rw [List.drop_drop]
      rw [hx, hd]; rfl
    have hb1 : 1 ≤ b := by
      by_contra hb0
      have hb00 : b = 0 := by omega
      rw [hb00] at hd; simp at hd
      rw [hd] at hv_head; simp at hv_head
    refine ⟨?_, hb1⟩
    conv_lhs => rw [hwv, hvb, hd]
    rw [hcs]
    simp [List.append_assoc]

/-! ### Dyck-path height machinery

To prove that `phiPath` produces a Dyck path we track the running height and a
"stays weakly above the diagonal" predicate, which compose well over `++`. -/

/-- Final height of a path started from height `h`. -/
def runHeight : List Bool → Int → Int
  | [], h => h
  | true :: r, h => runHeight r (h + 1)
  | false :: r, h => runHeight r (h - 1)

/-- The path stays weakly above the diagonal when started from height `h`
(every East step is taken from a strictly positive height). -/
def validFrom : List Bool → Int → Prop
  | [], _ => True
  | true :: r, h => validFrom r (h + 1)
  | false :: r, h => 0 < h ∧ validFrom r (h - 1)

theorem runHeight_append (p q : List Bool) (h : Int) :
    runHeight (p ++ q) h = runHeight q (runHeight p h) := by
  induction p generalizing h with
  | nil => simp [runHeight]
  | cons a t ih => cases a <;> simp [runHeight, ih]

theorem validFrom_append (p q : List Bool) (h : Int) :
    validFrom (p ++ q) h ↔ validFrom p h ∧ validFrom q (runHeight p h) := by
  induction p generalizing h with
  | nil => simp [validFrom, runHeight]
  | cons a t ih => cases a <;> simp [validFrom, runHeight, ih, and_assoc]

theorem isDyckAux_iff (p : List Bool) (h : Int) :
    IsDyckAux p h ↔ validFrom p h ∧ runHeight p h = 0 := by
  induction p generalizing h with
  | nil => simp [IsDyckAux, validFrom, runHeight]
  | cons a t ih => cases a <;> simp [IsDyckAux, validFrom, runHeight, ih, and_assoc]

theorem runHeight_replicate_true (n : ℕ) (h : Int) :
    runHeight (List.replicate n true) h = h + n := by
  induction n generalizing h with
  | zero => simp [runHeight]
  | succ n ih => rw [List.replicate_succ]; simp only [runHeight, ih]; push_cast; ring

theorem runHeight_replicate_false (n : ℕ) (h : Int) :
    runHeight (List.replicate n false) h = h - n := by
  induction n generalizing h with
  | zero => simp [runHeight]
  | succ n ih => rw [List.replicate_succ]; simp only [runHeight, ih]; push_cast; ring

theorem validFrom_replicate_true (n : ℕ) (h : Int) :
    validFrom (List.replicate n true) h := by
  induction n generalizing h with
  | zero => simp [validFrom]
  | succ n ih => rw [List.replicate_succ]; simpa [validFrom] using ih (h + 1)

theorem validFrom_replicate_false (n : ℕ) (h : Int) (hh : (n : Int) ≤ h) :
    validFrom (List.replicate n false) h := by
  induction n generalizing h with
  | zero => simp [validFrom]
  | succ n ih =>
      rw [List.replicate_succ]; simp only [validFrom]
      exact ⟨by push_cast at hh; omega, by apply ih; push_cast at hh ⊢; omega⟩

theorem runHeight_shift (p : List Bool) (h d : Int) :
    runHeight p (h + d) = runHeight p h + d := by
  induction p generalizing h with
  | nil => simp [runHeight]
  | cons a t ih => cases a with
    | true => simp only [runHeight]; rw [show h + d + 1 = (h + 1) + d from by ring, ih]
    | false => simp only [runHeight]; rw [show h + d - 1 = (h - 1) + d from by ring, ih]

theorem validFrom_mono (p : List Bool) (h h' : Int) (hle : h ≤ h')
    (hv : validFrom p h) : validFrom p h' := by
  induction p generalizing h h' with
  | nil => trivial
  | cons a t ih => cases a with
    | true => simp only [validFrom] at hv ⊢; exact ih (h + 1) (h' + 1) (by omega) hv
    | false => simp only [validFrom] at hv ⊢; exact ⟨by omega, ih (h - 1) (h' - 1) (by omega) hv.2⟩

theorem runHeight_nonneg (p : List Bool) (h : Int) (hh : 0 ≤ h)
    (hv : validFrom p h) : 0 ≤ runHeight p h := by
  induction p generalizing h with
  | nil => simpa [runHeight] using hh
  | cons a t ih => cases a with
    | true => simp only [runHeight, validFrom] at hv ⊢; exact ih (h + 1) (by omega) hv
    | false => simp only [runHeight, validFrom] at hv ⊢; exact ih (h - 1) (by omega) hv.2

theorem runHeight_flatten_UD (l : ℕ) (h : Int) :
    runHeight ((List.replicate l [true, false]).flatten) h = h := by
  induction l generalizing h with
  | zero => simp [runHeight]
  | succ l ih => rw [List.replicate_succ, List.flatten_cons, runHeight_append]; simp [runHeight, ih]

theorem validFrom_flatten_UD (l : ℕ) (h : Int) (hh : 0 ≤ h) :
    validFrom ((List.replicate l [true, false]).flatten) h := by
  induction l generalizing h with
  | zero => simp [validFrom]
  | succ l ih =>
      rw [List.replicate_succ, List.flatten_cons, validFrom_append]
      exact ⟨⟨by omega, trivial⟩, by
        rw [show runHeight [true, false] h = h from by simp [runHeight]]; exact ih h hh⟩

/-- The base path `(UD)^l U^{k+1} D^{k+1}` is a Dyck path. -/
theorem isDyck_base (l k : ℕ) :
    IsDyck ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) := by
  rw [IsDyck, isDyckAux_iff]
  refine ⟨?_, ?_⟩
  · rw [validFrom_append, validFrom_append]
    refine ⟨⟨validFrom_flatten_UD _ 0 le_rfl, ?_⟩, ?_⟩
    · rw [runHeight_flatten_UD]; exact validFrom_replicate_true _ _
    · rw [runHeight_append, runHeight_flatten_UD, runHeight_replicate_true]
      apply validFrom_replicate_false; push_cast; omega
  · rw [runHeight_append, runHeight_append, runHeight_flatten_UD, runHeight_replicate_true,
      runHeight_replicate_false]; push_cast; ring

/-- The recursive construction `(UD)^a U ρ U^b D^{b+1} ρ'` is a Dyck path,
given that `ρ ρ'` came from splitting a Dyck path (so `ρ` is a valid prefix and
`ρ'` completes it back to height `0`). -/
theorem isDyck_sandwich (a b : ℕ) (rho rho' : List Bool)
    (hv : validFrom rho 0) (hv' : validFrom rho' (runHeight rho 0))
    (he : runHeight rho' (runHeight rho 0) = 0) :
    IsDyck ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') := by
  have hρ0 : 0 ≤ runHeight rho 0 := runHeight_nonneg rho 0 le_rfl hv
  set F := (List.replicate a [true, false]).flatten with hF
  have hA : runHeight F 0 = 0 := runHeight_flatten_UD a 0
  have hB : runHeight (F ++ [true]) 0 = 1 := by rw [runHeight_append, hA]; norm_num [runHeight]
  have hC : runHeight (F ++ [true] ++ rho) 0 = runHeight rho 0 + 1 := by
    rw [runHeight_append, hB]; simpa using runHeight_shift rho 0 1
  have hD : runHeight (F ++ [true] ++ rho ++ List.replicate b true) 0 = runHeight rho 0 + 1 + b := by
    rw [runHeight_append, hC, runHeight_replicate_true]
  have hE : runHeight (F ++ [true] ++ rho ++ List.replicate b true ++ List.replicate (b + 1) false) 0
      = runHeight rho 0 := by
    rw [runHeight_append, hD, runHeight_replicate_false]; push_cast; ring
  rw [IsDyck, isDyckAux_iff]
  refine ⟨?_, ?_⟩
  · rw [validFrom_append, validFrom_append, validFrom_append, validFrom_append, validFrom_append]
    refine ⟨⟨⟨⟨⟨validFrom_flatten_UD _ 0 le_rfl, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hA]; simp [validFrom]
    · rw [hB]; exact validFrom_mono rho 0 1 (by norm_num) hv
    · rw [hC]; exact validFrom_replicate_true _ _
    · rw [hD]; apply validFrom_replicate_false; push_cast; omega
    · rw [hE]; exact hv'
  · rw [runHeight_append, hE]; exact he

/-! ### Valley/rise counting machinery -/

def stEast : List Bool → Bool → Bool
  | [], le => le
  | true :: r, _ => stEast r false
  | false :: r, _ => stEast r true
theorem countValleys_append (p q : List Bool) (le : Bool) :
    countValleys (p ++ q) le = countValleys p le + countValleys q (stEast p le) := by
  induction p generalizing le with
  | nil => simp [countValleys, stEast]
  | cons a t ih => cases a <;> (simp [countValleys, stEast, ih] <;> omega)
theorem stEast_append (p q : List Bool) (x : Bool) :
    stEast (p ++ q) x = stEast q (stEast p x) := by
  induction p generalizing x with
  | nil => simp [stEast]
  | cons a t ih => cases a <;> simp [stEast, ih]
theorem cV_replicate_true (n : Nat) (le : Bool) :
    countValleys (List.replicate n true) le = (if le ∧ 1 ≤ n then 1 else 0) := by
  cases n with
  | zero => simp [countValleys]
  | succ m =>
      rw [List.replicate_succ]
      have h0 : countValleys (List.replicate m true) false = 0 := by
        clear le; induction m with
        | zero => simp [countValleys]
        | succ k ih => rw [List.replicate_succ]; simpa [countValleys] using ih
      simp only [countValleys, h0]; cases le <;> simp
theorem cV_replicate_false (n : Nat) (le : Bool) :
    countValleys (List.replicate n false) le = 0 := by
  induction n generalizing le with
  | zero => simp [countValleys]
  | succ m ih => rw [List.replicate_succ]; simpa [countValleys] using ih true
theorem stEast_replicate_true (n : Nat) (x : Bool) :
    stEast (List.replicate n true) x = if 1 ≤ n then false else x := by
  induction n generalizing x with
  | zero => simp [stEast]
  | succ m ih => rw [List.replicate_succ]; simp only [stEast]; rw [ih false]; simp
theorem stEast_replicate_false (n : Nat) (x : Bool) :
    stEast (List.replicate n false) x = if 1 ≤ n then true else x := by
  induction n generalizing x with
  | zero => simp [stEast]
  | succ m ih => rw [List.replicate_succ]; simp only [stEast]; rw [ih true]; simp
def fUD (a : Nat) : List Bool := (List.replicate a [true, false]).flatten
theorem stEast_UDpair (x : Bool) : stEast [true, false] x = true := rfl
theorem cV_UDpair_false : countValleys [true, false] false = 0 := rfl
theorem cV_UDpair_true : countValleys [true, false] true = 1 := rfl
theorem fUD_succ (a : Nat) : fUD (a+1) = [true, false] ++ fUD a := by
  unfold fUD; rw [List.replicate_succ, List.flatten_cons]
theorem cV_fUD_true (a : Nat) : countValleys (fUD a) true = a := by
  induction a with
  | zero => simp [fUD, countValleys]
  | succ a ih => rw [fUD_succ, countValleys_append, cV_UDpair_true, stEast_UDpair, ih]; omega
theorem stEast_fUD_true (a : Nat) : stEast (fUD a) true = true := by
  induction a with
  | zero => simp [fUD, stEast]
  | succ a ih => rw [fUD_succ, stEast_append, stEast_UDpair, ih]
theorem stEast_fUD_false_pos (a : Nat) : stEast (fUD (a+1)) false = true := by
  rw [fUD_succ, stEast_append, stEast_UDpair, stEast_fUD_true]
theorem cVstate_fUD (a : Nat) :
    countValleys (fUD a) false + (if stEast (fUD a) false then 1 else 0) = a := by
  cases a with
  | zero => simp [fUD, countValleys, stEast]
  | succ a =>
      rw [fUD_succ, countValleys_append, cV_UDpair_false, stEast_UDpair, cV_fUD_true,
        ← fUD_succ, stEast_fUD_false_pos]; simp
theorem cV_true_false_head (p : List Bool) (hp : p.head? = some true) :
    countValleys p true = countValleys p false + 1 := by
  cases p with
  | nil => simp at hp
  | cons a t => cases a with
      | true => simp [countValleys]; omega
      | false => simp at hp
theorem stEast_nonempty (p : List Bool) (hp : p ≠ []) (x y : Bool) :
    stEast p x = stEast p y := by
  induction p generalizing x y with
  | nil => exact absurd rfl hp
  | cons a t ih => cases t with
      | nil => cases a <;> simp [stEast]
      | cons b s => cases a <;> exact ih (by simp) _ _
theorem dyck_head (p : List Bool) (hd : IsDyck p) (hne : p ≠ []) : p.head? = some true := by
  cases p with
  | nil => exact absurd rfl hne
  | cons a t => cases a with
      | true => rfl
      | false => simp only [IsDyck, IsDyckAux] at hd; omega
theorem stEast_getLast_false (p : List Bool) (hp : p.getLast? = some false) (x : Bool) :
    stEast p x = true := by
  induction p generalizing x with
  | nil => simp at hp
  | cons a t ih => cases t with
      | nil => simp at hp; subst hp; rfl
      | cons b s => rw [List.getLast?_cons_cons] at hp; cases a <;> exact ih hp _
theorem dyck_ends_east (p : List Bool) (hd : IsDyck p) (hne : p ≠ []) :
    p.getLast? = some false := by
  obtain ⟨ys, y, rfl⟩ := (List.eq_nil_or_concat p).resolve_left hne
  rw [List.concat_eq_append] at hd ⊢
  cases y with
  | false => simp
  | true =>
      exfalso
      rw [IsDyck, isDyckAux_iff, validFrom_append] at hd
      have h1 : runHeight (ys ++ [true]) 0 = runHeight ys 0 + 1 := by
        rw [runHeight_append]; simp [runHeight]
      have := runHeight_nonneg ys 0 le_rfl hd.1.1
      rw [h1] at hd; omega
theorem dyck_stEast (p : List Bool) (hd : IsDyck p) (hne : p ≠ []) :
    stEast p false = true := stEast_getLast_false p (dyck_ends_east p hd hne) false
theorem splitAtRow_pos_nil (p : List Bool) (h : Nat) :
    (splitAtRow p (h+1)).1 = [] → splitAtRow p (h+1) = ([], []) := by
  cases p with
  | nil => intro _; simp [splitAtRow]
  | cons a rest =>
      cases a with
      | true =>
          cases h with
          | zero => intro hh; simp only [splitAtRow] at hh ⊢; split at hh <;> simp_all
          | succ h => intro hh; simp only [splitAtRow] at hh; exact (List.cons_ne_nil _ _ hh).elim
      | false => intro hh; simp only [splitAtRow] at hh; exact (List.cons_ne_nil _ _ hh).elim
theorem sar_bound_pos (p : List Bool) (h : Nat) :
    (splitAtRow p h).1 ≠ [] → stEast (splitAtRow p h).1 false = false →
      (splitAtRow p h).2 = [] ∨ (splitAtRow p h).2.head? = some true := by
  fun_induction splitAtRow p h with
  | case1 p => intro hne _; exact absurd rfl hne
  | case2 h => intro hne _; exact absurd rfl hne
  | case3 rest' => intro _ hst; exact absurd hst (by simp [stEast])
  | case4 rest hx =>
      intro _ _
      cases rest with
      | nil => left; rfl
      | cons rh rt => cases rh with
          | true => right; rfl
          | false => exact (hx rt rfl).elim
  | case5 rest h ro ro' heq ihrec =>
      rw [heq] at ihrec
      intro _ hst
      simp only [stEast] at hst
      by_cases hro : ro = []
      · subst hro
        have h0 := splitAtRow_pos_nil rest h (by rw [heq])
        rw [heq, Prod.mk.injEq] at h0
        exact Or.inl h0.2
      · exact ihrec hro hst
  | case6 rest h ro ro' heq ihrec =>
      rw [heq] at ihrec
      intro _ hst
      simp only [stEast] at hst
      by_cases hro : ro = []
      · subst hro; simp [stEast] at hst
      · rw [stEast_nonempty ro hro true false] at hst
        exact ihrec hro hst
theorem phiPath_ne_nil (w : List Bool) (av : List ℕ) : phiPath w av ≠ [] := by
  fun_induction phiPath w av with
  | case1 w av h => simp [List.append_assoc, List.replicate_succ]
  | case2 w av h a after0 b w' hh av' pi rho rho' hsplit ihrec => simp
theorem numValleys_construction (a b : Nat) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hbd : stEast rho false = false → rho'.head? = some true) :
    numValleys (fUD a ++ [true] ++ rho ++ List.replicate b true
        ++ List.replicate (b+1) false ++ rho')
      = a + 1 + numValleys (rho ++ rho') := by
  unfold numValleys
  rw [show (fUD a ++ [true] ++ rho ++ List.replicate b true ++ List.replicate (b+1) false ++ rho')
        = fUD a ++ ([true] ++ (rho ++ (List.replicate b true
            ++ (List.replicate (b+1) false ++ rho')))) from by simp only [List.append_assoc]]
  rw [countValleys_append, countValleys_append, countValleys_append, countValleys_append,
    countValleys_append]
  rw [show stEast [true] (stEast (fUD a) false) = false from rfl]
  rw [show stEast (List.replicate b true) (stEast rho false) = false from by
        rw [stEast_replicate_true]; simp [hb]]
  rw [show stEast (List.replicate (b+1) false) false = true from by
        rw [stEast_replicate_false]; simp]
  rw [cV_replicate_false]
  rw [show countValleys [true] (stEast (fUD a) false)
        = (if stEast (fUD a) false then 1 else 0) from by
        cases stEast (fUD a) false <;> simp [countValleys]]
  rw [show countValleys (List.replicate b true) (stEast rho false)
        = (if stEast rho false then 1 else 0) from by rw [cV_replicate_true]; simp [hb]]
  rw [countValleys_append rho rho' false]
  have hfud := cVstate_fUD a
  by_cases hsr : stEast rho false = true
  · rw [hsr]; simp only [if_true]; omega
  · have hsrf : stEast rho false = false := Bool.not_eq_true _ |>.mp hsr
    have hcvh := cV_true_false_head rho' (hbd hsrf)
    rw [hsrf]; simp only [Bool.false_eq_true, if_false]; omega
theorem numValleys_base (l k : Nat) :
    numValleys ((List.replicate l [true, false]).flatten ++ List.replicate (k+1) true
      ++ List.replicate (k+1) false) = l := by
  unfold numValleys
  rw [show ((List.replicate l [true, false]).flatten ++ List.replicate (k+1) true
        ++ List.replicate (k+1) false) = fUD l ++ (List.replicate (k+1) true
          ++ List.replicate (k+1) false) from by unfold fUD; simp only [List.append_assoc]]
  rw [countValleys_append, countValleys_append, cV_replicate_false, add_zero, cV_replicate_true]
  simp only [show (1:Nat) ≤ k+1 from Nat.le_add_left 1 k, and_true]
  exact cVstate_fUD l
theorem filterF_replicate_false (n : Nat) :
    ((List.replicate n false).filter (· = false)).length = n := by
  induction n with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.filter_cons]; simp
theorem filterF_replicate_true (n : Nat) :
    ((List.replicate n true).filter (· = false)).length = 0 := by
  induction n with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.filter_cons]; simp


end Psi
