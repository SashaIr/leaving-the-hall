import RequestProject.Psi.PhiBasic

namespace Psi

/-! ### Area preservation (`lem:area`) infrastructure

We compute the area of a path with an integer-valued accumulator `areaH` that
tracks the running height directly, which makes the append/shift algebra clean
(no truncated `ℕ` subtraction).  `area_eq_areaH` connects it to the `ℕ`-valued
`area` for genuine Dyck paths. -/

/-- Number of East (`false`) steps. -/
def numE (p : List Bool) : ℕ := (p.filter (· = false)).length

theorem numE_cons_true (t : List Bool) : numE (true :: t) = numE t := by
  simp [numE]
theorem numE_cons_false (t : List Bool) : numE (false :: t) = numE t + 1 := by
  simp [numE]

theorem numN_cons_true (t : List Bool) : numN (true :: t) = numN t + 1 := by
  simp [numN]
theorem numN_cons_false (t : List Bool) : numN (false :: t) = numN t := by
  simp [numN]

/-- `runHeight p h = h + #North(p) - #East(p)`. -/
theorem runHeight_eq (p : List Bool) (h : Int) :
    runHeight p h = h + numN p - numE p := by
  induction p generalizing h with
  | nil => simp [runHeight, numN, numE]
  | cons a t ih =>
    cases a with
    | true => rw [numN_cons_true, numE_cons_true]; simp only [runHeight]; rw [ih]; push_cast; ring
    | false => rw [numN_cons_false, numE_cons_false]; simp only [runHeight]; rw [ih]; push_cast; ring

/-- Integer-valued area accumulator: `ht` is the current height (= North − East so
far), `le` says whether the previous step was an East step.  A North step
contributes its height `ht` exactly when it is a valley. -/
def areaH : List Bool → Int → Bool → Int
  | [], _, _ => 0
  | true :: r, ht, le => (if le then ht else 0) + areaH r (ht + 1) false
  | false :: r, ht, _ => areaH r (ht - 1) true

theorem areaH_append (p q : List Bool) (ht : Int) (le : Bool) :
    areaH (p ++ q) ht le = areaH p ht le + areaH q (runHeight p ht) (stEast p le) := by
  induction p generalizing ht le with
  | nil => simp [areaH, runHeight, stEast]
  | cons a t ih => cases a <;> simp [areaH, runHeight, stEast, ih] <;> ring

theorem areaH_shift (p : List Bool) (ht d : Int) (le : Bool) :
    areaH p (ht + d) le = areaH p ht le + d * (countValleys p le) := by
  induction p generalizing ht le with
  | nil => simp [areaH, countValleys]
  | cons a t ih =>
    cases a with
    | true =>
      simp only [areaH, countValleys]
      rw [show ht + d + 1 = (ht + 1) + d from by ring, ih]
      cases le <;> simp <;> ring
    | false =>
      simp only [areaH, countValleys]
      rw [show ht + d - 1 = (ht - 1) + d from by ring, ih]

theorem areaAux_eq_areaH (p : List Bool) (i e : ℕ) (le : Bool)
    (hle : e ≤ i) (hv : validFrom p ((i : Int) - e)) :
    (areaAux p i e le : Int) = areaH p ((i : Int) - e) le := by
  induction p generalizing i e le with
  | nil => simp [areaAux, areaH]
  | cons a t ih =>
    cases a with
    | true =>
      simp only [areaAux, areaH, validFrom] at *
      have hcast : ((if le then i - e else 0 : ℕ) : Int) = (if le then ((i:Int) - e) else 0) := by
        cases le <;> simp [Int.ofNat_sub hle]
      rw [Nat.cast_add, hcast]
      have key := ih (i+1) e false (by omega)
        (by rw [Nat.cast_add, Nat.cast_one, show (i:Int)+1-↑e = ((i:Int)-↑e)+1 from by ring]; exact hv)
      rw [key, show ((i+1:ℕ):Int) - ↑e = ((i:Int)-↑e)+1 from by push_cast; ring]
    | false =>
      simp only [areaAux, areaH, validFrom] at *
      obtain ⟨hpos, hv2⟩ := hv
      have hei : e + 1 ≤ i := by have : (0:Int) < (i:Int) - e := hpos; omega
      have hv2' : validFrom t ((i:Int) - ↑(e+1)) := by
        push_cast; rw [show (i:Int)-(↑e+1)=(i:Int)-↑e-1 from by ring]; exact hv2
      rw [ih i (e+1) true hei hv2', show (i:Int)-(↑(e+1))=(i:Int)-↑e-1 from by push_cast; ring]

/-- For a genuine Dyck path the `ℕ`-valued `area` agrees with `areaH`. -/
theorem area_eq_areaH (p : List Bool) (hv : validFrom p 0) :
    (area p : Int) = areaH p 0 false := by
  have := areaAux_eq_areaH p 0 0 false (le_refl 0) (by simpa using hv)
  simpa [area] using this

theorem areaH_replicate_false (n : Nat) (ht : Int) (le : Bool) :
    areaH (List.replicate n false) ht le = 0 := by
  induction n generalizing ht le with
  | zero => simp [areaH]
  | succ m ih => rw [List.replicate_succ]; simp only [areaH]; rw [ih]

theorem areaH_replicate_true (n : Nat) (ht : Int) (le : Bool) :
    areaH (List.replicate n true) ht le = if (le ∧ 1 ≤ n) then ht else 0 := by
  cases n with
  | zero => simp [areaH]
  | succ m =>
    rw [List.replicate_succ]; simp only [areaH]
    have h0 : ∀ (h2 : Int), areaH (List.replicate m true) h2 false = 0 := by
      intro h2; induction m generalizing h2 with
      | zero => simp [areaH]
      | succ k ih => rw [List.replicate_succ]; simp only [areaH]; rw [ih]; simp
    rw [h0]; cases le <;> simp

theorem areaH_fUD0 (a : Nat) (le : Bool) : areaH (fUD a) 0 le = 0 := by
  induction a generalizing le with
  | zero => simp [fUD, areaH]
  | succ m ih =>
    unfold fUD; rw [List.replicate_succ, List.flatten_cons, areaH_append]
    have h1 : areaH [true, false] 0 le = 0 := by cases le <;> simp [areaH]
    have hr : runHeight [true, false] 0 = 0 := by simp [runHeight]
    rw [h1, hr]; simpa [fUD] using ih (stEast [true, false] le)

/-- `splitAtRow` at row `h` yields a first piece with exactly `h` North steps
(provided `h` does not exceed the total number of North steps). -/
theorem split_numN (pi : List Bool) (h : ℕ) (hh : h ≤ numN pi) :
    numN (splitAtRow pi h).1 = h := by
  fun_induction splitAtRow pi h with
  | case1 p => simp [numN]
  | case2 h => simp only [numN, List.filter_nil, List.length_nil] at hh ⊢; omega
  | case3 rest' => simp [numN]
  | case4 rest hx => simp [numN]
  | case5 rest h ro ro' heq ih =>
      rw [numN_cons_true] at hh; rw [heq] at ih; simp only at ih
      rw [numN_cons_true, ih (by omega)]
  | case6 rest h ro ro' heq ih =>
      rw [numN_cons_false] at hh; rw [heq] at ih; simp only at ih
      rw [numN_cons_false]; exact ih hh

/-- Presence of two consecutive East steps (`DD`). -/
def hasDD : List Bool → Bool
  | false :: false :: _ => true
  | _ :: r => hasDD r
  | [] => false

theorem hasDD_cons (a : Bool) (rest : List Bool) :
    hasDD (a :: rest) = ((a == false && rest.head? == some false) || hasDD rest) := by
  cases a with
  | true => cases rest with | nil => rfl | cons b u => simp [hasDD]
  | false => cases rest with
      | nil => rfl
      | cons b u => cases b <;> simp [hasDD]

/-- No `DD` is preserved by concatenation provided the boundary does not create
one (either the left part does not end in an East step, or the right part does
not start with one). -/
theorem hasDD_append_false (s t : List Bool) (hs : hasDD s = false) (ht : hasDD t = false)
    (hbound : stEast s false = true → t.head? ≠ some false) : hasDD (s ++ t) = false := by
  induction s with
  | nil => simpa using ht
  | cons a s' ih =>
    rw [hasDD_cons a s'] at hs
    simp only [Bool.or_eq_false_iff] at hs
    obtain ⟨hhd, hs'⟩ := hs
    rw [List.cons_append, hasDD_cons a (s' ++ t)]
    simp only [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · cases s' with
      | nil =>
        simp only [List.nil_append]
        cases hb : (a == false && t.head? == some false) with
        | false => rfl
        | true =>
          exfalso
          simp only [Bool.and_eq_true, beq_iff_eq] at hb
          obtain ⟨ha, hth⟩ := hb
          have hse : stEast [a] false = true := by cases a <;> simp_all [stEast]
          exact hbound hse hth
      | cons y ys => simpa using hhd
    · apply ih hs'
      intro hse
      cases s' with
      | nil => simp [stEast] at hse
      | cons y ys =>
        have hst : stEast (a :: y :: ys) false = stEast (y :: ys) false := by
          cases a <;> simp only [stEast] <;> exact stEast_nonempty (y::ys) (by simp) _ _
        rw [hst] at hbound; exact hbound hse

/-- A prefix of a path with no `DD` has no `DD`. -/
theorem hasDD_prefix (s t : List Bool) (h : hasDD (s ++ t) = false) : hasDD s = false := by
  induction s with
  | nil => rfl
  | cons a s' ih =>
    rw [List.cons_append, hasDD_cons a (s' ++ t)] at h
    simp only [Bool.or_eq_false_iff] at h
    obtain ⟨hhd, htl⟩ := h
    rw [hasDD_cons a s']
    simp only [Bool.or_eq_false_iff]
    refine ⟨?_, ih htl⟩
    cases s' with
    | nil => simp
    | cons y ys => simpa using hhd

/-- When `B` ends in an East step and `h ≤ #North(B)`, the split of `B ++ C` at
row `h` completes inside `B`, so its first piece is exactly the split of `B`. -/
theorem splitAtRow_append_left_fst (B C : List Bool) (h : ℕ)
    (hend : stEast B false = true) (hh : h ≤ numN B) :
    (splitAtRow (B ++ C) h).1 = (splitAtRow B h).1 := by
  fun_induction splitAtRow B h with
  | case1 p => simp [splitAtRow]
  | case2 h => simp [stEast] at hend
  | case3 rest' => simp only [List.cons_append, splitAtRow]
  | case4 rest hx =>
      cases rest with
      | nil => simp [stEast] at hend
      | cons b rt => cases b with
        | false => exact (hx rt rfl).elim
        | true => simp only [List.cons_append, splitAtRow]
  | case5 rest h ro ro' heq ih =>
      simp only [List.cons_append, splitAtRow]
      have hst : stEast rest false = true := hend
      have hnn : h + 1 ≤ numN rest := by rw [numN_cons_true] at hh; omega
      congr 1
      have := ih hst hnn; rw [heq] at this; simpa using this
  | case6 rest h ro ro' heq ih =>
      simp only [List.cons_append, splitAtRow]
      have hrne : rest ≠ [] := by
        rw [numN_cons_false] at hh; intro h0; subst h0; simp [numN] at hh
      have hst : stEast rest false = true := by
        have h1 : stEast rest true = true := hend
        rwa [stEast_nonempty rest hrne true false] at h1
      have hnn : h + 1 ≤ numN rest := by rw [numN_cons_false] at hh; exact hh
      congr 1
      have := ih hst hnn; rw [heq] at this; simpa using this

theorem hasDD_replicate_true (n : Nat) : hasDD (List.replicate n true) = false := by
  induction n with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, hasDD_cons]; simp [ih]

theorem fUD_head (m : Nat) : (fUD m).head? ≠ some false := by
  cases m with
  | zero => simp [fUD]
  | succ k => rw [fUD, List.replicate_succ, List.flatten_cons]; simp

theorem hasDD_fUD (a : Nat) : hasDD (fUD a) = false := by
  induction a with
  | zero => rfl
  | succ m ih =>
    rw [fUD, List.replicate_succ, List.flatten_cons]
    exact hasDD_append_false _ _ rfl ih (fun _ => fUD_head m)

/-- Combining lemma: if `B` has no `DD`, ends in an East step, and has at least
`h` North steps, then the split of `B ++ C` at row `h` has no `DD`. -/
theorem hasDD_split_of_B (B C : List Bool) (h : ℕ) (hBend : stEast B false = true)
    (hBnum : h ≤ numN B) (hBnoDD : hasDD B = false) :
    hasDD (splitAtRow (B ++ C) h).1 = false := by
  rw [splitAtRow_append_left_fst B C h hBend hBnum]
  exact hasDD_prefix _ _ (by rw [splitAtRow_append]; exact hBnoDD)

/-- Base-case structural bound: any split of the base path `((UD)^l U^{k+1} D^{k+1})`
at a row `h ≤ l + k + 1` has no `DD` in its first piece. -/
theorem hasDD_split_base (l k h : ℕ) (hh : h ≤ l + k + 1) :
    hasDD (splitAtRow ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) h).1 = false := by
  rw [show (List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
        ++ List.replicate (k + 1) false
      = ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true ++ [false])
        ++ List.replicate k false from by
    rw [show List.replicate (k + 1) false = [false] ++ List.replicate k false from by
          rw [List.replicate_succ]; rfl]
    simp only [List.append_assoc]]
  apply hasDD_split_of_B
  · rw [stEast_append]; simp [stEast]
  · simp only [numN_append, numN_replicate_true,
      show numN ((List.replicate l [true, false]).flatten) = l from numN_fUD l,
      show numN [false] = 0 from rfl]
    omega
  · apply hasDD_append_false
    · apply hasDD_append_false
      · exact hasDD_fUD l
      · exact hasDD_replicate_true (k + 1)
      · intro _; rw [List.replicate_succ]; simp
    · rfl
    · intro hcontra
      rw [stEast_append, stEast_replicate_true] at hcontra
      simp at hcontra

/-- For a path with no `DD`, the number of East steps equals the number of
valleys plus one if the path ends in an East step (each maximal East-run has
length one, and each is followed by a North except possibly a final one). -/
theorem noDD_numE (p : List Bool) (hp : hasDD p = false) :
    numE p = numValleys p + (if stEast p false then 1 else 0) := by
  induction p with
  | nil => simp [numE, numValleys, countValleys, stEast]
  | cons a r ih =>
    rw [hasDD_cons] at hp
    simp only [Bool.or_eq_false_iff] at hp
    obtain ⟨hhead, hr⟩ := hp
    cases a with
    | true =>
      rw [numE_cons_true]
      have hv : numValleys (true :: r) = numValleys r := by simp [numValleys, countValleys]
      have hs : stEast (true :: r) false = stEast r false := rfl
      rw [hv, hs]; exact ih hr
    | false =>
      rw [numE_cons_false]
      have hnf : r.head? ≠ some false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hhead
        rcases hhead with h | h
        · simp at h
        · exact h
      have hv : numValleys (false :: r) = countValleys r true := by simp [numValleys, countValleys]
      have hs : stEast (false :: r) false = stEast r true := rfl
      rw [hv, hs]
      cases r with
      | nil => simp [numE, countValleys, stEast]
      | cons b r'' =>
        have hb : b = true := by cases b with | true => rfl | false => exact absurd rfl hnf
        subst hb
        rw [cV_true_false_head (true :: r'') rfl,
            stEast_nonempty (true :: r'') (by simp) true false]
        have := ih hr
        simp only [numValleys] at this ⊢
        omega

/-- Effect of the incoming `le` flag on `areaH`: turning it on adds the current
height exactly when the path starts with a North step. -/
theorem areaH_le_diff (q : List Bool) (ht : Int) :
    areaH q ht true - areaH q ht false = (if q.head? = some true then ht else 0) := by
  cases q with
  | nil => simp [areaH]
  | cons a r => cases a <;> simp [areaH]

/-- The area identity underlying `lem:area`: inserting the block
`(UD)^a U · ρ · U^b D^{b+1}` around the split `π = ρ ρ'` raises the area by
exactly `h = #North(ρ)`. Stated over `ℤ` via `areaH`. -/
theorem area_reconstruct (a b : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false)
    (hbd : stEast rho false = false → rho'.head? = some true) :
    areaH ((List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') 0 false
      = (numN rho : Int) + areaH (rho ++ rho') 0 false := by
  have hexp : areaH ((List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') 0 false
      = areaH rho 1 false + (if stEast rho false then 1 + runHeight rho 0 else 0)
        + areaH rho' (runHeight rho 0) true := by
    rw [show (List.replicate a [true, false]).flatten ++ [true] ++ rho ++ List.replicate b true
          ++ List.replicate (b + 1) false ++ rho'
        = (List.replicate a [true, false]).flatten ++ ([true] ++ (rho ++ (List.replicate b true
          ++ (List.replicate (b + 1) false ++ rho')))) from by simp only [List.append_assoc]]
    rw [areaH_append, show areaH ((List.replicate a [true, false]).flatten) 0 false = 0
          from areaH_fUD0 a false,
        show runHeight ((List.replicate a [true, false]).flatten) 0 = 0
          from runHeight_flatten_UD a 0, zero_add]
    rw [areaH_append,
        show areaH [true] 0 (stEast ((List.replicate a [true, false]).flatten) false) = 0
          from by cases stEast ((List.replicate a [true, false]).flatten) false <;> simp [areaH],
        show runHeight [true] 0 = 1 from by simp [runHeight],
        show stEast [true] (stEast ((List.replicate a [true, false]).flatten) false) = false
          from rfl, zero_add]
    rw [areaH_append,
        show runHeight rho 1 = 1 + runHeight rho 0 from by
          rw [add_comm]; exact runHeight_shift rho 0 1]
    rw [areaH_append, areaH_replicate_true,
        show runHeight (List.replicate b true) (1 + runHeight rho 0)
          = (1 + runHeight rho 0) + b from runHeight_replicate_true b _,
        show stEast (List.replicate b true) (stEast rho false) = false from by
          rw [stEast_replicate_true]; simp [hb]]
    rw [areaH_append, areaH_replicate_false, zero_add,
        show runHeight (List.replicate (b + 1) false) ((1 + runHeight rho 0) + b) = runHeight rho 0
          from by rw [runHeight_replicate_false]; push_cast; ring,
        show stEast (List.replicate (b + 1) false) false = true from by
          rw [stEast_replicate_false]; simp]
    simp only [hb, and_true]
    ring
  rw [hexp]
  rw [show areaH rho 1 false = areaH rho 0 false + 1 * (countValleys rho false : Int) from by
        have h := areaH_shift rho 0 1 false; simpa using h]
  rw [areaH_append]
  have hnumE := noDD_numE rho hnoDD
  have hrh : runHeight rho 0 = (numN rho : Int) - numE rho := by rw [runHeight_eq]; ring
  have hdiff := areaH_le_diff rho' (runHeight rho 0)
  have hnv : (countValleys rho false : Int) = (numValleys rho : Int) := by rfl
  cases hle : stEast rho false with
  | true =>
    simp only [hle, if_true] at *
    have : (numE rho : Int) = numValleys rho + 1 := by exact_mod_cast hnumE
    push_cast at hrh this ⊢
    linarith [hrh, this]
  | false =>
    have hhead := hbd hle
    rw [hhead] at hdiff
    simp only [hle, Bool.false_eq_true, if_false] at *
    have : (numE rho : Int) = numValleys rho := by exact_mod_cast hnumE
    push_cast at hrh this hdiff ⊢
    linarith [hrh, this, hdiff]

/-! ### Descent-composition / staircase theory -/

theorem deltaAux_shift (r : List ℕ) (acc : ℕ) :
    deltaAux r acc = (deltaAux r 0).map (· + acc) := by
  induction r generalizing acc with
  | nil => simp [deltaAux]
  | cons x xs ih =>
    conv_lhs => rw [deltaAux, ih (acc + x)]
    conv_rhs => rw [deltaAux, zero_add, List.map_cons, ih x, List.map_map]
    refine List.cons.injEq _ _ _ _ |>.mpr ⟨by omega, ?_⟩
    apply List.map_congr_left; intro y _; simp only [Function.comp_apply]; omega

theorem deltaOf_cons (x : ℕ) (r : List ℕ) :
    deltaOf (x :: r) = x :: (deltaOf r).map (· + x) := by
  simp only [deltaOf, deltaAux, zero_add]; rw [deltaAux_shift r x]

theorem desCompAux_noDescent (w : List Bool) (hnd : noDescent w = true) (cur : ℕ) :
    desCompAux w cur = [cur + w.length] := by
  induction w generalizing cur with
  | nil => simp [desCompAux]
  | cons a t iht =>
    cases t with
    | nil => simp [desCompAux]
    | cons b rest =>
      simp only [noDescent] at hnd
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hnd
      have hab : (a && !b) = false := by
        rcases a with _ | _ <;> rcases b with _ | _ <;> simp_all
      simp only [desCompAux, hab, if_false, Bool.false_eq_true]
      rw [iht h2 (cur+1)]; simp [List.length_cons]; omega

theorem desCompAux_zeros (a : ℕ) (rest : List Bool) (cur : ℕ) :
    desCompAux (List.replicate a false ++ (true :: rest)) cur
      = desCompAux (true :: rest) (cur + a) := by
  induction a generalizing cur with
  | zero => simp
  | succ m ih =>
    have hstart : List.replicate (m+1) false ++ (true :: rest)
        = false :: (List.replicate m false ++ (true :: rest)) := by
          rw [List.replicate_succ, List.cons_append]
    rw [hstart]
    cases hm : List.replicate m false ++ (true :: rest) with
    | nil => simp at hm
    | cons y ys =>
      simp only [desCompAux, Bool.false_and, if_false, Bool.false_eq_true]
      rw [← hm, ih]; congr 1; omega

theorem desCompAux_ones (b : ℕ) (hb : 1 ≤ b) (rest : List Bool) (cur : ℕ) :
    desCompAux (List.replicate b true ++ (false :: rest)) cur
      = (cur + b) :: desCompAux (false :: rest) 0 := by
  induction b generalizing cur with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp [desCompAux]
    | succ k =>
      have hstart : List.replicate (k+1+1) true ++ (false :: rest)
          = true :: true :: (List.replicate k true ++ (false :: rest)) := by
        rw [List.replicate_succ, List.replicate_succ, List.cons_append, List.cons_append]
      rw [hstart]
      simp only [desCompAux, Bool.and_false, Bool.not_true, if_false, Bool.false_eq_true]
      have hback : true :: (List.replicate k true ++ (false :: rest))
          = List.replicate (k+1) true ++ (false :: rest) := by
            rw [List.replicate_succ, List.cons_append]
      rw [hback, ih (by omega) (cur+1)]; congr 1; omega

/-- Base descent composition: for a weakly increasing `w`, `Des(0w) = [|w|+1]`. -/
theorem desComp_noDescent {w : List Bool} (hnd : noDescent w = true) :
    desComp (false :: w) = [w.length + 1] := by
  have h : noDescent (false :: w) = true := by rw [noDescent_cons_false]; exact hnd
  unfold desComp
  rw [desCompAux_noDescent (false :: w) h 0]; simp

/-- Descent recursion: for `w = 0^a 1^b 0 w'` (with `b ≥ 1`),
`Des(0w) = (a+1+b) :: Des(0w')`. -/
theorem desComp_descent {w : List Bool} (hnd : noDescent w = false) :
    desComp (false :: w)
      = (cLead0 w + 1 + cLead1 (w.drop (cLead0 w)))
        :: desComp (false :: (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) := by
  obtain ⟨hdec, hb⟩ := noDescent_false_decomp hnd
  set a := cLead0 w
  set b := cLead1 (w.drop a)
  set w' := (w.drop a).drop (b+1)
  clear_value w' b a
  conv_lhs => rw [hdec]
  have hre : false :: (List.replicate a false ++ List.replicate b true ++ false :: w')
      = List.replicate (a+1) false ++ (List.replicate b true ++ (false :: w')) := by
    rw [List.replicate_succ]; simp [List.append_assoc]
  rw [hre]
  have hstart : List.replicate b true ++ (false :: w')
      = true :: (List.replicate (b-1) true ++ (false :: w')) := by
    cases b with | zero => omega | succ m => rw [List.replicate_succ, List.cons_append]; simp
  unfold desComp
  rw [hstart, desCompAux_zeros, ← hstart, desCompAux_ones b hb]
  congr 1; omega

theorem deltaAux_length (γ : List ℕ) (acc : ℕ) : (deltaAux γ acc).length = γ.length := by
  induction γ generalizing acc with
  | nil => simp [deltaAux]
  | cons x xs ih => simp only [deltaAux, List.length_cons]; rw [ih]

theorem deltaOf_length (γ : List ℕ) : (deltaOf γ).length = γ.length := deltaAux_length γ 0

theorem zipWith_add_map (X Y : List ℕ) (c : ℕ) :
    List.zipWith (· + ·) (X.map (· + c)) Y = (List.zipWith (· + ·) X Y).map (· + c) := by
  induction X generalizing Y with
  | nil => simp
  | cons x xs ih => cases Y with
    | nil => simp
    | cons y ys => simp only [List.map_cons, List.zipWith_cons_cons, ih]; ring_nf

theorem isChain_head_le_getLast (l : List ℕ) (hc : l.IsChain (· ≤ ·)) (g : ℕ)
    (hg : l.getLast? = some g) : l.headD 0 ≤ g := by
  induction l with
  | nil => simp at hg
  | cons x xs ih =>
    cases xs with
    | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hg; subst hg; simp
    | cons y ys =>
      rw [List.isChain_cons_cons] at hc
      have hg' : (y :: ys).getLast? = some g := by rw [← hg]; simp [List.getLast?_cons_cons]
      have := ih hc.2 hg'
      simp only [List.headD_cons] at this ⊢
      omega

theorem isChain_map_add_reflect (l : List ℕ) (c : ℕ)
    (h : (l.map (· + c)).IsChain (· ≤ ·)) : l.IsChain (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons x xs ih => cases xs with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons] at h
      rw [List.isChain_cons_cons] at h ⊢
      exact ⟨by omega, ih (by simpa using h.2)⟩

theorem desCompAux_ne_nil (word : List Bool) (cur : ℕ) : desCompAux word cur ≠ [] := by
  induction word generalizing cur with
  | nil => simp [desCompAux]
  | cons a t iht =>
    cases t with
    | nil => simp [desCompAux]
    | cons b rest =>
      simp only [desCompAux]
      split
      · simp
      · exact iht (cur + 1)

theorem desComp_ne_nil (word : List Bool) : desComp word ≠ [] := desCompAux_ne_nil word 0

theorem w_length_descent {w : List Bool} (hnd : noDescent w = false) :
    w.length = cLead0 w + cLead1 (w.drop (cLead0 w)) + 1 +
      ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)).length := by
  conv_lhs => rw [(noDescent_false_decomp hnd).1]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Structure of `tauOf` under the descent recursion `w = 0^a 1^b 0 w'`. -/
theorem tauOf_descent {w : List Bool} (hnd : noDescent w = false) (ha : ℕ) (av' : List ℕ) :
    tauOf w (ha :: av') =
      ((cLead0 w + 1 + cLead1 (w.drop (cLead0 w))) + ha)
        :: (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av').map
            (· + (cLead0 w + 1 + cLead1 (w.drop (cLead0 w)))) := by
  unfold tauOf
  rw [desComp_descent hnd, deltaOf_cons]
  simp only [List.zipWith_cons_cons]
  rw [zipWith_add_map]

/-! ### Coupling of validity with the split structure -/

/-- `Ψ`-recursion of validity: if `(w, av)` is valid and `w` has a descent
`w = 0^a 1^b 0 w'`, then `(w', tail av)` is valid. -/
theorem isValid_tail (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) :
    IsValid ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av.tail := by
  obtain ⟨hlen, hchain, hlast⟩ := hv
  cases av with
  | nil => rw [desComp_descent hnd] at hlen; simp at hlen
  | cons ha av' =>
    have hwl := w_length_descent hnd
    rw [desComp_descent hnd] at hlen
    simp only [List.length_cons] at hlen
    rw [tauOf_descent hnd] at hchain hlast
    simp only [List.tail_cons]
    set c := cLead0 w + 1 + cLead1 (w.drop (cLead0 w)) with hcdef
    set w' := (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1) with hw'def
    have hlen' : av'.length = (desComp (false :: w')).length := by omega
    have hne : tauOf w' av' ≠ [] := by
      have hpos : 0 < (tauOf w' av').length := by
        rw [tauOf, List.length_zipWith, deltaOf_length, hlen', min_self]
        exact List.length_pos_of_ne_nil (desComp_ne_nil _)
      exact List.ne_nil_of_length_pos hpos
    refine ⟨hlen', ?_, ?_⟩
    · exact isChain_map_add_reflect _ c (List.IsChain.of_cons hchain)
    · have hM : (tauOf w' av').map (· + c) ≠ [] := by simpa using hne
      have hcl : ((c + ha) :: (tauOf w' av').map (· + c)).getLast?
          = ((tauOf w' av').map (· + c)).getLast? := by
        obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hM
        rw [hz]; simp [List.getLast?_cons_cons]
      rw [hcl, List.getLast?_map] at hlast
      obtain ⟨g, hg, hgc⟩ := Option.map_eq_some_iff.mp hlast
      rw [hg]; congr 1; omega

/-- Validity bounds the split row: `h = av.head ≤ (tauOf w' av').head`. -/
theorem isValid_head_le (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) :
    av.headD 0 ≤ (tauOf ((w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) av.tail).headD 0 := by
  obtain ⟨hlen, hchain, _⟩ := hv
  cases av with
  | nil => rw [desComp_descent hnd] at hlen; simp at hlen
  | cons ha av' =>
    rw [desComp_descent hnd] at hlen
    simp only [List.length_cons] at hlen
    rw [tauOf_descent hnd] at hchain
    simp only [List.headD_cons, List.tail_cons]
    set c := cLead0 w + 1 + cLead1 (w.drop (cLead0 w)) with hcdef
    set w' := (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1) with hw'def
    have hlen' : av'.length = (desComp (false :: w')).length := by omega
    have hne : tauOf w' av' ≠ [] := by
      have hpos : 0 < (tauOf w' av').length := by
        rw [tauOf, List.length_zipWith, deltaOf_length, hlen', min_self]
        exact List.length_pos_of_ne_nil (desComp_ne_nil _)
      exact List.ne_nil_of_length_pos hpos
    obtain ⟨x, xs, htau⟩ := List.exists_cons_of_ne_nil hne
    rw [htau] at hchain ⊢
    simp only [List.map_cons, List.headD_cons] at hchain ⊢
    rw [List.isChain_cons_cons] at hchain
    omega

/-- `av` is nonempty and its sum splits as head + tail-sum when `w` has a descent. -/
theorem isValid_av_cons (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = false) : av = av.headD 0 :: av.tail := by
  obtain ⟨hlen, _, _⟩ := hv
  cases av with
  | nil => rw [desComp_descent hnd] at hlen; simp at hlen
  | cons x xs => rfl

/-- In the base case (`w` weakly increasing) validity forces `Σ av = 0`. -/
theorem isValid_base_sum (w : List Bool) (av : List ℕ) (hv : IsValid w av)
    (hnd : noDescent w = true) : av.sum = 0 := by
  obtain ⟨hlen, _, hlast⟩ := hv
  rw [desComp_noDescent hnd, List.length_singleton] at hlen
  cases av with
  | nil => simp at hlen
  | cons c t =>
    cases t with
    | cons _ _ => simp at hlen
    | nil =>
      rw [tauOf, desComp_noDescent hnd] at hlast
      simp only [deltaOf, deltaAux, List.zipWith_cons_cons,
        List.zipWith_nil_right, List.getLast?_singleton, Option.some.injEq] at hlast
      simp only [List.sum_cons, List.sum_nil, add_zero]
      omega

/-- The head of `tauOf` is at most its last entry (a `≤`-chain), hence
`≤ #North(phiPath w' av') = |w'| + 1`. -/
theorem tau_headD_le_numN (w' : List Bool) (av' : List ℕ) (hv : IsValid w' av') :
    (tauOf w' av').headD 0 ≤ numN (phiPath w' av') := by
  obtain ⟨_, hchain, hlast⟩ := hv
  rw [numN_phiPath]
  exact isChain_head_le_getLast (tauOf w' av') hchain (w'.length + 1) hlast

/-- Structural key lemma (`STRUCT`): splitting `phiPath w' av'` at a row `h`
bounded by the first coordinate of `τ' = tauOf w' av'` never exposes a `DD`. -/
theorem phi_split_noDD (w' : List Bool) (av' : List ℕ) (hv : IsValid w' av')
    (h : ℕ) (hle : h ≤ (tauOf w' av').headD 0) :
    hasDD (splitAtRow (phiPath w' av') h).1 = false := by
  revert hle; revert h; revert hv
  fun_induction phiPath w' av' with
  | case1 w' av' hnd =>
      intro hv h hle
      have hbound : h ≤ (w'.filter (· = false)).length + (w'.filter id).length + 1 := by
        have h1 := le_trans hle (tau_headD_le_numN w' av' hv)
        rw [numN_phiPath] at h1
        have h2 := len_filter_split w'
        omega
      exact hasDD_split_base _ _ h hbound
  | case2 w' av' hnd a after0 b w'' hh av'' pi rho rho' hsplit ihrec =>
      intro hv h hle
      have hnd' : noDescent w' = false := by simpa using hnd
      have ivt : IsValid w'' av'' := isValid_tail w' av' hv hnd'
      have hb1 : 1 ≤ b := (noDescent_false_decomp hnd').2
      have hpiD : IsDyck pi := phi_isDyck w'' av''
      have hhle : hh ≤ (tauOf w'' av'').headD 0 := isValid_head_le w' av' hv hnd'
      have hhnum : hh ≤ numN pi := le_trans hhle (tau_headD_le_numN w'' av'' ivt)
      have hrhoNoDD : hasDD rho = false := by
        have := ihrec ivt hh hhle; rw [hsplit] at this; simpa using this
      have hnumRho : numN rho = hh := by
        have := split_numN pi hh hhnum; rw [hsplit] at this; simpa using this
      have htau : (tauOf w' av').headD 0 = a + 1 + b + hh := by
        have hcons : av' = av'.headD 0 :: av'.tail := isValid_av_cons w' av' hv hnd'
        conv_lhs => rw [hcons, tauOf_descent hnd']
        rfl
      rw [show (List.replicate a [true, false]).flatten ++ [true] ++ rho ++ List.replicate b true
            ++ List.replicate (b + 1) false ++ rho'
          = ((List.replicate a [true, false]).flatten ++ [true] ++ rho ++ List.replicate b true
              ++ [false]) ++ (List.replicate b false ++ rho') from by
        rw [show List.replicate (b + 1) false = [false] ++ List.replicate b false from by
              rw [List.replicate_succ]; rfl]
        simp only [List.append_assoc]]
      apply hasDD_split_of_B
      · rw [stEast_append]; simp [stEast]
      · simp only [numN_append, numN_single_true, numN_replicate_true,
          show numN ((List.replicate a [true, false]).flatten) = a from numN_fUD a,
          show numN [false] = 0 from rfl, hnumRho]
        omega
      · apply hasDD_append_false
        · apply hasDD_append_false
          · apply hasDD_append_false
            · apply hasDD_append_false
              · exact hasDD_fUD a
              · rfl
              · intro _; simp
            · exact hrhoNoDD
            · intro hc; rw [stEast_append] at hc; simp [stEast] at hc
          · exact hasDD_replicate_true b
          · intro _; cases b <;> simp [List.replicate_succ]
        · rfl
        · intro hc
          rw [stEast_append, stEast_replicate_true] at hc
          simp [hb1] at hc

/-- `ℕ`-level: the base path has area `0`. -/
theorem area_base_zero (l k : ℕ) :
    area ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) = 0 := by
  have hd : validFrom ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) 0 := ((isDyckAux_iff _ 0).mp (isDyck_base l k)).1
  have hAeq : areaH ((List.replicate l [true, false]).flatten) 0 false = 0 := areaH_fUD0 l false
  have hAht : runHeight ((List.replicate l [true, false]).flatten) 0 = 0 := runHeight_flatten_UD l 0
  have key : (area ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) : Int) = 0 := by
    rw [area_eq_areaH _ hd, areaH_append, areaH_append, hAeq, hAht,
      areaH_replicate_true, areaH_replicate_false]
    simp
  exact_mod_cast key

/-- `ℕ`-level area identity for the reconstruction block. -/
theorem area_sandwich (a b : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false)
    (hbd : stEast rho false = false → rho'.head? = some true)
    (hpi : IsDyck (rho ++ rho')) :
    area ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho')
      = numN rho + area (rho ++ rho') := by
  have hpiV : validFrom (rho ++ rho') 0 := ((isDyckAux_iff _ 0).mp hpi).1
  have hpiE : runHeight (rho ++ rho') 0 = 0 := ((isDyckAux_iff _ 0).mp hpi).2
  have hvrho : validFrom rho 0 := ((validFrom_append rho rho' 0).mp hpiV).1
  have hvrho' : validFrom rho' (runHeight rho 0) := ((validFrom_append rho rho' 0).mp hpiV).2
  have he : runHeight rho' (runHeight rho 0) = 0 := by rw [← runHeight_append]; exact hpiE
  have hdyckP : validFrom ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') 0 :=
    ((isDyckAux_iff _ 0).mp (isDyck_sandwich a b rho rho' hvrho hvrho' he)).1
  have h1 := area_eq_areaH _ hdyckP
  have h2 := area_eq_areaH (rho ++ rho') hpiV
  have h3 := area_reconstruct a b rho rho' hb hnoDD hbd
  have key : (area ((List.replicate a [true, false]).flatten ++ [true] ++ rho
      ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') : Int)
      = (numN rho : Int) + area (rho ++ rho') := by
    rw [h1, h3, ← h2]
  exact_mod_cast key

/-- Area preservation (`lem:area`): `area(π) = area(τ) = Σ av`. -/
theorem phi_area (w : List Bool) (av : List ℕ) (h : IsValid w av) :
    area (phiPath w av) = av.sum := by
  revert h
  fun_induction phiPath w av with
  | case1 w av hnd =>
      intro hv
      have hnd' : noDescent w = true := by simpa using hnd
      rw [isValid_base_sum w av hv hnd']
      exact area_base_zero _ _
  | case2 w av hnd a after0 b w' hh av' pi rho rho' hsplit ihrec =>
      intro hv
      have hnd' : noDescent w = false := by simpa using hnd
      have ivt : IsValid w' av' := isValid_tail w av hv hnd'
      have hb : 1 ≤ b := (noDescent_false_decomp hnd').2
      have hpiD : IsDyck pi := phi_isDyck w' av'
      have hpine : pi ≠ [] := phiPath_ne_nil w' av'
      have hpiV : validFrom pi 0 := ((isDyckAux_iff pi 0).mp hpiD).1
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
      have hle := isValid_head_le w av hv hnd'
      have hnoDD : hasDD rho = false := by
        have := phi_split_noDD w' av' ivt hh hle
        rw [hsplit] at this; simpa using this
      have hpiD' : IsDyck (rho ++ rho') := by rw [happ]; exact hpiD
      have hbound : hh ≤ numN pi := le_trans hle (tau_headD_le_numN w' av' ivt)
      have hnumN : numN rho = hh := by
        have := split_numN pi hh hbound; rw [hsplit] at this; simpa using this
      have hps : area pi = av'.sum := ihrec ivt
      rw [area_sandwich a b rho rho' hb hnoDD hbd hpiD', happ, hnumN, hps]
      have hcons : av = av.headD 0 :: av.tail := isValid_av_cons w av hv hnd'
      rw [hcons, List.sum_cons]


end Psi
