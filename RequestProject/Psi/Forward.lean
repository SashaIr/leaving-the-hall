import RequestProject.Psi.RiseComp

namespace Psi

/-! ## Bijectivity -/

/-- Domain of the bijection for size `n`: valid data `(w, av)` with `|w| = n - 1`. -/
def Dom (n : ℕ) : Set (List Bool × List ℕ) :=
  {p | p.1.length + 1 = n ∧ IsValid p.1 p.2}

/-- Codomain: Dyck paths of size `n`. -/
def Cod (n : ℕ) : Set (List Bool) :=
  {p | IsDyck p ∧ p.length = 2 * n}

/-- `Φ` maps the domain into the codomain: every reconstructed path from a valid
datum of "size `n`" is a Dyck path of size `n`.  This is the `MapsTo` part of the
bijectivity statement, and follows from `phi_isDyck` and `phi_size`. -/
theorem phi_mapsTo (n : ℕ) :
    Set.MapsTo (fun p : List Bool × List ℕ => phiPath p.1 p.2) (Dom n) (Cod n) := by
  rintro ⟨w, av⟩ ⟨hlen, _⟩
  refine ⟨phi_isDyck w av, ?_⟩
  rw [phi_size]; omega

/-! ### The forward map `Ψ` (`psiPath`)

`Ψ` is the explicit two-sided inverse of `Φ = phiPath` (Definition `def:psi`).
It is a computable recursion on a Dyck path `π`, validated to satisfy both
round-trips on all inputs up to size `7`. -/

/-- Auxiliary helper: `take m ++ drop n` never lengthens a list when `m ≤ n`. -/
theorem take_drop_len_le {α} (l : List α) (m n : ℕ) (h : m ≤ n) :
    (l.take m ++ l.drop n).length ≤ l.length := by
  rw [List.length_append, List.length_take, List.length_drop]; omega

/-- Greedy count of leading `UD` (= `[true, false]`) pairs. -/
def cUDraw : List Bool → ℕ
  | true :: false :: r => 1 + cUDraw r
  | _ => 0

/-- Number of leading `UD` pairs to strip in step `1` of `def:psi`: the greedy
count, capped down by one when `π = (UD)^a` exactly (so the remainder is
nonempty). -/
def cUD (π : List Bool) : ℕ :=
  let c := cUDraw π
  if 2 * c = π.length then c - 1 else c

/-- Index of the first `DD` (two consecutive East steps) in a path, if any.
Returns the index of the *first* of the two East steps. -/
def firstDDidx : List Bool → Option ℕ
  | false :: false :: _ => some 0
  | _ :: r => (firstDDidx r).map (· + 1)
  | [] => none

/-- The forward map `Ψ` (`def:psi`): from a decorated Dyck path `π`, produce the
datum `(w, av)`.  Strip `(UD)^a` and the following single `U`, leaving `rest`.
If `rest` has no `DD`, terminate (base word `0^a`).  Otherwise locate the pyramid
`U^b D^{b+1}` via the first `DD`: `i` its index, `L` the East-run length there,
`p` the preceding North-run; set `b := min p (L-1)`, `ρ := rest.take (i-b)`,
`ρ' := rest.drop (i+b+1)`; if `ρ ++ ρ'` is empty terminate with word `0^a 1^b`,
else emit block `0^a 1^b 0` and area entry `numN ρ`, recursing on `ρ ++ ρ'`. -/
def psiPath (π : List Bool) : List Bool × List ℕ :=
  let a := cUD π
  let rest := π.drop (2 * a + 1)
  match _h : firstDDidx rest with
  | none => (List.replicate a false, [0])
  | some i =>
     let b := min (((rest.take i).reverse.takeWhile id).length)
                  (((rest.drop i).takeWhile (· = false)).length - 1)
     let ρ := rest.take (i - b)
     let ρ' := rest.drop (i + b + 1)
     if _he : ρ ++ ρ' = [] then (List.replicate a false ++ List.replicate b true, [0])
     else
       let r := psiPath (ρ ++ ρ')
       (List.replicate a false ++ List.replicate b true ++ [false] ++ r.1, numN ρ :: r.2)
  termination_by π.length
  decreasing_by
    have hrest : rest ≠ [] := by
      intro hc; rw [hc] at _h; simp [firstDDidx] at _h
    have hpos : 0 < rest.length := List.length_pos_of_ne_nil hrest
    have hrl : rest.length = π.length - (2 * a + 1) := by simp [rest, List.length_drop]
    have hle : (ρ ++ ρ').length ≤ rest.length :=
      take_drop_len_le rest (i - b) (i + b + 1) (by omega)
    exact lt_of_le_of_lt hle (by omega)

/-! ### Computational helpers for `Ψ` -/

/-- `cUDraw` is additive over a leading `(UD)^a` block. -/
theorem cUDraw_fUD_append (a : ℕ) (t : List Bool) :
    cUDraw ((List.replicate a [true, false]).flatten ++ t) = a + cUDraw t := by
  induction a with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
      show cUDraw (true :: false :: ((List.replicate n [true, false]).flatten ++ t)) = _
      rw [cUDraw, ih]; omega

/-- `cUDraw` of `U :: L` is `0` when `L` starts with a North step. -/
theorem cUDraw_true_head (L : List Bool) (h : L.head? = some true) :
    cUDraw (true :: L) = 0 := by
  cases L with
  | nil => simp at h
  | cons y ys => simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

/-- `cUD` of a recursive step path is `a`. -/
theorem cUD_step (a b : ℕ) (ρ ρ' : List Bool) (hb : 1 ≤ b)
    (hρU : ρ = [] ∨ ρ.head? = some true) :
    cUD ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
          ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') = a := by
  set L := ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ' with hL
  have hLhead : L.head? = some true := by
    rcases hρU with h | h
    · subst h
      simp only [hL, List.nil_append]
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [List.replicate_succ]; rfl
    · cases ρ with
      | nil => simp at h
      | cons x xs =>
          simp only [List.head?_cons, Option.some.injEq] at h; subst h
          simp only [hL, List.cons_append, List.head?_cons]
  have hcr : cUDraw ((List.replicate a [true, false]).flatten ++ [true] ++ L) = a := by
    have hassoc : (List.replicate a [true, false]).flatten ++ [true] ++ L
        = (List.replicate a [true, false]).flatten ++ (true :: L) := by simp [List.append_assoc]
    rw [hassoc, cUDraw_fUD_append, cUDraw_true_head L hLhead, Nat.add_zero]
  rw [show (List.replicate a [true, false]).flatten ++ [true] ++ ρ
          ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
        = (List.replicate a [true, false]).flatten ++ [true] ++ L from by
        simp [hL, List.append_assoc]]
  rw [cUD, hcr, if_neg (by simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]; omega)]

/-- `firstDDidx` on a North step just shifts. -/
theorem firstDDidx_true (r : List Bool) :
    firstDDidx (true :: r) = (firstDDidx r).map (· + 1) := rfl

/-- `firstDDidx` finds a `DD` at position `0`. -/
theorem firstDDidx_ff (r : List Bool) : firstDDidx (false :: false :: r) = some 0 := rfl

/-- `firstDDidx` on `E U ...` shifts. -/
theorem firstDDidx_ft (r : List Bool) :
    firstDDidx (false :: true :: r) = (firstDDidx (true :: r)).map (· + 1) := rfl

/-- `firstDDidx (E :: L)` shifts when `L` starts with a North step. -/
theorem firstDDidx_false_headtrue (L : List Bool) (h : L.head? = some true) :
    firstDDidx (false :: L) = (firstDDidx L).map (· + 1) := by
  cases L with
  | nil => simp at h
  | cons y ys => simp only [List.head?_cons, Option.some.injEq] at h; subst h; rw [firstDDidx_ft]

/-- `firstDDidx` of `U^m` followed by a `DD` is `m`. -/
theorem firstDDidx_repl_true_DD (m : ℕ) (r : List Bool) :
    firstDDidx (List.replicate m true ++ false :: false :: r) = some m := by
  induction m with
  | zero => simp [firstDDidx_ff]
  | succ n ih => rw [List.replicate_succ, List.cons_append, firstDDidx_true, ih]; rfl

/-- Prepending a `DD`-free block whose junction stays clean shifts `firstDDidx`. -/
theorem firstDDidx_prepend (ρ t : List Bool) (j : ℕ)
    (hρ : hasDD ρ = false) (hhead : t.head? = some true) (ht : firstDDidx t = some j) :
    firstDDidx (ρ ++ t) = some (ρ.length + j) := by
  induction ρ with
  | nil => simpa using ht
  | cons x xs ih =>
      rw [hasDD_cons] at hρ
      have hxsDD : hasDD xs = false := (Bool.or_eq_false_iff.mp hρ).2
      have hihv := ih hxsDD
      cases x with
      | true =>
          rw [List.cons_append, firstDDidx_true, hihv]
          simp only [Option.map_some, List.length_cons]; congr 1; omega
      | false =>
          have h1 := (Bool.or_eq_false_iff.mp hρ).1
          have hLhead : (xs ++ t).head? = some true := by
            cases xs with
            | nil => simpa using hhead
            | cons z zs =>
                simp only [List.head?_cons] at h1
                have : z = true := by
                  by_contra hc; simp only [Bool.not_eq_true] at hc; subst hc; simp at h1
                subst this; simp
          rw [List.cons_append, firstDDidx_false_headtrue _ hLhead, hihv]
          simp only [Option.map_some, List.length_cons]; congr 1; omega

/-- `takeWhile id` passes through a leading `U^m`. -/
theorem takeWhile_repl_true (m : ℕ) (X : List Bool) :
    (List.replicate m true ++ X).takeWhile id = List.replicate m true ++ X.takeWhile id := by
  induction m with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, List.takeWhile_cons]; simp

/-- `takeWhile (· = false)` passes through a leading `E^m`. -/
theorem takeWhile_repl_false (m : ℕ) (X : List Bool) :
    (List.replicate m false ++ X).takeWhile (· = false)
      = List.replicate m false ++ X.takeWhile (· = false) := by
  induction m with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, List.takeWhile_cons]; simp

/-- No leading North run when the head is not a North step. -/
theorem takeWhile_id_head_ne (L : List Bool) (h : L.head? ≠ some true) :
    (L.takeWhile id).length = 0 := by
  cases L with
  | nil => simp
  | cons y ys =>
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      have : y = false := by cases y <;> simp_all
      subst this; simp

/-- No leading East run when the head is not an East step. -/
theorem takeWhile_false_head_ne (L : List Bool) (h : L.head? ≠ some false) :
    (L.takeWhile (· = false)).length = 0 := by
  cases L with
  | nil => simp
  | cons y ys =>
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      have : y = true := by cases y <;> simp_all
      subst this; simp

/-- The first piece of `splitAtRow` is a prefix, so shares the head of the path. -/
theorem splitAtRow_fst_head (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1 = [] ∨ (splitAtRow p h).1.head? = p.head? := by
  fun_induction splitAtRow p h with
  | case1 p => left; rfl
  | case2 h => left; rfl
  | case3 rest => right; rfl
  | case4 rest hx => right; rfl
  | case5 rest h ρ ρ' heq ih => right; rw [heq] at *; rfl
  | case6 rest h ρ ρ' heq ih => right; rw [heq] at *; rfl

/-- If the row is positive and the path nonempty, the first piece is nonempty. -/
theorem splitAtRow_fst_ne_nil (p : List Bool) (h : ℕ) (hh : h ≠ 0) (hp : p ≠ []) :
    (splitAtRow p h).1 ≠ [] := by
  fun_induction splitAtRow p h with
  | case1 p => omega
  | case2 h => simp at hp
  | case3 rest => simp
  | case4 rest hx => simp
  | case5 rest h ρ ρ' heq ih => rw [heq] at *; simp
  | case6 rest h ρ ρ' heq ih => rw [heq] at *; simp

/-- Maximality of the split: `ρ` never ends with a North step whose following
step (the head of `ρ'`) is an East step. -/
theorem splitAtRow_max (p : List Bool) (h : ℕ) :
    (splitAtRow p h).1.getLast? ≠ some true ∨ (splitAtRow p h).2.head? ≠ some false := by
  fun_induction splitAtRow p h with
  | case1 p => left; simp
  | case2 h => left; simp
  | case3 rest => left; simp
  | case4 rest hx =>
      right
      cases rest with
      | nil => simp
      | cons b u => cases b with
        | false => exact (hx u rfl).elim
        | true => simp
  | case5 rest h ρ ρ' heq ih =>
      rw [heq] at ih; dsimp only at ih ⊢
      by_cases hρ : ρ = []
      · right
        have hr : rest = [] := by
          by_contra hc
          exact splitAtRow_fst_ne_nil rest (h + 1) (by omega) hc (by rw [heq]; exact hρ)
        have h2 : ρ' = [] := by
          have h3 := splitAtRow_append rest (h + 1)
          rw [heq, hr] at h3; exact (List.append_eq_nil_iff.mp h3).2
        rw [h2]; simp
      · rcases ih with hL | hR
        · left
          obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hρ
          rw [List.getLast?_cons_cons]; exact hL
        · right; exact hR
  | case6 rest h ρ ρ' heq ih =>
      rw [heq] at ih; dsimp only at ih ⊢
      rcases ih with hL | hR
      · left
        by_cases hρ : ρ = []
        · subst hρ; simp
        · obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hρ
          rw [List.getLast?_cons_cons]; exact hL
      · right; exact hR

/-- An all-East (`numN = 0`) `DD`-free list is `[]` or `[E]`. -/
theorem allfalse_noDD (xs : List Bool) (h0 : numN xs = 0) (hd : hasDD xs = false) :
    xs = [] ∨ xs = [false] := by
  match xs with
  | [] => left; rfl
  | [a] =>
      right; cases a with
      | false => rfl
      | true => rw [numN_cons_true] at h0; omega
  | a :: b :: rest =>
      exfalso
      have ha : a = false := by
        cases a with | false => rfl | true => rw [numN_cons_true] at h0; omega
      have hb : b = false := by
        cases b with
        | false => rfl
        | true => subst ha; rw [numN_cons_false, numN_cons_true] at h0; omega
      subst ha; subst hb; rw [hasDD_cons] at hd; simp at hd

/-- Inverse of the split: reassembling `ρ ++ ρ'` and cutting at row `numN ρ`
recovers `(ρ, ρ')`, provided `ρ` is `DD`-free, does not start with an isolated
East step (`numN ρ = 0 → ρ = []`), and the maximality condition holds. -/
theorem splitAtRow_reconstruct (ρ ρ' : List Bool)
    (hne0 : numN ρ = 0 → ρ = []) (hρDD : hasDD ρ = false)
    (hmax : ρ.getLast? ≠ some true ∨ ρ'.head? ≠ some false) :
    splitAtRow (ρ ++ ρ') (numN ρ) = (ρ, ρ') := by
  induction ρ with
  | nil => simp [numN, splitAtRow]
  | cons x xs ih =>
      have hxsDD : hasDD xs = false := by
        have h := hρDD; rw [hasDD_cons] at h; exact (Bool.or_eq_false_iff.mp h).2
      cases x with
      | false =>
          rw [numN_cons_false]
          have hxsne : numN xs ≠ 0 := fun h0 => by
            have := hne0 (by rw [numN_cons_false]; exact h0); simp at this
          have hxsnil : xs ≠ [] := fun h => by rw [h] at hxsne; simp [numN] at hxsne
          obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxsnil
          obtain ⟨m, hm⟩ : ∃ m, numN (y :: ys) = m + 1 := ⟨numN (y :: ys) - 1, by omega⟩
          rw [hm]
          show splitAtRow (false :: (y :: ys ++ ρ')) (m + 1) = _
          have hmaxxs : (y :: ys).getLast? ≠ some true ∨ ρ'.head? ≠ some false := by
            rcases hmax with hm2 | hm2
            · left; rwa [List.getLast?_cons_cons] at hm2
            · right; exact hm2
          have hih := ih (fun h => by rw [h] at hm; simp at hm) hxsDD hmaxxs
          rw [hm] at hih; rw [splitAtRow, hih]
      | true =>
          rw [numN_cons_true]
          rcases Nat.eq_zero_or_pos (numN xs) with h0 | hpos
          · rw [h0]
            rcases allfalse_noDD xs h0 hxsDD with rfl | rfl
            · have hh : ρ'.head? ≠ some false := Or.resolve_left hmax (by simp)
              show splitAtRow (true :: ρ') 1 = ([true], ρ')
              cases ρ' with
              | nil => simp [splitAtRow]
              | cons z zs =>
                  simp only [List.head?_cons, ne_eq, Option.some.injEq] at hh
                  have : z = true := by cases z with | false => simp at hh | true => rfl
                  subst this; simp [splitAtRow]
            · show splitAtRow (true :: false :: ρ') 1 = ([true, false], ρ')
              simp [splitAtRow]
          · obtain ⟨m, hm⟩ : ∃ m, numN xs = m + 1 := ⟨numN xs - 1, by omega⟩
            rw [hm]
            have hxsnil : xs ≠ [] := fun h => by rw [h] at hm; simp [numN] at hm
            obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxsnil
            show splitAtRow (true :: (y :: ys ++ ρ')) (m + 1 + 1) = _
            have hmaxxs : (y :: ys).getLast? ≠ some true ∨ ρ'.head? ≠ some false := by
              rcases hmax with hm2 | hm2
              · left; rwa [List.getLast?_cons_cons] at hm2
              · right; exact hm2
            have hih := ih (fun h => by rw [h] at hm; simp at hm) hxsDD hmaxxs
            rw [hm] at hih; rw [splitAtRow, hih]

/-- A word with no descent is `0^l 1^k`. -/
theorem noDescent_true_eq (w : List Bool) (h : noDescent w = true) :
    w = List.replicate (w.filter (· = false)).length false
          ++ List.replicate (w.filter id).length true := by
  induction w with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => cases a <;> simp [List.filter]
      | cons b rest =>
          rw [noDescent] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨hab, hnd⟩ := h
          have iht := ih hnd
          cases a with
          | false =>
              conv_lhs => rw [iht]
              simp [List.filter_cons, List.replicate_succ]
          | true =>
              simp only [Bool.not_true, Bool.false_or] at hab
              subst hab
              have hnf' : (List.filter (· = false) (true :: rest)).length = 0 := by
                by_contra hc
                obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hc
                rw [hn, List.replicate_succ] at iht
                simp at iht
              have iht2 : true :: rest
                  = List.replicate (List.filter id (true :: rest)).length true := by
                conv_lhs => rw [iht]
                rw [hnf']; simp
              have hnfw : (List.filter (· = false) (true :: true :: rest)).length = 0 := by
                rw [List.filter_cons]; simpa using hnf'
              have hntw : (List.filter id (true :: true :: rest)).length
                  = (List.filter id (true :: rest)).length + 1 := by
                rw [List.filter_cons]; simp
              rw [hnfw, hntw]
              simp only [List.replicate_zero, List.nil_append, List.replicate_succ]
              rw [← iht2]

/-- `Ψ` on a base path `(UD)^l U^{k+1} D^{k+1}` returns `(0^l 1^k, [0])`. -/
theorem psiPath_base (l k : ℕ) :
    psiPath ((List.replicate l [true, false]).flatten
              ++ List.replicate (k + 1) true ++ List.replicate (k + 1) false)
      = (List.replicate l false ++ List.replicate k true, [0]) := by
  cases k with
  | zero =>
      set P := (List.replicate l [true, false]).flatten
              ++ List.replicate (0 + 1) true ++ List.replicate (0 + 1) false with hPdef
      have hPeq : P = ((List.replicate l [true, false]).flatten ++ [true]) ++ [false] := by
        rw [hPdef]; simp [List.append_assoc]
      have hcr : cUDraw P = l + 1 := by
        rw [hPeq, show ((List.replicate l [true, false]).flatten ++ [true]) ++ [false]
            = (List.replicate l [true, false]).flatten ++ [true, false] from by
            simp [List.append_assoc], cUDraw_fUD_append]; rfl
      have hlen : P.length = 2 * l + 2 := by
        rw [hPdef]; simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega
      have hcUD : cUD P = l := by rw [cUD, hcr, if_pos (by omega)]; omega
      have hrest : List.drop (2 * l + 1) P = [false] := by
        rw [hPeq, show 2 * l + 1 = ((List.replicate l [true, false]).flatten ++ [true]).length from by
          simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega, List.drop_left]
      rw [psiPath.eq_1, hcUD, hrest]
      split
      · simp
      · next i h => rw [show firstDDidx [false] = none from rfl] at h; exact absurd h (by simp)
  | succ k' =>
      set P := (List.replicate l [true, false]).flatten
              ++ List.replicate (k' + 1 + 1) true ++ List.replicate (k' + 1 + 1) false with hPdef
      set rest := List.replicate (k' + 1) true ++ List.replicate (k' + 1 + 1) false with hrestdef
      have hcr : cUDraw P = l := by
        rw [hPdef, List.append_assoc, cUDraw_fUD_append,
          show List.replicate (k' + 1 + 1) true = true :: true :: List.replicate k' true from by
            rw [List.replicate_succ, List.replicate_succ]]
        rfl
      have hlen : P.length = 2 * l + 2 * (k' + 2) := by
        rw [hPdef]; simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega
      have hcUD : cUD P = l := by rw [cUD, hcr, if_neg (by omega)]
      have hrestP : List.drop (2 * l + 1) P = rest := by
        rw [hPdef, hrestdef,
          show (List.replicate l [true, false]).flatten ++ List.replicate (k' + 1 + 1) true
              ++ List.replicate (k' + 1 + 1) false
            = ((List.replicate l [true, false]).flatten ++ [true])
              ++ (List.replicate (k' + 1) true ++ List.replicate (k' + 1 + 1) false) from by
            rw [show List.replicate (k' + 1 + 1) true = [true] ++ List.replicate (k' + 1) true from by
              rw [List.replicate_succ]; rfl]
            simp [List.append_assoc],
          show 2 * l + 1 = ((List.replicate l [true, false]).flatten ++ [true]).length from by
            simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega, List.drop_left]
      have hfdd : firstDDidx rest = some (k' + 1) := by
        rw [hrestdef, show List.replicate (k' + 1 + 1) false
            = false :: false :: List.replicate k' false from by
          rw [List.replicate_succ, List.replicate_succ]]
        exact firstDDidx_repl_true_DD (k' + 1) _
      have htk : rest.take (k' + 1) = List.replicate (k' + 1) true := by
        rw [hrestdef, List.take_append_of_le_length (by simp)]; simp
      have hdp : rest.drop (k' + 1) = List.replicate (k' + 1 + 1) false := by
        rw [hrestdef, List.drop_append_of_le_length (by simp)]; simp
      have hbc : min ((rest.take (k' + 1)).reverse.takeWhile id).length
                     (((rest.drop (k' + 1)).takeWhile (· = false)).length - 1) = k' + 1 := by
        rw [htk, hdp, List.reverse_replicate]; simp
      have hρrec : rest.take (k' + 1 - (k' + 1)) = [] := by simp
      have hρ'rec : rest.drop (k' + 1 + (k' + 1) + 1) = [] := by
        rw [hrestdef]; apply List.drop_eq_nil_of_le
        simp only [List.length_append, List.length_replicate]; omega
      rw [psiPath.eq_1, hcUD, hrestP]
      split
      · next h => rw [hfdd] at h; exact absurd h (by simp)
      · next i h =>
          rw [hfdd] at h; injection h with hh; subst hh
          simp only [hbc, hρrec, hρ'rec]
          rw [dif_pos (by simp)]

/-- `Ψ` on a recursive path `(UD)^a U ρ U^b D^{b+1} ρ'` peels off the block
`0^a 1^b 0` and area entry `numN ρ`, recursing on `ρ ++ ρ'`.  Requires: `b ≥ 1`,
`ρ` starts with a North step (or is empty), `ρ` has no `DD`, the maximality
condition, and `ρ ++ ρ'` nonempty. -/
theorem psiPath_step (a b : ℕ) (ρ ρ' : List Bool)
    (hb : 1 ≤ b)
    (hρU : ρ = [] ∨ ρ.head? = some true)
    (hρDD : hasDD ρ = false)
    (hmax : ρ.getLast? ≠ some true ∨ ρ'.head? ≠ some false)
    (hne : ρ ++ ρ' ≠ []) :
    psiPath ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
              ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
      = (List.replicate a false ++ List.replicate b true ++ [false] ++ (psiPath (ρ ++ ρ')).1,
         numN ρ :: (psiPath (ρ ++ ρ')).2) := by
  have hcUD : cUD ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
              ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') = a :=
    cUD_step a b ρ ρ' hb hρU
  set L := ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ' with hLdef
  have hLsplit1 : L = (ρ ++ List.replicate b true) ++ (List.replicate (b + 1) false ++ ρ') := by
    rw [hLdef]; simp [List.append_assoc]
  have hLsplit2 : L = ρ ++ (List.replicate b true ++ List.replicate (b + 1) false ++ ρ') := by
    rw [hLdef]; simp [List.append_assoc]
  have hLsplit3 : L = (ρ ++ List.replicate b true ++ List.replicate (b + 1) false) ++ ρ' := by
    rw [hLdef]
  have hrestL : List.drop (2 * a + 1)
      ((List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') = L := by
    have hPeq : (List.replicate a [true, false]).flatten ++ [true] ++ ρ
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
        = ((List.replicate a [true, false]).flatten ++ [true]) ++ L := by
      rw [hLdef]; simp [List.append_assoc]
    rw [hPeq, show 2 * a + 1 = ((List.replicate a [true, false]).flatten ++ [true]).length from by
      simp [List.length_flatten, List.map_replicate, List.sum_replicate]; omega, List.drop_left]
  have ht_head : (List.replicate b true ++ List.replicate (b + 1) false ++ ρ').head? = some true := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [List.replicate_succ]; simp
  have ht_fdd : firstDDidx (List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
      = some b := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hEE : List.replicate (b' + 1 + 1) false ++ ρ'
        = false :: false :: (List.replicate b' false ++ ρ') := by
      rw [show b' + 1 + 1 = b' + 2 from rfl, List.replicate_succ, List.replicate_succ]; rfl
    rw [List.append_assoc, hEE, firstDDidx_repl_true_DD]
  have hfdd : firstDDidx L = some (ρ.length + b) := by
    rw [hLsplit2]; exact firstDDidx_prepend ρ _ b hρDD ht_head ht_fdd
  have htake_i0 : L.take (ρ.length + b) = ρ ++ List.replicate b true := by
    rw [hLsplit1, show ρ.length + b = (ρ ++ List.replicate b true).length from by simp,
      List.take_left]
  have hdrop_i0 : L.drop (ρ.length + b) = List.replicate (b + 1) false ++ ρ' := by
    rw [hLsplit1, show ρ.length + b = (ρ ++ List.replicate b true).length from by simp,
      List.drop_left]
  have hρrec : L.take (ρ.length + b - b) = ρ := by
    rw [show ρ.length + b - b = ρ.length from by omega, hLsplit2, List.take_left]
  have hρ'rec : L.drop (ρ.length + b + b + 1) = ρ' := by
    rw [hLsplit3, show ρ.length + b + b + 1
      = (ρ ++ List.replicate b true ++ List.replicate (b + 1) false).length from by
        simp [List.append_assoc]; omega, List.drop_left]
  have hbc : min ((L.take (ρ.length + b)).reverse.takeWhile id).length
                 (((L.drop (ρ.length + b)).takeWhile (· = false)).length - 1) = b := by
    rw [htake_i0, hdrop_i0, List.reverse_append, List.reverse_replicate, takeWhile_repl_true,
        takeWhile_repl_false]
    simp only [List.length_append, List.length_replicate]
    rcases hmax with hm | hm
    · have : (ρ.reverse.takeWhile id).length = 0 :=
        takeWhile_id_head_ne _ (by rw [List.head?_reverse]; exact hm)
      omega
    · have : (ρ'.takeWhile (· = false)).length = 0 := takeWhile_false_head_ne _ hm
      omega
  rw [psiPath.eq_1, hcUD, hrestL]
  split
  · next h => rw [hfdd] at h; exact absurd h (by simp)
  · next i h =>
      rw [hfdd] at h; injection h with hh; subst hh
      simp only [hbc, hρrec, hρ'rec]
      rw [dif_neg hne]

/-- Round-trip `Ψ ∘ Φ = id` on valid data (the injectivity content). -/
theorem psi_phi (w : List Bool) (av : List ℕ) (h : IsValid w av) :
    psiPath (phiPath w av) = (w, av) := by
  revert h
  fun_induction phiPath w av with
  | case1 w av hnd =>
      intro hv
      have hnd' : noDescent w = true := by simpa using hnd
      set l := (w.filter (· = false)).length with hl
      set k := (w.filter id).length with hk
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
      rw [psiPath_base l k]
      have hw : w = List.replicate l false ++ List.replicate k true := noDescent_true_eq w hnd'
      rw [← hw]
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
      have hpihead : pi.head? = some true := dyck_head pi hpiD hpine
      have hρU : rho = [] ∨ rho.head? = some true := by
        rcases splitAtRow_fst_head pi hh with h | h
        · left; rw [hsplit] at h; simpa using h
        · right; rw [hsplit] at h; simp only at h; rw [h, hpihead]
      have hmax : rho.getLast? ≠ some true ∨ rho'.head? ≠ some false := by
        rcases splitAtRow_max pi hh with h | h
        · left; rw [hsplit] at h; simpa using h
        · right; rw [hsplit] at h; simpa using h
      have hne : rho ++ rho' ≠ [] := by rw [happ]; exact hpine
      rw [psiPath_step a b rho rho' hb hρU hnoDD hmax hne, happ, ihrec ivt, hnumN]
      have hav : av = hh :: av' := isValid_av_cons w av hv hnd'
      refine Prod.ext ?_ ?_
      · show List.replicate a false ++ List.replicate b true ++ [false] ++ w' = w
        conv_rhs => rw [(noDescent_false_decomp hnd').1]
        simp only [List.append_assoc, List.singleton_append]
        rfl
      · show hh :: av' = av
        rw [hav]


end Psi
