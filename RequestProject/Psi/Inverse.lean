import RequestProject.Psi.Forward

namespace Psi

/-! ### Run-structure helpers for surjectivity -/

/-- `takeWhile id` of a `Bool` list is an all-North run. -/
theorem takeWhile_id_replicate (xs : List Bool) :
    xs.takeWhile id = List.replicate (xs.takeWhile id).length true := by
  induction xs with
  | nil => simp
  | cons a t ih => cases a with
    | false => simp
    | true => rw [show (true :: t).takeWhile id = true :: t.takeWhile id from rfl,
                  List.length_cons, List.replicate_succ, ← ih]

/-- `takeWhile (· = false)` of a `Bool` list is an all-East run. -/
theorem takeWhile_false_replicate (xs : List Bool) :
    xs.takeWhile (· = false) = List.replicate (xs.takeWhile (· = false)).length false := by
  induction xs with
  | nil => simp
  | cons a t ih => cases a with
    | true => simp
    | false => rw [show (false :: t).takeWhile (· = false) = false :: t.takeWhile (· = false) from rfl,
                  List.length_cons, List.replicate_succ, ← ih]

/-- `dropWhile` is a `drop` by the `takeWhile` length. -/
theorem dropWhile_eq_drop {α} (p : α → Bool) (l : List α) :
    l.dropWhile p = l.drop (l.takeWhile p).length := by
  have h := List.takeWhile_append_dropWhile (p := p) (l := l)
  calc l.dropWhile p = (l.takeWhile p ++ l.dropWhile p).drop (l.takeWhile p).length := by
          rw [List.drop_left]
    _ = l.drop (l.takeWhile p).length := by rw [h]

theorem head_dropWhile_id (l : List Bool) : (l.dropWhile id).head? ≠ some true := by
  induction l with
  | nil => simp
  | cons a t ih => cases a with | true => simpa using ih | false => simp

theorem head_dropWhile_false (l : List Bool) : (l.dropWhile (· = false)).head? ≠ some false := by
  induction l with
  | nil => simp
  | cons a t ih => cases a with | false => simpa using ih | true => simp

/-- Leading North-run split. -/
theorem lead_true_split (C : List Bool) :
    C = List.replicate ((C.takeWhile id).length) true ++ C.dropWhile id := by
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := id) (l := C), takeWhile_id_replicate]

/-- Leading East-run split. -/
theorem lead_false_split (B : List Bool) :
    B = List.replicate ((B.takeWhile (· = false)).length) false ++ B.dropWhile (· = false) := by
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := (· = false)) (l := B),
    takeWhile_false_replicate]

/-- Trailing North-run split (with the pre-run part not ending in a North step). -/
theorem trail_true_split (A : List Bool) :
    A = A.take (A.length - (A.reverse.takeWhile id).length)
          ++ List.replicate ((A.reverse.takeWhile id).length) true
      ∧ (A.take (A.length - (A.reverse.takeWhile id).length)).getLast? ≠ some true := by
  set p := (A.reverse.takeWhile id).length with hp
  have hrev : A.reverse = List.replicate p true ++ A.reverse.dropWhile id := lead_true_split A.reverse
  have hdw : A.reverse.dropWhile id = A.reverse.drop p := by rw [dropWhile_eq_drop, hp]
  have hAeq : A = (A.reverse.drop p).reverse ++ List.replicate p true := by
    have := congrArg List.reverse hrev
    rw [List.reverse_reverse, List.reverse_append, List.reverse_replicate, hdw] at this
    exact this
  have hdrev : (A.reverse.drop p).reverse = A.take (A.length - p) := by
    rw [List.reverse_drop, List.reverse_reverse, List.length_reverse]
  refine ⟨by rw [hdrev] at hAeq; exact hAeq, ?_⟩
  rw [hdrev] at hAeq
  have : (A.take (A.length - p)).getLast? = (A.reverse.drop p).head? := by
    rw [← hdrev, List.getLast?_reverse]
  rw [this, ← hdw]; exact head_dropWhile_id _

/-- Case analysis for `firstDDidx` on a two-element-plus prefix. -/
theorem firstDDidx_key (a b : Bool) (u : List Bool) (i : ℕ)
    (h : firstDDidx (a :: b :: u) = some i) :
    (a = false ∧ b = false ∧ i = 0) ∨
      (∃ j, firstDDidx (b :: u) = some j ∧ i = j + 1 ∧ ¬(a = false ∧ b = false)) := by
  cases a with
  | true =>
      right; rw [firstDDidx_true] at h
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨j, hj, rfl, by simp⟩
  | false => cases b with
    | false => left; rw [firstDDidx_ff] at h; exact ⟨rfl, rfl, (Option.some.inj h).symm⟩
    | true =>
        right; rw [firstDDidx_ft] at h
        obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨j, hj, rfl, by simp⟩

/-- The `DD` lies within the path bounds. -/
theorem firstDDidx_lt (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    i + 1 < rest.length := by
  induction rest generalizing i with
  | nil => simp [firstDDidx] at h
  | cons a t ih =>
      cases t with
      | nil => rw [show firstDDidx [a] = none from by cases a <;> rfl] at h; simp at h
      | cons b u =>
          rcases firstDDidx_key a b u i h with ⟨rfl, rfl, rfl⟩ | ⟨j, hj, rfl, _⟩
          · simp
          · have := ih j hj; simp only [List.length_cons] at this ⊢; omega

/-- The path drops to two consecutive East steps at the `DD`. -/
theorem firstDDidx_drop_ff (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    ∃ r, rest.drop i = false :: false :: r := by
  induction rest generalizing i with
  | nil => simp [firstDDidx] at h
  | cons a t ih =>
      cases t with
      | nil => rw [show firstDDidx [a] = none from by cases a <;> rfl] at h; simp at h
      | cons b u =>
          rcases firstDDidx_key a b u i h with ⟨rfl, rfl, rfl⟩ | ⟨j, hj, rfl, _⟩
          · exact ⟨u, rfl⟩
          · obtain ⟨r, hr⟩ := ih j hj; exact ⟨r, by rw [List.drop_succ_cons]; exact hr⟩

/-- No `DD` occurs strictly before the first one. -/
theorem firstDDidx_take_noDD (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    hasDD (rest.take i) = false := by
  induction rest generalizing i with
  | nil => simp [firstDDidx] at h
  | cons a t ih =>
      cases t with
      | nil => rw [show firstDDidx [a] = none from by cases a <;> rfl] at h; simp at h
      | cons b u =>
          rcases firstDDidx_key a b u i h with ⟨rfl, rfl, rfl⟩ | ⟨j, hj, rfl, hne⟩
          · rfl
          · rw [List.take_succ_cons, hasDD_cons]
            have ihv := ih j hj
            cases j with
            | zero => simp [hasDD]
            | succ n =>
                rw [List.take_succ_cons] at ihv ⊢
                rw [List.head?_cons]
                have hand : (a == false && some b == some false) = false := by
                  by_cases ha : a = false <;> by_cases hb : b = false <;> simp_all
                rw [hand, Bool.false_or]; exact ihv

/-- The step just before the first `DD` is a North step. -/
theorem firstDDidx_prev_true (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) (hi : 1 ≤ i) :
    (rest.take i).getLast? = some true := by
  induction rest generalizing i with
  | nil => simp [firstDDidx] at h
  | cons a t ih =>
      cases t with
      | nil => rw [show firstDDidx [a] = none from by cases a <;> rfl] at h; simp at h
      | cons b u =>
          rcases firstDDidx_key a b u i h with ⟨rfl, rfl, rfl⟩ | ⟨j, hj, rfl, hne⟩
          · omega
          · rw [List.take_succ_cons]
            cases j with
            | zero =>
                have hbf : b = false := by
                  rcases firstDDidx_key b (u.headD false) (u.tail) 0 (by
                    cases u with
                    | nil => simp [firstDDidx] at hj
                    | cons c v => simpa using hj) with ⟨hb, _, _⟩ | ⟨_, _, hc, _⟩
                  · exact hb
                  · omega
                have haf : a = true := by
                  by_contra hc; simp only [Bool.not_eq_true] at hc; exact hne ⟨hc, hbf⟩
                subst haf; simp
            | succ n =>
                rw [List.take_succ_cons, List.getLast?_cons_cons]
                have := ih (n + 1) hj (by omega)
                rw [List.take_succ_cons] at this
                exact this

/-- **Run-structure decomposition** (`some`-branch of `Ψ`): if `rest` starts with a
North step and has a first `DD` at index `i`, then with `b`, `ρ = rest.take (i-b)`,
`ρ' = rest.drop (i+b+1)` as `Ψ` extracts, `rest = ρ U^b D^{b+1} ρ'` with `ρ` `DD`-free,
the maximality condition, `b ≥ 1`, and `ρ` `[]` or starting North. -/
theorem psi_rest_struct (rest : List Bool) (i p L b : ℕ)
    (h : firstDDidx rest = some i) (hstart : rest.head? = some true)
    (hp : p = ((rest.take i).reverse.takeWhile id).length)
    (hL : L = ((rest.drop i).takeWhile (· = false)).length)
    (hb : b = min p (L - 1)) :
    rest = rest.take (i - b) ++ List.replicate b true ++ List.replicate (b + 1) false
             ++ rest.drop (i + b + 1)
      ∧ hasDD (rest.take (i - b)) = false
      ∧ ((rest.take (i - b)).getLast? ≠ some true ∨ (rest.drop (i + b + 1)).head? ≠ some false)
      ∧ 1 ≤ b
      ∧ (numN (rest.take (i - b)) = 0 → rest.take (i - b) = []) := by
  have hiLt : i + 1 < rest.length := firstDDidx_lt rest i h
  have hAlen : (rest.take i).length = i := by rw [List.length_take]; omega
  obtain ⟨htrailA, hgl⟩ := trail_true_split (rest.take i)
  rw [hAlen, ← hp] at htrailA hgl
  have hAtake : (rest.take i).take (i - p) = rest.take (i - p) := by rw [List.take_take]; congr 1; omega
  rw [hAtake] at htrailA hgl
  have hleadB := lead_false_split (rest.drop i)
  rw [← hL] at hleadB
  set B1 := (rest.drop i).dropWhile (· = false) with hB1
  have hB1head : B1.head? ≠ some false := head_dropWhile_false _
  have hL2 : 2 ≤ L := by
    obtain ⟨r, hr⟩ := firstDDidx_drop_ff rest i h
    rw [hL, hr]; simp [List.takeWhile]
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exfalso; obtain ⟨r, hr⟩ := firstDDidx_drop_ff rest i h
      rw [h0, List.drop_zero] at hr; rw [hr] at hstart; simp at hstart
    · exact hpos
  have hpi : p ≤ i := by
    rw [hp]
    have := (List.takeWhile_sublist (l := (rest.take i).reverse) id).length_le
    rw [List.length_reverse, hAlen] at this; exact this
  have hp1 : 1 ≤ p := by
    have hgt : (rest.take i).getLast? = some true := firstDDidx_prev_true rest i h hi1
    have hrh : (rest.take i).reverse.head? = some true := by rw [List.head?_reverse]; exact hgt
    obtain ⟨t, ht⟩ : ∃ t, (rest.take i).reverse = true :: t := by
      cases hc : (rest.take i).reverse with
      | nil => rw [hc] at hrh; simp at hrh
      | cons x xs => rw [hc] at hrh; simp only [List.head?_cons, Option.some.injEq] at hrh
                     subst hrh; exact ⟨xs, rfl⟩
    rw [hp, ht]; simp [List.takeWhile]
  have hb1 : 1 ≤ b := by rw [hb]; omega
  have hlenip : (rest.take (i - p)).length = i - p := by rw [List.length_take]; omega
  have hG1 : rest.take (i - b) = rest.take (i - p) ++ List.replicate (p - b) true := by
    have ht : rest.take (i - b) = (rest.take i).take (i - b) := by rw [List.take_take]; congr 1; omega
    rw [ht, htrailA, List.take_append, hlenip, show i - b - (i - p) = p - b from by omega,
      List.take_of_length_le (by rw [hlenip]; omega), List.take_replicate, Nat.min_eq_left (by omega)]
  have hG2 : rest.drop (i + b + 1) = List.replicate (L - b - 1) false ++ B1 := by
    have hdd : rest.drop (i + b + 1) = (rest.drop i).drop (b + 1) := by rw [List.drop_drop]; congr 1
    rw [hdd, hleadB, List.drop_append_of_le_length (by rw [List.length_replicate]; omega),
      List.drop_replicate]
    exact congrArg (fun n => List.replicate n false ++ B1) (by omega)
  refine ⟨?_, ?_, ?_, hb1, ?_⟩
  · conv_lhs => rw [← List.take_append_drop i rest, htrailA, hleadB]
    rw [hG1, hG2,
      show List.replicate p true = List.replicate (p - b) true ++ List.replicate b true from by
        rw [← List.replicate_add]; congr 1; omega,
      show List.replicate L false = List.replicate (b + 1) false ++ List.replicate (L - b - 1) false from by
        rw [← List.replicate_add]; congr 1; omega]
    simp only [List.append_assoc]
  · have hnoA : hasDD (rest.take i) = false := firstDDidx_take_noDD rest i h
    have hpre : rest.take i = rest.take (i - b) ++ (rest.take i).drop (i - b) := by
      rw [show rest.take (i - b) = (rest.take i).take (i - b) from by rw [List.take_take]; congr 1; omega,
        List.take_append_drop]
    rw [hpre] at hnoA
    exact hasDD_prefix _ _ hnoA
  · rcases (by omega : b = p ∨ b = L - 1) with hbp | hbL
    · left; rw [hG1, show p - b = 0 from by omega]; simpa using hgl
    · right; rw [hG2, show L - b - 1 = 0 from by omega]; simpa using hB1head
  · intro h0
    by_contra hc
    have hib : 0 < i - b := by
      have := List.length_pos_of_ne_nil hc; rw [List.length_take] at this; omega
    have hh : (rest.take (i - b)).head? = rest.head? := by rw [List.head?_take, if_neg (by omega)]
    obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hc
    rw [hys] at hh; simp only [List.head?_cons] at hh
    rw [hstart] at hh
    have hy : y = true := Option.some.inj hh
    subst hy; rw [hys, numN_cons_true] at h0; omega

/-! ### Leading `(UD)^a` decomposition of a Dyck path -/

/-- `cUDraw` peels a genuine `(UD)^a` prefix. -/
theorem cUDraw_prefix (π : List Bool) :
    π = (List.replicate (cUDraw π) [true, false]).flatten ++ π.drop (2 * cUDraw π) := by
  fun_induction cUDraw π with
  | case1 r ih1 =>
      rw [List.replicate_add, List.flatten_append]
      simp only [List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [show 2 * (1 + cUDraw r) = 2 * cUDraw r + 1 + 1 from by ring,
        List.drop_succ_cons, List.drop_succ_cons, List.append_assoc, ← ih1]; rfl
  | case2 x hx => simp

theorem cUDraw_len (π : List Bool) : 2 * cUDraw π ≤ π.length := by
  conv_rhs => rw [cUDraw_prefix π]
  rw [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate]; simp; omega

theorem fUD_len (n : ℕ) : (List.replicate n [true, false]).flatten.length = 2 * n := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; simp; ring

theorem fUD_drop_last (n : ℕ) (hn : 1 ≤ n) :
    (List.replicate n [true, false]).flatten.drop (2 * n - 1) = [false] := by
  have hsplit : (List.replicate n [true, false]).flatten
      = (List.replicate (n - 1) [true, false]).flatten ++ [true, false] := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega, List.replicate_add]
    simp [List.flatten_append]
  rw [hsplit, List.drop_append, fUD_len,
    List.drop_eq_nil_of_le (by rw [fUD_len]; omega), List.nil_append,
    show 2 * n - 1 - 2 * (n - 1) = 1 from by omega]; rfl

theorem dyck_drop_fUD (π : List Bool) (hd : IsDyck π) : IsDyck (π.drop (2 * cUDraw π)) := by
  have hpre := cUDraw_prefix π
  rw [IsDyck, isDyckAux_iff] at hd ⊢
  obtain ⟨hv, he⟩ := hd
  conv at hv => rw [hpre]
  conv at he => rw [hpre]
  rw [validFrom_append, runHeight_flatten_UD] at hv
  rw [runHeight_append, runHeight_flatten_UD] at he
  exact ⟨hv.2, he⟩

/-- Leading decomposition: a nonempty Dyck path is `(UD)^a U rest`. -/
theorem dyck_leading (π : List Bool) (hd : IsDyck π) (hne : π ≠ []) :
    π = (List.replicate (cUD π) [true, false]).flatten ++ true :: π.drop (2 * cUD π + 1) := by
  set c := cUDraw π with hc
  have hpre := cUDraw_prefix π
  have hsuf : IsDyck (π.drop (2 * c)) := dyck_drop_fUD π hd
  by_cases hcap : 2 * c = π.length
  · have hcge : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | hp
      · exfalso; rw [h0] at hcap; simp at hcap; exact hne (List.eq_nil_of_length_eq_zero hcap.symm)
      · exact hp
    have hcUD : cUD π = c - 1 := by rw [cUD, ← hc, if_pos hcap]
    have hπfUD : π = (List.replicate c [true, false]).flatten := by
      conv_lhs => rw [hpre]
      rw [List.drop_eq_nil_of_le (by rw [hcap]), List.append_nil]
    have hsplit : π = (List.replicate (c - 1) [true, false]).flatten ++ [true, false] := by
      rw [hπfUD, show c = (c - 1) + 1 from by omega, List.replicate_add]
      simp [List.flatten_append]
    have hpd : π.drop (2 * (c - 1) + 1) = [false] := by
      rw [hπfUD, show 2 * (c - 1) + 1 = 2 * c - 1 from by omega, fUD_drop_last c hcge]
    rw [hcUD, hpd]; exact hsplit
  · have hcUD : cUD π = c := by rw [cUD, ← hc, if_neg hcap]
    have hdropne : π.drop (2 * c) ≠ [] := by
      intro hnil; rw [List.drop_eq_nil_iff] at hnil; have := cUDraw_len π; omega
    have hhead : (π.drop (2 * c)).head? = some true := dyck_head _ hsuf hdropne
    obtain ⟨r, hr⟩ : ∃ r, π.drop (2 * c) = true :: r := by
      cases hh : π.drop (2 * c) with
      | nil => exact absurd hh hdropne
      | cons x xs => rw [hh] at hhead; simp only [List.head?_cons, Option.some.injEq] at hhead
                     subst hhead; exact ⟨xs, rfl⟩
    rw [hcUD]; conv_lhs => rw [hpre]
    rw [hr]
    have hrr : π.drop (2 * c + 1) = r := by rw [← List.drop_drop, hr]; rfl
    rw [hrr]

/-- In the `some` branch (a `DD` exists), the residual path starts with a North step. -/
theorem dyck_rest_head (π : List Bool) (i : ℕ) (hd : IsDyck π) (hne : π ≠ [])
    (hsome : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    (π.drop (2 * cUD π + 1)).head? = some true := by
  set c := cUDraw π with hc
  have hncap : 2 * c ≠ π.length := by
    intro hcap
    have hcge : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | hp
      · exfalso; rw [h0] at hcap; simp at hcap; exact hne (List.eq_nil_of_length_eq_zero hcap.symm)
      · exact hp
    have hπ : π = (List.replicate c [true, false]).flatten := by
      conv_lhs => rw [cUDraw_prefix π]
      rw [List.drop_eq_nil_of_le (by rw [hcap]), List.append_nil]
    have hcUD : cUD π = c - 1 := by rw [cUD, ← hc, if_pos hcap]
    have hrf : π.drop (2 * cUD π + 1) = [false] := by
      rw [hcUD, hπ, show 2 * (c - 1) + 1 = 2 * c - 1 from by omega, fUD_drop_last c hcge]
    rw [hrf] at hsome; simp [firstDDidx] at hsome
  have hcUD : cUD π = c := by rw [cUD, ← hc, if_neg hncap]
  set rest := π.drop (2 * cUD π + 1) with hrest
  have hrestne : rest ≠ [] := by intro hh; rw [hh] at hsome; simp [firstDDidx] at hsome
  by_contra hcon
  obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hrestne
  have hx : x = false := by
    rw [hxs] at hcon; simp only [List.head?_cons] at hcon
    cases x with | true => exact absurd rfl hcon | false => rfl
  subst hx
  have hlead := dyck_leading π hd hne
  rw [← hrest, hxs] at hlead
  have hcount : cUDraw π = cUD π + 1 + cUDraw xs := by
    conv_lhs => rw [hlead]
    rw [show (List.replicate (cUD π) [true,false]).flatten ++ true :: false :: xs
        = (List.replicate (cUD π) [true,false]).flatten ++ ([true,false] ++ xs) from rfl,
      ← List.append_assoc,
      show (List.replicate (cUD π) [true,false]).flatten ++ [true,false]
        = (List.replicate (cUD π + 1) [true,false]).flatten from by
        rw [List.replicate_add]; simp [List.flatten_append],
      cUDraw_fUD_append]
  rw [← hc, hcUD] at hcount; omega

/-- A path from height `≥ 2` cannot return to `0` without a `DD` (no two
consecutive East steps). -/
theorem noDD_high : ∀ (k : ℕ) (r : List Bool) (h : ℤ), r.length = k → 2 ≤ h →
    validFrom r h → runHeight r h = 0 → hasDD r = false → False := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro r h hlen hh hv he hdd
    cases r with
    | nil => simp only [runHeight] at he; omega
    | cons x r' =>
        cases x with
        | true =>
            refine IH r'.length (by simp only [List.length_cons] at hlen; omega) r' (h + 1) rfl
              (by omega) ?_ ?_ ?_
            · simpa only [validFrom] using hv
            · simpa only [runHeight] using he
            · rw [hasDD_cons] at hdd; simpa using hdd
        | false =>
            simp only [validFrom] at hv
            obtain ⟨_, hv'⟩ := hv
            simp only [runHeight] at he
            rw [hasDD_cons] at hdd
            have hddr' := (Bool.or_eq_false_iff.mp hdd).2
            have hjunc := (Bool.or_eq_false_iff.mp hdd).1
            by_cases hh2 : 2 ≤ h - 1
            · exact IH r'.length (by simp only [List.length_cons] at hlen; omega) r' (h - 1) rfl
                hh2 hv' he hddr'
            · have hh1 : h - 1 = 1 := by omega
              rw [hh1] at hv' he
              cases r' with
              | nil => simp only [runHeight] at he; omega
              | cons y ys =>
                  have hy : y = true := by
                    simp only [List.head?_cons] at hjunc
                    cases y with | false => simp at hjunc | true => rfl
                  subst hy
                  refine IH ys.length (by simp only [List.length_cons] at hlen; omega) ys 2 rfl
                    (by omega) ?_ ?_ ?_
                  · simpa only [validFrom] using hv'
                  · simpa only [runHeight] using he
                  · rw [hasDD_cons] at hddr'; simpa using hddr'

/-- `firstDDidx` returning `none` means no `DD`. -/
theorem hasDD_of_none (l : List Bool) (hn : firstDDidx l = none) : hasDD l = false := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      cases t with
      | nil => cases a <;> rfl
      | cons b u =>
          by_cases hab : a = false ∧ b = false
          · obtain ⟨rfl, rfl⟩ := hab; rw [firstDDidx_ff] at hn; simp at hn
          · have hmap : firstDDidx (a :: b :: u) = (firstDDidx (b :: u)).map (· + 1) := by
              cases a with
              | true => rw [firstDDidx_true]
              | false => cases b with
                | false => exact absurd ⟨rfl, rfl⟩ hab
                | true => rw [firstDDidx_ft]
            rw [hmap] at hn
            have hbu : firstDDidx (b :: u) = none := by
              cases hh : firstDDidx (b :: u) with
              | none => rfl
              | some j => rw [hh] at hn; simp at hn
            have hih := ih hbu
            rw [hasDD_cons]; simp only [List.head?_cons]
            have h1 : (a == false && some b == some false) = false := by
              by_cases ha : a = false <;> by_cases hb : b = false <;> simp_all
            rw [h1, Bool.false_or]; exact hih

/-- In the `none` branch (no `DD`), the residual path is a single East step, so
`π = (UD)^a U D`. -/
theorem dyck_none_rest (π : List Bool) (hd : IsDyck π) (hne : π ≠ [])
    (hnone : firstDDidx (π.drop (2 * cUD π + 1)) = none) :
    π.drop (2 * cUD π + 1) = [false] := by
  set c := cUDraw π with hc
  by_cases hcap : 2 * c = π.length
  · have hcge : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | hp
      · exfalso; rw [h0] at hcap; simp at hcap; exact hne (List.eq_nil_of_length_eq_zero hcap.symm)
      · exact hp
    have hcUD : cUD π = c - 1 := by rw [cUD, ← hc, if_pos hcap]
    have hπ : π = (List.replicate c [true, false]).flatten := by
      conv_lhs => rw [cUDraw_prefix π]
      rw [List.drop_eq_nil_of_le (by rw [hcap]), List.append_nil]
    rw [hcUD, hπ, show 2 * (c - 1) + 1 = 2 * c - 1 from by omega, fUD_drop_last c hcge]
  · exfalso
    have hcUD : cUD π = c := by rw [cUD, ← hc, if_neg hcap]
    have hlead := dyck_leading π hd hne
    rw [hcUD] at hlead hnone
    set rest := π.drop (2 * c + 1) with hrestdef
    have hddrest : hasDD rest = false := hasDD_of_none rest hnone
    have hvhe : validFrom rest 1 ∧ runHeight rest 1 = 0 := by
      have hdd2 := hd; rw [IsDyck, isDyckAux_iff] at hdd2; obtain ⟨hv, he⟩ := hdd2
      rw [hlead, validFrom_append, runHeight_flatten_UD] at hv
      rw [hlead, runHeight_append, runHeight_flatten_UD] at he
      exact ⟨by simpa [validFrom] using hv.2, by simpa [runHeight] using he⟩
    have hrestne : rest ≠ [] := by intro h0; rw [h0] at hvhe; simp [runHeight] at hvhe
    obtain ⟨y, r, hyr⟩ := List.exists_cons_of_ne_nil hrestne
    have hy : y = true := by
      by_contra hyf; simp only [Bool.not_eq_true] at hyf; subst hyf
      have hcount : cUDraw π = c + 1 + cUDraw r := by
        conv_lhs => rw [hlead, hyr]
        rw [show (List.replicate c [true, false]).flatten ++ true :: false :: r
            = (List.replicate (c + 1) [true, false]).flatten ++ r from by
            rw [List.replicate_add]; simp [List.flatten_append], cUDraw_fUD_append]
      rw [← hc] at hcount; omega
    subst hy
    rw [hyr] at hvhe hddrest
    refine noDD_high r.length r 2 rfl (by norm_num) ?_ ?_ ?_
    · simpa only [validFrom] using hvhe.1
    · simpa only [runHeight] using hvhe.2
    · rw [hasDD_cons] at hddrest; simpa using hddrest

/-- A `DD`-free path starting with a North step (or empty) is valid from height 0
(each East step is preceded by a North step). -/
theorem noDD_validFrom_gen (ρ : List Bool) : ∀ (h : ℤ), 0 ≤ h → hasDD ρ = false →
    (ρ.head? = some false → 1 ≤ h) → validFrom ρ h := by
  induction ρ with
  | nil => intro h _ _ _; trivial
  | cons x r' ih =>
      intro h hh hdd hpre
      cases x with
      | true => simp only [validFrom]
                exact ih (h + 1) (by omega) (by rw [hasDD_cons] at hdd; simpa using hdd)
                  (fun _ => by omega)
      | false =>
          simp only [validFrom]
          have hjunc : r'.head? ≠ some false := by
            rw [hasDD_cons] at hdd
            have := (Bool.or_eq_false_iff.mp hdd).1
            intro hcon; rw [hcon] at this; simp at this
          have hh1 : 1 ≤ h := hpre (by simp)
          exact ⟨by omega, ih (h - 1) (by omega)
            (by rw [hasDD_cons] at hdd; exact (Bool.or_eq_false_iff.mp hdd).2)
            (fun hcon => absurd hcon hjunc)⟩

/-- The residual `ρ ++ ρ'` (path with the pyramid removed) is again a Dyck path. -/
theorem dyck_residual (π : List Bool) (b : ℕ) (ρ ρ' : List Bool)
    (hd : IsDyck π) (hne : π ≠ [])
    (hstruct : π.drop (2 * cUD π + 1)
      = ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ')
    (hρDD : hasDD ρ = false) (hρU : ρ = [] ∨ ρ.head? = some true) :
    IsDyck (ρ ++ ρ') := by
  have hlead := dyck_leading π hd hne
  rw [hstruct] at hlead
  have hvρ0 : validFrom ρ 0 :=
    noDD_validFrom_gen ρ 0 le_rfl hρDD (by rcases hρU with h | h <;> rw [h] <;> simp)
  have hshift : runHeight ρ 1 = runHeight ρ 0 + 1 := by
    have := runHeight_shift ρ 0 1; simpa using this
  have hcast : runHeight ρ 1 + (b : ℤ) - ((b + 1 : ℕ) : ℤ) = runHeight ρ 0 := by
    rw [hshift]; push_cast; ring
  have hd2 := hd
  rw [IsDyck, isDyckAux_iff] at hd2
  obtain ⟨hv, he⟩ := hd2
  rw [hlead] at hv he
  rw [validFrom_append, runHeight_flatten_UD] at hv
  have hvM : validFrom (ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') 1 := by
    have := hv.2; simpa only [validFrom] using this
  rw [runHeight_append, runHeight_flatten_UD] at he
  have heM : runHeight (ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ') 1 = 0 := by
    simpa only [runHeight] using he
  rw [show ρ ++ List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
      = ρ ++ (List.replicate b true ++ (List.replicate (b + 1) false ++ ρ')) from by
      simp [List.append_assoc]] at hvM heM
  rw [validFrom_append] at hvM
  rw [runHeight_append] at heM
  have hvρ' : validFrom ρ' (runHeight ρ 0) := by
    have h2 := hvM.2
    rw [validFrom_append, runHeight_replicate_true] at h2
    have h3 := h2.2
    rw [validFrom_append, runHeight_replicate_false] at h3
    rw [hcast] at h3; exact h3.2
  have herρ' : runHeight ρ' (runHeight ρ 0) = 0 := by
    rw [runHeight_append, runHeight_replicate_true, runHeight_append, runHeight_replicate_false] at heM
    rw [hcast] at heM; exact heM
  rw [IsDyck, isDyckAux_iff]
  exact ⟨by rw [validFrom_append]; exact ⟨hvρ0, hvρ'⟩, by rw [runHeight_append]; exact herρ'⟩

/-! ### Forward `Φ` computation on the reconstructed word -/

theorem cLead0_false' (r : List Bool) : cLead0 (false :: r) = 1 + cLead0 r := rfl
theorem cLead0_true' (r : List Bool) : cLead0 (true :: r) = 0 := rfl
theorem cLead1_true' (r : List Bool) : cLead1 (true :: r) = 1 + cLead1 r := rfl
theorem cLead1_false' (r : List Bool) : cLead1 (false :: r) = 0 := rfl
theorem noDescent_cc (x y : Bool) (r : List Bool) :
    noDescent (x :: y :: r) = ((!x || y) && noDescent (y :: r)) := rfl

theorem noDescent_of_desc (s t : List Bool) : noDescent (s ++ true :: false :: t) = false := by
  induction s with
  | nil => rw [List.nil_append, noDescent_cc]; simp
  | cons x s' ih =>
      cases s' with
      | nil => rw [List.nil_append] at ih; show noDescent (x :: true :: false :: t) = false
               rw [noDescent_cc, ih]; simp
      | cons y s'' => show noDescent (x :: y :: (s'' ++ true :: false :: t)) = false
                      rw [noDescent_cc]
                      show ((!x || y) && noDescent (y :: s'' ++ true :: false :: t)) = false
                      rw [ih]; simp

theorem noDescent_block (a b : ℕ) (w' : List Bool) (hb : 1 ≤ b) :
    noDescent (List.replicate a false ++ List.replicate b true ++ false :: w') = false := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have heq : List.replicate a false ++ List.replicate (b' + 1) true ++ false :: w'
       = (List.replicate a false ++ List.replicate b' true) ++ true :: false :: w' := by
    rw [List.replicate_succ']; simp [List.append_assoc]
  rw [heq]; exact noDescent_of_desc _ _

theorem cLead0_block (a b : ℕ) (w' : List Bool) (hb : 1 ≤ b) :
    cLead0 (List.replicate a false ++ List.replicate b true ++ false :: w') = a := by
  induction a with
  | zero => obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append, cLead0_true']
  | succ n ih => rw [List.replicate_succ]; simp only [List.cons_append]; rw [cLead0_false', ih]; omega

theorem cLead1_block (b : ℕ) (w' : List Bool) :
    cLead1 (List.replicate b true ++ false :: w') = b := by
  induction b with
  | zero => rw [List.replicate_zero, List.nil_append, cLead1_false']
  | succ n ih => rw [List.replicate_succ]; simp only [List.cons_append]; rw [cLead1_true', ih]; omega

theorem drop_block (b : ℕ) (w' : List Bool) :
    (List.replicate b true ++ false :: w').drop (b + 1) = w' := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append, List.length_replicate,
    show b + 1 - b = 1 from by omega]; rfl

theorem drop_a_block (a b : ℕ) (w' : List Bool) :
    (List.replicate a false ++ List.replicate b true ++ false :: w').drop a
      = List.replicate b true ++ false :: w' := by
  rw [List.append_assoc, List.drop_append_of_le_length (by simp),
    List.drop_eq_nil_of_le (by simp), List.nil_append]

/-- `Φ` on the recursive word `0^a 1^b 0 w'` performs the split reconstruction. -/
theorem phiPath_block (a b : ℕ) (w' : List Bool) (h : ℕ) (av' : List ℕ) (hb : 1 ≤ b) :
    phiPath (List.replicate a false ++ List.replicate b true ++ [false] ++ w') (h :: av')
      = (List.replicate a [true, false]).flatten ++ [true]
          ++ (splitAtRow (phiPath w' av') h).1 ++ List.replicate b true
          ++ List.replicate (b + 1) false ++ (splitAtRow (phiPath w' av') h).2 := by
  have hword : List.replicate a false ++ List.replicate b true ++ [false] ++ w'
      = List.replicate a false ++ List.replicate b true ++ false :: w' := by simp [List.append_assoc]
  rw [hword, phiPath.eq_1, if_neg (by rw [noDescent_block a b w' hb]; simp)]
  simp only [cLead0_block a b w' hb, drop_a_block a b w', cLead1_block b w', drop_block b w',
    List.headD_cons, List.tail_cons]

/-- The `some`-branch (a `DD` exists) of the surjectivity round-trip. -/
theorem phi_psi_some (n : ℕ)
    (IH : ∀ m, m < n → ∀ π : List Bool, π.length = m → IsDyck π → π ≠ [] →
      phiPath (psiPath π).1 (psiPath π).2 = π)
    (π : List Bool) (hlen : π.length = n) (hd : IsDyck π) (hne : π ≠ []) (i : ℕ)
    (hfd : firstDDidx (π.drop (2 * cUD π + 1)) = some i) :
    phiPath (psiPath π).1 (psiPath π).2 = π := by
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
    rw [hpsi, hbase, phiPath.eq_1, if_pos (by simpa using noDescent_sorted a b)]
    simp [List.filter_append, List.filter_replicate, List.append_assoc]
  · have hpsi : psiPath π = (List.replicate a false ++ List.replicate b true ++ [false]
          ++ (psiPath (ρ ++ ρ')).1, numN ρ :: (psiPath (ρ ++ ρ')).2) := by
      rw [hπ]; exact psiPath_step a b ρ ρ' hb1 hρU hρDD hmax hemp
    rw [hpsi]
    have hreslen : (ρ ++ ρ').length < n := by
      rw [← hlen]; conv_rhs => rw [hπ]
      simp only [List.length_append, List.length_cons, List.length_replicate, fUD_len,
        List.length_nil]; omega
    have hIH := IH (ρ ++ ρ').length hreslen (ρ ++ ρ') rfl hresD hemp
    rw [phiPath_block a b (psiPath (ρ ++ ρ')).1 (numN ρ) (psiPath (ρ ++ ρ')).2 hb1, hIH,
      splitAtRow_reconstruct ρ ρ' hne0 hρDD hmax]
    exact hπ.symm

/-- Round-trip `Φ ∘ Ψ = id` on nonempty Dyck paths (the surjectivity content).
The empty path is excluded: `Φ` always produces a nonempty path. -/
theorem phi_psi (π : List Bool) (h : IsDyck π) (hne : π ≠ []) :
    phiPath (psiPath π).1 (psiPath π).2 = π := by
  suffices H : ∀ n, ∀ π : List Bool, π.length = n → IsDyck π → π ≠ [] →
      phiPath (psiPath π).1 (psiPath π).2 = π by exact H π.length π rfl h hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro π hlen hd hne
    rcases hfd : firstDDidx (π.drop (2 * cUD π + 1)) with _ | i
    · have hrf : π.drop (2 * cUD π + 1) = [false] := dyck_none_rest π hd hne hfd
      have hpsi : psiPath π = (List.replicate (cUD π) false, [0]) := by rw [psiPath.eq_1, hfd]
      rw [hpsi]
      conv_rhs => rw [dyck_leading π hd hne, hrf]
      rw [phiPath.eq_1, if_pos (by simpa using noDescent_sorted (cUD π) 0)]
      simp [List.filter_replicate, List.append_assoc]
    · exact phi_psi_some n IH π hlen hd hne i hfd


end Psi
