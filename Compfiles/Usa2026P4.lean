/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Liao, Kimi K3
-/

module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# USA Mathematical Olympiad 2026, Problem 4

A positive integer n is called solitary if, for any non-negative integers a and b such
that a + b = n, either a or b contains the digit "1".
Determine, with proof, the number of solitary integers less than 10^2026.
-/

namespace Usa2026P4

open Classical

determine solution : ℕ := 2^2026 - 1

def has_digit_one (n : ℕ) : Prop :=
  1 ∈ Nat.digits 10 n

def is_solitary (n : ℕ) : Prop :=
  n > 0 ∧ ∀ a b : ℕ, a + b = n → has_digit_one a ∨ has_digit_one b

snip begin

lemma solitary_implies_has_one {n : ℕ} (h : is_solitary n) : has_digit_one n := by
  have h_eq : n + 0 = n := add_zero n
  have h_or := h.2 n 0 h_eq
  have h_not_zero : ¬ has_digit_one 0 := by
    intro hc
    unfold has_digit_one at hc
    rw [Nat.digits_zero] at hc
    cases hc
  cases h_or with
  | inl hl => exact hl
  | inr hr => contradiction

lemma one_is_solitary : is_solitary 1 := by
  refine ⟨by decide, ?_⟩
  intro a b hab
  cases a with
  | zero =>
    right
    have hb : b = 1 := by omega
    subst hb
    unfold has_digit_one
    change 1 ∈ [1]
    simp
  | succ a' =>
    cases a' with
    | zero =>
      left
      unfold has_digit_one
      change 1 ∈ [1]
      simp
    | succ =>
      exfalso
      omega

inductive IsSolitaryDigits : List ℕ → Prop
  | one_base (l : List ℕ) (h : ∀ x ∈ l, x = 0 ∨ x = 2) : IsSolitaryDigits (1 :: l)
  | nine_step (l : List ℕ) (h : IsSolitaryDigits l) : IsSolitaryDigits (9 :: l)

def is_solitary_form (n : ℕ) : Prop :=
  IsSolitaryDigits (Nat.digits 10 n)

lemma is_solitary_digits_has_one {l : List ℕ} (h : IsSolitaryDigits l) : 1 ∈ l := by
  induction h with
  | one_base l _ => exact List.Mem.head l
  | nine_step l _ ih => exact List.Mem.tail 9 ih

lemma solitary_form_has_one (n : ℕ) (h : is_solitary_form n) : has_digit_one n := by
  exact is_solitary_digits_has_one h

lemma solitary_digits_subset {l : List ℕ} (h : IsSolitaryDigits l) :
    ∀ d ∈ l, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 9 := by
  induction h with
  | one_base lst hlst =>
    intro d hd
    cases hd with
    | head _ =>
      right; left; rfl
    | tail _ htail =>
      have h02 := hlst d htail
      cases h02 with
      | inl hz => left; exact hz
      | inr htwo => right; right; left; exact htwo
  | nine_step lst hlst ih =>
    intro d hd
    cases hd with
    | head _ =>
      right; right; right; rfl
    | tail _ htail =>
      exact ih d htail

lemma solitary_digits_head {l : List ℕ} (h : IsSolitaryDigits l) :
    l.head? = some 1 ∨ l.head? = some 9 := by
  cases h with
  | one_base _ _ => left; rfl
  | nine_step _ _ => right; rfl

lemma solitary_form_pos (n : ℕ) (h : is_solitary_form n) : n > 0 := by
  by_contra hc
  have h0 : n = 0 := by omega
  subst h0
  unfold is_solitary_form at h
  rw [Nat.digits_zero] at h
  cases h

lemma solitary_digits_exactly_one_one {l : List ℕ} (h : IsSolitaryDigits l) : l.count 1 = 1 := by
  induction h with
  | one_base lst hlst =>
    have h_not_mem : 1 ∉ lst := by
      intro h1
      have h_or := hlst 1 h1
      omega
    have h_count_zero : lst.count 1 = 0 := List.count_eq_zero.mpr h_not_mem
    simp [h_count_zero]
  | nine_step lst hlst ih =>
    simp [ih]

lemma add_mod_ten (a b n : ℕ) (h : a + b = n) :
    a % 10 + b % 10 = n % 10 ∨ a % 10 + b % 10 = n % 10 + 10 := by
  omega

lemma sum_ends_in_nine_no_carry (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 9) :
    a % 10 + b % 10 = 9 := by
  have h1 : a % 10 < 10 := Nat.mod_lt a (by decide)
  have h2 : b % 10 < 10 := Nat.mod_lt b (by decide)
  have h3 : a % 10 + b % 10 = n % 10 ∨ a % 10 + b % 10 = n % 10 + 10 := add_mod_ten a b n h
  omega

lemma sum_ends_in_one (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 1) :
    (a % 10 = 1 ∧ b % 10 = 0) ∨ (a % 10 = 0 ∧ b % 10 = 1) ∨ (a % 10 + b % 10 = 11) := by
  have h1 : a % 10 < 10 := Nat.mod_lt a (by decide)
  have h2 : b % 10 < 10 := Nat.mod_lt b (by decide)
  have h3 : a % 10 + b % 10 = n % 10 ∨ a % 10 + b % 10 = n % 10 + 10 := add_mod_ten a b n h
  omega

lemma sum_eq_two_no_ones (a b : ℕ) (h : a + b = 2) (_ha : a ≠ 1) (_hb : b ≠ 1) :
    (a = 2 ∧ b = 0) ∨ (a = 0 ∧ b = 2) := by
  omega

lemma div_ten_of_sum_nine (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 9) :
    a / 10 + b / 10 = n / 10 := by
  have h_sum : a % 10 + b % 10 = 9 := sum_ends_in_nine_no_carry a b n h hn
  have _ := (Nat.div_add_mod a 10).symm
  have _ := (Nat.div_add_mod b 10).symm
  have _ := (Nat.div_add_mod n 10).symm
  omega

lemma div_ten_of_sum_one_no_carry (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 1)
    (h_sum : a % 10 + b % 10 = 1) : a / 10 + b / 10 = n / 10 := by
  have _ := (Nat.div_add_mod a 10).symm
  have _ := (Nat.div_add_mod b 10).symm
  have _ := (Nat.div_add_mod n 10).symm
  omega

lemma div_ten_of_sum_one_carry (a b n : ℕ) (h : a + b = n) (hn : n % 10 = 1)
    (h_sum : a % 10 + b % 10 = 11) : a / 10 + b / 10 + 1 = n / 10 := by
  have _ := (Nat.div_add_mod a 10).symm
  have _ := (Nat.div_add_mod b 10).symm
  have _ := (Nat.div_add_mod n 10).symm
  omega

/-! ### Basic facts about the digit `1` -/

lemma not_has_digit_one_zero : ¬ has_digit_one 0 := by
  unfold has_digit_one
  rw [Nat.digits_zero]
  simp

lemma has_digit_one_of_mod {a : ℕ} (h : a % 10 = 1) : has_digit_one a := by
  unfold has_digit_one
  have ha : 0 < a := by omega
  rw [Nat.digits_def' (by decide) ha, h]
  exact List.Mem.head _

lemma has_digit_one_of_div {a : ℕ} (h : has_digit_one (a / 10)) : has_digit_one a := by
  unfold has_digit_one at h ⊢
  by_cases ha0 : a = 0
  · subst ha0
    simp at h
  · have ha : 0 < a := Nat.pos_of_ne_zero ha0
    rw [Nat.digits_def' (by decide) ha]
    exact List.Mem.tail _ h

lemma not_has_digit_one_of_cons {d : ℕ} {a : ℕ} (hd : d ≠ 1) (ha : ¬ has_digit_one a)
    (hd10 : d < 10) : ¬ has_digit_one (10 * a + d) := by
  unfold has_digit_one at ha ⊢
  by_cases h0 : 10 * a + d = 0
  · rw [h0, Nat.digits_zero]
    simp
  · have hpos : 0 < 10 * a + d := Nat.pos_of_ne_zero h0
    rw [Nat.digits_def' (by decide) hpos]
    have hmod : (10 * a + d) % 10 = d := by omega
    have hdiv : (10 * a + d) / 10 = a := by omega
    rw [hmod, hdiv]
    intro hmem
    cases hmem with
    | head _ => exact hd rfl
    | tail _ htail => exact ha htail

lemma not_has_digit_one_of_lt {u : ℕ} (hu1 : u ≠ 1) (hu10 : u < 10) : ¬ has_digit_one u := by
  unfold has_digit_one
  by_cases hu0 : u = 0
  · subst hu0
    rw [Nat.digits_zero]
    simp
  · rw [Nat.digits_of_lt 10 u hu0 hu10]
    simp only [List.mem_singleton]
    omega

/-! ### Structural facts about `IsSolitaryDigits` -/

lemma IsSolitaryDigits.ne_nil {l : List ℕ} (h : IsSolitaryDigits l) : l ≠ [] := by
  cases h <;> simp

lemma IsSolitaryDigits.head_eq {d : ℕ} {l : List ℕ} (h : IsSolitaryDigits (d :: l)) :
    d = 1 ∨ d = 9 := by
  cases h with
  | one_base _ _ => left; rfl
  | nine_step _ _ => right; rfl

lemma IsSolitaryDigits.tail_all02_of_head_one {d : ℕ} {l : List ℕ} (h : IsSolitaryDigits (d :: l))
    (hd : d = 1) : ∀ x ∈ l, x = 0 ∨ x = 2 := by
  cases h with
  | one_base _ hl => exact hl
  | nine_step _ _ => exact absurd hd (by decide)

lemma IsSolitaryDigits.tail_form_of_head_nine {d : ℕ} {l : List ℕ} (h : IsSolitaryDigits (d :: l))
    (hd : d = 9) : IsSolitaryDigits l := by
  cases h with
  | one_base _ _ => exact absurd hd (by decide)
  | nine_step _ hl => exact hl

lemma IsSolitaryDigits.append_zero {l : List ℕ} (h : IsSolitaryDigits l) :
    IsSolitaryDigits (l ++ [0]) := by
  induction h with
  | one_base rest hr =>
    rw [List.cons_append]
    apply IsSolitaryDigits.one_base
    intro x hx
    rcases List.mem_append.mp hx with h' | h'
    · exact hr x h'
    · left
      exact List.mem_singleton.mp h'
  | nine_step rest hr ih =>
    rw [List.cons_append]
    exact IsSolitaryDigits.nine_step _ ih

lemma IsSolitaryDigits.append_two {l : List ℕ} (h : IsSolitaryDigits l) :
    IsSolitaryDigits (l ++ [2]) := by
  induction h with
  | one_base rest hr =>
    rw [List.cons_append]
    apply IsSolitaryDigits.one_base
    intro x hx
    rcases List.mem_append.mp hx with h' | h'
    · exact hr x h'
    · right
      exact List.mem_singleton.mp h'
  | nine_step rest hr ih =>
    rw [List.cons_append]
    exact IsSolitaryDigits.nine_step _ ih

lemma IsSolitaryDigits.append_replicate_zero (j : ℕ) :
    ∀ {l : List ℕ}, IsSolitaryDigits l → IsSolitaryDigits (l ++ List.replicate j 0) := by
  induction j with
  | zero => intro l h; simpa using h
  | succ j ih =>
    intro l h
    rw [List.replicate_succ, List.append_cons]
    exact ih (IsSolitaryDigits.append_zero h)

lemma IsSolitaryDigits.getLast_eq_one_or_two {l : List ℕ} (h : IsSolitaryDigits l) :
    l.getLast h.ne_nil ≠ 0 → l.getLast h.ne_nil = 1 ∨ l.getLast h.ne_nil = 2 := by
  induction h with
  | one_base rest hr =>
    intro h0
    by_cases hrest : rest = []
    · subst hrest
      left
      rfl
    · rw [List.getLast_cons hrest] at h0 ⊢
      have hmem := List.getLast_mem hrest
      rcases hr _ hmem with h' | h'
      · exact absurd h' h0
      · exact Or.inr h'
  | nine_step rest hr ih =>
    intro h0
    rw [List.getLast_cons hr.ne_nil] at h0 ⊢
    exact ih h0

lemma IsSolitaryDigits.dropLast_of_getLast_zero {l : List ℕ} (h : IsSolitaryDigits l) :
    l.getLast h.ne_nil = 0 → IsSolitaryDigits l.dropLast := by
  induction h with
  | one_base rest hr =>
    intro h0
    by_cases hrest : rest = []
    · subst hrest
      exfalso
      have h1 : (1 :: ([] : List ℕ)).getLast (IsSolitaryDigits.one_base [] hr).ne_nil = 1 := rfl
      omega
    · rw [List.dropLast_cons_of_ne_nil hrest]
      apply IsSolitaryDigits.one_base
      intro x hx
      exact hr x (List.mem_of_mem_dropLast hx)
  | nine_step rest hr ih =>
    intro h0
    rw [List.dropLast_cons_of_ne_nil hr.ne_nil]
    apply IsSolitaryDigits.nine_step
    apply ih
    rw [List.getLast_cons hr.ne_nil] at h0
    exact h0

lemma IsSolitaryDigits.dropLast_of_getLast_two {l : List ℕ} (h : IsSolitaryDigits l) :
    l.getLast h.ne_nil = 2 → IsSolitaryDigits l.dropLast := by
  induction h with
  | one_base rest hr =>
    intro h2
    by_cases hrest : rest = []
    · subst hrest
      exfalso
      have h1 : (1 :: ([] : List ℕ)).getLast (IsSolitaryDigits.one_base [] hr).ne_nil = 1 := rfl
      omega
    · rw [List.dropLast_cons_of_ne_nil hrest]
      apply IsSolitaryDigits.one_base
      intro x hx
      exact hr x (List.mem_of_mem_dropLast hx)
  | nine_step rest hr ih =>
    intro h2
    rw [List.dropLast_cons_of_ne_nil hr.ne_nil]
    apply IsSolitaryDigits.nine_step
    apply ih
    rw [List.getLast_cons hr.ne_nil] at h2
    exact h2

lemma IsSolitaryDigits.of_append_replicate_zero (j : ℕ) :
    ∀ {l : List ℕ}, IsSolitaryDigits (l ++ List.replicate j 0) → IsSolitaryDigits l := by
  induction j with
  | zero => intro l h; simpa using h
  | succ j ih =>
    intro l h
    rw [List.replicate_succ, List.append_cons] at h
    have h' := ih h
    have h0 : (l ++ [0]).getLast h'.ne_nil = 0 := by
      rw [List.getLast_concat]
    have h'' := h'.dropLast_of_getLast_zero h0
    rw [List.dropLast_concat] at h''
    exact h''

lemma IsSolitaryDigits.of_append_replicate_zero_two {l : List ℕ} (j : ℕ)
    (h : IsSolitaryDigits (l ++ (List.replicate j 0 ++ [2]))) : IsSolitaryDigits l := by
  rw [← List.append_assoc] at h
  have h2 : ((l ++ List.replicate j 0) ++ [2]).getLast h.ne_nil = 2 := by
    rw [List.getLast_concat]
  have h' := h.dropLast_of_getLast_two h2
  rw [List.dropLast_concat] at h'
  exact IsSolitaryDigits.of_append_replicate_zero j h'

lemma IsSolitaryDigits.eq_replicate_nine_one {l : List ℕ} (h : IsSolitaryDigits l) :
    l.getLast h.ne_nil = 1 → l = List.replicate (l.length - 1) 9 ++ [1] := by
  induction h with
  | one_base rest hr =>
    intro h1
    by_cases hrest : rest = []
    · subst hrest
      simp
    · exfalso
      rw [List.getLast_cons hrest] at h1
      have hmem := List.getLast_mem hrest
      rcases hr _ hmem with h' | h' <;> omega
  | nine_step rest hr ih =>
    intro h1
    rw [List.getLast_cons hr.ne_nil] at h1
    have h2 := ih h1
    have hlen : 0 < rest.length := List.length_pos_of_ne_nil hr.ne_nil
    rw [List.length_cons]
    have h3 : List.replicate (rest.length + 1 - 1) 9 ++ [1] =
        9 :: (List.replicate (rest.length - 1) 9 ++ [1]) := by
      have e1 : rest.length + 1 - 1 = (rest.length - 1) + 1 := by omega
      rw [e1, List.replicate_succ, List.cons_append]
    rw [h3]
    exact congrArg (9 :: ·) h2

/-! ### The key carry lemmas -/

/-- If all digits of `n` are `0` or `2`, then any `x + y + 1 = n` forces a digit `1`
in `x` or `y`. -/
lemma all_zero_two_add_succ (n : ℕ) :
    (∀ x ∈ Nat.digits 10 n, x = 0 ∨ x = 2) →
    ∀ x y : ℕ, x + y + 1 = n → has_digit_one x ∨ has_digit_one y := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro h02 x y hxy
    by_cases hn0 : n = 0
    · subst hn0
      omega
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hdig : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_def' (by decide) hn
      have hhead : n % 10 = 0 ∨ n % 10 = 2 := by
        apply h02
        rw [hdig]
        exact List.Mem.head _
      have htail : ∀ x ∈ Nat.digits 10 (n / 10), x = 0 ∨ x = 2 := by
        intro x hx
        apply h02
        rw [hdig]
        exact List.Mem.tail _ hx
      have hx10 : x % 10 < 10 := Nat.mod_lt x (by decide)
      have hy10 : y % 10 < 10 := Nat.mod_lt y (by decide)
      have hdiv : x / 10 + y / 10 + 1 = n / 10 ∨ (x % 10 = 1 ∨ y % 10 = 1) := by
        have hxd := Nat.div_add_mod x 10
        have hyd := Nat.div_add_mod y 10
        have hnd := Nat.div_add_mod n 10
        rcases hhead with h | h <;> omega
      rcases hdiv with hdiv | h1
      · have hlt : n / 10 < n := Nat.div_lt_self hn (by decide)
        rcases IH (n / 10) hlt htail (x / 10) (y / 10) hdiv with h | h
        · left; exact has_digit_one_of_div h
        · right; exact has_digit_one_of_div h
      · rcases h1 with h1 | h1
        · left; exact has_digit_one_of_mod h1
        · right; exact has_digit_one_of_mod h1

/-- If `m` has solitary form, then all digits of `m + 1` are `0` or `2`. -/
lemma all_zero_two_succ_of_form_aux {l : List ℕ} (h : IsSolitaryDigits l) :
    ∀ {m : ℕ}, Nat.digits 10 m = l → ∀ x ∈ Nat.digits 10 (m + 1), x = 0 ∨ x = 2 := by
  induction h with
  | one_base rest hr =>
    intro m hm
    have hm0 : 0 < m := by
      by_contra hc
      have hm0 : m = 0 := by omega
      rw [hm0, Nat.digits_zero] at hm
      simp at hm
    have hdig : Nat.digits 10 m = (m % 10) :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (by decide) hm0
    rw [hdig] at hm
    have hmod : m % 10 = 1 := (List.cons.inj hm).1
    have hrest : Nat.digits 10 (m / 10) = rest := (List.cons.inj hm).2
    have hdig1 : Nat.digits 10 (m + 1) = 2 :: Nat.digits 10 (m / 10) := by
      have h1 : m + 1 = 2 + 10 * (m / 10) := by
        have hdd := Nat.div_add_mod m 10
        omega
      rw [h1]
      exact Nat.digits_add 10 (by decide) 2 (m / 10) (by decide) (Or.inl (by decide))
    intro x hx
    rw [hdig1, hrest] at hx
    cases hx with
    | head _ => right; rfl
    | tail _ htail => exact hr x htail
  | nine_step rest hr ih =>
    intro m hm
    have hm0 : 0 < m := by
      by_contra hc
      have hm0 : m = 0 := by omega
      rw [hm0, Nat.digits_zero] at hm
      simp at hm
    have hdig : Nat.digits 10 m = (m % 10) :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (by decide) hm0
    rw [hdig] at hm
    have hmod : m % 10 = 9 := (List.cons.inj hm).1
    have hrest : Nat.digits 10 (m / 10) = rest := (List.cons.inj hm).2
    have hdig1 : Nat.digits 10 (m + 1) = 0 :: Nat.digits 10 (m / 10 + 1) := by
      have h1 : m + 1 = 0 + 10 * (m / 10 + 1) := by
        have hdd := Nat.div_add_mod m 10
        omega
      rw [h1]
      exact Nat.digits_add 10 (by decide) 0 (m / 10 + 1) (by decide) (Or.inr (by omega))
    intro x hx
    rw [hdig1] at hx
    cases hx with
    | head _ => left; rfl
    | tail _ htail => exact ih hrest x htail

lemma all_zero_two_succ_of_form {m : ℕ} (h : is_solitary_form m) :
    ∀ x ∈ Nat.digits 10 (m + 1), x = 0 ∨ x = 2 :=
  all_zero_two_succ_of_form_aux h rfl

lemma not_form_pred_of_form {t : ℕ} (h : is_solitary_form t) : ¬ is_solitary_form (t - 1) := by
  intro hpred
  have ht1 : 0 < t := solitary_form_pos t h
  have h02 := all_zero_two_succ_of_form hpred
  rw [Nat.sub_add_cancel ht1] at h02
  have h1 := is_solitary_digits_has_one h
  rcases h02 1 h1 with h' | h' <;> omega

/-- The core equivalence, proved by strong induction on `n` with three
mutually reinforcing parts. -/
lemma solitary_form_iff_core (n : ℕ) :
    (is_solitary_form n → ∀ a b : ℕ, a + b = n → has_digit_one a ∨ has_digit_one b) ∧
    (0 < n → ¬ is_solitary_form n →
      ∃ a b : ℕ, a + b = n ∧ ¬ has_digit_one a ∧ ¬ has_digit_one b) ∧
    ((¬ ∀ x ∈ Nat.digits 10 n, x = 0 ∨ x = 2) →
      ∃ x y : ℕ, x + y + 1 = n ∧ ¬ has_digit_one x ∧ ¬ has_digit_one y) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    refine ⟨?_, ?_, ?_⟩
    · -- Part 1: solitary form implies the summand property.
      intro hf a b hab
      have hn : 0 < n := solitary_form_pos n hf
      have hdig : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_def' (by decide) hn
      have hf' : IsSolitaryDigits (Nat.digits 10 n) := hf
      rw [hdig] at hf'
      by_cases h1 : n % 10 = 1
      · have h02 := IsSolitaryDigits.tail_all02_of_head_one hf' h1
        have hsum := sum_ends_in_one a b n hab h1
        rcases hsum with ⟨ha1, -⟩ | ⟨-, hb1⟩ | hsum11
        · left; exact has_digit_one_of_mod ha1
        · right; exact has_digit_one_of_mod hb1
        · have hdiv := div_ten_of_sum_one_carry a b n hab h1 hsum11
          have hlt : n / 10 < n := Nat.div_lt_self hn (by decide)
          rcases all_zero_two_add_succ (n / 10) h02 (a / 10) (b / 10) hdiv with h | h
          · left; exact has_digit_one_of_div h
          · right; exact has_digit_one_of_div h
      · by_cases h9 : n % 10 = 9
        · have hf9 := IsSolitaryDigits.tail_form_of_head_nine hf' h9
          have hdiv := div_ten_of_sum_nine a b n hab h9
          have hlt : n / 10 < n := Nat.div_lt_self hn (by decide)
          rcases (IH (n / 10) hlt).1 hf9 (a / 10) (b / 10) hdiv with h | h
          · left; exact has_digit_one_of_div h
          · right; exact has_digit_one_of_div h
        · exfalso
          have hhd := IsSolitaryDigits.head_eq hf'
          omega
    · -- Part 2: numbers not of solitary form split with no digit `1`.
      intro hn hnf
      have hdig : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) :=
        Nat.digits_def' (by decide) hn
      have hd10 : n % 10 < 10 := Nat.mod_lt n (by decide)
      by_cases h9 : n % 10 = 9
      · have hnf9 : ¬ is_solitary_form (n / 10) := by
          intro hf9
          apply hnf
          show IsSolitaryDigits (Nat.digits 10 n)
          rw [hdig, h9]
          exact IsSolitaryDigits.nine_step _ hf9
        have hnd : n = 10 * (n / 10) + 9 := by
          have hdd := Nat.div_add_mod n 10
          omega
        have hab0 : ∃ a' b' : ℕ, a' + b' = n / 10 ∧ ¬ has_digit_one a' ∧ ¬ has_digit_one b' := by
          by_cases ht0 : n / 10 = 0
          · exact ⟨0, 0, by omega, not_has_digit_one_zero, not_has_digit_one_zero⟩
          · exact (IH (n / 10) (Nat.div_lt_self hn (by decide))).2.1 (by omega) hnf9
        rcases hab0 with ⟨a', b', hab', ha', hb'⟩
        refine ⟨10 * a', 10 * b' + 9, by omega, ?_, ?_⟩
        · exact not_has_digit_one_of_cons (d := 0) (by decide) ha' (by decide)
        · exact not_has_digit_one_of_cons (by decide) hb' (by decide)
      · by_cases h1 : n % 10 = 1
        · have hna : ¬ ∀ x ∈ Nat.digits 10 (n / 10), x = 0 ∨ x = 2 := by
            intro h02
            apply hnf
            show IsSolitaryDigits (Nat.digits 10 n)
            rw [hdig, h1]
            exact IsSolitaryDigits.one_base _ h02
          have hnd : n = 10 * (n / 10) + 1 := by
            have hdd := Nat.div_add_mod n 10
            omega
          rcases (IH (n / 10) (Nat.div_lt_self hn (by decide))).2.2 hna with ⟨x, y, hxy, hx, hy⟩
          refine ⟨10 * x + 2, 10 * y + 9, by omega, ?_, ?_⟩
          · exact not_has_digit_one_of_cons (by decide) hx (by decide)
          · exact not_has_digit_one_of_cons (by decide) hy (by decide)
        · have hnd : n = 10 * (n / 10) + n % 10 := by
            have hdd := Nat.div_add_mod n 10
            omega
          by_cases ht0 : n / 10 = 0
          · refine ⟨0, n, by omega, not_has_digit_one_zero, ?_⟩
            have hnn : n = n % 10 := by omega
            have hn0' : n ≠ 0 := by omega
            have hn10' : n < 10 := by omega
            unfold has_digit_one
            rw [Nat.digits_of_lt 10 n hn0' hn10']
            simp only [List.mem_singleton]
            omega
          · by_cases hft : is_solitary_form (n / 10)
            · have hnf1 : ¬ is_solitary_form (n / 10 - 1) := not_form_pred_of_form hft
              have ht1 : 0 < n / 10 := solitary_form_pos _ hft
              have huv : ∃ u v : ℕ, u + v = n % 10 + 10 ∧ u ≠ 1 ∧ v ≠ 1 ∧
                  0 < u ∧ u < 10 ∧ 0 < v ∧ v < 10 := by
                by_cases hd0 : n % 10 = 0
                · exact ⟨2, 8, by omega, by decide, by decide, by decide, by decide,
                    by decide, by decide⟩
                · exact ⟨n % 10 + 1, 9, by omega, by omega, by decide, by omega, by omega,
                    by decide, by decide⟩
              rcases huv with ⟨u, v, huvsum, hu1, hv1, hu0, hu10, hv0, hv10⟩
              have hab0 : ∃ x y : ℕ, x + y = n / 10 - 1 ∧ ¬ has_digit_one x ∧ ¬ has_digit_one y := by
                by_cases ht10 : n / 10 - 1 = 0
                · exact ⟨0, 0, by omega, not_has_digit_one_zero, not_has_digit_one_zero⟩
                · have hlt : n / 10 - 1 < n := by
                    have hlt' := Nat.div_lt_self hn (by decide : 1 < 10)
                    omega
                  exact (IH (n / 10 - 1) hlt).2.1 (by omega) hnf1
              rcases hab0 with ⟨x, y, hxy, hx, hy⟩
              refine ⟨10 * x + u, 10 * y + v, by omega, ?_, ?_⟩
              · exact not_has_digit_one_of_cons hu1 hx hu10
              · exact not_has_digit_one_of_cons hv1 hy hv10
            · have hlt : n / 10 < n := Nat.div_lt_self hn (by decide)
              rcases (IH (n / 10) hlt).2.1 (by omega) hft with ⟨a', b', hab', ha', hb'⟩
              refine ⟨10 * a', 10 * b' + n % 10, by omega, ?_, ?_⟩
              · exact not_has_digit_one_of_cons (d := 0) (by decide) ha' (by decide)
              · by_cases hd0 : n % 10 = 0
                · rw [hd0]
                  exact not_has_digit_one_of_cons (by decide) hb' (by decide)
                · exact not_has_digit_one_of_cons (by omega) hb' hd10
    · -- Part 3: a digit outside `{0, 2}` gives `x + y + 1 = n` with no digit `1`.
      intro hna
      have hn1 : 1 ≤ n := by
        by_contra hc
        have hn0 : n = 0 := by omega
        subst hn0
        simp [Nat.digits_zero] at hna
      have hnf1 : ¬ is_solitary_form (n - 1) := by
        intro hf1
        have h02 := all_zero_two_succ_of_form hf1
        rw [Nat.sub_add_cancel hn1] at h02
        exact hna h02
      by_cases hn10 : n = 1
      · subst hn10
        exact ⟨0, 0, by omega, not_has_digit_one_zero, not_has_digit_one_zero⟩
      · have hlt : n - 1 < n := by omega
        rcases (IH (n - 1) hlt).2.1 (by omega) hnf1 with ⟨x, y, hxy, hx, hy⟩
        exact ⟨x, y, by omega, hx, hy⟩

lemma solitary_implies_form (n : ℕ) (h : is_solitary n) : is_solitary_form n := by
  by_contra hnf
  have hn : 0 < n := h.1
  rcases (solitary_form_iff_core n).2.1 hn hnf with ⟨a, b, hab, ha, hb⟩
  rcases h.2 a b hab with h1 | h1
  · exact ha h1
  · exact hb h1

lemma form_implies_solitary_summands (n : ℕ) (h : is_solitary_form n) :
    ∀ a b : ℕ, a + b = n → has_digit_one a ∨ has_digit_one b :=
  (solitary_form_iff_core n).1 h

lemma form_implies_solitary (n : ℕ) (h : is_solitary_form n) : is_solitary n := by
  unfold is_solitary
  exact ⟨solitary_form_pos n h, form_implies_solitary_summands n h⟩

lemma solitary_iff_form (n : ℕ) : is_solitary n ↔ is_solitary_form n := by
  exact ⟨solitary_implies_form n, form_implies_solitary n⟩

/-! ### Counting -/

lemma ofDigits_replicate_nine_append_one (k : ℕ) :
    Nat.ofDigits 10 (List.replicate k 9 ++ [1]) = 2 * 10^k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, Nat.ofDigits_cons, ih]
    have h10 : 0 < 10^k := Nat.pow_pos (by decide)
    rw [pow_succ]
    omega

lemma form_replicate_nine_one (k : ℕ) : IsSolitaryDigits (List.replicate k 9 ++ [1]) := by
  induction k with
  | zero => exact IsSolitaryDigits.one_base [] (fun x hx => by simp at hx)
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    exact IsSolitaryDigits.nine_step _ ih

lemma digits_two_mul_pow (j : ℕ) : Nat.digits 10 (2 * 10^j) = List.replicate j 0 ++ [2] := by
  have h1 : Nat.ofDigits 10 (List.replicate j 0 ++ [2]) = 2 * 10^j := by
    rw [Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate]
    have h2 : Nat.ofDigits 10 [2] = 2 := rfl
    rw [h2]
    ring
  rw [← h1]
  apply Nat.digits_ofDigits 10 (by decide)
  · intro d hd
    rcases List.mem_append.mp hd with h | h
    · have h' := (List.mem_replicate.mp h).2
      omega
    · rw [List.mem_singleton] at h
      omega
  · intro hne
    rw [List.getLast_concat]
    decide

/-- The solitary-form numbers in `[10^k, 10^(k+1))` are exactly `2*10^k - 1` and
the numbers `2*10^k + m` with `m` solitary-form in `[1, 10^k)`. -/
lemma solitary_form_mem_top (k : ℕ) {n : ℕ} (hlo : 10^k ≤ n) (hhi : n < 10^(k+1))
    (hf : is_solitary_form n) :
    n = 2 * 10^k - 1 ∨ ∃ m : ℕ, 1 ≤ m ∧ m < 10^k ∧ is_solitary_form m ∧ 2 * 10^k + m = n := by
  have hn0 : n ≠ 0 := by
    have h10 : 0 < 10^k := Nat.pow_pos (by decide)
    omega
  have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn0
  have hf' : IsSolitaryDigits (Nat.digits 10 n) := hf
  have hlen : (Nat.digits 10 n).length = k + 1 := by
    have h1 : k < (Nat.digits 10 n).length := (Nat.lt_digits_length_iff (by decide) n).mpr hlo
    have h2 : (Nat.digits 10 n).length ≤ k + 1 := (Nat.digits_length_le_iff (by decide) n).mpr hhi
    omega
  have h0 : (Nat.digits 10 n).getLast hf'.ne_nil ≠ 0 := Nat.getLast_digit_ne_zero 10 hn0
  rcases hf'.getLast_eq_one_or_two h0 with hg | hg
  · -- The leading digit is `1`: all other digits are `9`.
    left
    have hrep := hf'.eq_replicate_nine_one hg
    rw [hlen] at hrep
    have hlen' : k + 1 - 1 = k := by omega
    rw [hlen'] at hrep
    have hof : Nat.ofDigits 10 (Nat.digits 10 n) = n := Nat.ofDigits_digits 10 n
    rw [hrep, ofDigits_replicate_nine_append_one] at hof
    exact hof.symm
  · -- The leading digit is `2`: strip it off.
    right
    set m := Nat.ofDigits 10 (Nat.digits 10 n).dropLast with hm_def
    have hdrop_len : (Nat.digits 10 n).dropLast.length = k := by
      rw [List.length_dropLast, hlen]
      omega
    have hg2 : (Nat.digits 10 n).getLast hne = 2 := hg
    have hn_eq : n = m + 10^k * 2 := by
      have hof : n = Nat.ofDigits 10 (Nat.digits 10 n) := (Nat.ofDigits_digits 10 n).symm
      have hsplit : Nat.digits 10 n =
          (Nat.digits 10 n).dropLast ++ [(Nat.digits 10 n).getLast hne] :=
        (List.dropLast_append_getLast hne).symm
      rw [hsplit, Nat.ofDigits_append, hdrop_len, hg2] at hof
      rw [show Nat.ofDigits 10 [2] = 2 from rfl] at hof
      exact hof
    have hm_lt : m < 10^k := by
      have h := Nat.ofDigits_lt_base_pow_length (b := 10) (by decide)
        (l := (Nat.digits 10 n).dropLast)
        (fun x hx => Nat.digits_lt_base (by decide) (List.mem_of_mem_dropLast hx))
      rwa [hdrop_len] at h
    have hm_pos : 1 ≤ m := by
      have hf_drop : IsSolitaryDigits (Nat.digits 10 n).dropLast :=
        hf'.dropLast_of_getLast_two hg
      have h1mem : 1 ∈ (Nat.digits 10 n).dropLast := is_solitary_digits_has_one hf_drop
      by_contra hc
      have hm0 : m = 0 := by omega
      have hz := Nat.digits_zero_of_eq_zero (by decide : (10:ℕ) ≠ 0) hm0 1 h1mem
      omega
    have hlen_m : (Nat.digits 10 m).length ≤ k := (Nat.digits_length_le_iff (by decide) m).mpr hm_lt
    set j := k - (Nat.digits 10 m).length with hj_def
    have hdecomp : Nat.digits 10 m ++ (List.replicate j 0 ++ [2]) = Nat.digits 10 n := by
      have h1 := Nat.digits_append_digits (b := 10) (n := m) (m := 2 * 10^j) (by decide)
      rw [digits_two_mul_pow j] at h1
      have h2 : 10 ^ (Nat.digits 10 m).length * (2 * 10^j) = 2 * 10^k := by
        have hj2 : (Nat.digits 10 m).length + j = k := by omega
        calc 10 ^ (Nat.digits 10 m).length * (2 * 10^j)
            = 2 * (10 ^ (Nat.digits 10 m).length * 10^j) := by ring
          _ = 2 * 10 ^ ((Nat.digits 10 m).length + j) := by rw [pow_add]
          _ = 2 * 10^k := by rw [hj2]
      have h3 : m + 10 ^ (Nat.digits 10 m).length * (2 * 10^j) = n := by
        rw [h2]
        omega
      rw [h3] at h1
      exact h1
    have hfm : is_solitary_form m := by
      have hf'' : IsSolitaryDigits (Nat.digits 10 n) := hf
      rw [← hdecomp] at hf''
      exact IsSolitaryDigits.of_append_replicate_zero_two j hf''
    exact ⟨m, hm_pos, hm_lt, hfm, by omega⟩

lemma solitary_form_mem_top_of_eq (k : ℕ) {n : ℕ}
    (h : n = 2 * 10^k - 1 ∨ ∃ m : ℕ, 1 ≤ m ∧ m < 10^k ∧ is_solitary_form m ∧ 2 * 10^k + m = n) :
    10^k ≤ n ∧ n < 10^(k+1) ∧ is_solitary_form n := by
  have h10 : 0 < 10^k := Nat.pow_pos (by decide)
  rcases h with rfl | ⟨m, hm1, hm2, hfm, rfl⟩
  · have hdig : Nat.digits 10 (2 * 10^k - 1) = List.replicate k 9 ++ [1] := by
      rw [← ofDigits_replicate_nine_append_one k]
      apply Nat.digits_ofDigits 10 (by decide)
      · intro d hd
        rcases List.mem_append.mp hd with h' | h'
        · have h'' := (List.mem_replicate.mp h').2
          omega
        · rw [List.mem_singleton] at h'
          omega
      · intro hne
        rw [List.getLast_concat]
        decide
    refine ⟨by omega, by rw [pow_succ]; omega, ?_⟩
    show IsSolitaryDigits (Nat.digits 10 (2 * 10^k - 1))
    rw [hdig]
    exact form_replicate_nine_one k
  · have hlen_m : (Nat.digits 10 m).length ≤ k := (Nat.digits_length_le_iff (by decide) m).mpr hm2
    have hm0 : m ≠ 0 := by omega
    set j := k - (Nat.digits 10 m).length with hj_def
    have hdig : Nat.digits 10 (2 * 10^k + m) = Nat.digits 10 m ++ (List.replicate j 0 ++ [2]) := by
      have h1 := Nat.digits_append_digits (b := 10) (n := m) (m := 2 * 10^j) (by decide)
      rw [digits_two_mul_pow j] at h1
      have h2 : m + 10 ^ (Nat.digits 10 m).length * (2 * 10^j) = 2 * 10^k + m := by
        have h3 : 10 ^ (Nat.digits 10 m).length * (2 * 10^j) = 2 * 10^k := by
          have hj2 : (Nat.digits 10 m).length + j = k := by omega
          calc 10 ^ (Nat.digits 10 m).length * (2 * 10^j)
              = 2 * (10 ^ (Nat.digits 10 m).length * 10^j) := by ring
            _ = 2 * 10 ^ ((Nat.digits 10 m).length + j) := by rw [pow_add]
            _ = 2 * 10^k := by rw [hj2]
        omega
      rw [h2] at h1
      exact h1.symm
    refine ⟨by omega, by rw [pow_succ]; omega, ?_⟩
    show IsSolitaryDigits (Nat.digits 10 (2 * 10^k + m))
    rw [hdig, ← List.append_assoc]
    exact IsSolitaryDigits.append_two (IsSolitaryDigits.append_replicate_zero j hfm)

lemma count_solitary_form_upto (k : ℕ) :
    (Finset.filter is_solitary_form (Finset.Ico 1 (10^k))).card = 2^k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h10 : 0 < 10^k := Nat.pow_pos (by decide)
    have h2k : 0 < 2^k := Nat.pow_pos (by decide)
    have hsplit : Finset.filter is_solitary_form (Finset.Ico 1 (10^(k+1))) =
        Finset.filter is_solitary_form (Finset.Ico 1 (10^k)) ∪
        Finset.filter is_solitary_form (Finset.Ico (10^k) (10^(k+1))) := by
      rw [← Finset.filter_union,
        Finset.Ico_union_Ico_eq_Ico h10 (Nat.pow_le_pow_right (by decide) (Nat.le_succ k))]
    have hdisj : Disjoint (Finset.filter is_solitary_form (Finset.Ico 1 (10^k)))
        (Finset.filter is_solitary_form (Finset.Ico (10^k) (10^(k+1)))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_Ico] at hx1 hx2
      omega
    have hnotmem : 2 * 10^k - 1 ∉
        (Finset.filter is_solitary_form (Finset.Ico 1 (10^k))).image (fun m => 2 * 10^k + m) := by
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
      rintro ⟨m, ⟨⟨hm1, hm2⟩, -⟩, hm⟩
      omega
    have hinj : Function.Injective (fun m : ℕ => 2 * 10^k + m) :=
      fun a b hab => Nat.add_left_cancel hab
    have htop : Finset.filter is_solitary_form (Finset.Ico (10^k) (10^(k+1))) =
        insert (2 * 10^k - 1)
          ((Finset.filter is_solitary_form (Finset.Ico 1 (10^k))).image (fun m => 2 * 10^k + m)) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_image]
      constructor
      · intro h
        rcases h with ⟨⟨hlo, hhi⟩, hf⟩
        rcases solitary_form_mem_top k hlo hhi hf with h | ⟨m, hm1, hm2, hfm, hmn⟩
        · exact Or.inl h
        · exact Or.inr ⟨m, ⟨⟨hm1, hm2⟩, hfm⟩, hmn⟩
      · intro h
        rcases h with rfl | ⟨m, ⟨⟨hm1, hm2⟩, hfm⟩, rfl⟩
        · have hh := solitary_form_mem_top_of_eq k (Or.inl rfl)
          exact ⟨⟨hh.1, hh.2.1⟩, hh.2.2⟩
        · have hh := solitary_form_mem_top_of_eq k (Or.inr ⟨m, hm1, hm2, hfm, rfl⟩)
          exact ⟨⟨hh.1, hh.2.1⟩, hh.2.2⟩
    rw [hsplit, Finset.card_union_of_disjoint hdisj, htop,
      Finset.card_insert_of_notMem hnotmem, Finset.card_image_of_injective _ hinj, ih, pow_succ]
    omega

lemma count_solitary_form :
    (Finset.filter is_solitary_form (Finset.Ico 1 (10^2026))).card = solution :=
  count_solitary_form_upto 2026

snip end

problem usa2026_p4 :
    (Finset.filter is_solitary (Finset.Ico 1 (10^2026))).card = solution := by
  have h_equiv : Finset.filter is_solitary (Finset.Ico 1 (10^2026)) =
                 Finset.filter is_solitary_form (Finset.Ico 1 (10^2026)) := by
    apply Finset.filter_congr
    intro n _
    exact solitary_iff_form n
  rw [h_equiv]
  exact count_solitary_form

end Usa2026P4
