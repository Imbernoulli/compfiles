/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Normed.Field.Basic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 2016, Problem 4

Find all functions f : ℝ → ℝ such that for all real numbers x and y,

  (f(x) + xy) · f(x - 3y) + (f(y) + xy) · f(3x - y) = (f(x + y))².
-/

namespace Usa2016P4

determine SolutionSet : Set (ℝ → ℝ) := {0, fun x ↦ x ^ 2}

snip begin

/-- The functional equation of the problem, as a predicate on `f`. -/
def Fe (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, (f x + x * y) * f (x - 3 * y) + (f y + x * y) * f (3 * x - y) =
    (f (x + y)) ^ 2

/-- Substituting `x = y = 0` forces `f 0 = 0`. -/
lemma fe_f_zero {f : ℝ → ℝ} (hf : Fe f) : f 0 = 0 := by
  have h := hf 0 0
  simp only [mul_zero, add_zero, sub_zero] at h
  have h2 : f 0 ^ 2 = 0 := by nlinarith [h]
  exact sq_eq_zero_iff.mp h2

/-- Substituting `x = 0` shows that `f` is even. -/
lemma fe_even {f : ℝ → ℝ} (hf : Fe f) (y : ℝ) : f (-y) = f y := by
  have h0 := fe_f_zero hf
  have hA := hf 0 y
  have hB := hf 0 (-y)
  simp only [h0, zero_mul, mul_zero, add_zero, zero_add, zero_sub, neg_neg] at hA hB
  -- hA : f y * f (-y) = f y ^ 2 and hB : f (-y) * f y = f (-y) ^ 2
  by_cases hy : f y = 0
  · have hB' : f (-y) ^ 2 = 0 := by
      rw [hy, mul_zero] at hB
      exact hB.symm
    rw [sq_eq_zero_iff] at hB'
    rw [hB', hy]
  · have hA' : f y * f (-y) = f y * f y := by
      rw [← pow_two]
      exact hA
    exact mul_left_cancel₀ hy hA'

/-- Substituting `x = -y` shows that for each `t`,
either `f t = t ^ 2` or `f (4 * t) = 0`. -/
lemma fe_star {f : ℝ → ℝ} (hf : Fe f) (t : ℝ) : f t = t ^ 2 ∨ f (4 * t) = 0 := by
  have h0 := fe_f_zero hf
  have hev := fe_even hf
  have h := hf (-t) t
  have e1 : -t + t = 0 := neg_add_cancel t
  have e2 : -t - 3 * t = -(4 * t) := by ring
  have e3 : 3 * -t - t = -(4 * t) := by ring
  have e4 : -t * t = -(t ^ 2) := by ring
  rw [e1, e2, e3, e4, hev t, h0, hev (4 * t)] at h
  have hz2 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [hz2] at h
  have h2 : (f t - t ^ 2) * f (4 * t) = 0 := by linarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left
    linarith [h3]
  · right
    exact h3

/-- Substituting `(x, y) = (3t, t)` gives the key identity
relating the values `f t`, `f (8 * t)` and `f (4 * t)`. -/
lemma fe_key {f : ℝ → ℝ} (hf : Fe f) (t : ℝ) :
    (f t + 3 * t ^ 2) * f (8 * t) = (f (4 * t)) ^ 2 := by
  have h0 := fe_f_zero hf
  have h := hf (3 * t) t
  have e1 : 3 * t - 3 * t = 0 := by ring
  have e2 : 3 * (3 * t) - t = 8 * t := by ring
  have e3 : 3 * t + t = 4 * t := by ring
  have e4 : 3 * t * t = 3 * t ^ 2 := by ring
  rw [e1, e2, e3, e4, h0] at h
  rw [mul_zero, zero_add] at h
  exact h

/-- `f` vanishes at `z` if and only if it vanishes at `2 * z`. -/
lemma fe_double_zero {f : ℝ → ℝ} (hf : Fe f) (z : ℝ) : f z = 0 ↔ f (2 * z) = 0 := by
  have h0 := fe_f_zero hf
  have rev : ∀ u : ℝ, f u ≠ 0 → f (2 * u) ≠ 0 := by
    intro u hu h2u
    have h := fe_key hf (u / 4)
    have e1 : 8 * (u / 4) = 2 * u := by ring
    have e2 : 4 * (u / 4) = u := by ring
    rw [e1, e2, h2u, mul_zero] at h
    exact hu (sq_eq_zero_iff.mp h.symm)
  constructor
  · intro hz
    by_contra h2z
    have ht : f (z / 2) = (z / 2) ^ 2 := by
      rcases fe_star hf (z / 2) with h | h
      · exact h
      · have e : 4 * (z / 2) = 2 * z := by ring
        rw [e] at h
        exact absurd h h2z
    have hzz : z / 2 ≠ 0 := by
      intro hzz0
      have hz0 : z = 0 := by linarith [hzz0]
      rw [hz0, mul_zero] at h2z
      exact h2z h0
    have hne : f (z / 2) ≠ 0 := by
      rw [ht]
      exact pow_ne_zero 2 hzz
    have h3 : f (2 * (z / 2)) ≠ 0 := rev (z / 2) hne
    have e : 2 * (z / 2) = z := by ring
    rw [e] at h3
    exact h3 hz
  · intro h2z
    by_contra hz
    exact rev z hz h2z

/-- For every `x`, either `f x = x ^ 2` or `f x = 0`. -/
lemma fe_cases {f : ℝ → ℝ} (hf : Fe f) (x : ℝ) : f x = x ^ 2 ∨ f x = 0 := by
  rcases fe_star hf x with h | h
  · exact Or.inl h
  · have h4 : f (2 * (2 * x)) = 0 := by
      have e : 2 * (2 * x) = 4 * x := by ring
      rw [e]
      exact h
    have h1 : f (2 * x) = 0 := (fe_double_zero hf (2 * x)).mpr h4
    exact Or.inr ((fe_double_zero hf x).mpr h1)

/-- `f` is nonnegative everywhere. -/
lemma fe_nn {f : ℝ → ℝ} (hf : Fe f) (x : ℝ) : 0 ≤ f x := by
  rcases fe_cases hf x with h | h
  · rw [h]
    exact sq_nonneg x
  · exact h.ge

/-- If `f` vanishes at some positive `a`, then it vanishes at every positive `b`. -/
lemma fe_all_zero {f : ℝ → ℝ} (hf : Fe f) {a : ℝ} (ha : 0 < a) (ha0 : f a = 0)
    (b : ℝ) (hb : 0 < b) : f b = 0 := by
  have hnn := fe_nn hf
  have hd := fe_double_zero hf
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b < (2 : ℝ) ^ n * a := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / a) (one_lt_two : (1 : ℝ) < 2)
    exact ⟨n, (div_lt_iff₀ ha).mp hn⟩
  set c : ℝ := (2 : ℝ) ^ n * a with hc
  have hpow : ∀ k : ℕ, f ((2 : ℝ) ^ k * a) = 0 := by
    intro k
    induction k with
    | zero => simpa using ha0
    | succ k ih =>
      have e : (2 : ℝ) ^ (k + 1) * a = 2 * ((2 : ℝ) ^ k * a) := by ring
      rw [e]
      exact (hd _).mp ih
  have hc0 : f c = 0 := by
    rw [hc]
    exact hpow n
  have hcb : b < c := hn
  have hcpos : 0 < c := by
    rw [hc]
    exact mul_pos (pow_pos (by norm_num) n) ha
  set x : ℝ := (3 * c + b) / 4 with hx
  set y : ℝ := (c - b) / 4 with hy
  have e1 : x - 3 * y = b := by rw [hx, hy]; ring
  have e2 : x + y = c := by rw [hx, hy]; ring
  have e3 : 3 * x - y = 2 * c + b := by rw [hx, hy]; ring
  have hypos : 0 < y := by rw [hy]; linarith [hcb]
  have hxpos : 0 < x := by rw [hx]; linarith [hcpos, hb]
  have hxy : 0 < x * y := mul_pos hxpos hypos
  have h := hf x y
  rw [e1, e2, e3, hc0] at h
  have hz2 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [hz2] at h
  have t1 : 0 ≤ (f x + x * y) * f b := mul_nonneg (by linarith [hnn x, hxy]) (hnn b)
  have t2 : 0 ≤ (f y + x * y) * f (2 * c + b) :=
    mul_nonneg (by linarith [hnn y, hxy]) (hnn _)
  have ht1 : (f x + x * y) * f b = 0 := by linarith [h, t1, t2]
  have hpos : 0 < f x + x * y := by linarith [hnn x, hxy]
  rcases mul_eq_zero.mp ht1 with hcase | hcase
  · linarith [hcase, hpos]
  · exact hcase

snip end

problem usa2016_p4 (f : ℝ → ℝ) :
    f ∈ SolutionSet ↔
      ∀ x y : ℝ, (f x + x * y) * f (x - 3 * y) + (f y + x * y) * f (3 * x - y) =
        (f (x + y)) ^ 2 := by
  -- informal solution from
  -- https://web.evanchen.cc/exams/USAMO-2016-notes.pdf
  constructor
  · rintro (rfl | rfl) x y
    · show (0 + x * y) * 0 + (0 + x * y) * 0 = (0 : ℝ) ^ 2
      ring
    · show (x ^ 2 + x * y) * (x - 3 * y) ^ 2 + (y ^ 2 + x * y) * (3 * x - y) ^ 2 =
        ((x + y) ^ 2) ^ 2
      ring
  · intro hf
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hcase : ∃ a : ℝ, a ≠ 0 ∧ f a = 0
    · -- in this case we show that `f` is identically zero
      left
      obtain ⟨a, hane, ha0⟩ := hcase
      have h0 := fe_f_zero hf
      have hev := fe_even hf
      have ha' : 0 < |a| := abs_pos.mpr hane
      have hfa' : f |a| = 0 := by
        rcases lt_or_ge a 0 with hlt | hle
        · rw [abs_of_neg hlt, hev a]
          exact ha0
        · rwa [abs_of_nonneg hle]
      funext b
      show f b = 0
      by_cases hb0 : b = 0
      · rw [hb0]
        exact h0
      · have hb' : 0 < |b| := abs_pos.mpr hb0
        have hfb : f b = f |b| := by
          rcases lt_or_ge b 0 with hlt | hle
          · rw [abs_of_neg hlt]
            exact (hev b).symm
          · rw [abs_of_nonneg hle]
        rw [hfb]
        exact fe_all_zero hf ha' hfa' |b| hb'
    · -- in this case `f x ≠ 0` for all `x ≠ 0`, so `f x = x ^ 2` everywhere
      right
      push Not at hcase
      funext x
      show f x = x ^ 2
      by_cases hx : x = 0
      · rw [hx, fe_f_zero hf]
        norm_num
      · rcases fe_cases hf x with h | h
        · exact h
        · exact absurd h (hcase x hx)

end Usa2016P4
