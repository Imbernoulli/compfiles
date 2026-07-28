/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Mathlib
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Algebra] }

/-!
# USA Mathematical Olympiad 1983, Problem 2

Show that the five roots of the quintic
a₅x⁵ + a₄x⁴ + a₃x³ + a₂x² + a₁x + a₀ = 0
are not all real if 2a₄² < 5a₅a₃.
-/

namespace Usa1983P2

open Polynomial Finset

snip begin

-- The sum of the squares of the differences of the roots is nonnegative;
-- equivalently `5 * e₂ ≤ 2 * e₁²` for the elementary symmetric sums
-- `e₁ = ∑ rᵢ` and `e₂ = ∑_{i<j} rᵢrⱼ` of five real numbers.  This is the
-- heart of the solution: combined with Vieta's formulas it says
-- `5a₅a₃ ≤ 2a₄²` whenever all roots are real.

/-- Vieta's formula for the coefficient of `X⁴` in a product of five monic
linear factors. -/
lemma coeff_four_prod (c : ℝ) (r : Fin 5 → ℝ) :
    (C c * ∏ i : Fin 5, (X - C (r i))).coeff 4 = c * (-(∑ i, r i)) := by
  rw [coeff_C_mul]
  congr 1
  have key := Polynomial.prod_X_sub_C_coeff_card_pred (univ : Finset (Fin 5)) r (by simp)
  simpa using key

/-- Vieta's formula for the coefficient of `X³` in a product of five monic
linear factors. -/
lemma coeff_three_prod (c : ℝ) (r : Fin 5 → ℝ) :
    (C c * ∏ i : Fin 5, (X - C (r i))).coeff 3
      = c * ∑ t ∈ (univ : Finset (Fin 5)).powersetCard 2, ∏ l ∈ t, r l := by
  have h1 : ∀ i : Fin 5, (X : ℝ[X]) - C (r i) = X + C (-(r i)) := fun i => by
    rw [map_neg, sub_eq_add_neg]
  have h2 : ∏ i : Fin 5, ((X : ℝ[X]) - C (r i)) = ∏ i : Fin 5, (X + C (-(r i))) :=
    Finset.prod_congr rfl fun i _ => h1 i
  rw [coeff_C_mul, h2, Finset.prod_X_add_C_coeff _ _ (by simp),
    Finset.card_univ, Fintype.card_fin]
  show c * ∑ t ∈ (univ : Finset (Fin 5)).powersetCard 2, ∏ i ∈ t, -(r i) = _
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [mem_powersetCard] at ht
  rw [Finset.prod_neg, ht.2]
  simp

/-- The second elementary symmetric sum of five numbers, expanded. -/
lemma sum_pairs_five (r : Fin 5 → ℝ) :
    ∑ t ∈ (univ : Finset (Fin 5)).powersetCard 2, ∏ l ∈ t, r l
      = r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 0 * r 4 + r 1 * r 2 + r 1 * r 3
        + r 1 * r 4 + r 2 * r 3 + r 2 * r 4 + r 3 * r 4 := by
  rw [show (univ : Finset (Fin 5)).powersetCard 2 =
    {{0,1},{0,2},{0,3},{0,4},{1,2},{1,3},{1,4},{2,3},{2,4},{3,4}} by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  repeat rw [Finset.prod_pair (by decide)]
  ring

/-- The key inequality: for five real numbers,
`5 * ∑_{i<j} rᵢrⱼ ≤ 2 * (∑ rᵢ)²`, since the difference is one half of the
sum of the squares of the pairwise differences. -/
lemma five_mul_pairs_le_two_mul_sq_sum (r : Fin 5 → ℝ) :
    5 * (r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 0 * r 4 + r 1 * r 2 + r 1 * r 3
        + r 1 * r 4 + r 2 * r 3 + r 2 * r 4 + r 3 * r 4)
      ≤ 2 * (r 0 + r 1 + r 2 + r 3 + r 4)^2 := by
  have h : 2 * (r 0 + r 1 + r 2 + r 3 + r 4)^2
      - 5 * (r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 0 * r 4 + r 1 * r 2 + r 1 * r 3
        + r 1 * r 4 + r 2 * r 3 + r 2 * r 4 + r 3 * r 4)
      = ((r 0 - r 1)^2 + (r 0 - r 2)^2 + (r 0 - r 3)^2 + (r 0 - r 4)^2
        + (r 1 - r 2)^2 + (r 1 - r 3)^2 + (r 1 - r 4)^2
        + (r 2 - r 3)^2 + (r 2 - r 4)^2 + (r 3 - r 4)^2) / 2 := by ring
  have h2 : 0 ≤ 2 * (r 0 + r 1 + r 2 + r 3 + r 4)^2
      - 5 * (r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 0 * r 4 + r 1 * r 2 + r 1 * r 3
        + r 1 * r 4 + r 2 * r 3 + r 2 * r 4 + r 3 * r 4) := by
    rw [h]; positivity
  linarith

snip end

problem usa1983_p2 (a5 a4 a3 a2 a1 a0 : ℝ)
    (h : 2 * a4 ^ 2 < 5 * a5 * a3) :
    ¬ ∃ r : Fin 5 → ℝ,
      C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0
        = C a5 * ∏ i, (X - C (r i)) := by
  rintro ⟨r, hr⟩
  -- Vieta's relations read off the coefficients of `X⁴` and `X³`.
  have h4 : a4 = a5 * (-(∑ i, r i)) := by
    have hc := congrArg (fun p : ℝ[X] => p.coeff 4) hr
    rw [coeff_four_prod] at hc
    simpa [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] using hc
  have h3 : a3 = a5 * (∑ t ∈ (univ : Finset (Fin 5)).powersetCard 2, ∏ l ∈ t, r l) := by
    have hc := congrArg (fun p : ℝ[X] => p.coeff 3) hr
    rw [coeff_three_prod] at hc
    simpa [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] using hc
  -- Hence `2 * e₁² < 5 * e₂` for the symmetric sums of the roots.
  have hlt : 2 * (∑ i, r i)^2
      < 5 * (∑ t ∈ (univ : Finset (Fin 5)).powersetCard 2, ∏ l ∈ t, r l) := by
    rw [h4, h3] at h
    have h' : a5^2 * (2 * (∑ i, r i)^2)
        < a5^2 * (5 * (∑ t ∈ (univ : Finset (Fin 5)).powersetCard 2, ∏ l ∈ t, r l)) := by
      convert h using 1 <;> ring
    exact lt_of_mul_lt_mul_left h' (sq_nonneg a5)
  -- But the key inequality gives the reverse (non-strict) inequality.
  have key : 5 * (∑ t ∈ (univ : Finset (Fin 5)).powersetCard 2, ∏ l ∈ t, r l)
      ≤ 2 * (∑ i, r i)^2 := by
    rw [Fin.sum_univ_five r, sum_pairs_five r]
    exact five_mul_pairs_le_two_mul_sq_sum r
  linarith

end Usa1983P2
