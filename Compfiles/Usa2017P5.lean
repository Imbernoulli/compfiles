/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Mathlib.Tactic
public import ProblemExtraction

@[expose] public section

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 2017, Problem 5

Determine the set of positive real numbers c such that there exists
a labeling of the lattice points in ℤ² with positive integers for which:

  1. only finitely many distinct labels occur, and
  2. for each label i, the distance between any two points labeled i
     is at least cⁱ.
-/

namespace Usa2017P5

determine solution_set : Set ℝ := Set.Ioo 0 (Real.sqrt 2)

noncomputable def dist : ℤ × ℤ → ℤ × ℤ → ℝ
| ⟨x1, y1⟩, ⟨x2, y2⟩ => Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2)

snip begin

lemma dist_eq' (p1 p2 : ℤ × ℤ) :
    dist p1 p2 = Real.sqrt (((p2.1 : ℝ) - p1.1)^2 + ((p2.2 : ℝ) - p1.2)^2) := by
  obtain ⟨x1, y1⟩ := p1
  obtain ⟨x2, y2⟩ := p2
  rfl

/-- Among any four vectors in ℝ², some two have nonnegative dot product. -/
lemma four_vecs (v : Fin 4 → ℝ × ℝ) :
    ∃ i j : Fin 4, i ≠ j ∧ 0 ≤ (v i).1 * (v j).1 + (v i).2 * (v j).2 := by
  by_contra h
  push Not at h
  classical
  by_cases hinj : Function.Injective
      (fun i => (decide (0 ≤ (v i).1), decide (0 ≤ (v i).2)) : Fin 4 → Bool × Bool)
  · -- each of the four sign-quadrants occurs exactly once
    have hbij : Function.Bijective
        (fun i => (decide (0 ≤ (v i).1), decide (0 ≤ (v i).2)) : Fin 4 → Bool × Bool) := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hinj, by decide⟩
    obtain ⟨i1, hi1⟩ := hbij.2 (true, true)
    obtain ⟨i2, hi2⟩ := hbij.2 (false, true)
    obtain ⟨i3, hi3⟩ := hbij.2 (false, false)
    obtain ⟨i4, hi4⟩ := hbij.2 (true, false)
    have d12 : i1 ≠ i2 := by
      intro hh; subst hh; rw [hi1] at hi2; exact absurd hi2 (by decide)
    have d23 : i2 ≠ i3 := by
      intro hh; subst hh; rw [hi2] at hi3; exact absurd hi3 (by decide)
    have d34 : i3 ≠ i4 := by
      intro hh; subst hh; rw [hi3] at hi4; exact absurd hi4 (by decide)
    have d41 : i4 ≠ i1 := by
      intro hh; subst hh; rw [hi4] at hi1; exact absurd hi1 (by decide)
    have ha1 : 0 ≤ (v i1).1 := of_decide_eq_true (congrArg Prod.fst hi1)
    have hb1 : 0 ≤ (v i1).2 := of_decide_eq_true (congrArg Prod.snd hi1)
    have ha2 : (v i2).1 < 0 := not_le.mp (of_decide_eq_false (congrArg Prod.fst hi2))
    have hb2 : 0 ≤ (v i2).2 := of_decide_eq_true (congrArg Prod.snd hi2)
    have ha3 : (v i3).1 < 0 := not_le.mp (of_decide_eq_false (congrArg Prod.fst hi3))
    have hb3 : (v i3).2 < 0 := not_le.mp (of_decide_eq_false (congrArg Prod.snd hi3))
    have ha4 : 0 ≤ (v i4).1 := of_decide_eq_true (congrArg Prod.fst hi4)
    have hb4 : (v i4).2 < 0 := not_le.mp (of_decide_eq_false (congrArg Prod.snd hi4))
    have h12 : (v i1).1 * (v i2).1 < 0 := by nlinarith [h i1 i2 d12, mul_nonneg hb1 hb2]
    have a1pos : 0 < (v i1).1 := pos_of_mul_neg_left h12 (le_of_lt ha2)
    have h23 : (v i2).2 * (v i3).2 < 0 := by
      nlinarith [h i2 i3 d23, mul_pos_of_neg_of_neg ha2 ha3]
    have b2pos : 0 < (v i2).2 := pos_of_mul_neg_left h23 (le_of_lt hb3)
    have h34 : (v i3).1 * (v i4).1 < 0 := by
      nlinarith [h i3 i4 d34, mul_pos_of_neg_of_neg hb3 hb4]
    have a4pos : 0 < (v i4).1 := pos_of_mul_neg_right h34 (le_of_lt ha3)
    have h41 : (v i4).2 * (v i1).2 < 0 := by
      nlinarith [h i4 i1 d41, mul_nonneg ha4 (le_of_lt a1pos)]
    have b1pos : 0 < (v i1).2 := pos_of_mul_neg_right h41 (le_of_lt hb4)
    have c12 : (v i1).2 * (v i2).2 < (v i1).1 * (-(v i2).1) := by nlinarith [h i1 i2 d12]
    have c23 : (-(v i2).1) * (-(v i3).1) < (v i2).2 * (-(v i3).2) := by
      nlinarith [h i2 i3 d23]
    have c34 : (-(v i3).2) * (-(v i4).2) < (-(v i3).1) * (v i4).1 := by
      nlinarith [h i3 i4 d34]
    have c41 : (v i4).1 * (v i1).1 < (-(v i4).2) * (v i1).2 := by nlinarith [h i4 i1 d41]
    have m1 := mul_lt_mul c12 c23.le
      (mul_pos (neg_pos.mpr ha2) (neg_pos.mpr ha3))
      (le_of_lt (mul_pos a1pos (neg_pos.mpr ha2)))
    have m2 := mul_lt_mul m1 c34.le
      (mul_pos (neg_pos.mpr hb3) (neg_pos.mpr hb4))
      (le_of_lt (mul_pos (mul_pos a1pos (neg_pos.mpr ha2)) (mul_pos b2pos (neg_pos.mpr hb3))))
    have m3 := mul_lt_mul m2 c41.le (mul_pos a4pos a1pos)
      (le_of_lt (mul_pos (mul_pos (mul_pos a1pos (neg_pos.mpr ha2))
        (mul_pos b2pos (neg_pos.mpr hb3))) (mul_pos (neg_pos.mpr ha3) a4pos)))
    have e : ((v i1).1 * -(v i2).1) * ((v i2).2 * -(v i3).2) * ((-(v i3).1) * (v i4).1) *
        ((-(v i4).2) * (v i1).2) =
        ((v i1).2 * (v i2).2) * ((-(v i2).1) * (-(v i3).1)) * ((-(v i3).2) * (-(v i4).2)) *
        ((v i4).1 * (v i1).1) := by ring
    rw [e] at m3
    exact absurd m3 (lt_irrefl _)
  · -- two vectors lie in the same sign-quadrant
    have hni : ∃ i j, (decide (0 ≤ (v i).1), decide (0 ≤ (v i).2)) =
        (decide (0 ≤ (v j).1), decide (0 ≤ (v j).2)) ∧ i ≠ j := by
      by_contra hc
      push Not at hc
      exact hinj (fun i j hh => hc i j hh)
    obtain ⟨i, j, hqq, hne⟩ := hni
    have hx : (0 ≤ (v i).1) ↔ (0 ≤ (v j).1) := decide_eq_decide.mp (congrArg Prod.fst hqq)
    have hy : (0 ≤ (v i).2) ↔ (0 ≤ (v j).2) := decide_eq_decide.mp (congrArg Prod.snd hqq)
    have h1 : 0 ≤ (v i).1 * (v j).1 := by
      by_cases h0 : 0 ≤ (v i).1
      · exact mul_nonneg h0 (hx.mp h0)
      · have h0' : ¬ 0 ≤ (v j).1 := fun hj => h0 (hx.mpr hj)
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt (not_le.mp h0)) (le_of_lt (not_le.mp h0'))
    have h2 : 0 ≤ (v i).2 * (v j).2 := by
      by_cases h0 : 0 ≤ (v i).2
      · exact mul_nonneg h0 (hy.mp h0)
      · have h0' : ¬ 0 ≤ (v j).2 := fun hj => h0 (hy.mpr hj)
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt (not_le.mp h0)) (le_of_lt (not_le.mp h0'))
    exact absurd (add_nonneg h1 h2) (not_le.mpr (h i j hne))

lemma sq_le_of_abs_le {x u : ℤ} (hu : 0 ≤ u) (h : |x| ≤ u) : x^2 ≤ u^2 :=
  sq_le_sq.mpr (by rwa [abs_of_nonneg hu])

lemma dist_le_of_sq {p1 p2 : ℤ × ℤ} {u v B : ℤ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : |p2.1 - p1.1| ≤ u) (hy : |p2.2 - p1.2| ≤ v) (hB : u^2 + v^2 ≤ B) :
    dist p1 p2 ≤ Real.sqrt (B : ℤ) := by
  rw [dist_eq']
  apply Real.sqrt_le_sqrt
  have h1 : (p2.1 - p1.1)^2 ≤ u^2 := sq_le_of_abs_le hu hx
  have h2 : (p2.2 - p1.2)^2 ≤ v^2 := sq_le_of_abs_le hv hy
  have h3 : (p2.1 - p1.1)^2 + (p2.2 - p1.2)^2 ≤ B := (add_le_add h1 h2).trans hB
  exact_mod_cast h3

lemma dist_lt_of_sq {p1 p2 : ℤ × ℤ} {u v B : ℤ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : |p2.1 - p1.1| ≤ u) (hy : |p2.2 - p1.2| ≤ v) (hB : u^2 + v^2 < B) :
    dist p1 p2 < Real.sqrt (B : ℤ) := by
  have h1 : dist p1 p2 ≤ Real.sqrt ((u^2 + v^2 : ℤ)) :=
    dist_le_of_sq hu hv hx hy (le_refl _)
  refine lt_of_le_of_lt h1 (Real.sqrt_lt_sqrt ?_ ?_)
  · exact_mod_cast (by positivity : (0:ℤ) ≤ u^2 + v^2)
  · exact_mod_cast hB

lemma sqrt_two_mul_sq {m : ℝ} (hm : 0 ≤ m) : Real.sqrt (2 * m^2) = Real.sqrt 2 * m := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hm]

lemma sqrt2_pow_odd (n : ℕ) : (Real.sqrt 2)^(2*n+1) = Real.sqrt 2 * 2^n := by
  rw [pow_succ', pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma sqrt2_pow_even (n : ℕ) : (Real.sqrt 2)^(2*n+2) = 2^(n+1) := by
  rw [show 2*n+2 = 2*(n+1) by ring, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- Among any four points of a `2^(n+1) × 2^(n+1)` grid of lattice points,
some two are at distance strictly less than `2^(n+1)`. -/
lemma grid_four {n : ℕ} {a b : ℤ} {p : Fin 4 → ℤ × ℤ}
    (hp : ∀ i, a ≤ (p i).1 ∧ (p i).1 < a + 2^(n+1) ∧ b ≤ (p i).2 ∧ (p i).2 < b + 2^(n+1)) :
    ∃ i j : Fin 4, i ≠ j ∧ dist (p i) (p j) < (2:ℝ)^(n+1) := by
  have hR1 : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hps : (2:ℝ)^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
  obtain ⟨i, j, hij, hdot⟩ :=
    four_vecs (fun i => ((p i).1 - (a + 2^n - 1/2), (p i).2 - (b + 2^n - 1/2)))
  have hub : ∀ i, |(p i).1 - (a + 2^n - 1/2 : ℝ)| ≤ (2:ℝ)^n - 1/2 ∧
      |(p i).2 - (b + 2^n - 1/2 : ℝ)| ≤ (2:ℝ)^n - 1/2 := by
    intro i
    obtain ⟨h1, h2, h3, h4⟩ := hp i
    have hx1 : (a:ℝ) ≤ (p i).1 := Int.cast_le.mpr h1
    have hx2 : ((p i).1 : ℝ) ≤ a + 2 * 2^n - 1 := by
      have hh : (p i).1 ≤ a + 2^(n+1) - 1 := by omega
      have hh' : (((p i).1 : ℤ) : ℝ) ≤ (a + 2^(n+1) - 1 : ℤ) := Int.cast_le.mpr hh
      push_cast at hh'
      rw [hps] at hh'
      linarith [hh']
    have hy1 : (b:ℝ) ≤ (p i).2 := Int.cast_le.mpr h3
    have hy2 : ((p i).2 : ℝ) ≤ b + 2 * 2^n - 1 := by
      have hh : (p i).2 ≤ b + 2^(n+1) - 1 := by omega
      have hh' : (((p i).2 : ℤ) : ℝ) ≤ (b + 2^(n+1) - 1 : ℤ) := Int.cast_le.mpr hh
      push_cast at hh'
      rw [hps] at hh'
      linarith [hh']
    constructor <;> rw [abs_le] <;> constructor <;> linarith
  obtain ⟨hxi, hyi⟩ := hub i
  obtain ⟨hxj, hyj⟩ := hub j
  refine ⟨i, j, hij, ?_⟩
  have hr : (0:ℝ) ≤ (2:ℝ)^n - 1/2 := by linarith [hR1]
  have hsqi1 : ((p i).1 - (a + 2^n - 1/2 : ℝ))^2 ≤ ((2:ℝ)^n - 1/2)^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hr])
  have hsqi2 : ((p i).2 - (b + 2^n - 1/2 : ℝ))^2 ≤ ((2:ℝ)^n - 1/2)^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hr])
  have hsqj1 : ((p j).1 - (a + 2^n - 1/2 : ℝ))^2 ≤ ((2:ℝ)^n - 1/2)^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hr])
  have hsqj2 : ((p j).2 - (b + 2^n - 1/2 : ℝ))^2 ≤ ((2:ℝ)^n - 1/2)^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hr])
  have hdist : dist (p i) (p j) ≤ 2 * (2:ℝ)^n - 1 := by
    rw [dist_eq', Real.sqrt_le_iff]
    refine ⟨by linarith [hR1], ?_⟩
    have key : ((p j).1 - (p i).1 : ℝ)^2 + ((p j).2 - (p i).2 : ℝ)^2 ≤
        ((p i).1 - (a + 2^n - 1/2 : ℝ))^2 + ((p i).2 - (b + 2^n - 1/2 : ℝ))^2 +
        ((p j).1 - (a + 2^n - 1/2 : ℝ))^2 + ((p j).2 - (b + 2^n - 1/2 : ℝ))^2 := by
      nlinarith [hdot]
    nlinarith [key, hsqi1, hsqi2, hsqj1, hsqj2]
  rw [hps]
  linarith [hdist, hR1]

lemma grid_main (n : ℕ) : ∀ (a b : ℤ) (l : ℤ × ℤ → ℕ),
    (∀ p, 0 < l p) →
    (∀ {p1 p2}, p1 ≠ p2 → l p1 = l p2 → (Real.sqrt 2) ^ (l p1) ≤ dist p1 p2) →
    ∃ p : ℤ × ℤ, a ≤ p.1 ∧ p.1 < a + 2^n ∧ b ≤ p.2 ∧ p.2 < b + 2^n ∧ 2 * n + 1 ≤ l p := by
  induction n with
  | zero =>
    intro a b l hpos _
    exact ⟨⟨a, b⟩, le_refl a, by omega, le_refl b, by omega, hpos _⟩
  | succ n ih =>
    intro a b l hpos hvalid
    have hm : (0:ℤ) < 2^n := by positivity
    have h2n1 : (2:ℤ)^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    by_contra hcon
    push Not at hcon
    rw [h2n1] at hcon
    have hall : ∀ p, a ≤ p.1 → p.1 < a + 2*2^n → b ≤ p.2 → p.2 < b + 2*2^n →
        l p ≤ 2*n+2 := fun p h1 h2 h3 h4 => by
      have h := hcon p h1 h2 h3 h4
      omega
    -- conversion: the bound `√(2·(2^n)²) = (√2)^(2n+1)`
    have hconv : Real.sqrt ((2*(2^n)^2 : ℤ) : ℝ) = (Real.sqrt 2)^(2*n+1) := by
      rw [show ((2*(2^n)^2 : ℤ) : ℝ) = 2 * ((2:ℝ)^n)^2 by push_cast; ring,
          sqrt_two_mul_sq (by positivity), ← sqrt2_pow_odd]
    have hstep : (Real.sqrt 2)^(2*n+1) < (Real.sqrt 2)^(2*n+2) := by
      have hs2 : Real.sqrt 2 < 2 := by
        have h1 : (Real.sqrt 2)^2 < (2:ℝ)^2 := by
          rw [Real.sq_sqrt (by norm_num)]; norm_num
        nlinarith [h1, Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)]
      rw [sqrt2_pow_odd, sqrt2_pow_even, pow_succ]
      nlinarith [hs2, pow_pos (by norm_num : (0:ℝ) < 2) n]
    -- the heart of the argument: contradiction from an empty "northwest" quadrant
    have core : ∀ (a b : ℤ) (l : ℤ × ℤ → ℕ),
        (∀ p, 0 < l p) →
        (∀ {p1 p2}, p1 ≠ p2 → l p1 = l p2 → (Real.sqrt 2) ^ (l p1) ≤ dist p1 p2) →
        (∀ p, a ≤ p.1 → p.1 < a + 2*2^n → b ≤ p.2 → p.2 < b + 2*2^n → l p ≤ 2*n+2) →
        (∀ p, a ≤ p.1 → p.1 < a + 2^n → b + 2^n ≤ p.2 → p.2 < b + 2*2^n → l p ≠ 2*n+2) →
        False := by
      intro a b l hpos hvalid hall hnw
      obtain ⟨P, hP1, hP2, hP3, hP4, hP5⟩ := ih a (b + 2^n) l hpos hvalid
      have hPl : l P = 2*n+1 := by
        have h6 : l P ≤ 2*n+2 := hall P hP1 (by omega) (by omega) (by omega)
        have h7 : l P ≠ 2*n+2 := hnw P hP1 hP2 hP3 (by omega)
        omega
      obtain ⟨Q, hQ1, hQ2, hQ3, hQ4, hQ5⟩ := ih (P.1 + 1) (b + 2^n) l hpos hvalid
      have hPQ : dist P Q < (Real.sqrt 2)^(2*n+1) := by
        have h1 : dist P Q < Real.sqrt ((2*(2^n)^2 : ℤ) : ℝ) :=
          dist_lt_of_sq (u := 2^n) (v := 2^n - 1) (B := 2*(2^n)^2) hm.le (by omega)
            (by rw [abs_le]; constructor <;> omega)
            (by rw [abs_le]; constructor <;> omega)
            (by nlinarith [hm])
        rwa [hconv] at h1
      have hQne1 : l Q ≠ 2*n+1 := by
        intro hh
        have hne : P ≠ Q := fun h => by rw [h] at hQ1; omega
        have h2 := hvalid hne (by rw [hPl, hh])
        rw [hPl] at h2
        linarith [hPQ, h2]
      have hQl : l Q = 2*n+2 := by
        have h6 : l Q ≤ 2*n+2 := hall Q (by omega) (by omega) (by omega) (by omega)
        omega
      have hQne : a + 2^n ≤ Q.1 := by
        by_contra hh
        push Not at hh
        exact hnw Q (by omega) hh hQ3 (by omega) hQl
      rcases em (Q.2 ≤ P.2) with hcase | hcase
      · -- B = [Q.1 - 2^n, Q.1 - 1] × [P.2 - 2^n, P.2 - 1]
        obtain ⟨R, hR1, hR2, hR3, hR4, hR5⟩ := ih (Q.1 - 2^n) (P.2 - 2^n) l hpos hvalid
        have hRgrid : l R ≤ 2*n+2 := hall R (by omega) (by omega) (by omega) (by omega)
        have hRP : dist R P < (Real.sqrt 2)^(2*n+1) := by
          have h1 : dist R P < Real.sqrt ((2*(2^n)^2 : ℤ) : ℝ) :=
            dist_lt_of_sq (u := 2^n - 1) (v := 2^n) (B := 2*(2^n)^2) (by omega) hm.le
              (by rw [abs_le]; constructor <;> omega)
              (by rw [abs_le]; constructor <;> omega)
              (by nlinarith [hm])
          rwa [hconv] at h1
        have hRQ : dist R Q < (Real.sqrt 2)^(2*n+2) := by
          have h1 : dist R Q ≤ Real.sqrt ((2*(2^n)^2 : ℤ) : ℝ) :=
            dist_le_of_sq (u := 2^n) (v := 2^n) (B := 2*(2^n)^2) hm.le hm.le
              (by rw [abs_le]; constructor <;> omega)
              (by rw [abs_le]; constructor <;> omega)
              (by nlinarith [hm])
          rw [hconv] at h1
          exact lt_of_le_of_lt h1 hstep
        have hn1 : l R ≠ 2*n+1 := by
          intro hh
          have hne : R ≠ P := fun h => by rw [h] at hR4; omega
          have h2 := hvalid hne (by rw [hh, hPl])
          rw [hh] at h2
          linarith [hRP, h2]
        have hn2 : l R ≠ 2*n+2 := by
          intro hh
          have hne : R ≠ Q := fun h => by rw [h] at hR2; omega
          have h2 := hvalid hne (by rw [hh, hQl])
          rw [hh] at h2
          linarith [hRQ, h2]
        omega
      · push Not at hcase
        -- B = [P.1 + 1, P.1 + 2^n] × [Q.2 - 2^n, Q.2 - 1]
        obtain ⟨R, hR1, hR2, hR3, hR4, hR5⟩ := ih (P.1 + 1) (Q.2 - 2^n) l hpos hvalid
        have hRgrid : l R ≤ 2*n+2 := hall R (by omega) (by omega) (by omega) (by omega)
        have hRP : dist R P < (Real.sqrt 2)^(2*n+1) := by
          have h1 : dist R P < Real.sqrt ((2*(2^n)^2 : ℤ) : ℝ) :=
            dist_lt_of_sq (u := 2^n) (v := 2^n - 1) (B := 2*(2^n)^2) hm.le (by omega)
              (by rw [abs_le]; constructor <;> omega)
              (by rw [abs_le]; constructor <;> omega)
              (by nlinarith [hm])
          rwa [hconv] at h1
        have hRQ : dist R Q < (Real.sqrt 2)^(2*n+2) := by
          have h1 : dist R Q < Real.sqrt ((2*(2^n)^2 : ℤ) : ℝ) :=
            dist_lt_of_sq (u := 2^n - 1) (v := 2^n) (B := 2*(2^n)^2) (by omega) hm.le
              (by rw [abs_le]; constructor <;> omega)
              (by rw [abs_le]; constructor <;> omega)
              (by nlinarith [hm])
          rw [hconv] at h1
          exact lt_trans h1 hstep
        have hn1 : l R ≠ 2*n+1 := by
          intro hh
          have hne : R ≠ P := fun h => by rw [h] at hR1; omega
          have h2 := hvalid hne (by rw [hh, hPl])
          rw [hh] at h2
          linarith [hRP, h2]
        have hn2 : l R ≠ 2*n+2 := by
          intro hh
          have hne : R ≠ Q := fun h => by rw [h] at hR4; omega
          have h2 := hvalid hne (by rw [hh, hQl])
          rw [hh] at h2
          linarith [hRQ, h2]
        omega
    -- some quadrant has no label `2n+2`
    have quad : (∀ p, a ≤ p.1 → p.1 < a + 2^n → b + 2^n ≤ p.2 → p.2 < b + 2*2^n →
        l p ≠ 2*n+2) ∨
        (∀ p, a + 2^n ≤ p.1 → p.1 < a + 2*2^n → b + 2^n ≤ p.2 → p.2 < b + 2*2^n →
          l p ≠ 2*n+2) ∨
        (∀ p, a ≤ p.1 → p.1 < a + 2^n → b ≤ p.2 → p.2 < b + 2^n → l p ≠ 2*n+2) ∨
        (∀ p, a + 2^n ≤ p.1 → p.1 < a + 2*2^n → b ≤ p.2 → p.2 < b + 2^n →
          l p ≠ 2*n+2) := by
      by_contra hq
      push Not at hq
      obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩, ⟨p4, hp4⟩⟩ := hq
      obtain ⟨hp1a, hp1b, hp1c, hp1d, hp1e⟩ := hp1
      obtain ⟨hp2a, hp2b, hp2c, hp2d, hp2e⟩ := hp2
      obtain ⟨hp3a, hp3b, hp3c, hp3d, hp3e⟩ := hp3
      obtain ⟨hp4a, hp4b, hp4c, hp4d, hp4e⟩ := hp4
      have hpd : ∀ i j : Fin 4, i ≠ j →
          (![p1, p2, p3, p4] : Fin 4 → ℤ × ℤ) i ≠ ![p1, p2, p3, p4] j := by
        intro i j hh he
        fin_cases i <;> fin_cases j
        all_goals first
          | exact absurd rfl hh
          | (have e1 := congrArg Prod.fst he
             have e2 := congrArg Prod.snd he
             simp at e1 e2
             omega)
      obtain ⟨i, j, hij, hclose⟩ := grid_four (n := n) (a := a) (b := b)
        (p := ![p1, p2, p3, p4]) (fun i => by
        fin_cases i
        · exact ⟨show a ≤ p1.1 from hp1a, show p1.1 < a + 2^(n+1) from by rw [h2n1]; omega,
            show b ≤ p1.2 from by omega, show p1.2 < b + 2^(n+1) from by rw [h2n1]; omega⟩
        · exact ⟨show a ≤ p2.1 from by omega, show p2.1 < a + 2^(n+1) from by rw [h2n1]; omega,
            show b ≤ p2.2 from by omega, show p2.2 < b + 2^(n+1) from by rw [h2n1]; omega⟩
        · exact ⟨show a ≤ p3.1 from by omega, show p3.1 < a + 2^(n+1) from by rw [h2n1]; omega,
            show b ≤ p3.2 from by omega, show p3.2 < b + 2^(n+1) from by rw [h2n1]; omega⟩
        · exact ⟨show a ≤ p4.1 from by omega, show p4.1 < a + 2^(n+1) from by rw [h2n1]; omega,
            show b ≤ p4.2 from by omega, show p4.2 < b + 2^(n+1) from by rw [h2n1]; omega⟩)
      have hlab : ∀ k : Fin 4, l ((![p1, p2, p3, p4] : Fin 4 → ℤ × ℤ) k) = 2*n+2 := by
        intro k
        fin_cases k
        · exact hp1e
        · exact hp2e
        · exact hp3e
        · exact hp4e
      have hvd := hvalid (hpd i j hij) (by rw [hlab i, hlab j])
      rw [hlab i, sqrt2_pow_even] at hvd
      linarith [hclose, hvd]
    rcases quad with hnw | hne | hsw | hse
    · exact core a b l hpos hvalid hall hnw
    · -- northeast is empty: reflect in x
      have dist_rx : ∀ p1 p2 : ℤ × ℤ,
          dist ⟨2*a + 2*2^n - 1 - p1.1, p1.2⟩ ⟨2*a + 2*2^n - 1 - p2.1, p2.2⟩ =
            dist p1 p2 := by
        intro p1 p2
        rw [dist_eq', dist_eq']
        congr 1
        push_cast
        ring
      exact core a b (fun p => l ⟨2*a + 2*2^n - 1 - p.1, p.2⟩) (fun p => hpos _)
        (fun {p1 p2} hne12 hll => by
          have hinj : (⟨2*a + 2*2^n - 1 - p1.1, p1.2⟩ : ℤ × ℤ) ≠
              ⟨2*a + 2*2^n - 1 - p2.1, p2.2⟩ := by
            intro h
            apply hne12
            obtain ⟨e1, e2⟩ := Prod.mk.inj h
            ext <;> omega
          have h2 := hvalid hinj hll
          rwa [dist_rx] at h2)
        (fun p h1 h2 h3 h4 => hall ⟨2*a + 2*2^n - 1 - p.1, p.2⟩ (by omega) (by omega) h3 h4)
        (fun p h1 h2 h3 h4 => hne ⟨2*a + 2*2^n - 1 - p.1, p.2⟩ (by omega) (by omega) h3 h4)
    · -- southwest is empty: reflect in y
      have dist_ry : ∀ p1 p2 : ℤ × ℤ,
          dist ⟨p1.1, 2*b + 2*2^n - 1 - p1.2⟩ ⟨p2.1, 2*b + 2*2^n - 1 - p2.2⟩ =
            dist p1 p2 := by
        intro p1 p2
        rw [dist_eq', dist_eq']
        congr 1
        push_cast
        ring
      exact core a b (fun p => l ⟨p.1, 2*b + 2*2^n - 1 - p.2⟩) (fun p => hpos _)
        (fun {p1 p2} hne12 hll => by
          have hinj : (⟨p1.1, 2*b + 2*2^n - 1 - p1.2⟩ : ℤ × ℤ) ≠
              ⟨p2.1, 2*b + 2*2^n - 1 - p2.2⟩ := by
            intro h
            apply hne12
            obtain ⟨e1, e2⟩ := Prod.mk.inj h
            ext <;> omega
          have h2 := hvalid hinj hll
          rwa [dist_ry] at h2)
        (fun p h1 h2 h3 h4 => hall ⟨p.1, 2*b + 2*2^n - 1 - p.2⟩ h1 h2 (by omega) (by omega))
        (fun p h1 h2 h3 h4 => hsw ⟨p.1, 2*b + 2*2^n - 1 - p.2⟩ h1 h2 (by omega) (by omega))
    · -- southeast is empty: reflect in both coordinates
      have dist_rxy : ∀ p1 p2 : ℤ × ℤ,
          dist ⟨2*a + 2*2^n - 1 - p1.1, 2*b + 2*2^n - 1 - p1.2⟩
            ⟨2*a + 2*2^n - 1 - p2.1, 2*b + 2*2^n - 1 - p2.2⟩ = dist p1 p2 := by
        intro p1 p2
        rw [dist_eq', dist_eq']
        congr 1
        push_cast
        ring
      exact core a b (fun p => l ⟨2*a + 2*2^n - 1 - p.1, 2*b + 2*2^n - 1 - p.2⟩)
        (fun p => hpos _)
        (fun {p1 p2} hne12 hll => by
          have hinj : (⟨2*a + 2*2^n - 1 - p1.1, 2*b + 2*2^n - 1 - p1.2⟩ : ℤ × ℤ) ≠
              ⟨2*a + 2*2^n - 1 - p2.1, 2*b + 2*2^n - 1 - p2.2⟩ := by
            intro h
            apply hne12
            obtain ⟨e1, e2⟩ := Prod.mk.inj h
            ext <;> omega
          have h2 := hvalid hinj hll
          rwa [dist_rxy] at h2)
        (fun p h1 h2 h3 h4 =>
          hall ⟨2*a + 2*2^n - 1 - p.1, 2*b + 2*2^n - 1 - p.2⟩
            (by omega) (by omega) (by omega) (by omega))
        (fun p h1 h2 h3 h4 =>
          hse ⟨2*a + 2*2^n - 1 - p.1, 2*b + 2*2^n - 1 - p.2⟩
            (by omega) (by omega) (by omega) (by omega))

theorem impossibility {c : ℝ} (hc : Real.sqrt 2 ≤ c) (l : ℤ × ℤ → ℕ)
    (hfin : (Set.range l).Finite) (hpos : ∀ p, 0 < l p)
    (hdist : ∀ {p1 p2}, p1 ≠ p2 → l p1 = l p2 → c ^ (l p1) ≤ dist p1 p2) : False := by
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have hbound : ∀ p, l p ≤ M := fun p => mem_upperBounds.mp hM (l p) (Set.mem_range_self p)
  have hvalid : ∀ {p1 p2}, p1 ≠ p2 → l p1 = l p2 → (Real.sqrt 2)^(l p1) ≤ dist p1 p2 := by
    intro p1 p2 h1 h2
    exact le_trans (pow_le_pow_left₀ (by positivity) hc (l p1)) (hdist h1 h2)
  obtain ⟨p, -, -, -, -, hp⟩ := grid_main M 0 0 l hpos hvalid
  have h1 : l p ≤ M := hbound p
  omega

/-- The dyadic labeling: label 1 = points with `x + y` odd; on the complement
(which is a √2-scaled copy of ℤ² via `(x, y) ↦ ((x+y)/2, (x-y)/2)`), recurse with labels shifted by 1. -/
def Lbl : ℕ → ℤ × ℤ → ℕ
  | 0, _ => 1
  | 1, _ => 1
  | k + 2, p => if (p.1 + p.2) % 2 = 1 then 1
                else 1 + Lbl (k + 1) ⟨(p.1 + p.2) / 2, (p.1 - p.2) / 2⟩

theorem dist_eq (x1 y1 x2 y2 : ℤ) :
    dist ⟨x1, y1⟩ ⟨x2, y2⟩ = Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2) := rfl

theorem lbl_eq_two (k : ℕ) (x y : ℤ) :
    Lbl (k + 2) ⟨x, y⟩ = if (x + y) % 2 = 1 then 1
      else 1 + Lbl (k + 1) ⟨(x + y) / 2, (x - y) / 2⟩ := by
  rw [Lbl]

theorem lbl_pos : ∀ (k : ℕ) (p : ℤ × ℤ), 1 ≤ Lbl k p := by
  intro k
  induction k with
  | zero => exact fun p => le_refl 1
  | succ n ih =>
    cases n with
    | zero => exact fun p => le_refl 1
    | succ m =>
      intro p
      obtain ⟨x, y⟩ := p
      show 1 ≤ Lbl (m + 2) ⟨x, y⟩
      rw [lbl_eq_two]
      split <;> omega

theorem lbl_le : ∀ (k : ℕ) (p : ℤ × ℤ), 1 ≤ k → Lbl k p ≤ k := by
  intro k
  induction k with
  | zero => intro p h; omega
  | succ n ih =>
    cases n with
    | zero => intro p h; exact le_refl _
    | succ m =>
      intro p h
      obtain ⟨x, y⟩ := p
      show Lbl (m + 2) ⟨x, y⟩ ≤ m + 2
      rw [lbl_eq_two]
      split
      · omega
      · have hih : Lbl (m + 1) ⟨(x + y) / 2, (x - y) / 2⟩ ≤ m + 1 := ih _ (by omega)
        omega

theorem one_le_dist {p1 p2 : ℤ × ℤ} (h : p1 ≠ p2) : 1 ≤ dist p1 p2 := by
  obtain ⟨x1, y1⟩ := p1
  obtain ⟨x2, y2⟩ := p2
  have hne : x2 - x1 ≠ 0 ∨ y2 - y1 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h
    simp only [Prod.mk.injEq]
    omega
  have hw : (1 : ℤ) ≤ (x2 - x1) ^ 2 + (y2 - y1) ^ 2 := by
    rcases hne with hdx | hdy
    · have s1 := sq_pos_of_ne_zero hdx
      have s2 := sq_nonneg (y2 - y1)
      omega
    · have s1 := sq_pos_of_ne_zero hdy
      have s2 := sq_nonneg (x2 - x1)
      omega
  rw [dist_eq, ← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hw)

/-- If both points have even `x + y`, then `dist` factors through the
√2-rescaled sublattice: `dist p1 p2 = √2 * dist q1 q2`. -/
theorem dist_even (x1 y1 x2 y2 : ℤ) (h1 : 2 ∣ x1 + y1) (h2 : 2 ∣ x2 + y2) :
    dist ⟨x1, y1⟩ ⟨x2, y2⟩ =
      Real.sqrt 2 * dist ⟨(x1 + y1) / 2, (x1 - y1) / 2⟩ ⟨(x2 + y2) / 2, (x2 - y2) / 2⟩ := by
  have e1 : x2 - x1 = ((x2 + y2) / 2 - (x1 + y1) / 2) + ((x2 - y2) / 2 - (x1 - y1) / 2) := by
    omega
  have e2 : y2 - y1 = ((x2 + y2) / 2 - (x1 + y1) / 2) - ((x2 - y2) / 2 - (x1 - y1) / 2) := by
    omega
  rw [dist_eq, dist_eq]
  have e1r : (x2 : ℝ) - (x1 : ℝ) = (((x2 + y2) / 2 - (x1 + y1) / 2 : ℤ) : ℝ) +
      (((x2 - y2) / 2 - (x1 - y1) / 2 : ℤ) : ℝ) := by exact_mod_cast e1
  have e2r : (y2 : ℝ) - (y1 : ℝ) = (((x2 + y2) / 2 - (x1 + y1) / 2 : ℤ) : ℝ) -
      (((x2 - y2) / 2 - (x1 - y1) / 2 : ℤ) : ℝ) := by exact_mod_cast e2
  rw [e1r, e2r]
  have hwr : ((((x2 + y2) / 2 - (x1 + y1) / 2 : ℤ) : ℝ) + (((x2 - y2) / 2 - (x1 - y1) / 2 : ℤ) : ℝ)) ^ 2 +
      ((((x2 + y2) / 2 - (x1 + y1) / 2 : ℤ) : ℝ) - (((x2 - y2) / 2 - (x1 - y1) / 2 : ℤ) : ℝ)) ^ 2 =
      2 * ((((x2 + y2) / 2 : ℤ) : ℝ) - (((x1 + y1) / 2 : ℤ) : ℝ)) ^ 2 +
        2 * ((((x2 - y2) / 2 : ℤ) : ℝ) - (((x1 - y1) / 2 : ℤ) : ℝ)) ^ 2 := by
    push_cast
    ring
  rw [hwr, ← mul_add, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- Two distinct points with `x + y` odd at both ends are at distance ≥ √2. -/
theorem sqrt_two_le_dist {x1 y1 x2 y2 : ℤ} (ho1 : (x1 + y1) % 2 = 1) (ho2 : (x2 + y2) % 2 = 1)
    (hne : (⟨x1, y1⟩ : ℤ × ℤ) ≠ ⟨x2, y2⟩) :
    Real.sqrt 2 ≤ dist ⟨x1, y1⟩ ⟨x2, y2⟩ := by
  have hsum : ((x2 - x1) + (y2 - y1)) % 2 = 0 := by omega
  have hpar : (x2 - x1) % 2 = (y2 - y1) % 2 := by omega
  have hw : (2 : ℤ) ≤ (x2 - x1) ^ 2 + (y2 - y1) ^ 2 := by
    by_cases hd : (x2 - x1) % 2 = 1
    · have s1 : (0 : ℤ) < (x2 - x1) ^ 2 := sq_pos_of_ne_zero (by omega)
      have s2 : (0 : ℤ) < (y2 - y1) ^ 2 := sq_pos_of_ne_zero (by omega)
      omega
    · have hne2 : x2 - x1 ≠ 0 ∨ y2 - y1 ≠ 0 := by
        by_contra hc
        push Not at hc
        apply hne
        simp only [Prod.mk.injEq]
        omega
      rcases hne2 with hdx | hdy
      · obtain ⟨t, ht⟩ := (show 2 ∣ x2 - x1 by omega)
        have ht2 : (x2 - x1) ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
        have ht1 : (1 : ℤ) ≤ t ^ 2 := by
          have htne : t ≠ 0 := by omega
          have := sq_pos_of_ne_zero htne
          omega
        have s2 : (0 : ℤ) ≤ (y2 - y1) ^ 2 := sq_nonneg _
        omega
      · obtain ⟨t, ht⟩ := (show 2 ∣ y2 - y1 by omega)
        have ht2 : (y2 - y1) ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
        have ht1 : (1 : ℤ) ≤ t ^ 2 := by
          have htne : t ≠ 0 := by omega
          have := sq_pos_of_ne_zero htne
          omega
        have s2 : (0 : ℤ) ≤ (x2 - x1) ^ 2 := sq_nonneg _
        omega
  rw [dist_eq]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hw)

theorem lbl_key (k : ℕ) : ∀ {p1 p2 : ℤ × ℤ}, 1 ≤ k → p1 ≠ p2 → Lbl k p1 = Lbl k p2 →
    (Real.sqrt 2) ^ min (Lbl k p1) (k - 1) ≤ dist p1 p2 := by
  induction k with
  | zero => intro p1 p2 h1; omega
  | succ n ih =>
    cases n with
    | zero =>
      intro p1 p2 h1 hne heq
      show (Real.sqrt 2) ^ min (Lbl 1 p1) (1 - 1) ≤ dist p1 p2
      have hexp : min (Lbl 1 p1) (1 - 1) = 0 := by omega
      rw [hexp, pow_zero]
      exact one_le_dist hne
    | succ m =>
      intro p1 p2 h1 hne heq
      obtain ⟨x1, y1⟩ := p1
      obtain ⟨x2, y2⟩ := p2
      show (Real.sqrt 2) ^ min (Lbl (m + 2) ⟨x1, y1⟩) (m + 1) ≤ dist ⟨x1, y1⟩ ⟨x2, y2⟩
      have heq' : Lbl (m + 2) ⟨x1, y1⟩ = Lbl (m + 2) ⟨x2, y2⟩ := heq
      rw [lbl_eq_two, lbl_eq_two] at heq'
      by_cases ho1 : (x1 + y1) % 2 = 1 <;> by_cases ho2 : (x2 + y2) % 2 = 1
      · -- both odd: labels are 1, and dist ≥ √2
        have hl1 : Lbl (m + 2) ⟨x1, y1⟩ = 1 := by rw [lbl_eq_two, if_pos ho1]
        have hdist := sqrt_two_le_dist ho1 ho2 hne
        rw [hl1]
        have hmin : min 1 (m + 1) = 1 := by omega
        rw [hmin, pow_one]
        exact hdist
      · -- odd vs even: labels 1 vs ≥ 2, contradiction
        rw [if_pos ho1, if_neg ho2] at heq'
        have hpos := lbl_pos (m + 1) ⟨(x2 + y2) / 2, (x2 - y2) / 2⟩
        omega
      · -- even vs odd: labels ≥ 2 vs 1, contradiction
        rw [if_neg ho1, if_pos ho2] at heq'
        have hpos := lbl_pos (m + 1) ⟨(x1 + y1) / 2, (x1 - y1) / 2⟩
        omega
      · -- both even: recurse on the rescaled sublattice
        rw [if_neg ho1, if_neg ho2] at heq'
        have heq2 : Lbl (m + 1) ⟨(x1 + y1) / 2, (x1 - y1) / 2⟩ =
            Lbl (m + 1) ⟨(x2 + y2) / 2, (x2 - y2) / 2⟩ := by omega
        have hqne : (⟨(x1 + y1) / 2, (x1 - y1) / 2⟩ : ℤ × ℤ) ≠
            ⟨(x2 + y2) / 2, (x2 - y2) / 2⟩ := by
          intro hq
          apply hne
          simp only [Prod.mk.injEq] at hq
          simp only [Prod.mk.injEq]
          omega
        have ih' : (Real.sqrt 2) ^ min (Lbl (m + 1) ⟨(x1 + y1) / 2, (x1 - y1) / 2⟩) m ≤
            dist ⟨(x1 + y1) / 2, (x1 - y1) / 2⟩ ⟨(x2 + y2) / 2, (x2 - y2) / 2⟩ :=
          ih (by omega) hqne heq2
        have hdist := dist_even x1 y1 x2 y2 (by omega) (by omega)
        have hl1 : Lbl (m + 2) ⟨x1, y1⟩ = 1 + Lbl (m + 1) ⟨(x1 + y1) / 2, (x1 - y1) / 2⟩ := by
          rw [lbl_eq_two, if_neg ho1]
        rw [hdist, hl1]
        have hmin : min (1 + Lbl (m + 1) ⟨(x1 + y1) / 2, (x1 - y1) / 2⟩) (m + 1) =
            min (Lbl (m + 1) ⟨(x1 + y1) / 2, (x1 - y1) / 2⟩) m + 1 := by omega
        rw [hmin, pow_succ']
        exact mul_le_mul_of_nonneg_left ih' (Real.sqrt_nonneg 2)

/-- Step 1: pick `N` large enough that `c ^ N ≤ (√2) ^ (N - 1)`. -/
theorem exists_N (c : ℝ) (hc0 : 0 < c) (hc : c < Real.sqrt 2) :
    ∃ N : ℕ, 1 ≤ N ∧ c ^ N ≤ (Real.sqrt 2) ^ (N - 1) := by
  have hcsq : c ^ 2 < 2 := by
    have h := pow_lt_pow_left₀ hc hc0.le two_ne_zero
    rwa [Real.sq_sqrt zero_le_two] at h
  have hr0 : (0:ℝ) ≤ c ^ 2 / 2 := by positivity
  have hr1 : c ^ 2 / 2 < 1 := by linarith
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (c ^ 2 / 2) ^ n < 1 / 2 :=
    ht.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / 2 by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N0, hN0⟩ := hev
  refine ⟨max N0 1, le_max_right _ _, ?_⟩
  have hN1 : 1 ≤ max N0 1 := le_max_right _ _
  have hrN : (c ^ 2 / 2) ^ max N0 1 < 1 / 2 := hN0 (max N0 1) (le_max_left _ _)
  have hlt : (c ^ 2) ^ max N0 1 < 2 ^ (max N0 1 - 1) := by
    have e1 : (c ^ 2) ^ max N0 1 = 2 ^ max N0 1 * (c ^ 2 / 2) ^ max N0 1 := by
      rw [← mul_pow]
      congr 1
      ring
    have e2 : (2:ℝ) ^ max N0 1 * (c ^ 2 / 2) ^ max N0 1 < 2 ^ max N0 1 * (1 / 2) :=
      mul_lt_mul_of_pos_left hrN (pow_pos (by norm_num) _)
    have e3a : (2:ℝ) ^ max N0 1 = 2 ^ (max N0 1 - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have e3 : (2:ℝ) ^ max N0 1 * (1 / 2) = 2 ^ (max N0 1 - 1) := by rw [e3a]; ring
    rw [e1]
    linarith [e2, e3]
  have hle : (c ^ max N0 1) ^ 2 ≤ ((Real.sqrt 2) ^ (max N0 1 - 1)) ^ 2 := by
    have e1 : (c ^ max N0 1) ^ 2 = (c ^ 2) ^ max N0 1 := by
      rw [← pow_mul, mul_comm (max N0 1) 2, pow_mul]
    have e2 : ((Real.sqrt 2) ^ (max N0 1 - 1)) ^ 2 = 2 ^ (max N0 1 - 1) := by
      rw [← pow_mul, mul_comm (max N0 1 - 1) 2, pow_mul, Real.sq_sqrt zero_le_two]
    rw [e1, e2]
    exact hlt.le
  have hfin := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (pow_nonneg hc0.le _), Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg 2) _)] at hfin

theorem construction (c : ℝ) (hc0 : 0 < c) (hc : c < Real.sqrt 2) :
    ∃ l : ℤ × ℤ → ℕ, (Set.range l).Finite ∧ (∀ p, 0 < l p) ∧
      ∀ {p1 p2}, p1 ≠ p2 → l p1 = l p2 → c ^ (l p1) ≤ dist p1 p2 := by
  obtain ⟨N, hN1, hNc⟩ := exists_N c hc0 hc
  refine ⟨Lbl N, ?_, fun p => lbl_pos N p, ?_⟩
  · apply Set.Finite.subset (Set.finite_Icc 1 N)
    intro x hx
    obtain ⟨p, rfl⟩ := hx
    exact Set.mem_Icc.mpr ⟨lbl_pos N p, lbl_le N p hN1⟩
  · intro p1 p2 hne heq
    have hkey := lbl_key N hN1 hne heq
    by_cases htop : Lbl N p1 = N
    · have hmin : min (Lbl N p1) (N - 1) = N - 1 := by omega
      rw [hmin] at hkey
      rw [htop]
      exact le_trans hNc hkey
    · have hmin : min (Lbl N p1) (N - 1) = Lbl N p1 := by
        have := lbl_le N p1 hN1
        omega
      rw [hmin] at hkey
      exact le_trans (pow_le_pow_left₀ hc0.le hc.le _) hkey

snip end

problem usa2017_p5 (c : ℝ) :
    c ∈ solution_set ↔
    (0 < c ∧
     ∃ l : ℤ × ℤ → ℕ,
       (Set.range l).Finite ∧
       (∀ p, 0 < l p) ∧
       ∀ {p1 p2}, p1 ≠ p2 → (l p1 = l p2) →
            c ^ (l p1) ≤ dist p1 p2) := by
  constructor
  · intro h
    have h' : 0 < c ∧ c < Real.sqrt 2 := Set.mem_Ioo.mp h
    exact ⟨h'.1, construction c h'.1 h'.2⟩
  · rintro ⟨hc0, l, hfin, hpos, hdist⟩
    apply Set.mem_Ioo.mpr
    refine ⟨hc0, ?_⟩
    by_contra hnot
    push Not at hnot
    exact impossibility hnot l hfin hpos hdist


end Usa2017P5
