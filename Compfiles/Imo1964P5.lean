/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

import Mathlib
import ProblemExtraction

problem_file { tags := [.Combinatorics, .Geometry] }

/-!
# International Mathematical Olympiad 1964, Problem 5

Suppose five points in a plane are situated so that no two of the
straight lines joining them are parallel, perpendicular, or coincident.
From each point perpendiculars are drawn to all the lines joining the
other four points. Determine the maximum number of intersections that
these perpendiculars can have.
-/

namespace Imo1964P5

open Finset

variable {K : Type*} [Field K]

/-- The standard dot product on the coordinatized plane `Fin 2 → K`. -/
def dot (u v : Fin 2 → K) : K := u 0 * v 0 + u 1 * v 1

/-- The 2-dimensional cross product (determinant) on `Fin 2 → K`. -/
def cross (u v : Fin 2 → K) : K := u 0 * v 1 - u 1 * v 0

theorem dot_comm (u v : Fin 2 → K) : dot u v = dot v u := by simp [dot]; ring

theorem dot_neg_left (u v : Fin 2 → K) : dot (-u) v = -dot u v := by simp [dot]; ring

theorem dot_sub_right (u v w : Fin 2 → K) : dot u (v - w) = dot u v - dot u w := by
  simp [dot, Pi.sub_apply]; ring

theorem cross_self (u : Fin 2 → K) : cross u u = 0 := by simp [cross]; ring

theorem cross_antisymm (u v : Fin 2 → K) : cross u v = -cross v u := by simp [cross]; ring

/-- A line in the plane, given by the equation `dot ℓ.n x = ℓ.c`. -/
@[ext]
structure Line2 (K : Type*) [Field K] where
  n : Fin 2 → K
  c : K

/-- The intersection point of two lines; a junk value when the lines are parallel. -/
def interPt (ℓ₁ ℓ₂ : Line2 K) : Fin 2 → K :=
  ![ (ℓ₁.c * ℓ₂.n 1 - ℓ₂.c * ℓ₁.n 1) / cross ℓ₁.n ℓ₂.n
   , (ℓ₁.n 0 * ℓ₂.c - ℓ₂.n 0 * ℓ₁.c) / cross ℓ₁.n ℓ₂.n ]

theorem interPt_comm (ℓ₁ ℓ₂ : Line2 K) : interPt ℓ₁ ℓ₂ = interPt ℓ₂ ℓ₁ := by
  have h1 : ℓ₂.c * ℓ₁.n 1 - ℓ₁.c * ℓ₂.n 1 = -(ℓ₁.c * ℓ₂.n 1 - ℓ₂.c * ℓ₁.n 1) := by ring
  have h2 : ℓ₂.n 0 * ℓ₁.c - ℓ₁.n 0 * ℓ₂.c = -(ℓ₁.n 0 * ℓ₂.c - ℓ₂.n 0 * ℓ₁.c) := by ring
  have hc : cross ℓ₂.n ℓ₁.n = -cross ℓ₁.n ℓ₂.n := cross_antisymm _ _
  funext i
  fin_cases i
  · show (ℓ₁.c * ℓ₂.n 1 - ℓ₂.c * ℓ₁.n 1) / cross ℓ₁.n ℓ₂.n =
      (ℓ₂.c * ℓ₁.n 1 - ℓ₁.c * ℓ₂.n 1) / cross ℓ₂.n ℓ₁.n
    rw [h1, hc, neg_div_neg_eq]
  · show (ℓ₁.n 0 * ℓ₂.c - ℓ₂.n 0 * ℓ₁.c) / cross ℓ₁.n ℓ₂.n =
      (ℓ₂.n 0 * ℓ₁.c - ℓ₁.n 0 * ℓ₂.c) / cross ℓ₂.n ℓ₁.n
    rw [h2, hc, neg_div_neg_eq]

theorem interPt_mem₁ {ℓ₁ ℓ₂ : Line2 K} (h : cross ℓ₁.n ℓ₂.n ≠ 0) :
    dot ℓ₁.n (interPt ℓ₁ ℓ₂) = ℓ₁.c := by
  have key : cross ℓ₁.n ℓ₂.n * dot ℓ₁.n (interPt ℓ₁ ℓ₂) = cross ℓ₁.n ℓ₂.n * ℓ₁.c := by
    simp only [dot, interPt, cross, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
    field_simp
    ring
  exact mul_left_cancel₀ h key

theorem interPt_mem₂ {ℓ₁ ℓ₂ : Line2 K} (h : cross ℓ₁.n ℓ₂.n ≠ 0) :
    dot ℓ₂.n (interPt ℓ₁ ℓ₂) = ℓ₂.c := by
  have key : cross ℓ₁.n ℓ₂.n * dot ℓ₂.n (interPt ℓ₁ ℓ₂) = cross ℓ₁.n ℓ₂.n * ℓ₂.c := by
    simp only [dot, interPt, cross, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
    field_simp
    ring
  exact mul_left_cancel₀ h key

/-- Two non-parallel lines meet in at most one point. -/
theorem mem_unique {ℓ₁ ℓ₂ : Line2 K} (h : cross ℓ₁.n ℓ₂.n ≠ 0) {x y : Fin 2 → K}
    (h1x : dot ℓ₁.n x = ℓ₁.c) (h2x : dot ℓ₂.n x = ℓ₂.c)
    (h1y : dot ℓ₁.n y = ℓ₁.c) (h2y : dot ℓ₂.n y = ℓ₂.c) : x = y := by
  have e0 : cross ℓ₁.n ℓ₂.n * (x 0 - y 0) = 0 := by
    have g1 := h1x; have g2 := h2x; have g3 := h1y; have g4 := h2y
    simp only [dot, cross] at g1 g2 g3 g4 ⊢
    linear_combination ℓ₂.n 1 * g1 - ℓ₁.n 1 * g2 - ℓ₂.n 1 * g3 + ℓ₁.n 1 * g4
  have e1 : cross ℓ₁.n ℓ₂.n * (x 1 - y 1) = 0 := by
    have g1 := h1x; have g2 := h2x; have g3 := h1y; have g4 := h2y
    simp only [dot, cross] at g1 g2 g3 g4 ⊢
    linear_combination -ℓ₂.n 0 * g1 + ℓ₁.n 0 * g2 + ℓ₂.n 0 * g3 - ℓ₁.n 0 * g4
  have hx0 : x 0 = y 0 := by
    rcases mul_eq_zero.mp e0 with hD | hxy
    · exact absurd hD h
    · exact sub_eq_zero.mp hxy
  have hx1 : x 1 = y 1 := by
    rcases mul_eq_zero.mp e1 with hD | hxy
    · exact absurd hD h
    · exact sub_eq_zero.mp hxy
  funext i
  fin_cases i
  · exact hx0
  · exact hx1

/-- The three altitudes of a (non-degenerate) triangle are concurrent. -/
theorem orthocenter_exists {A B C : Fin 2 → K} (h : cross (C - B) (C - A) ≠ 0) :
    ∃ H, dot (C - B) H = dot (C - B) A ∧ dot (C - A) H = dot (C - A) B ∧
      dot (B - A) H = dot (B - A) C := by
  have h1 : dot (C - B) (interPt ⟨C - B, dot (C - B) A⟩ ⟨C - A, dot (C - A) B⟩) =
      dot (C - B) A :=
    interPt_mem₁ (ℓ₁ := ⟨C - B, dot (C - B) A⟩) (ℓ₂ := ⟨C - A, dot (C - A) B⟩) h
  have h2 : dot (C - A) (interPt ⟨C - B, dot (C - B) A⟩ ⟨C - A, dot (C - A) B⟩) =
      dot (C - A) B :=
    interPt_mem₂ (ℓ₁ := ⟨C - B, dot (C - B) A⟩) (ℓ₂ := ⟨C - A, dot (C - A) B⟩) h
  refine ⟨_, h1, h2, ?_⟩
  simp only [dot, Pi.sub_apply] at h1 h2 ⊢
  linear_combination -h1 + h2

/-- Index triples parametrizing the perpendiculars: from point `t.1` to the line
through points `t.2.1` and `t.2.2`. -/
abbrev Triple := Fin 5 × Fin 5 × Fin 5

/-- The 30 index triples giving the perpendiculars of the problem. -/
def perpIdx : Finset Triple :=
  Finset.univ.filter (fun t => t.2.1 < t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2)

theorem mem_perpIdx {t : Triple} (ht : t ∈ perpIdx) :
    t.2.1 < t.2.2 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 := by
  simp only [perpIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  exact ht

/-- If two index triples have the same target pair, the targets agree as
ordered pairs (thanks to the canonical order in `perpIdx`). -/
theorem tgt3_injective_of_mem {a b : Triple} (ha : a ∈ perpIdx) (hb : b ∈ perpIdx)
    (h : ({a.2.1, a.2.2} : Finset (Fin 5)) = {b.2.1, b.2.2}) :
    a.2.1 = b.2.1 ∧ a.2.2 = b.2.2 := by
  obtain ⟨haj, -, -⟩ := mem_perpIdx ha
  obtain ⟨hbj, -, -⟩ := mem_perpIdx hb
  have h1 : a.2.1 ∈ ({b.2.1, b.2.2} : Finset (Fin 5)) := by
    rw [← h]; exact Finset.mem_insert_self _ _
  have h2 : a.2.2 ∈ ({b.2.1, b.2.2} : Finset (Fin 5)) := by
    rw [← h]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1 ▸ h2 ▸ haj) (lt_irrefl _)
  · exact ⟨h1, h2⟩
  · exfalso; rw [h1, h2] at haj; exact lt_irrefl _ (lt_trans hbj haj)
  · exact absurd (h1 ▸ h2 ▸ haj) (lt_irrefl _)

/-- A configuration of five points satisfying the hypotheses of the problem:
the lines joining pairs of points are pairwise non-parallel (in particular
pairwise distinct, i.e. non-coincident and with no three points collinear)
and pairwise non-perpendicular. -/
structure Config (K : Type*) [Field K] where
  p : Fin 5 → Fin 2 → K
  inj : Function.Injective p
  npar : ∀ i j k l : Fin 5, i ≠ j → k ≠ l → ({i, j} : Finset (Fin 5)) ≠ {k, l} →
    cross (p j - p i) (p l - p k) ≠ 0
  nperp : ∀ i j k l : Fin 5, i ≠ j → k ≠ l → ({i, j} : Finset (Fin 5)) ≠ {k, l} →
    dot (p j - p i) (p l - p k) ≠ 0

namespace Config

variable (cfg : Config K)

/-- The perpendicular from `cfg.p t.1` to the line through `cfg.p t.2.1` and
`cfg.p t.2.2`. -/
def perpOf (t : Triple) : Line2 K :=
  ⟨cfg.p t.2.2 - cfg.p t.2.1, dot (cfg.p t.2.2 - cfg.p t.2.1) (cfg.p t.1)⟩

theorem perpOf_n (t : Triple) : (cfg.perpOf t).n = cfg.p t.2.2 - cfg.p t.2.1 := rfl

theorem perpOf_c (t : Triple) :
    (cfg.perpOf t).c = dot (cfg.p t.2.2 - cfg.p t.2.1) (cfg.p t.1) := rfl

theorem perpOf_n_ne_zero {t : Triple} (ht : t ∈ perpIdx) : (cfg.perpOf t).n ≠ 0 := by
  rw [perpOf_n]
  exact sub_ne_zero_of_ne ((cfg.inj.ne (mem_perpIdx ht).1.ne).symm)

/-- The perpendicular from a point to a target line passes through that point. -/
theorem perpOf_mem_self {t : Triple} :
    dot (cfg.perpOf t).n (cfg.p t.1) = (cfg.perpOf t).c := rfl

/-- If two perpendiculars pass through a common point, they are not parallel. -/
theorem cross_ne_zero_of_mem {a b : Triple} (ha : a ∈ perpIdx) (hb : b ∈ perpIdx)
    (hab : a ≠ b) {x : Fin 2 → K}
    (hxa : dot (cfg.perpOf a).n x = (cfg.perpOf a).c)
    (hxb : dot (cfg.perpOf b).n x = (cfg.perpOf b).c) :
    cross (cfg.perpOf a).n (cfg.perpOf b).n ≠ 0 := by
  intro hcross
  by_cases htgt : ({a.2.1, a.2.2} : Finset (Fin 5)) = {b.2.1, b.2.2}
  · -- The target lines coincide; the two perpendiculars are then parallel,
    -- and they are distinct because the line `a.1 b.1` is not perpendicular
    -- to the target line.
    obtain ⟨h21, h22⟩ := tgt3_injective_of_mem ha hb htgt
    have hpt : a.1 ≠ b.1 := fun h1 => hab (Prod.ext h1 (Prod.ext h21 h22))
    have hn : (cfg.perpOf a).n = (cfg.perpOf b).n := by
      rw [perpOf_n, perpOf_n, h21, h22]
    have e : dot (cfg.p a.2.2 - cfg.p a.2.1) (cfg.p a.1) =
        dot (cfg.p a.2.2 - cfg.p a.2.1) (cfg.p b.1) := by
      have e1 : dot (cfg.perpOf a).n x = dot (cfg.p a.2.2 - cfg.p a.2.1) (cfg.p a.1) := hxa
      have e2 : dot (cfg.perpOf b).n x = dot (cfg.p b.2.2 - cfg.p b.2.1) (cfg.p b.1) := hxb
      rw [← h21, ← h22] at e2
      rw [hn] at e1
      exact e1.symm.trans e2
    have ez : dot (cfg.p a.2.2 - cfg.p a.2.1) (cfg.p a.1 - cfg.p b.1) = 0 := by
      rw [dot_sub_right]
      exact sub_eq_zero.mpr e
    have hpairs : ({b.1, a.1} : Finset (Fin 5)) ≠ {a.2.1, a.2.2} := by
      intro h
      have : a.1 ∈ ({a.2.1, a.2.2} : Finset (Fin 5)) := by
        rw [← h]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h1 | h1
      · exact (mem_perpIdx ha).2.1 h1
      · exact (mem_perpIdx ha).2.2 h1
    exact cfg.nperp b.1 a.1 a.2.1 a.2.2 hpt.symm (mem_perpIdx ha).1.ne hpairs
      (by rw [dot_comm]; exact ez)
  · exact (cfg.npar a.2.1 a.2.2 b.2.1 b.2.2 (mem_perpIdx ha).1.ne
      (mem_perpIdx hb).1.ne htgt) hcross

end Config

/-- The set of intersection points of the 30 perpendiculars: the points lying
on at least two distinct perpendiculars. -/
def interSet (cfg : Config K) : Set (Fin 2 → K) :=
  {x | ∃ a ∈ perpIdx, ∃ b ∈ perpIdx, a ≠ b ∧
    dot (cfg.perpOf a).n x = (cfg.perpOf a).c ∧ dot (cfg.perpOf b).n x = (cfg.perpOf b).c}

determine answer : ℕ := 315

snip begin

open Classical

theorem perpIdx_card : perpIdx.card = 30 := by decide

/-- The source point of an index triple. -/
abbrev pt3 (t : Triple) : Fin 5 := t.1

/-- The target pair of an index triple. -/
abbrev tgt3 (t : Triple) : Finset (Fin 5) := {t.2.1, t.2.2}

/-- The vertex set of an index triple. -/
abbrev tri3 (t : Triple) : Finset (Fin 5) := {t.1, t.2.1, t.2.2}

theorem eq_of_card_image_pair_eq_one {α : Type*} [DecidableEq α] {f : Triple → α} {a b : Triple}
    (h : (({a, b} : Finset Triple).image f).card = 1) : f a = f b := by
  by_contra hne
  rw [Finset.image_insert, Finset.image_singleton, Finset.card_pair_eq_two_iff.mpr hne] at h
  exact absurd h (by decide)

theorem ne_of_card_image_pair_eq_two {α : Type*} [DecidableEq α] {f : Triple → α} {a b : Triple}
    (h : (({a, b} : Finset Triple).image f).card = 2) : f a ≠ f b := by
  intro hne
  rw [Finset.image_insert, Finset.image_singleton, hne, Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
    Finset.card_singleton] at h
  exact absurd h (by decide)

/-- The 2-subsets of the 30 index triples. -/
def allPairs : Finset (Finset Triple) := perpIdx.powersetCard 2

theorem allPairs_card : allPairs.card = 435 := by
  rw [allPairs, Finset.card_powersetCard, perpIdx_card]
  decide

/-- Pairs of perpendiculars to the same target line (from two distinct points):
these are parallel. -/
abbrev parPred (s : Finset Triple) : Prop :=
  (s.image tgt3).card = 1 ∧ (s.image pt3).card = 2

/-- Pairs of perpendiculars from the same point: these concur at that point. -/
abbrev samePtPred (s : Finset Triple) : Prop :=
  (s.image pt3).card = 1 ∧ (s.image tgt3).card = 2

/-- Pairs of altitudes of the same triangle: these concur at the orthocenter. -/
abbrev altPred (s : Finset Triple) : Prop :=
  (s.image tri3).card = 1 ∧ (s.image pt3).card = 2

/-- The 30 pairs of perpendiculars to a common target line. -/
def parPairs : Finset (Finset Triple) := allPairs.filter parPred

/-- The 75 pairs of perpendiculars through a common one of the five points. -/
def samePtPairs : Finset (Finset Triple) := allPairs.filter samePtPred

/-- The 30 pairs of altitudes of a common triangle. -/
def altPairs : Finset (Finset Triple) := allPairs.filter altPred

theorem parPairs_card : parPairs.card = 30 := by decide

theorem samePtPairs_card : samePtPairs.card = 75 := by decide

theorem altPairs_card : altPairs.card = 30 := by decide

theorem disjoint_parPairs_samePtPairs : Disjoint parPairs samePtPairs := by
  rw [Finset.disjoint_left]
  intro s hs hmem
  have h1 : (s.image pt3).card = 1 := (Finset.mem_filter.mp hmem).2.1
  have h2 : (s.image pt3).card = 2 := (Finset.mem_filter.mp hs).2.2
  rw [h1] at h2
  exact absurd h2 (by decide)

theorem disjoint_parPairs_altPairs : Disjoint parPairs altPairs := by
  rw [Finset.disjoint_left]
  intro s hs hmem
  obtain ⟨hsa, htgt1, hpt2⟩ := Finset.mem_filter.mp hs
  obtain ⟨-, htri1, -⟩ := Finset.mem_filter.mp hmem
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hsa
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ perpIdx := hsub (Finset.mem_insert_self _ _)
  have hb : b ∈ perpIdx := hsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
  have htgt : tgt3 a = tgt3 b := eq_of_card_image_pair_eq_one htgt1
  have htri : tri3 a = tri3 b := eq_of_card_image_pair_eq_one htri1
  have hpt : pt3 a ≠ pt3 b := ne_of_card_image_pair_eq_two hpt2
  apply hpt
  have key : insert (pt3 a) (tgt3 a) = insert (pt3 b) (tgt3 b) := htri
  rw [htgt] at key
  have hna : pt3 a ∉ tgt3 b := by
    rw [← htgt]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(mem_perpIdx ha).2.1, (mem_perpIdx ha).2.2⟩
  exact (Finset.insert_inj hna).mp key

theorem disjoint_samePtPairs_altPairs : Disjoint samePtPairs altPairs := by
  rw [Finset.disjoint_left]
  intro s hs hmem
  obtain ⟨hsa, hpt1, htgt2⟩ := Finset.mem_filter.mp hs
  obtain ⟨-, htri1, -⟩ := Finset.mem_filter.mp hmem
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hsa
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ perpIdx := hsub (Finset.mem_insert_self _ _)
  have hb : b ∈ perpIdx := hsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
  have hpt : pt3 a = pt3 b := eq_of_card_image_pair_eq_one hpt1
  have htgt : tgt3 a ≠ tgt3 b := ne_of_card_image_pair_eq_two htgt2
  have htri : tri3 a = tri3 b := eq_of_card_image_pair_eq_one htri1
  apply htgt
  have e1 : (tri3 a).erase (pt3 a) = tgt3 a :=
    Finset.erase_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(mem_perpIdx ha).2.1, (mem_perpIdx ha).2.2⟩)
  have e2 : (tri3 b).erase (pt3 b) = tgt3 b :=
    Finset.erase_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(mem_perpIdx hb).2.1, (mem_perpIdx hb).2.2⟩)
  rw [← e1, htri, hpt, e2]

/-- The "forced" special pairs of perpendiculars. -/
def fams : Finset (Finset Triple) := parPairs ∪ samePtPairs ∪ altPairs

theorem fams_card : fams.card = 135 := by
  have d1 := disjoint_parPairs_samePtPairs
  have d2 := disjoint_parPairs_altPairs
  have d3 := disjoint_samePtPairs_altPairs
  rw [fams, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d2, d3⟩),
    Finset.card_union_of_disjoint d1, parPairs_card, samePtPairs_card, altPairs_card]

theorem fams_subset : fams ⊆ allPairs := by
  rw [fams]
  exact Finset.union_subset
    (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    (Finset.filter_subset _ _)

/-- The predicate on pairs of triples: the two perpendiculars are not parallel. -/
def nonparP (cfg : Config K) (s : Finset Triple) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ cross (cfg.perpOf a).n (cfg.perpOf b).n ≠ 0

/-- The pairs of perpendiculars that actually intersect. -/
noncomputable def goodPairs (cfg : Config K) : Finset (Finset Triple) :=
  allPairs.filter (nonparP cfg)

/-- The intersection point of the two perpendiculars of a pair. -/
noncomputable def pairPt (cfg : Config K) (s : Finset Triple) : Fin 2 → K :=
  if h : s.card = 2 then
    interPt (cfg.perpOf (Finset.card_eq_two.mp h).choose)
      (cfg.perpOf (Finset.card_eq_two.mp h).choose_spec.choose)
  else 0

theorem pairPt_pair (cfg : Config K) {a b : Triple} (hab : a ≠ b) :
    pairPt cfg {a, b} = interPt (cfg.perpOf a) (cfg.perpOf b) := by
  have h2 : ({a, b} : Finset Triple).card = 2 := Finset.card_pair_eq_two_iff.mpr hab
  unfold pairPt
  rw [dif_pos h2]
  set w := Finset.card_eq_two.mp h2
  generalize hb' : w.choose_spec.choose = b'
  generalize ha' : w.choose = a'
  have hne : a' ≠ b' := by
    rw [← ha', ← hb']
    exact w.choose_spec.choose_spec.1
  have heq : ({a, b} : Finset Triple) = {a', b'} := by
    rw [← ha', ← hb']
    exact w.choose_spec.choose_spec.2
  have h1 : a' ∈ ({a, b} : Finset Triple) := by
    rw [heq]; exact Finset.mem_insert_self _ _
  have h2m : b' ∈ ({a, b} : Finset Triple) := by
    rw [heq]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2m
  rcases h1 with h1 | h1 <;> rcases h2m with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2]
  · rw [h1, h2]; exact interPt_comm _ _
  · exact absurd (h1.trans h2.symm) hne

theorem goodPairs_cross (cfg : Config K) {a b : Triple}
    (hs : ({a, b} : Finset Triple) ∈ goodPairs cfg) (_hab : a ≠ b) :
    cross (cfg.perpOf a).n (cfg.perpOf b).n ≠ 0 := by
  obtain ⟨-, a', ha', b', hb', hne, hcross⟩ := Finset.mem_filter.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
  rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2] at hcross; exact hcross
  · rw [h1, h2] at hcross
    rw [cross_antisymm] at hcross
    exact neg_ne_zero.mp hcross
  · exact absurd (h1.trans h2.symm) hne

theorem pairPt_mem₁ (cfg : Config K) {a b : Triple}
    (hs : ({a, b} : Finset Triple) ∈ goodPairs cfg) (hab : a ≠ b) :
    dot (cfg.perpOf a).n (pairPt cfg {a, b}) = (cfg.perpOf a).c := by
  rw [pairPt_pair cfg hab]
  exact interPt_mem₁ (goodPairs_cross cfg hs hab)

theorem pairPt_mem₂ (cfg : Config K) {a b : Triple}
    (hs : ({a, b} : Finset Triple) ∈ goodPairs cfg) (hab : a ≠ b) :
    dot (cfg.perpOf b).n (pairPt cfg {a, b}) = (cfg.perpOf b).c := by
  rw [pairPt_pair cfg hab]
  exact interPt_mem₂ (goodPairs_cross cfg hs hab)

theorem pairPt_eq_of_mem (cfg : Config K) {a b : Triple} {x : Fin 2 → K}
    (hs : ({a, b} : Finset Triple) ∈ goodPairs cfg) (hab : a ≠ b)
    (hxa : dot (cfg.perpOf a).n x = (cfg.perpOf a).c)
    (hxb : dot (cfg.perpOf b).n x = (cfg.perpOf b).c) :
    x = pairPt cfg {a, b} := by
  rw [pairPt_pair cfg hab]
  exact mem_unique (goodPairs_cross cfg hs hab) hxa hxb
    (interPt_mem₁ (goodPairs_cross cfg hs hab)) (interPt_mem₂ (goodPairs_cross cfg hs hab))

/-- Pairs of perpendiculars to a common target line are parallel,
so they do not satisfy `nonparP`. -/
theorem not_nonparP_of_parPred (cfg : Config K) {s : Finset Triple}
    (hs : s ∈ allPairs) (hp : parPred s) : ¬ nonparP cfg s := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ perpIdx := hsub (Finset.mem_insert_self _ _)
  have hb : b ∈ perpIdx := hsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
  have htgt : tgt3 a = tgt3 b := eq_of_card_image_pair_eq_one hp.1
  obtain ⟨h21, h22⟩ := tgt3_injective_of_mem ha hb htgt
  have hn : (cfg.perpOf a).n = (cfg.perpOf b).n := by
    rw [Config.perpOf_n, Config.perpOf_n, h21, h22]
  rintro ⟨a', ha', b', hb', hne, hcross⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
  rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2, hn, cross_self] at hcross; exact hcross rfl
  · rw [h1, h2, hn, cross_self] at hcross; exact hcross rfl
  · exact absurd (h1.trans h2.symm) hne

/-- The five given points, as a finset. -/
noncomputable def ptsFin (cfg : Config K) : Finset (Fin 2 → K) := Finset.univ.image cfg.p

/-- Through each of the five points pass six perpendiculars, so a pair of
perpendiculars through the same point intersects at that point. -/
theorem mem_ptsFin_of_samePt (cfg : Config K) {s : Finset Triple}
    (hs : s ∈ goodPairs cfg) (hp : samePtPred s) : pairPt cfg s ∈ ptsFin cfg := by
  obtain ⟨hsa, hsnp⟩ := Finset.mem_filter.mp hs
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hsa
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hpt : pt3 a = pt3 b := eq_of_card_image_pair_eq_one hp.1
  have hpt' : a.1 = b.1 := hpt
  have hxa : dot (cfg.perpOf a).n (cfg.p a.1) = (cfg.perpOf a).c := cfg.perpOf_mem_self
  have hxb : dot (cfg.perpOf b).n (cfg.p a.1) = (cfg.perpOf b).c := by
    have e : dot (cfg.perpOf b).n (cfg.p b.1) = (cfg.perpOf b).c := cfg.perpOf_mem_self
    rwa [← hpt'] at e
  have hs' : ({a, b} : Finset Triple) ∈ goodPairs cfg := Finset.mem_filter.mpr ⟨hsa, hsnp⟩
  rw [(pairPt_eq_of_mem cfg hs' hab hxa hxb).symm]
  exact Finset.mem_image.mpr ⟨a.1, Finset.mem_univ _, rfl⟩

theorem tri3_card {t : Triple} (ht : t ∈ perpIdx) : (tri3 t).card = 3 := by
  obtain ⟨hlt, h1, h2⟩ := mem_perpIdx ht
  have h0 : t.1 ∉ ({t.2.1, t.2.2} : Finset (Fin 5)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, h2⟩
  show (({t.1, t.2.1, t.2.2} : Finset (Fin 5))).card = 3
  rw [Finset.card_insert_of_notMem h0, Finset.card_pair_eq_two_iff.mpr hlt.ne]

theorem cross_ne_zero_of_triple (cfg : Config K) {x y z : Fin 5}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    cross (cfg.p z - cfg.p y) (cfg.p z - cfg.p x) ≠ 0 :=
  cfg.npar y z x z hyz hxz (by
    intro h
    have hm : y ∈ ({x, z} : Finset (Fin 5)) := by
      rw [← h]; exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h1 | h1
    · exact hxy h1.symm
    · exact hyz h1)

/-- The orthocenter of the triangle with vertices `p x, p y, p z`. -/
noncomputable def orthoOfPts (cfg : Config K) {x y z : Fin 5}
    (h : cross (cfg.p z - cfg.p y) (cfg.p z - cfg.p x) ≠ 0) : Fin 2 → K :=
  (orthocenter_exists h).choose

theorem orthoOfPts_spec (cfg : Config K) {x y z : Fin 5}
    (h : cross (cfg.p z - cfg.p y) (cfg.p z - cfg.p x) ≠ 0) :
    dot (cfg.p z - cfg.p y) (orthoOfPts cfg h) = dot (cfg.p z - cfg.p y) (cfg.p x) ∧
    dot (cfg.p z - cfg.p x) (orthoOfPts cfg h) = dot (cfg.p z - cfg.p x) (cfg.p y) ∧
    dot (cfg.p y - cfg.p x) (orthoOfPts cfg h) = dot (cfg.p y - cfg.p x) (cfg.p z) :=
  (orthocenter_exists h).choose_spec

/-- The orthocenter of the triangle with vertex set `T` (for `T` a 3-set). -/
noncomputable def orthoPtT (cfg : Config K) (T : Finset (Fin 5)) : Fin 2 → K :=
  if hT : T.card = 3 then
    let w := Finset.card_eq_three.mp hT
    orthoOfPts cfg (cross_ne_zero_of_triple cfg w.choose_spec.choose_spec.choose_spec.1
      w.choose_spec.choose_spec.choose_spec.2.1 w.choose_spec.choose_spec.choose_spec.2.2.1)
  else 0

theorem orthoPtT_spec (cfg : Config K) {T : Finset (Fin 5)} (hT : T.card = 3) :
    ∃ x y z : Fin 5, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ T = {x, y, z} ∧
      dot (cfg.p z - cfg.p y) (orthoPtT cfg T) = dot (cfg.p z - cfg.p y) (cfg.p x) ∧
      dot (cfg.p z - cfg.p x) (orthoPtT cfg T) = dot (cfg.p z - cfg.p x) (cfg.p y) ∧
      dot (cfg.p y - cfg.p x) (orthoPtT cfg T) = dot (cfg.p y - cfg.p x) (cfg.p z) := by
  unfold orthoPtT
  rw [dif_pos hT]
  refine ⟨(Finset.card_eq_three.mp hT).choose, (Finset.card_eq_three.mp hT).choose_spec.choose,
    (Finset.card_eq_three.mp hT).choose_spec.choose_spec.choose,
    (Finset.card_eq_three.mp hT).choose_spec.choose_spec.choose_spec.1,
    (Finset.card_eq_three.mp hT).choose_spec.choose_spec.choose_spec.2.1,
    (Finset.card_eq_three.mp hT).choose_spec.choose_spec.choose_spec.2.2.1,
    (Finset.card_eq_three.mp hT).choose_spec.choose_spec.choose_spec.2.2.2, ?_⟩
  exact orthoOfPts_spec cfg _

/-- The orthocenter of a triangle lies on every altitude of the triangle. -/
theorem mem_perpOf_orthoPtT (cfg : Config K) {T : Finset (Fin 5)} (hT : T.card = 3)
    {t : Triple} (ht : t ∈ perpIdx) (htri : tri3 t = T) :
    dot (cfg.perpOf t).n (orthoPtT cfg T) = (cfg.perpOf t).c := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hTeq, hA, hB, hC⟩ := orthoPtT_spec cfg hT
  have h1mem : t.1 ∈ ({x, y, z} : Finset (Fin 5)) := by
    rw [← hTeq, ← htri]; exact Finset.mem_insert_self _ _
  have htgt : ({t.2.1, t.2.2} : Finset (Fin 5)) = ({x, y, z} : Finset (Fin 5)).erase t.1 := by
    have e : ((tri3 t).erase t.1) = ({t.2.1, t.2.2} : Finset (Fin 5)) :=
      Finset.erase_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(mem_perpIdx ht).2.1, (mem_perpIdx ht).2.2⟩)
    rw [htri, hTeq] at e
    exact e.symm
  obtain ⟨hlt, -, -⟩ := mem_perpIdx ht
  rw [Config.perpOf_c, Config.perpOf_n]
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1mem
  rcases h1mem with rfl | rfl | rfl
  · rw [Finset.erase_insert (by simp [hxy, hxz])] at htgt
    have hm1 : t.2.1 ∈ ({y, z} : Finset (Fin 5)) := by
      rw [← htgt]; exact Finset.mem_insert_self _ _
    have hm2 : t.2.2 ∈ ({y, z} : Finset (Fin 5)) := by
      rw [← htgt]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2
    · exact absurd (h1 ▸ h2 ▸ hlt) (lt_irrefl _)
    · rw [h1, h2]; exact hA
    · rw [h1, h2, show cfg.p y - cfg.p z = -(cfg.p z - cfg.p y) by rw [neg_sub],
        dot_neg_left, dot_neg_left, hA]
    · exact absurd (h1 ▸ h2 ▸ hlt) (lt_irrefl _)
  · rw [Finset.erase_insert_of_ne hxy, Finset.erase_insert (by simp [hyz])] at htgt
    have hm1 : t.2.1 ∈ ({x, z} : Finset (Fin 5)) := by
      rw [← htgt]; exact Finset.mem_insert_self _ _
    have hm2 : t.2.2 ∈ ({x, z} : Finset (Fin 5)) := by
      rw [← htgt]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2
    · exact absurd (h1 ▸ h2 ▸ hlt) (lt_irrefl _)
    · rw [h1, h2]; exact hB
    · rw [h1, h2, show cfg.p x - cfg.p z = -(cfg.p z - cfg.p x) by rw [neg_sub],
        dot_neg_left, dot_neg_left, hB]
    · exact absurd (h1 ▸ h2 ▸ hlt) (lt_irrefl _)
  · rw [Finset.erase_insert_of_ne hxz, Finset.erase_insert_of_ne hyz,
      Finset.erase_singleton] at htgt
    change ({t.2.1, t.2.2} : Finset (Fin 5)) = ({x, y} : Finset (Fin 5)) at htgt
    have hm1 : t.2.1 ∈ ({x, y} : Finset (Fin 5)) := by
      rw [← htgt]; exact Finset.mem_insert_self _ _
    have hm2 : t.2.2 ∈ ({x, y} : Finset (Fin 5)) := by
      rw [← htgt]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2
    · exact absurd (h1 ▸ h2 ▸ hlt) (lt_irrefl _)
    · rw [h1, h2]; exact hC
    · rw [h1, h2, show cfg.p x - cfg.p y = -(cfg.p y - cfg.p x) by rw [neg_sub],
        dot_neg_left, dot_neg_left, hC]
    · exact absurd (h1 ▸ h2 ▸ hlt) (lt_irrefl _)

/-- A pair of altitudes of a triangle intersects at the orthocenter. -/
theorem pairPt_eq_orthoPtT (cfg : Config K) {a b : Triple}
    (hs : ({a, b} : Finset Triple) ∈ goodPairs cfg)
    (ha : a ∈ perpIdx) (hb : b ∈ perpIdx) (htri : tri3 a = tri3 b) (hab : a ≠ b) :
    pairPt cfg {a, b} = orthoPtT cfg (tri3 a) := by
  have hT : (tri3 a).card = 3 := tri3_card ha
  have hma : dot (cfg.perpOf a).n (orthoPtT cfg (tri3 a)) = (cfg.perpOf a).c :=
    mem_perpOf_orthoPtT cfg hT ha rfl
  have hmb : dot (cfg.perpOf b).n (orthoPtT cfg (tri3 a)) = (cfg.perpOf b).c :=
    mem_perpOf_orthoPtT cfg hT hb htri.symm
  exact (pairPt_eq_of_mem cfg hs hab hma hmb).symm

/-- The orthocenters of the ten triangles, as a finset. -/
noncomputable def orthoFin (cfg : Config K) : Finset (Fin 2 → K) :=
  (Finset.univ.powersetCard 3).image (orthoPtT cfg)

theorem mem_orthoFin_of_alt (cfg : Config K) {s : Finset Triple}
    (hs : s ∈ goodPairs cfg) (hp : altPred s) : pairPt cfg s ∈ orthoFin cfg := by
  obtain ⟨hsa, hsnp⟩ := Finset.mem_filter.mp hs
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hsa
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ perpIdx := hsub (Finset.mem_insert_self _ _)
  have hb : b ∈ perpIdx := hsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
  have htri : tri3 a = tri3 b := eq_of_card_image_pair_eq_one hp.1
  have hs' : ({a, b} : Finset Triple) ∈ goodPairs cfg := Finset.mem_filter.mpr ⟨hsa, hsnp⟩
  show pairPt cfg {a, b} ∈ (Finset.univ.powersetCard 3).image (orthoPtT cfg)
  rw [Finset.mem_image]
  refine ⟨tri3 a, ?_, (pairPt_eq_orthoPtT cfg hs' ha hb htri hab).symm⟩
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ _, tri3_card ha⟩

/-- The key counting estimate: the intersection points are at most
315 = (5 + 10) + (435 - 135). -/
theorem card_inter_image_le (cfg : Config K) :
    ((goodPairs cfg).image (pairPt cfg)).card ≤ 315 := by
  have key : (goodPairs cfg).image (pairPt cfg) ⊆
      (ptsFin cfg ∪ orthoFin cfg) ∪ (allPairs \ fams).image (pairPt cfg) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hsa, hsnp⟩ := Finset.mem_filter.mp hs
    by_cases h1 : samePtPred s
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (mem_ptsFin_of_samePt cfg (Finset.mem_filter.mpr ⟨hsa, hsnp⟩) h1))
    · by_cases h2 : altPred s
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_orthoFin_of_alt cfg (Finset.mem_filter.mpr ⟨hsa, hsnp⟩) h2))
      · have hsmem : s ∈ allPairs \ fams := by
          rw [Finset.mem_sdiff]
          refine ⟨hsa, fun hf => ?_⟩
          rw [fams, Finset.mem_union, Finset.mem_union] at hf
          rcases hf with (h | h) | h
          · exact absurd hsnp (not_nonparP_of_parPred cfg hsa (Finset.mem_filter.mp h).2)
          · exact h1 (Finset.mem_filter.mp h).2
          · exact h2 (Finset.mem_filter.mp h).2
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hsmem, rfl⟩)
  have e1 : (ptsFin cfg ∪ orthoFin cfg).card ≤ 15 :=
    calc (ptsFin cfg ∪ orthoFin cfg).card
        ≤ (ptsFin cfg).card + (orthoFin cfg).card := Finset.card_union_le _ _
      _ ≤ 5 + 10 := Nat.add_le_add
          (calc (ptsFin cfg).card ≤ (Finset.univ : Finset (Fin 5)).card :=
              Finset.card_image_le
            _ = 5 := by rw [Finset.card_univ, Fintype.card_fin])
          (calc (orthoFin cfg).card ≤ ((Finset.univ : Finset (Fin 5)).powersetCard 3).card :=
              Finset.card_image_le
            _ = 10 := by
              rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
              decide)
      _ = 15 := by norm_num
  have e2 : (allPairs \ fams).card = 300 := by
    rw [Finset.card_sdiff_of_subset fams_subset, fams_card, allPairs_card]
  calc ((goodPairs cfg).image (pairPt cfg)).card
      ≤ ((ptsFin cfg ∪ orthoFin cfg) ∪ (allPairs \ fams).image (pairPt cfg)).card :=
        Finset.card_le_card key
    _ ≤ (ptsFin cfg ∪ orthoFin cfg).card + ((allPairs \ fams).image (pairPt cfg)).card :=
        Finset.card_union_le _ _
    _ ≤ 15 + 300 := Nat.add_le_add e1 (le_trans Finset.card_image_le (le_of_eq e2))
    _ = 315 := by norm_num

theorem interSet_eq_image (cfg : Config K) :
    interSet cfg = ↑((goodPairs cfg).image (pairPt cfg)) := by
  ext x
  simp only [interSet, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, b, hb, hab, hxa, hxb⟩
    have hcross : cross (cfg.perpOf a).n (cfg.perpOf b).n ≠ 0 :=
      cfg.cross_ne_zero_of_mem ha hb hab hxa hxb
    have hsub : ({a, b} : Finset Triple) ⊆ perpIdx :=
      Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
    have hs : ({a, b} : Finset Triple) ∈ goodPairs cfg := by
      show ({a, b} : Finset Triple) ∈ allPairs.filter (nonparP cfg)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powersetCard.mpr ⟨hsub, Finset.card_pair_eq_two_iff.mpr hab⟩,
        a, Finset.mem_insert_self _ _, b,
        Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)), hab, hcross⟩
    exact ⟨{a, b}, hs, (pairPt_eq_of_mem cfg hs hab hxa hxb).symm⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hsa, hsnp⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hsa
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha : a ∈ perpIdx := hsub (Finset.mem_insert_self _ _)
    have hb : b ∈ perpIdx := hsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)))
    have hs' : ({a, b} : Finset Triple) ∈ goodPairs cfg := Finset.mem_filter.mpr ⟨hsa, hsnp⟩
    exact ⟨a, ha, b, hb, hab, pairPt_mem₁ cfg hs' hab, pairPt_mem₂ cfg hs' hab⟩

/-- The cardinality of a finset viewed as a set. -/
theorem ncard_coe_finset {α : Type*} (s : Finset α) : (↑s : Set α).ncard = s.card := by
  rw [Set.ncard_def, Set.encard_coe_eq_coe_finsetCard, ENat.toNat_coe]

/-- The upper bound: no admissible configuration has more than 315
intersection points. -/
theorem interSet_ncard_le (cfg : Config K) : (interSet cfg).ncard ≤ 315 := by
  rw [interSet_eq_image, ncard_coe_finset]
  exact card_inter_image_le cfg

/-- The five explicit rational points achieving the maximum. -/
def ptsQ : Fin 5 → Fin 2 → ℚ := ![![3, 5], ![1, 7], ![2, 0], ![6, 3], ![0, 4]]

theorem ptsQ_inj : Function.Injective ptsQ := fun a b h => by
  have hall : ∀ i j : Fin 5, ptsQ i = ptsQ j → i = j := by decide
  exact hall a b h

/-- The rational configuration. -/
def cfgQ : Config ℚ where
  p := ptsQ
  inj := ptsQ_inj
  npar := by
    have h : ∀ i j k l : Fin 5, i ≠ j → k ≠ l → ({i, j} : Finset (Fin 5)) ≠ {k, l} →
        cross (ptsQ j - ptsQ i) (ptsQ l - ptsQ k) ≠ 0 := by decide +kernel
    exact h
  nperp := by
    have h : ∀ i j k l : Fin 5, i ≠ j → k ≠ l → ({i, j} : Finset (Fin 5)) ≠ {k, l} →
        dot (ptsQ j - ptsQ i) (ptsQ l - ptsQ k) ≠ 0 := by decide +kernel
    exact h

/-- The perpendiculars of the rational configuration, as a computable function. -/
def perpOfQ (t : Triple) : Line2 ℚ :=
  ⟨ptsQ t.2.2 - ptsQ t.2.1, dot (ptsQ t.2.2 - ptsQ t.2.1) (ptsQ t.1)⟩

theorem perpOfQ_eq (t : Triple) : cfgQ.perpOf t = perpOfQ t := rfl

/-- The finset of intersection points of the 30 perpendiculars of `cfgQ`. -/
def computedPts : Finset (Fin 2 → ℚ) :=
  ((perpIdx ×ˢ perpIdx).filter (fun ab => ab.1 ≠ ab.2 ∧
    cross (perpOfQ ab.1).n (perpOfQ ab.2).n ≠ 0)).image
    (fun ab => interPt (perpOfQ ab.1) (perpOfQ ab.2))

theorem computedPts_card : computedPts.card = 315 := by decide +kernel

/-- Embedding of rational points into real points. -/
def castPt (v : Fin 2 → ℚ) : Fin 2 → ℝ := fun i => (v i : ℝ)

theorem castPt_inj : Function.Injective castPt := fun v w h => by
  funext i
  exact Rat.cast_injective (congrFun h i)

theorem dot_castPt (u v : Fin 2 → ℚ) :
    dot (castPt u) (castPt v) = ((dot u v : ℚ) : ℝ) := by
  simp [dot, castPt]

theorem cross_castPt (u v : Fin 2 → ℚ) :
    cross (castPt u) (castPt v) = ((cross u v : ℚ) : ℝ) := by
  simp [cross, castPt]

/-- Embedding of rational lines into real lines. -/
def castLine (ℓ : Line2 ℚ) : Line2 ℝ := ⟨castPt ℓ.n, (ℓ.c : ℝ)⟩

theorem cast_mem {ℓ : Line2 ℚ} {v : Fin 2 → ℚ}
    (h : dot ℓ.n v = ℓ.c) : dot (castLine ℓ).n (castPt v) = (castLine ℓ).c := by
  show dot (castPt ℓ.n) (castPt v) = ((ℓ.c : ℚ) : ℝ)
  rw [dot_castPt]
  exact congrArg _ h

theorem interPt_cast_of_ne {ℓ₁ ℓ₂ : Line2 ℚ} (h : cross ℓ₁.n ℓ₂.n ≠ 0) :
    interPt (castLine ℓ₁) (castLine ℓ₂) = castPt (interPt ℓ₁ ℓ₂) := by
  have hc : cross (castLine ℓ₁).n (castLine ℓ₂).n ≠ 0 := by
    show cross (castPt ℓ₁.n) (castPt ℓ₂.n) ≠ 0
    rw [cross_castPt]
    exact fun hh => h (Rat.cast_eq_zero.mp hh)
  exact mem_unique hc (interPt_mem₁ hc) (interPt_mem₂ hc)
    (cast_mem (interPt_mem₁ h)) (cast_mem (interPt_mem₂ h))

/-- The five real points obtained from the rational configuration. -/
def ptsR : Fin 5 → Fin 2 → ℝ := fun i => castPt (ptsQ i)

theorem ptsR_sub (i j : Fin 5) : ptsR j - ptsR i = castPt (ptsQ j - ptsQ i) := by
  funext x
  simp [ptsR, castPt, Pi.sub_apply, Rat.cast_sub]

/-- The real configuration. -/
def cfgR : Config ℝ where
  p := ptsR
  inj := castPt_inj.comp ptsQ_inj
  npar := by
    intro i j k l hij hkl hpairs
    have h := cfgQ.npar i j k l hij hkl hpairs
    rw [ptsR_sub, ptsR_sub, cross_castPt]
    exact fun hc => h (Rat.cast_eq_zero.mp hc)
  nperp := by
    intro i j k l hij hkl hpairs
    have h := cfgQ.nperp i j k l hij hkl hpairs
    rw [ptsR_sub, ptsR_sub, dot_castPt]
    exact fun hc => h (Rat.cast_eq_zero.mp hc)

theorem cfgR_p : cfgR.p = ptsR := rfl

theorem perpOfR_eq (t : Triple) : cfgR.perpOf t = castLine (perpOfQ t) := by
  have hn : (cfgR.perpOf t).n = castPt ((perpOfQ t).n) := by
    funext x
    simp [Config.perpOf, perpOfQ, cfgR_p, ptsR, castPt, Pi.sub_apply, Rat.cast_sub]
  have hc : (cfgR.perpOf t).c = ((perpOfQ t).c : ℝ) := by
    simp [Config.perpOf, perpOfQ, cfgR_p, ptsR, castPt, dot, Pi.sub_apply, Rat.cast_sub,
      Rat.cast_add, Rat.cast_mul]
  exact Line2.ext hn hc

theorem mem_of_memQ {t : Triple} {v : Fin 2 → ℚ}
    (h : dot (perpOfQ t).n v = (perpOfQ t).c) :
    dot (cfgR.perpOf t).n (castPt v) = (cfgR.perpOf t).c := by
  rw [perpOfR_eq]
  exact cast_mem h

/-- The intersection set of the real configuration is exactly the image of
the computed 315 rational points. -/
theorem interSet_cfgR : interSet cfgR = ↑(computedPts.image castPt) := by
  ext x
  simp only [interSet, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, b, hb, hab, hxa, hxb⟩
    have hcrossR : cross (cfgR.perpOf a).n (cfgR.perpOf b).n ≠ 0 :=
      cfgR.cross_ne_zero_of_mem ha hb hab hxa hxb
    have hcrossQ : cross (perpOfQ a).n (perpOfQ b).n ≠ 0 := by
      intro hq
      apply hcrossR
      rw [perpOfR_eq, perpOfR_eq]
      show cross (castPt (perpOfQ a).n) (castPt (perpOfQ b).n) = 0
      rw [cross_castPt, hq]
      simp
    have hv : interPt (perpOfQ a) (perpOfQ b) ∈ computedPts := by
      rw [computedPts, Finset.mem_image]
      exact ⟨(a, b), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab, hcrossQ⟩, rfl⟩
    refine ⟨interPt (perpOfQ a) (perpOfQ b), hv, ?_⟩
    have e : x = interPt (cfgR.perpOf a) (cfgR.perpOf b) :=
      mem_unique hcrossR hxa hxb (interPt_mem₁ hcrossR) (interPt_mem₂ hcrossR)
    rw [e, perpOfR_eq a, perpOfR_eq b]
    exact (interPt_cast_of_ne hcrossQ).symm
  · rintro ⟨v, hv, rfl⟩
    rw [computedPts, Finset.mem_image] at hv
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hv
    rw [Finset.mem_filter, Finset.mem_product] at hab
    obtain ⟨⟨ha, hb⟩, hne, hcrossQ⟩ := hab
    exact ⟨a, ha, b, hb, hne, mem_of_memQ (interPt_mem₁ hcrossQ),
      mem_of_memQ (interPt_mem₂ hcrossQ)⟩

/-- The lower bound: the maximum 315 is attained. -/
theorem interSet_cfgR_ncard : (interSet cfgR).ncard = 315 := by
  rw [interSet_cfgR, ncard_coe_finset, Finset.card_image_of_injective _ castPt_inj,
    computedPts_card]

snip end

problem imo1964_p5 :
    IsGreatest {n : ℕ | ∃ cfg : Config ℝ, (interSet cfg).ncard = n} answer := by
  constructor
  · exact ⟨cfgR, interSet_cfgR_ncard⟩
  · rintro n ⟨cfg, rfl⟩
    exact interSet_ncard_le cfg

end Imo1964P5
