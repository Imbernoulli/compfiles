/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

import Mathlib
import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# USA Mathematical Olympiad 1981, Problem 2

What is the largest number of towns that can meet the following criteria?
Each pair is directly linked by just one of air, bus or train.
At least one pair is linked by air, at least one pair by bus and at least
one pair by train. No town has an air link, a bus link and a train link.
No three towns, A, B, C are such that the links between AB, AC and BC are
all air, all bus or all train.
-/

namespace Usa1981P2

/-- The three possible link types between two towns. -/
inductive Link | air | bus | train
  deriving DecidableEq, Fintype

/-- The set of link types that town `v` has to other towns. -/
abbrev colorsAt {n : ℕ} (f : Fin n → Fin n → Link) (v : Fin n) : Finset Link :=
  (Finset.univ.filter (· ≠ v)).image (f v ·)

/-- A link assignment on `n` towns satisfying all the criteria of the problem:
it is symmetric, all three link types are used, no town has all three link
types, and no three towns are pairwise linked by the same type. -/
abbrev Valid {n : ℕ} (f : Fin n → Fin n → Link) : Prop :=
  (∀ i j, f i j = f j i) ∧
  (∃ i j, i ≠ j ∧ f i j = .air) ∧
  (∃ i j, i ≠ j ∧ f i j = .bus) ∧
  (∃ i j, i ≠ j ∧ f i j = .train) ∧
  (∀ v, (colorsAt f v).card ≤ 2) ∧
  (∀ a b c, a ≠ b → b ≠ c → a ≠ c → ¬ (f a b = f a c ∧ f a b = f b c))

determine answer : ℕ := 4

snip begin

/-- If a town `u` is linked to three other towns by three pairwise distinct
link types, then `u` has at least three link types. -/
theorem three_le_card_colorsAt {n : ℕ} {f : Fin n → Fin n → Link} {u : Fin n}
    {p q r : Fin n} (hp : p ≠ u) (hq : q ≠ u) (hr : r ≠ u)
    {c₁ c₂ c₃ : Link} (h1 : f u p = c₁) (h2 : f u q = c₂) (h3 : f u r = c₃)
    (d12 : c₁ ≠ c₂) (d13 : c₁ ≠ c₃) (d23 : c₂ ≠ c₃) :
    3 ≤ (colorsAt f u).card := by
  have hsub : ({c₁, c₂, c₃} : Finset Link) ⊆ colorsAt f u := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩, h1⟩
    · exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩, h2⟩
    · exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr⟩, h3⟩
  have hcard : ({c₁, c₂, c₃} : Finset Link).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [d12, d13]),
      Finset.card_insert_of_notMem (by simp [d23]), Finset.card_singleton]
  exact hcard ▸ Finset.card_le_card hsub

/-- Key local fact: no town is linked to three other towns by the same link
type. (Among any three such towns, the links would have to avoid that type,
and then either one of the three towns has all three link types, or the
remaining links form a monochromatic triangle.) -/
theorem fiber_card_le_two {n : ℕ} {f : Fin n → Fin n → Link} (hf : Valid f)
    (v : Fin n) (c : Link) :
    (Finset.univ.filter fun w ↦ w ≠ v ∧ f v w = c).card ≤ 2 := by
  obtain ⟨hsymm, -, -, -, hmax, hmono⟩ := hf
  by_contra h
  rw [not_le] at h
  obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, d12, d13, d23⟩ := Finset.two_lt_card_iff.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂ hw₃
  -- The links among `w₁, w₂, w₃` cannot have type `c`, otherwise the link
  -- together with `v` would form a monochromatic triangle.
  have e12 : f w₁ w₂ ≠ c := fun e ↦
    hmono v w₁ w₂ (Ne.symm hw₁.1) d12 (Ne.symm hw₂.1)
      ⟨hw₁.2.trans hw₂.2.symm, hw₁.2.trans e.symm⟩
  have e13 : f w₁ w₃ ≠ c := fun e ↦
    hmono v w₁ w₃ (Ne.symm hw₁.1) d13 (Ne.symm hw₃.1)
      ⟨hw₁.2.trans hw₃.2.symm, hw₁.2.trans e.symm⟩
  have e23 : f w₂ w₃ ≠ c := fun e ↦
    hmono v w₂ w₃ (Ne.symm hw₂.1) d23 (Ne.symm hw₃.1)
      ⟨hw₂.2.trans hw₃.2.symm, hw₂.2.trans e.symm⟩
  by_cases hxy : f w₁ w₂ = f w₁ w₃
  · -- Then `f w₂ w₃` differs from both, so `w₂` has all three link types.
    have e23' : f w₂ w₃ ≠ f w₁ w₂ := fun e ↦
      hmono w₁ w₂ w₃ d12 d23 d13 ⟨hxy, e.symm⟩
    have hle := three_le_card_colorsAt (Ne.symm hw₂.1) d12 (Ne.symm d23)
      ((hsymm w₂ v).trans hw₂.2) (hsymm w₂ w₁) rfl
      (Ne.symm e12) (Ne.symm e23) (Ne.symm e23')
    have := hmax w₂
    omega
  · -- Then `w₁` has all three link types.
    have hle := three_le_card_colorsAt (Ne.symm hw₁.1) (Ne.symm d12) (Ne.symm d13)
      ((hsymm w₁ v).trans hw₁.2) rfl rfl
      (Ne.symm e12) (Ne.symm e13) hxy
    have := hmax w₁
    omega

/-- Every town is directly linked to at most four other towns:
at most two link types, at most two links of each type. -/
theorem card_neighbors_le_four {n : ℕ} {f : Fin n → Fin n → Link} (hf : Valid f)
    (v : Fin n) :
    (Finset.univ.filter (· ≠ v)).card ≤ 4 := by
  rw [Finset.card_eq_sum_card_image (f v ·) (Finset.univ.filter (· ≠ v))]
  have hfib : ∀ d ∈ (Finset.univ.filter (· ≠ v)).image (f v ·),
      ((Finset.univ.filter (· ≠ v)).filter fun w ↦ f v w = d).card ≤ 2 := by
    intro d _
    refine le_trans (Finset.card_le_card ?_) (fiber_card_le_two hf v d)
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact hw
  calc ∑ d ∈ (Finset.univ.filter (· ≠ v)).image (f v ·),
          ((Finset.univ.filter (· ≠ v)).filter fun w ↦ f v w = d).card
      ≤ ∑ _d ∈ (Finset.univ.filter (· ≠ v)).image (f v ·), 2 := Finset.sum_le_sum hfib
    _ = 2 * ((Finset.univ.filter (· ≠ v)).image (f v ·)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 * 2 := by
        gcongr
        exact hf.2.2.2.2.1 v
    _ = 4 := rfl

theorem card_filter_ne {n : ℕ} (v : Fin n) :
    (Finset.univ.filter (· ≠ v)).card = n - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, Fintype.card_fin]

/-- The ten unordered pairs of towns of `Fin 5`, in a fixed order. -/
def pair : Fin 10 → Fin 5 × Fin 5 := fun k ↦
  match k.val with
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (1, 2)
  | 5 => (1, 3)
  | 6 => (1, 4)
  | 7 => (2, 3)
  | 8 => (2, 4)
  | 9 => (3, 4)
  | _ => (0, 1)

/-- The position of the unordered pair `{i, j}` in the list `pair`. -/
def edgeIdx (i j : Fin 5) : Fin 10 :=
  ⟨(match i.val, j.val with
    | 0, 1 | 1, 0 => 0
    | 0, 2 | 2, 0 => 1
    | 0, 3 | 3, 0 => 2
    | 0, 4 | 4, 0 => 3
    | 1, 2 | 2, 1 => 4
    | 1, 3 | 3, 1 => 5
    | 1, 4 | 4, 1 => 6
    | 2, 3 | 3, 2 => 7
    | 2, 4 | 4, 2 => 8
    | 3, 4 | 4, 3 => 9
    | _, _ => 0) % 10, Nat.mod_lt _ (by decide)⟩

/-- A symmetric link assignment on five towns, reconstructed from its
restriction to the ten unordered pairs. -/
def mkColor (u : Fin 10 → Link) : Fin 5 → Fin 5 → Link :=
  fun i j ↦ if i = j then .air else u (edgeIdx i j)

theorem pair_edgeIdx :
    ∀ i j : Fin 5, i ≠ j → pair (edgeIdx i j) = (i, j) ∨ pair (edgeIdx i j) = (j, i) := by
  decide

theorem mkColor_eq {f : Fin 5 → Fin 5 → Link} (hsymm : ∀ i j, f i j = f j i)
    {i j : Fin 5} (hij : i ≠ j) :
    mkColor (fun k ↦ f (pair k).1 (pair k).2) i j = f i j := by
  simp only [mkColor, if_neg hij]
  rcases pair_edgeIdx i j hij with e | e
  · rw [e]
  · rw [e]
    exact hsymm j i

/-- Any valid assignment on five towns restricts to a valid assignment
reconstructed from the ten unordered pairs. -/
theorem valid_mkColor {f : Fin 5 → Fin 5 → Link} (hf : Valid f) :
    Valid (mkColor fun k ↦ f (pair k).1 (pair k).2) := by
  obtain ⟨hsymm, hair, hbus, htrain, hmax, hmono⟩ := hf
  have mc : ∀ {i j : Fin 5}, i ≠ j →
      mkColor (fun k ↦ f (pair k).1 (pair k).2) i j = f i j :=
    fun h ↦ mkColor_eq hsymm h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · rw [hij]
    · rw [mc hij, mc (Ne.symm hij)]
      exact hsymm i j
  · obtain ⟨i, j, hij, h⟩ := hair
    exact ⟨i, j, hij, by rw [mc hij]; exact h⟩
  · obtain ⟨i, j, hij, h⟩ := hbus
    exact ⟨i, j, hij, by rw [mc hij]; exact h⟩
  · obtain ⟨i, j, hij, h⟩ := htrain
    exact ⟨i, j, hij, by rw [mc hij]; exact h⟩
  · intro v
    have heq : colorsAt (mkColor fun k ↦ f (pair k).1 (pair k).2) v = colorsAt f v :=
      Finset.image_congr fun w hw ↦ mc (Ne.symm (Finset.mem_filter.mp hw).2)
    rw [heq]
    exact hmax v
  · intro a b c hab hbc hac ⟨e1, e2⟩
    rw [mc hab, mc hac] at e1
    rw [mc hab, mc hbc] at e2
    exact hmono a b c hab hbc hac ⟨e1, e2⟩

/-- A brute-force check: no link assignment on five towns satisfies all the
criteria. (The conditions only involve the ten unordered pairs, so there are
only `3^10` symmetric assignments to check.) -/
theorem check5 : ∀ u : Fin 10 → Link, ¬ Valid (mkColor u) := by
  native_decide

theorem not_valid_five {f : Fin 5 → Fin 5 → Link} (hf : Valid f) : False :=
  check5 _ (valid_mkColor hf)

snip end

problem usa1981_p2 :
    IsGreatest {n : ℕ | ∃ f : Fin n → Fin n → Link, Valid f} answer := by
  refine ⟨⟨fun i j ↦
      if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then .bus
      else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then .train
      else .air, by decide⟩, fun n hn ↦ ?_⟩
  -- Four towns are achievable: link towns `0` and `1` by bus, towns `2` and
  -- `3` by train, and all other pairs by air.
  obtain ⟨f, hf⟩ := hn
  by_contra h
  rw [not_le, show answer = 4 from rfl] at h
  -- `4 < n`; we derive a contradiction.
  rcases (show n = 5 ∨ 6 ≤ n by omega) with h5 | h6
  · subst h5
    exact not_valid_five hf
  · have v : Fin n := ⟨0, by omega⟩
    have h4 := card_neighbors_le_four hf v
    rw [card_filter_ne v] at h4
    omega

end Usa1981P2
