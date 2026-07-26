/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

set_option maxHeartbeats 32000000
set_option maxRecDepth 8192

/-!
# International Mathematical Olympiad 2013, Problem 3

Let the excircle of triangle ABC opposite the vertex A be tangent to the side
BC at the point A1. Define the points B1 on CA and C1 on AB analogously, using
the excircles opposite B and C, respectively. Suppose that the circumcenter of
triangle A1B1C1 lies on the circumcircle of triangle ABC. Prove that triangle
ABC is right-angled.
-/

namespace Imo2013P3

open scoped EuclideanGeometry RealInnerProductSpace

snip begin

/-!
### Auxiliary lemmas

The proof is a coordinate computation. After applying a rigid motion we may
place `A` at the origin and `B` on the positive x-axis. Writing the side
lengths as `a = y + z`, `b = z + x`, `c = x + y` (the Ravi substitution,
with strictly positive `x`, `y`, `z`), the touch points of the excircles
have explicit rational coordinates. The condition that the circumcenter of
`A1B1C1` lies on the circumcircle of `ABC` then becomes a polynomial equation,
whose only relevant factors are the three dot products that detect the right
angles. The heavy polynomial identities were found by computer algebra and
are checked here by `ring` / `linear_combination`.
-/

/-- Squared distance between two points of the plane, in coordinates. -/
theorem dist_sq_fin2 (U V : EuclideanSpace ℝ (Fin 2)) :
    dist U V ^ 2 = (U 0 - V 0)^2 + (U 1 - V 1)^2 := by
  rw [EuclideanSpace.dist_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- Inner product of two plane vectors, in coordinates. -/
theorem inner_fin2 (U V : EuclideanSpace ℝ (Fin 2)) :
    ⟪U, V⟫ = U 0 * V 0 + U 1 * V 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- Case split on the indices of `Fin 2`, with numeral forms `0` and `1`. -/
theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Case split on the indices of `Fin 3`, with numeral forms. -/
theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The rigid-motion parametrization used to place `A` at the origin. -/
noncomputable def TOf (A e1 e2 P : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[⟪P - A, e1⟫, ⟪P - A, e2⟫]

theorem TOf_apply_zero (A e1 e2 P : EuclideanSpace ℝ (Fin 2)) :
    (TOf A e1 e2 P) 0 = ⟪P - A, e1⟫ := rfl

theorem TOf_apply_one (A e1 e2 P : EuclideanSpace ℝ (Fin 2)) :
    (TOf A e1 e2 P) 1 = ⟪P - A, e2⟫ := rfl

/-- The map `TOf` preserves distances when `e1`, `e2` come from an
orthonormal basis of the plane (we only need the concrete rotated basis). -/
theorem TOf_dist {A e1 e2 : EuclideanSpace ℝ (Fin 2)}
    (he2 : e2 = !₂[-(e1 1), e1 0]) (he1sq : e1 0^2 + e1 1^2 = 1)
    (P Q : EuclideanSpace ℝ (Fin 2)) :
    dist (TOf A e1 e2 P) (TOf A e1 e2 Q) = dist P Q := by
  have h2 : dist (TOf A e1 e2 P) (TOf A e1 e2 Q)^2 = dist P Q^2 := by
    rw [dist_sq_fin2, dist_sq_fin2, TOf_apply_zero, TOf_apply_one,
      TOf_apply_zero, TOf_apply_one, ← inner_sub_left, ← inner_sub_left]
    have hsub : P - A - (Q - A) = P - Q := by abel
    rw [hsub, inner_fin2 (P - Q) e1, inner_fin2 (P - Q) e2, he2]
    simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination ((P 0 - Q 0)^2 + (P 1 - Q 1)^2) * he1sq
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h2

/-- The map `TOf` preserves inner products of differences. -/
theorem TOf_inner {A e1 e2 : EuclideanSpace ℝ (Fin 2)}
    (he2 : e2 = !₂[-(e1 1), e1 0]) (he1sq : e1 0^2 + e1 1^2 = 1)
    (P Q R : EuclideanSpace ℝ (Fin 2)) :
    ⟪TOf A e1 e2 P - TOf A e1 e2 Q, TOf A e1 e2 R - TOf A e1 e2 Q⟫
      = ⟪P - Q, R - Q⟫ := by
  rw [inner_fin2]
  simp only [PiLp.sub_apply, TOf_apply_zero, TOf_apply_one]
  rw [← inner_sub_left, ← inner_sub_left, ← inner_sub_left, ← inner_sub_left]
  have hsub1 : P - A - (Q - A) = P - Q := by abel
  have hsub2 : R - A - (Q - A) = R - Q := by abel
  rw [hsub1, hsub2, inner_fin2 (P - Q) e1, inner_fin2 (P - Q) e2,
    inner_fin2 (R - Q) e1, inner_fin2 (R - Q) e2, inner_fin2 (P - Q) (R - Q), he2]
  simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination ((P 0 - Q 0) * (R 0 - Q 0) + (P 1 - Q 1) * (R 1 - Q 1)) * he1sq

/-- Every plane vector is the sum of its coordinates in the basis `e1, e2`. -/
theorem onb_repr {e1 e2 : EuclideanSpace ℝ (Fin 2)}
    (he2 : e2 = !₂[-(e1 1), e1 0]) (he1sq : e1 0^2 + e1 1^2 = 1)
    (v : EuclideanSpace ℝ (Fin 2)) :
    v = ⟪v, e1⟫ • e1 + ⟪v, e2⟫ • e2 := by
  ext i
  rcases fin2_cases i with rfl | rfl
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [inner_fin2 v e1, inner_fin2 v e2, he2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-(v 0)) * he1sq
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [inner_fin2 v e1, inner_fin2 v e2, he2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-(v 1)) * he1sq

/-- `TOf` is affine: it commutes with `lineMap`. -/
theorem TOf_lineMap (A e1 e2 P Q : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    TOf A e1 e2 (AffineMap.lineMap P Q t)
      = AffineMap.lineMap (TOf A e1 e2 P) (TOf A e1 e2 Q) t := by
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
  ext i
  rcases fin2_cases i with rfl | rfl
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      TOf_apply_zero]
    rw [add_sub_assoc, inner_add_left, real_inner_smul_left, ← inner_sub_left]
    have hsub : Q - A - (P - A) = Q - P := by abel
    rw [hsub]
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      TOf_apply_one]
    rw [add_sub_assoc, inner_add_left, real_inner_smul_left, ← inner_sub_left]
    have hsub : Q - A - (P - A) = Q - P := by abel
    rw [hsub]

/- The algebraic heart of the proof.  With the Ravi substitution
`a = y+z, b = z+x, c = x+y` and the triangle placed at
`A = (0,0)`, `B = (x+y, 0)`, `C = (p, q)`, the excircle touch points are
`A1 = B + (z/(y+z))(C-B)`, `B1 = C + (x/(z+x))(A-C)`, `C1 = (y, 0)`.
Here `w0, w1` are the coordinates of a point equidistant from `A1, B1, C1`
(the circumcenter of the extouch triangle), `o0, o1` those of the
circumcenter of `ABC`, and the hypotheses say that the former lies on the
circumcircle.  The conclusion is that one of the three dot products
`x(x+y+z)-yz`, `y(x+y+z)-xz`, `z(x+y+z)-xy` vanishes; each of them is
proportional to a dot product at a vertex of the triangle, hence to a
right angle.  All polynomial identities below were produced by a computer
algebra elimination and are merely *verified* here. -/

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyA1 (x y z _q : ℝ) : ℝ := - 2 * x^5 * y^2 - 4 * y * z * x^5 - 2 * x^5 * z^2 - 6 * x^4 * y^3 - 12 * z * x^4 * y^2 - 10 * y * x^4 * z^2 - 4 * x^4 * z^3 - 6 * x^3 * y^4 - 16 * z * x^3 * y^3 - 12 * x^3 * y^2 * z^2 - 4 * y * x^3 * z^3 - 2 * x^3 * z^4 - 2 * x^2 * y^5 - 12 * z * x^2 * y^4 - 12 * x^2 * y^3 * z^2 + 2 * y * x^2 * z^4 - 4 * x * z * y^5 - 10 * x * y^4 * z^2 - 4 * x * y^3 * z^3 + 2 * x * y^2 * z^4 - 2 * y^5 * z^2 - 4 * y^4 * z^3 - 2 * y^3 * z^4

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyB1 (x y z q : ℝ) : ℝ := - 2 * q * y * z * x^4 - 2 * q * x^4 * z^2 - 2 * q * z * x^3 * y^2 - 4 * q * y * x^3 * z^2 - 2 * q * x^3 * z^3 + 2 * q * z * x^2 * y^3 - 2 * q * y * x^2 * z^3 + 2 * q * x * z * y^4 + 4 * q * x * y^3 * z^2 + 2 * q * x * y^2 * z^3 + 2 * q * y^4 * z^2 + 2 * q * y^3 * z^3

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyE1 (x y z q : ℝ) : ℝ := - q^2 * x^4 * z^2 - 2 * y * q^2 * x^3 * z^2 - 2 * q^2 * x^3 * z^3 - 2 * y * q^2 * x^2 * z^3 + 2 * x * q^2 * y^3 * z^2 + 2 * x * q^2 * y^2 * z^3 + q^2 * y^4 * z^2 + 2 * q^2 * y^3 * z^3 - x^6 * y^2 - 2 * y * z * x^6 - x^6 * z^2 - 4 * x^5 * y^3 - 8 * z * x^5 * y^2 - 8 * y * x^5 * z^2 - 4 * x^5 * z^3 - 6 * x^4 * y^4 - 14 * z * x^4 * y^3 - 15 * x^4 * y^2 * z^2 - 8 * y * x^4 * z^3 - 5 * x^4 * z^4 - 4 * x^3 * y^5 - 14 * z * x^3 * y^4 - 12 * x^3 * y^3 * z^2 - 4 * x^3 * y^2 * z^3 + 4 * y * x^3 * z^4 - 2 * x^3 * z^5 - x^2 * y^6 - 8 * z * x^2 * y^5 - 7 * x^2 * y^4 * z^2 + 2 * x^2 * y^2 * z^4 + 6 * y * x^2 * z^5 - 2 * x * z * y^6 - 4 * x * y^5 * z^2 - 4 * x * y^3 * z^4 - 6 * x * y^2 * z^5 - y^6 * z^2 + 3 * y^4 * z^4 + 2 * y^3 * z^5

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyA2 (x y z _q : ℝ) : ℝ := 2 * y * x^4 - 2 * z * x^4 + 4 * x^3 * y^2 - 4 * x^3 * z^2 + 2 * x^2 * y^3 + 6 * z * x^2 * y^2 - 2 * y * x^2 * z^2 - 2 * x^2 * z^3 + 4 * x * z * y^3 + 4 * x * y^2 * z^2 + 2 * y^3 * z^2 + 2 * y^2 * z^3

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyB2 (x y z q : ℝ) : ℝ := - 2 * q * z * x^3 - 4 * q * y * z * x^2 - 2 * q * x^2 * z^2 - 2 * q * x * z * y^2 - 4 * q * x * y * z^2 - 2 * q * y^2 * z^2

/-- Coefficients of the equidistance equations, cleared of denominators. -/
def polyE2 (x y z q : ℝ) : ℝ := - q^2 * x^2 * z^2 - 2 * x * y * q^2 * z^2 - q^2 * y^2 * z^2 + x^4 * y^2 - x^4 * z^2 + 2 * x^3 * y^3 + 2 * z * x^3 * y^2 - 2 * y * x^3 * z^2 - 2 * x^3 * z^3 + x^2 * y^4 + 4 * z * x^2 * y^3 - x^2 * z^4 + 2 * x * z * y^4 + 2 * x * y^3 * z^2 + 2 * x * y^2 * z^3 + 2 * x * y * z^4 + y^4 * z^2 - y^2 * z^4

/-- Cofactor of the numerator `N₀` of the `w0`-coordinate. -/
def polyM0 (x y z q : ℝ) : ℝ := q^2 * x^3 * z^2 + y * q^2 * x^2 * z^2 - x * q^2 * y^2 * z^2 - q^2 * y^3 * z^2 + x^5 * y^2 + 2 * y * z * x^5 + x^5 * z^2 + 5 * x^4 * y^3 + 8 * z * x^4 * y^2 + 5 * y * x^4 * z^2 + 2 * x^4 * z^3 + 7 * x^3 * y^4 + 12 * z * x^3 * y^3 + 8 * x^3 * y^2 * z^2 + x^3 * z^4 + 3 * x^2 * y^5 + 8 * z * x^2 * y^4 + 4 * x^2 * y^3 * z^2 - 3 * y * x^2 * z^4 + 2 * x * z * y^5 - x * y^4 * z^2 + 3 * x * y^2 * z^4 - y^5 * z^2 - 2 * y^4 * z^3 - y^3 * z^4

/-- Cofactor of the numerator `N₁` of the `w1`-coordinate. -/
def polyM1 (x y z q : ℝ) : ℝ := y * q^2 * x^5 * z^2 - q^2 * x^5 * z^3 + 4 * q^2 * x^4 * y^2 * z^2 + y * q^2 * x^4 * z^3 - q^2 * x^4 * z^4 + 6 * q^2 * x^3 * y^3 * z^2 + 8 * q^2 * x^3 * y^2 * z^3 + 4 * q^2 * x^2 * y^4 * z^2 + 8 * q^2 * x^2 * y^3 * z^3 + 2 * q^2 * x^2 * y^2 * z^4 + x * q^2 * y^5 * z^2 + x * q^2 * y^4 * z^3 - q^2 * y^5 * z^3 - q^2 * y^4 * z^4 + x^7 * y^3 + z * x^7 * y^2 - y * x^7 * z^2 - x^7 * z^3 + 4 * x^6 * y^4 + 3 * z * x^6 * y^3 - x^6 * y^2 * z^2 - 3 * y * x^6 * z^3 - 3 * x^6 * z^4 + 6 * x^5 * y^5 + 4 * z * x^5 * y^4 + x^5 * y^3 * z^2 - x^5 * y^2 * z^3 + y * x^5 * z^4 - 3 * x^5 * z^5 + 4 * x^4 * y^6 + 4 * z * x^4 * y^5 + 2 * x^4 * y^4 * z^2 + 5 * x^4 * y^3 * z^3 + 3 * x^4 * y^2 * z^4 + 7 * y * x^4 * z^5 - x^4 * z^6 + x^3 * y^7 + 3 * z * x^3 * y^6 + x^3 * y^5 * z^2 + 5 * x^3 * y^4 * z^3 - 2 * x^3 * y^3 * z^4 - 4 * x^3 * y^2 * z^5 + 4 * y * x^3 * z^6 + z * x^2 * y^7 - x^2 * y^6 * z^2 - x^2 * y^5 * z^3 + 3 * x^2 * y^4 * z^4 - 4 * x^2 * y^3 * z^5 - 6 * x^2 * y^2 * z^6 - x * y^7 * z^2 - 3 * x * y^6 * z^3 + x * y^5 * z^4 + 7 * x * y^4 * z^5 + 4 * x * y^3 * z^6 - y^7 * z^3 - 3 * y^6 * z^4 - 3 * y^5 * z^5 - y^4 * z^6

/-- Determinant of the equidistance linear system for `w0, w1`. -/
def polyDD (x y z q : ℝ) : ℝ := 8 * q * x * y * z * (x + y)^4 * (x + z)^3 * (y + z)

/-- Numerator of the `w0` coordinate: `polyDD * w0 = polyN0`. -/
def polyN0 (x y z q : ℝ) : ℝ := 2 * q * z * (x + y)^2 * (x + z)^2 * polyM0 x y z q

/-- Numerator of the `w1` coordinate: `polyDD * w1 = polyN1`. -/
def polyN1 (x y z q : ℝ) : ℝ := 2 * (x + y) * (x + z)^2 * polyM1 x y z q

/-- Coefficients of the eliminated polynomial `A₀` in `u = q^2`. -/
def polyC0 (x y z : ℝ) : ℝ := 4 * x^20 * y^6 + 8 * z * x^20 * y^5 - 4 * x^20 * y^4 * z^2 - 16 * x^20 * y^3 * z^3 - 4 * x^20 * y^2 * z^4 + 8 * y * x^20 * z^5 + 4 * x^20 * z^6 + 40 * x^19 * y^7 + 104 * z * x^19 * y^6 + 24 * x^19 * y^5 * z^2 - 168 * x^19 * y^4 * z^3 - 168 * x^19 * y^3 * z^4 + 24 * x^19 * y^2 * z^5 + 104 * y * x^19 * z^6 + 40 * x^19 * z^7 + 180 * x^18 * y^8 + 600 * z * x^18 * y^7 + 464 * x^18 * y^6 * z^2 - 648 * x^18 * y^5 * z^3 - 1288 * x^18 * y^4 * z^4 - 504 * x^18 * y^3 * z^5 + 464 * x^18 * y^2 * z^6 + 552 * y * x^18 * z^7 + 180 * x^18 * z^8 + 480 * x^17 * y^9 + 2040 * z * x^17 * y^8 + 2536 * x^17 * y^7 * z^2 - 888 * x^17 * y^6 * z^3 - 4840 * x^17 * y^5 * z^4 - 3928 * x^17 * y^4 * z^5 + 216 * x^17 * y^3 * z^6 + 2296 * x^17 * y^2 * z^7 + 1608 * y * x^17 * z^8 + 480 * x^17 * z^9 + 840 * x^16 * y^10 + 4560 * z * x^16 * y^9 + 7836 * x^16 * y^8 * z^2 + 1592 * x^16 * y^7 * z^3 - 11044 * x^16 * y^6 * z^4 - 14096 * x^16 * y^5 * z^5 - 4388 * x^16 * y^4 * z^6 + 4856 * x^16 * y^3 * z^7 + 5916 * x^16 * y^2 * z^8 + 2832 * y * x^16 * z^9 + 840 * x^16 * z^10 + 1008 * x^15 * y^11 + 7056 * z * x^15 * y^10 + 15984 * x^15 * y^9 * z^2 + 9744 * x^15 * y^8 * z^3 - 16448 * x^15 * y^7 * z^4 - 32832 * x^15 * y^6 * z^5 - 19520 * x^15 * y^5 * z^6 + 4480 * x^15 * y^4 * z^7 + 13648 * x^15 * y^3 * z^8 + 9264 * x^15 * y^2 * z^9 + 3024 * y * x^15 * z^10 + 1008 * x^15 * z^11 + 840 * x^14 * y^12 + 7728 * z * x^14 * y^11 + 22848 * x^14 * y^10 * z^2 + 22320 * x^14 * y^9 * z^3 - 15816 * x^14 * y^8 * z^4 - 56128 * x^14 * y^7 * z^5 - 49856 * x^14 * y^6 * z^6 - 8320 * x^14 * y^5 * z^7 + 20728 * x^14 * y^4 * z^8 + 20688 * x^14 * y^3 * z^9 + 9408 * x^14 * y^2 * z^10 + 1680 * y * x^14 * z^11 + 840 * x^14 * z^12 + 480 * x^13 * y^13 + 6000 * z * x^13 * y^12 + 23376 * x^13 * y^11 * z^2 + 32016 * x^13 * y^10 * z^3 - 8272 * x^13 * y^9 * z^4 - 74272 * x^13 * y^8 * z^5 - 91520 * x^13 * y^7 * z^6 - 44864 * x^13 * y^6 * z^7 + 11808 * x^13 * y^5 * z^8 + 29008 * x^13 * y^4 * z^9 + 20144 * x^13 * y^3 * z^10 + 6576 * x^13 * y^2 * z^11 - 48 * y * x^13 * z^12 + 480 * x^13 * z^13 + 180 * x^12 * y^14 + 3240 * z * x^12 * y^13 + 17076 * x^12 * y^12 * z^2 + 31584 * x^12 * y^11 * z^3 + 372 * x^12 * y^10 * z^4 - 78296 * x^12 * y^9 * z^5 - 126364 * x^12 * y^8 * z^6 - 99232 * x^12 * y^7 * z^7 - 30172 * x^12 * y^6 * z^8 + 17064 * x^12 * y^5 * z^9 + 19764 * x^12 * y^4 * z^10 + 13664 * x^12 * y^3 * z^11 + 3636 * x^12 * y^2 * z^12 - 792 * y * x^12 * z^13 + 180 * x^12 * z^14 + 40 * x^11 * y^15 + 1160 * z * x^11 * y^14 + 8696 * x^11 * y^13 * z^2 + 21752 * x^11 * y^12 * z^3 + 3800 * x^11 * y^11 * z^4 - 68008 * x^11 * y^10 * z^5 - 133272 * x^11 * y^9 * z^6 - 137208 * x^11 * y^8 * z^7 - 90104 * x^11 * y^7 * z^8 - 24216 * x^11 * y^6 * z^9 + 3928 * x^11 * y^5 * z^10 + 2776 * x^11 * y^4 * z^11 + 6776 * x^11 * y^3 * z^12 + 1976 * x^11 * y^2 * z^13 - 568 * y * x^11 * z^14 + 40 * x^11 * z^15 + 4 * x^10 * y^16 + 248 * z * x^10 * y^15 + 2928 * x^10 * y^14 * z^2 + 10200 * x^10 * y^13 * z^3 + 2056 * x^10 * y^12 * z^4 - 50552 * x^10 * y^11 * z^5 - 110992 * x^10 * y^10 * z^6 - 128792 * x^10 * y^9 * z^7 - 116824 * x^10 * y^8 * z^8 - 74408 * x^10 * y^7 * z^9 - 18384 * x^10 * y^6 * z^10 - 7176 * x^10 * y^5 * z^11 - 7096 * x^10 * y^4 * z^12 + 2344 * x^10 * y^3 * z^13 + 1008 * x^10 * y^2 * z^14 - 184 * y * x^10 * z^15 + 4 * x^10 * z^16 + 24 * z * x^9 * y^16 + 584 * x^9 * y^15 * z^2 + 3048 * x^9 * y^14 * z^3 - 328 * x^9 * y^13 * z^4 - 32152 * x^9 * y^12 * z^5 - 76776 * x^9 * y^11 * z^6 - 87176 * x^9 * y^10 * z^7 - 83832 * x^9 * y^9 * z^8 - 85128 * x^9 * y^8 * z^9 - 46680 * x^9 * y^7 * z^10 - 3256 * x^9 * y^6 * z^11 - 5544 * x^9 * y^5 * z^12 - 6904 * x^9 * y^4 * z^13 + 376 * x^9 * y^3 * z^14 + 344 * x^9 * y^2 * z^15 - 24 * y * x^9 * z^16 + 52 * x^8 * y^16 * z^2 + 504 * x^8 * y^15 * z^3 - 844 * x^8 * y^14 * z^4 - 16288 * x^8 * y^13 * z^5 - 44684 * x^8 * y^12 * z^6 - 47304 * x^8 * y^11 * z^7 - 28700 * x^8 * y^10 * z^8 - 39648 * x^8 * y^9 * z^9 - 51612 * x^8 * y^8 * z^10 - 17992 * x^8 * y^7 * z^11 + 8372 * x^8 * y^6 * z^12 + 96 * x^8 * y^5 * z^13 - 3084 * x^8 * y^4 * z^14 - 72 * x^8 * y^3 * z^15 + 52 * x^8 * y^2 * z^16 + 32 * x^7 * y^16 * z^3 - 368 * x^7 * y^15 * z^4 - 5808 * x^7 * y^14 * z^5 - 20240 * x^7 * y^13 * z^6 - 22608 * x^7 * y^12 * z^7 + 2144 * x^7 * y^11 * z^8 + 11968 * x^7 * y^10 * z^9 - 14016 * x^7 * y^9 * z^10 - 26528 * x^7 * y^8 * z^11 - 5328 * x^7 * y^7 * z^12 + 7536 * x^7 * y^6 * z^13 + 1744 * x^7 * y^5 * z^14 - 688 * x^7 * y^4 * z^15 - 32 * x^7 * y^3 * z^16 - 56 * x^6 * y^16 * z^4 - 1232 * x^6 * y^15 * z^5 - 6144 * x^6 * y^14 * z^6 - 8464 * x^6 * y^13 * z^7 + 7288 * x^6 * y^12 * z^8 + 27264 * x^6 * y^11 * z^9 + 20608 * x^6 * y^10 * z^10 - 3136 * x^6 * y^9 * z^11 - 12488 * x^6 * y^8 * z^12 - 3696 * x^6 * y^7 * z^13 + 2368 * x^6 * y^6 * z^14 + 784 * x^6 * y^5 * z^15 - 56 * x^6 * y^4 * z^16 - 112 * x^5 * y^16 * z^5 - 1008 * x^5 * y^15 * z^6 - 1712 * x^5 * y^14 * z^7 + 4880 * x^5 * y^13 * z^8 + 18880 * x^5 * y^12 * z^9 + 23424 * x^5 * y^11 * z^10 + 13248 * x^5 * y^10 * z^11 + 1024 * x^5 * y^9 * z^12 - 4304 * x^5 * y^8 * z^13 - 2320 * x^5 * y^7 * z^14 + 112 * x^5 * y^6 * z^15 + 112 * x^5 * y^5 * z^16 - 56 * x^4 * y^16 * z^6 - 16 * x^4 * y^15 * z^7 + 2268 * x^4 * y^14 * z^8 + 8872 * x^4 * y^13 * z^9 + 13724 * x^4 * y^12 * z^10 + 10576 * x^4 * y^11 * z^11 + 5084 * x^4 * y^10 * z^12 + 1768 * x^4 * y^9 * z^13 - 356 * x^4 * y^8 * z^14 - 592 * x^4 * y^7 * z^15 - 56 * x^4 * y^6 * z^16 + 32 * x^3 * y^16 * z^7 + 584 * x^3 * y^15 * z^8 + 2856 * x^3 * y^14 * z^9 + 5912 * x^3 * y^13 * z^10 + 5720 * x^3 * y^12 * z^11 + 2520 * x^3 * y^11 * z^12 + 856 * x^3 * y^10 * z^13 + 744 * x^3 * y^9 * z^14 + 264 * x^3 * y^8 * z^15 - 32 * x^3 * y^7 * z^16 + 52 * x^2 * y^16 * z^8 + 472 * x^2 * y^15 * z^9 + 1552 * x^2 * y^14 * z^10 + 2360 * x^2 * y^13 * z^11 + 1592 * x^2 * y^12 * z^12 + 200 * x^2 * y^11 * z^13 - 176 * x^2 * y^10 * z^14 + 40 * x^2 * y^9 * z^15 + 52 * x^2 * y^8 * z^16 + 24 * x * y^16 * z^9 + 168 * x * y^15 * z^10 + 456 * x * y^14 * z^11 + 600 * x * y^13 * z^12 + 360 * x * y^12 * z^13 + 24 * x * y^11 * z^14 - 72 * x * y^10 * z^15 - 24 * x * y^9 * z^16 + 4 * y^16 * z^10 + 24 * y^15 * z^11 + 60 * y^14 * z^12 + 80 * y^13 * z^13 + 60 * y^12 * z^14 + 24 * y^11 * z^15 + 4 * y^10 * z^16

/-- Coefficients of the eliminated polynomial `A₀` in `u = q^2`. -/
def polyC1 (x y z : ℝ) : ℝ := - 4 * x^18 * y^4 * z^2 - 32 * x^18 * y^3 * z^3 - 40 * x^18 * y^2 * z^4 + 12 * x^18 * z^6 - 56 * x^17 * y^5 * z^2 - 320 * x^17 * y^4 * z^3 - 528 * x^17 * y^3 * z^4 - 288 * x^17 * y^2 * z^5 + 72 * y * x^17 * z^6 + 96 * x^17 * z^7 - 308 * x^16 * y^6 * z^2 - 1552 * x^16 * y^5 * z^3 - 3080 * x^16 * y^4 * z^4 - 2800 * x^16 * y^3 * z^5 - 692 * x^16 * y^2 * z^6 + 480 * y * x^16 * z^7 + 336 * x^16 * z^8 - 928 * x^15 * y^7 * z^2 - 4784 * x^15 * y^6 * z^3 - 10848 * x^15 * y^5 * z^4 - 12960 * x^15 * y^4 * z^5 - 7296 * x^15 * y^3 * z^6 - 400 * x^15 * y^2 * z^7 + 1344 * y * x^15 * z^8 + 672 * x^15 * z^9 - 1736 * x^14 * y^8 * z^2 - 10240 * x^14 * y^7 * z^3 - 26256 * x^14 * y^6 * z^4 - 37952 * x^14 * y^5 * z^5 - 31008 * x^14 * y^4 * z^6 - 10656 * x^14 * y^3 * z^7 + 1008 * x^14 * y^2 * z^8 + 2016 * y * x^14 * z^9 + 840 * x^14 * z^10 - 2128 * x^13 * y^9 * z^2 - 15680 * x^13 * y^8 * z^3 - 46560 * x^13 * y^7 * z^4 - 78704 * x^13 * y^6 * z^5 - 82144 * x^13 * y^5 * z^6 - 47008 * x^13 * y^4 * z^7 - 8768 * x^13 * y^3 * z^8 + 1904 * x^13 * y^2 * z^9 + 1680 * y * x^13 * z^10 + 672 * x^13 * z^11 - 1736 * x^12 * y^10 * z^2 - 17248 * x^12 * y^9 * z^3 - 62160 * x^12 * y^8 * z^4 - 122336 * x^12 * y^7 * z^5 - 154000 * x^12 * y^6 * z^6 - 121696 * x^12 * y^5 * z^7 - 47008 * x^12 * y^4 * z^8 - 3072 * x^12 * y^3 * z^9 + 952 * x^12 * y^2 * z^10 + 672 * y * x^12 * z^11 + 336 * x^12 * z^12 - 928 * x^11 * y^11 * z^2 - 13472 * x^11 * y^10 * z^3 - 62592 * x^11 * y^9 * z^4 - 146496 * x^11 * y^8 * z^5 - 216224 * x^11 * y^7 * z^6 - 216048 * x^11 * y^6 * z^7 - 129312 * x^11 * y^5 * z^8 - 30240 * x^11 * y^4 * z^9 + 1440 * x^11 * y^3 * z^10 - 432 * x^11 * y^2 * z^11 + 96 * x^11 * z^13 - 308 * x^10 * y^12 * z^2 - 7264 * x^10 * y^11 * z^3 - 46728 * x^10 * y^10 * z^4 - 135808 * x^10 * y^9 * z^5 - 234068 * x^10 * y^8 * z^6 - 278464 * x^10 * y^7 * z^7 - 225536 * x^10 * y^6 * z^8 - 99200 * x^10 * y^5 * z^9 - 10516 * x^10 * y^4 * z^10 + 2624 * x^10 * y^3 * z^11 - 680 * x^10 * y^2 * z^12 - 96 * y * x^10 * z^13 + 12 * x^10 * z^14 - 56 * x^9 * y^13 * z^2 - 2560 * x^9 * y^12 * z^3 - 24976 * x^9 * y^11 * z^4 - 95872 * x^9 * y^10 * z^5 - 197528 * x^9 * y^9 * z^6 - 269792 * x^9 * y^8 * z^7 - 266624 * x^9 * y^7 * z^8 - 172976 * x^9 * y^6 * z^9 - 53784 * x^9 * y^5 * z^10 - 32 * x^9 * y^4 * z^11 + 1744 * x^9 * y^3 * z^12 - 272 * x^9 * y^2 * z^13 - 24 * y * x^9 * z^14 - 4 * x^8 * y^14 * z^2 - 528 * x^8 * y^13 * z^3 - 9000 * x^8 * y^12 * z^4 - 49584 * x^8 * y^11 * z^5 - 128596 * x^8 * y^10 * z^6 - 201312 * x^8 * y^9 * z^7 - 225136 * x^8 * y^8 * z^8 - 182784 * x^8 * y^7 * z^9 - 92660 * x^8 * y^6 * z^10 - 20112 * x^8 * y^5 * z^11 + 1480 * x^8 * y^4 * z^12 + 624 * x^8 * y^3 * z^13 - 36 * x^8 * y^2 * z^14 - 48 * x^7 * y^14 * z^3 - 1952 * x^7 * y^13 * z^4 - 17568 * x^7 * y^12 * z^5 - 62112 * x^7 * y^11 * z^6 - 115952 * x^7 * y^10 * z^7 - 142336 * x^7 * y^9 * z^8 - 128544 * x^7 * y^8 * z^9 - 81696 * x^7 * y^7 * z^10 - 31904 * x^7 * y^6 * z^11 - 5312 * x^7 * y^5 * z^12 + 448 * x^7 * y^4 * z^13 + 96 * x^7 * y^3 * z^14 - 192 * x^6 * y^14 * z^4 - 3776 * x^6 * y^13 * z^5 - 20632 * x^6 * y^12 * z^6 - 49568 * x^6 * y^11 * z^7 - 68368 * x^6 * y^10 * z^8 - 65312 * x^6 * y^9 * z^9 - 43808 * x^6 * y^8 * z^10 - 19264 * x^6 * y^7 * z^11 - 6096 * x^6 * y^6 * z^12 - 1088 * x^6 * y^5 * z^13 + 24 * x^6 * y^4 * z^14 - 368 * x^5 * y^14 * z^5 - 4112 * x^5 * y^13 * z^6 - 14304 * x^5 * y^12 * z^7 - 23360 * x^5 * y^11 * z^8 - 23792 * x^5 * y^10 * z^9 - 16832 * x^5 * y^9 * z^10 - 5856 * x^5 * y^8 * z^11 - 416 * x^5 * y^7 * z^12 - 416 * x^5 * y^6 * z^13 - 144 * x^5 * y^5 * z^14 - 360 * x^4 * y^14 * z^6 - 2336 * x^4 * y^13 * z^7 - 4672 * x^4 * y^12 * z^8 - 4352 * x^4 * y^11 * z^9 - 3536 * x^4 * y^10 * z^10 - 1984 * x^4 * y^9 * z^11 + 672 * x^4 * y^8 * z^12 + 736 * x^4 * y^7 * z^13 + 24 * x^4 * y^6 * z^14 - 144 * x^3 * y^14 * z^7 - 288 * x^3 * y^13 * z^8 + 672 * x^3 * y^12 * z^9 + 1472 * x^3 * y^11 * z^10 + 208 * x^3 * y^10 * z^11 - 448 * x^3 * y^9 * z^12 + 96 * x^3 * y^8 * z^13 + 96 * x^3 * y^7 * z^14 + 32 * x^2 * y^14 * z^8 + 448 * x^2 * y^13 * z^9 + 1260 * x^2 * y^12 * z^10 + 1152 * x^2 * y^11 * z^11 + 120 * x^2 * y^10 * z^12 - 224 * x^2 * y^9 * z^13 - 36 * x^2 * y^8 * z^14 + 48 * x * y^14 * z^9 + 264 * x * y^13 * z^10 + 480 * x * y^12 * z^11 + 336 * x * y^11 * z^12 + 48 * x * y^10 * z^13 - 24 * x * y^9 * z^14 + 12 * y^14 * z^10 + 48 * y^13 * z^11 + 72 * y^12 * z^12 + 48 * y^11 * z^13 + 12 * y^10 * z^14

/-- Coefficients of the eliminated polynomial `A₀` in `u = q^2`. -/
def polyC2 (x y z : ℝ) : ℝ := - 4 * x^16 * y^2 * z^4 - 8 * y * x^16 * z^5 + 12 * x^16 * z^6 - 8 * x^15 * y^3 * z^4 - 56 * x^15 * y^2 * z^5 + 24 * y * x^15 * z^6 + 72 * x^15 * z^7 + 76 * x^14 * y^4 * z^4 - 40 * x^14 * y^3 * z^5 - 96 * x^14 * y^2 * z^6 + 264 * y * x^14 * z^7 + 180 * x^14 * z^8 + 416 * x^13 * y^5 * z^4 + 712 * x^13 * y^4 * z^5 + 8 * x^13 * y^3 * z^6 + 152 * x^13 * y^2 * z^7 + 680 * y * x^13 * z^8 + 240 * x^13 * z^9 + 952 * x^12 * y^6 * z^4 + 3056 * x^12 * y^5 * z^5 + 2396 * x^12 * y^4 * z^6 + 136 * x^12 * y^3 * z^7 + 552 * x^12 * y^2 * z^8 + 840 * y * x^12 * z^9 + 180 * x^12 * z^10 + 1232 * x^11 * y^7 * z^4 + 6160 * x^11 * y^6 * z^5 + 8944 * x^11 * y^5 * z^6 + 3840 * x^11 * y^4 * z^7 - 152 * x^11 * y^3 * z^8 + 504 * x^11 * y^2 * z^9 + 552 * y * x^11 * z^10 + 72 * x^11 * z^11 + 952 * x^10 * y^8 * z^4 + 7280 * x^10 * y^7 * z^5 + 16352 * x^10 * y^6 * z^6 + 13648 * x^10 * y^5 * z^7 + 3004 * x^10 * y^4 * z^8 - 856 * x^10 * y^3 * z^9 + 96 * x^10 * y^2 * z^10 + 184 * y * x^10 * z^11 + 12 * x^10 * z^12 + 416 * x^9 * y^9 * z^4 + 5200 * x^9 * y^8 * z^5 + 17680 * x^9 * y^7 * z^6 + 22960 * x^9 * y^6 * z^7 + 11856 * x^9 * y^5 * z^8 + 872 * x^9 * y^4 * z^9 - 1032 * x^9 * y^3 * z^10 - 88 * x^9 * y^2 * z^11 + 24 * y * x^9 * z^12 + 76 * x^8 * y^10 * z^4 + 2072 * x^8 * y^9 * z^5 + 11588 * x^8 * y^8 * z^6 + 22416 * x^8 * y^7 * z^7 + 18224 * x^8 * y^6 * z^8 + 6160 * x^8 * y^5 * z^9 - 124 * x^8 * y^4 * z^10 - 520 * x^8 * y^3 * z^11 - 36 * x^8 * y^2 * z^12 - 8 * x^7 * y^11 * z^4 + 296 * x^7 * y^10 * z^5 + 4216 * x^7 * y^9 * z^6 + 13256 * x^7 * y^8 * z^7 + 15248 * x^7 * y^7 * z^8 + 8048 * x^7 * y^6 * z^9 + 2192 * x^7 * y^5 * z^10 - 48 * x^7 * y^4 * z^11 - 96 * x^7 * y^3 * z^12 - 4 * x^6 * y^12 * z^4 - 72 * x^6 * y^11 * z^5 + 512 * x^6 * y^10 * z^6 + 4520 * x^6 * y^9 * z^7 + 7788 * x^6 * y^8 * z^8 + 4624 * x^6 * y^7 * z^9 + 1824 * x^6 * y^6 * z^10 + 688 * x^6 * y^5 * z^11 + 24 * x^6 * y^4 * z^12 - 24 * x^5 * y^12 * z^5 - 152 * x^5 * y^11 * z^6 + 696 * x^5 * y^10 * z^7 + 2824 * x^5 * y^9 * z^8 + 1664 * x^5 * y^8 * z^9 - 272 * x^5 * y^7 * z^10 + 208 * x^5 * y^6 * z^11 + 144 * x^5 * y^5 * z^12 - 44 * x^4 * y^12 * z^6 - 24 * x^4 * y^11 * z^7 + 936 * x^4 * y^10 * z^8 + 1192 * x^4 * y^9 * z^9 - 452 * x^4 * y^8 * z^10 - 528 * x^4 * y^7 * z^11 + 24 * x^4 * y^6 * z^12 - 16 * x^3 * y^12 * z^7 + 264 * x^3 * y^11 * z^8 + 920 * x^3 * y^10 * z^9 + 456 * x^3 * y^9 * z^10 - 280 * x^3 * y^8 * z^11 - 96 * x^3 * y^7 * z^12 + 36 * x^2 * y^12 * z^8 + 328 * x^2 * y^11 * z^9 + 512 * x^2 * y^10 * z^10 + 152 * x^2 * y^9 * z^11 - 36 * x^2 * y^8 * z^12 + 40 * x * y^12 * z^9 + 152 * x * y^11 * z^10 + 136 * x * y^10 * z^11 + 24 * x * y^9 * z^12 + 12 * y^12 * z^10 + 24 * y^11 * z^11 + 12 * y^10 * z^12

/-- Coefficients of the eliminated polynomial `A₀` in `u = q^2`. -/
def polyC3 (x y z : ℝ) : ℝ := 4 * x^14 * z^6 + 24 * y * x^13 * z^6 + 16 * x^13 * z^7 + 52 * x^12 * y^2 * z^6 + 96 * y * x^12 * z^7 + 24 * x^12 * z^8 + 32 * x^11 * y^3 * z^6 + 208 * x^11 * y^2 * z^7 + 144 * y * x^11 * z^8 + 16 * x^11 * z^9 - 56 * x^10 * y^4 * z^6 + 128 * x^10 * y^3 * z^7 + 312 * x^10 * y^2 * z^8 + 96 * y * x^10 * z^9 + 4 * x^10 * z^10 - 112 * x^9 * y^5 * z^6 - 224 * x^9 * y^4 * z^7 + 192 * x^9 * y^3 * z^8 + 208 * x^9 * y^2 * z^9 + 24 * y * x^9 * z^10 - 56 * x^8 * y^6 * z^6 - 448 * x^8 * y^5 * z^7 - 336 * x^8 * y^4 * z^8 + 128 * x^8 * y^3 * z^9 + 52 * x^8 * y^2 * z^10 + 32 * x^7 * y^7 * z^6 - 224 * x^7 * y^6 * z^7 - 672 * x^7 * y^5 * z^8 - 224 * x^7 * y^4 * z^9 + 32 * x^7 * y^3 * z^10 + 52 * x^6 * y^8 * z^6 + 128 * x^6 * y^7 * z^7 - 336 * x^6 * y^6 * z^8 - 448 * x^6 * y^5 * z^9 - 56 * x^6 * y^4 * z^10 + 24 * x^5 * y^9 * z^6 + 208 * x^5 * y^8 * z^7 + 192 * x^5 * y^7 * z^8 - 224 * x^5 * y^6 * z^9 - 112 * x^5 * y^5 * z^10 + 4 * x^4 * y^10 * z^6 + 96 * x^4 * y^9 * z^7 + 312 * x^4 * y^8 * z^8 + 128 * x^4 * y^7 * z^9 - 56 * x^4 * y^6 * z^10 + 16 * x^3 * y^10 * z^7 + 144 * x^3 * y^9 * z^8 + 208 * x^3 * y^8 * z^9 + 32 * x^3 * y^7 * z^10 + 24 * x^2 * y^10 * z^8 + 96 * x^2 * y^9 * z^9 + 52 * x^2 * y^8 * z^10 + 16 * x * y^10 * z^9 + 24 * x * y^9 * z^10 + 4 * y^10 * z^10

/-- The eliminated condition `A₀` with the circumcircle condition
reduced to a polynomial in `x, y, z, q^2`. -/
def polyA0 (x y z q : ℝ) : ℝ :=
  polyC0 x y z + polyC1 x y z * q^2 + polyC2 x y z * (q^2)^2 + polyC3 x y z * (q^2)^3

/- The big elimination identity `T = q * A₀` (lemma `coreC`) used to be
checked by a single `ring` call on the fully expanded polynomials, which
needed an excessive amount of memory (the squares `polyM1²` expand to tens
of thousands of monomials).  To keep every `ring` call small we split
`polyM0` and `polyM1` by powers of `q` as `Mᵢ = q²·Mᵢₐ + Mᵢ_b`, and verify
the four coefficients of `q²` in `A₀` independently (`polyC0_eq` …
`polyC3_eq`).  All of these identities were produced by the same computer
algebra elimination and are merely *verified* here. -/

/-- The `q²`-part of `polyM0`; it factors as `z²(x+y)²(x-y)`. -/
def polyM0a (x y z : ℝ) : ℝ := z^2 * (x + y)^2 * (x - y)

/-- The `q⁰`-part of `polyM0`. -/
def polyM0b (x y z : ℝ) : ℝ := x^5 * y^2 + 2 * y * z * x^5 + x^5 * z^2 + 5 * x^4 * y^3 + 8 * z * x^4 * y^2 + 5 * y * x^4 * z^2 + 2 * x^4 * z^3 + 7 * x^3 * y^4 + 12 * z * x^3 * y^3 + 8 * x^3 * y^2 * z^2 + x^3 * z^4 + 3 * x^2 * y^5 + 8 * z * x^2 * y^4 + 4 * x^2 * y^3 * z^2 - 3 * y * x^2 * z^4 + 2 * x * z * y^5 - x * y^4 * z^2 + 3 * x * y^2 * z^4 - y^5 * z^2 - 2 * y^4 * z^3 - y^3 * z^4

/-- The `q²`-part of `polyM1`. -/
def polyM1a (x y z : ℝ) : ℝ := y * x^5 * z^2 - x^5 * z^3 + 4 * x^4 * y^2 * z^2 + y * x^4 * z^3 - x^4 * z^4 + 6 * x^3 * y^3 * z^2 + 8 * x^3 * y^2 * z^3 + 4 * x^2 * y^4 * z^2 + 8 * x^2 * y^3 * z^3 + 2 * x^2 * y^2 * z^4 + x * y^5 * z^2 + x * y^4 * z^3 - y^5 * z^3 - y^4 * z^4

/-- The `q⁰`-part of `polyM1`. -/
def polyM1b (x y z : ℝ) : ℝ := x^7 * y^3 + z * x^7 * y^2 - y * x^7 * z^2 - x^7 * z^3 + 4 * x^6 * y^4 + 3 * z * x^6 * y^3 - x^6 * y^2 * z^2 - 3 * y * x^6 * z^3 - 3 * x^6 * z^4 + 6 * x^5 * y^5 + 4 * z * x^5 * y^4 + x^5 * y^3 * z^2 - x^5 * y^2 * z^3 + y * x^5 * z^4 - 3 * x^5 * z^5 + 4 * x^4 * y^6 + 4 * z * x^4 * y^5 + 2 * x^4 * y^4 * z^2 + 5 * x^4 * y^3 * z^3 + 3 * x^4 * y^2 * z^4 + 7 * y * x^4 * z^5 - x^4 * z^6 + x^3 * y^7 + 3 * z * x^3 * y^6 + x^3 * y^5 * z^2 + 5 * x^3 * y^4 * z^3 - 2 * x^3 * y^3 * z^4 - 4 * x^3 * y^2 * z^5 + 4 * y * x^3 * z^6 + z * x^2 * y^7 - x^2 * y^6 * z^2 - x^2 * y^5 * z^3 + 3 * x^2 * y^4 * z^4 - 4 * x^2 * y^3 * z^5 - 6 * x^2 * y^2 * z^6 - x * y^7 * z^2 - 3 * x * y^6 * z^3 + x * y^5 * z^4 + 7 * x * y^4 * z^5 + 4 * x * y^3 * z^6 - y^7 * z^3 - 3 * y^6 * z^4 - 3 * y^5 * z^5 - y^4 * z^6

/-- Split of `polyM0` by powers of `q`. -/
lemma polyM0_split (x y z q : ℝ) :
    polyM0 x y z q = q^2 * polyM0a x y z + polyM0b x y z := by
  simp only [polyM0, polyM0a, polyM0b]
  ring

/-- Split of `polyM1` by powers of `q`. -/
lemma polyM1_split (x y z q : ℝ) :
    polyM1 x y z q = q^2 * polyM1a x y z + polyM1b x y z := by
  simp only [polyM1, polyM1a, polyM1b]
  ring

/-- The `(q²)³`-coefficient of `polyA0`, as a small product. -/
lemma polyC3_eq (x y z : ℝ) :
    polyC3 x y z = 4 * z^2 * (x + y)^4 * (x + z)^4 * (polyM0a x y z)^2 := by
  simp only [polyC3, polyM0a]
  ring

/-- The `(q²)²`-coefficient of `polyA0`, as a small product. -/
lemma polyC2_eq (x y z : ℝ) :
    polyC2 x y z
      = 8 * z^2 * (x + y)^4 * (x + z)^4 * polyM0a x y z * polyM0b x y z
        - 16 * x * y * z^2 * (x + y)^7 * (x + z)^5 * (y + z) * polyM0a x y z
        + 4 * (x + y)^2 * (x + z)^4 * (polyM1a x y z)^2 := by
  simp only [polyC2, polyM0a, polyM0b, polyM1a]
  ring

/-- The `q²`-coefficient of `polyA0`, as a small product. -/
lemma polyC1_eq (x y z : ℝ) :
    polyC1 x y z
      = 4 * z^2 * (x + y)^4 * (x + z)^4 * (polyM0b x y z)^2
        - 16 * x * y * z^2 * (x + y)^7 * (x + z)^5 * (y + z) * polyM0b x y z
        + 8 * (x + y)^2 * (x + z)^4 * polyM1a x y z * polyM1b x y z
        - 16 * x * y * z * (x + y)^5 * (x + z)^5 * (y + z)
          * (z * (x + y + z) - x * y) * polyM1a x y z := by
  simp only [polyC1, polyM0b, polyM1a, polyM1b]
  ring

/-- The `(q²)⁰`-coefficient of `polyA0`, as a small product. -/
lemma polyC0_eq (x y z : ℝ) :
    polyC0 x y z
      = 4 * (x + y)^2 * (x + z)^4 * (polyM1b x y z)^2
        - 16 * x * y * z * (x + y)^5 * (x + z)^5 * (y + z)
          * (z * (x + y + z) - x * y) * polyM1b x y z := by
  simp only [polyC0, polyM1b]
  ring

/-- First elimination step: Cramer's rule on the equidistance equations. -/
lemma coreA
    (x y z q w0 w1 : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq1 : (w0 - (x + y + z) * (x * y + x * z + y^2 - y * z) / ((x + y) * (y + z)))^2
        + (w1 - q * z / (y + z))^2
      = (w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
        + (w1 - q * z / (x + z))^2)
    (heq2 : (w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
        + (w1 - q * z / (x + z))^2
      = (w0 - y)^2 + w1^2) :
    polyDD x y z q * w0 = polyN0 x y z q
      ∧ polyDD x y z q * w1 = polyN1 x y z q := by
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hyz : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have hzx : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  have heq1' : ((x + y) * (y + z) * (x + z))^2
        * ((w0 - (x + y + z) * (x * y + x * z + y^2 - y * z) / ((x + y) * (y + z)))^2
          + (w1 - q * z / (y + z))^2)
      = ((x + y) * (y + z) * (x + z))^2
        * ((w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
          + (w1 - q * z / (x + z))^2) := by
    rw [heq1]
  have heq2' : ((x + y) * (x + z))^2
        * ((w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
          + (w1 - q * z / (x + z))^2)
      = ((x + y) * (x + z))^2 * ((w0 - y)^2 + w1^2) := by
    rw [heq2]
  have eq1c : polyA1 x y z q * w0 + polyB1 x y z q * w1 = polyE1 x y z q := by
    simp only [polyA1, polyB1, polyE1]
    field_simp [hxy, hyz, hzx] at heq1'
    linear_combination heq1'
  have eq2c : polyA2 x y z q * w0 + polyB2 x y z q * w1 = polyE2 x y z q := by
    simp only [polyA2, polyB2, polyE2]
    field_simp [hxy, hzx] at heq2'
    linear_combination heq2'
  have hdd_eq : polyDD x y z q
      = polyA1 x y z q * polyB2 x y z q - polyA2 x y z q * polyB1 x y z q := by
    simp only [polyDD, polyA1, polyB1, polyA2, polyB2]
    ring
  have hN0_eq : polyN0 x y z q
      = polyE1 x y z q * polyB2 x y z q - polyE2 x y z q * polyB1 x y z q := by
    simp only [polyN0, polyM0, polyE1, polyB1, polyE2, polyB2]
    ring
  have hN1_eq : polyN1 x y z q
      = polyA1 x y z q * polyE2 x y z q - polyA2 x y z q * polyE1 x y z q := by
    simp only [polyN1, polyM1, polyA1, polyE1, polyA2, polyE2]
    ring
  have hcr0 : (polyA1 x y z q * polyB2 x y z q - polyA2 x y z q * polyB1 x y z q) * w0
      = polyE1 x y z q * polyB2 x y z q - polyE2 x y z q * polyB1 x y z q := by
    linear_combination polyB2 x y z q * eq1c - polyB1 x y z q * eq2c
  have hcr1 : (polyA1 x y z q * polyB2 x y z q - polyA2 x y z q * polyB1 x y z q) * w1
      = polyA1 x y z q * polyE2 x y z q - polyA2 x y z q * polyE1 x y z q := by
    linear_combination (-polyA2 x y z q) * eq1c + polyA1 x y z q * eq2c
  constructor
  · rw [hdd_eq, hN0_eq]
    exact hcr0
  · rw [hdd_eq, hN1_eq]
    exact hcr1

/-- Second elimination step: substitute into the circumcircle condition. -/
lemma coreB
    (x y z q w0 w1 o0 o1 : ℝ)
    (hO0 : 2 * o0 = x + y)
    (hO1 : 2 * q * o1 = z * (x + y + z) - x * y)
    (hcond : w0^2 - 2 * w0 * o0 + w1^2 - 2 * w1 * o1 = 0)
    (hcr : polyDD x y z q * w0 = polyN0 x y z q
      ∧ polyDD x y z q * w1 = polyN1 x y z q) :
    q * (polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
        + polyN1 x y z q^2)
      - polyN1 x y z q * polyDD x y z q * (z * (x + y + z) - x * y) = 0 := by
  obtain ⟨cramer0, cramer1⟩ := hcr
  have hT1 : polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
      + polyN1 x y z q^2
      = polyDD x y z q^2 * (w0^2 - (x + y) * w0 + w1^2) := by
    linear_combination
      (-(polyDD x y z q * w0 + polyN0 x y z q - (x + y) * polyDD x y z q)) * cramer0
      + (-(polyDD x y z q * w1 + polyN1 x y z q)) * cramer1
  rw [hT1]
  linear_combination (q * polyDD x y z q^2) * hcond
    + (q * polyDD x y z q^2 * w0) * hO0
    + (polyDD x y z q^2 * w1) * hO1
    + (polyDD x y z q * (z * (x + y + z) - x * y)) * cramer1

/-- Final elimination step: the result is `q` times a polynomial in `q^2`,
which yields the right-angle factorization. -/
lemma coreC
    (x y z q : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hq : q ≠ 0)
    (hQ : q^2 * (x + y)^2 = 4 * x * y * z * (x + y + z))
    (hT : q * (polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
        + polyN1 x y z q^2)
      - polyN1 x y z q * polyDD x y z q * (z * (x + y + z) - x * y) = 0) :
    (x * (x + y + z) - y * z) * (y * (x + y + z) - x * z)
      * (z * (x + y + z) - x * y) = 0 := by
  -- With `N₀ = 2qz(x+y)²(x+z)²·M₀`, `N₁ = 2(x+y)(x+z)²·M₁` and
  -- `D = 8qxyz(x+y)⁴(x+z)³(y+z)`, the left side of `hT` factors as `q` times
  -- a polynomial in `q²`.  This `ring` is small: `polyM0`/`polyM1` stay folded.
  have hT1 : q * (polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
        + polyN1 x y z q^2)
      - polyN1 x y z q * polyDD x y z q * (z * (x + y + z) - x * y)
      = q * (4 * z^2 * (x + y)^4 * (x + z)^4 * q^2 * (polyM0 x y z q)^2
        - 16 * x * y * z^2 * (x + y)^7 * (x + z)^5 * (y + z) * q^2 * polyM0 x y z q
        + 4 * (x + y)^2 * (x + z)^4 * (polyM1 x y z q)^2
        - 16 * x * y * z * (x + y)^5 * (x + z)^5 * (y + z) * (z * (x + y + z) - x * y)
          * polyM1 x y z q) := by
    simp only [polyN0, polyN1, polyDD]
    ring
  -- Collecting by powers of `q²` gives `polyA0`: the coefficients are exactly
  -- the small products of `polyC0_eq` … `polyC3_eq`.  With the splits
  -- `Mᵢ = q²·Mᵢₐ + Mᵢ_b` this `ring` only handles folded atoms, so it is small.
  have hT2 : 4 * z^2 * (x + y)^4 * (x + z)^4 * q^2 * (polyM0 x y z q)^2
      - 16 * x * y * z^2 * (x + y)^7 * (x + z)^5 * (y + z) * q^2 * polyM0 x y z q
      + 4 * (x + y)^2 * (x + z)^4 * (polyM1 x y z q)^2
      - 16 * x * y * z * (x + y)^5 * (x + z)^5 * (y + z) * (z * (x + y + z) - x * y)
        * polyM1 x y z q
      = polyA0 x y z q := by
    rw [polyM0_split, polyM1_split]
    simp only [polyA0, polyC0_eq, polyC1_eq, polyC2_eq, polyC3_eq]
    ring
  have hTform : q * (polyN0 x y z q^2 - (x + y) * polyN0 x y z q * polyDD x y z q
        + polyN1 x y z q^2)
      - polyN1 x y z q * polyDD x y z q * (z * (x + y + z) - x * y)
      = q * polyA0 x y z q := by
    rw [hT1, hT2]
  have hA0 : polyA0 x y z q = 0 := by
    rw [hTform] at hT
    rcases mul_eq_zero.mp hT with hq0 | hA0
    · exact absurd hq0 hq
    · exact hA0
  have hstep : (x + y)^6 * polyA0 x y z q
      = polyC0 x y z * (x + y)^6 + polyC1 x y z * (q^2 * (x + y)^2) * (x + y)^4
        + polyC2 x y z * (q^2 * (x + y)^2)^2 * (x + y)^2
        + polyC3 x y z * (q^2 * (x + y)^2)^3 := by
    simp only [polyA0]
    ring
  rw [hQ] at hstep
  rw [hA0, mul_zero] at hstep
  -- The eliminated condition: the `polyC`-part plus the factored big term
  -- vanishes.  This is the one remaining sizable `ring` of the proof.
  have hfin : polyC0 x y z * (x + y)^6
      + polyC1 x y z * (4 * x * y * z * (x + y + z)) * (x + y)^4
      + polyC2 x y z * (4 * x * y * z * (x + y + z))^2 * (x + y)^2
      + polyC3 x y z * (4 * x * y * z * (x + y + z))^3
      + 4 * (x + y)^13 * (x + z)^7 * (y + z)^3
        * ((x * (x + y + z) - y * z) * (y * (x + y + z) - x * z)
          * (z * (x + y + z) - x * y))
        * ((x + y) * (x * y + z^2) + z * (x - y)^2) = 0 := by
    simp only [polyC0, polyC1, polyC2, polyC3]
    ring
  -- `hfin` contains `hstep`'s (vanishing) right side as a subterm; rewriting
  -- with it leaves only `big · K · SOS = 0` — no further normalization needed.
  rw [← hstep, zero_add] at hfin
  have hposP : 0 < 4 * (x + y)^13 * (x + z)^7 * (y + z)^3 := by positivity
  have hposS : 0 < (x + y) * (x * y + z^2) + z * (x - y)^2 := by positivity
  rcases mul_eq_zero.mp hfin with hPK | hS
  · rcases mul_eq_zero.mp hPK with hP | hprod
    · exact absurd hP (ne_of_gt hposP)
    · exact hprod
  · exact absurd hS (ne_of_gt hposS)

theorem core
    (x y z q w0 w1 o0 o1 : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hq : q ≠ 0)
    (hQ : q^2 * (x + y)^2 = 4 * x * y * z * (x + y + z))
    (hO0 : 2 * o0 = x + y)
    (hO1 : 2 * q * o1 = z * (x + y + z) - x * y)
    (hcond : w0^2 - 2 * w0 * o0 + w1^2 - 2 * w1 * o1 = 0)
    (heq1 : (w0 - (x + y + z) * (x * y + x * z + y^2 - y * z) / ((x + y) * (y + z)))^2
        + (w1 - q * z / (y + z))^2
      = (w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
        + (w1 - q * z / (x + z))^2)
    (heq2 : (w0 - z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)))^2
        + (w1 - q * z / (x + z))^2
      = (w0 - y)^2 + w1^2) :
    (x * (x + y + z) - y * z) * (y * (x + y + z) - x * z)
      * (z * (x + y + z) - x * y) = 0 := by
  have hcr := coreA x y z q w0 w1 hx hy hz heq1 heq2
  have hT := coreB x y z q w0 w1 o0 o1 hO0 hO1 hcond hcr
  exact coreC x y z q hx hy hz hq hQ hT

snip end

problem imo2013_p3
    (A B C A1 B1 C1 : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hA1 : A1 = AffineMap.lineMap B C
      (((dist B C + dist C A + dist A B) / 2 - dist A B) / dist B C))
    (hB1 : B1 = AffineMap.lineMap C A
      (((dist B C + dist C A + dist A B) / 2 - dist B C) / dist C A))
    (hC1 : C1 = AffineMap.lineMap A B
      (((dist B C + dist C A + dist A B) / 2 - dist C A) / dist A B))
    (hW : ∃ W, dist W A1 = dist W B1 ∧ dist W B1 = dist W C1 ∧
      dist W (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ _).circumcenter
        = (⟨![A, B, C], hABC⟩ : Affine.Triangle ℝ _).circumradius) :
    ∠ C A B = Real.pi / 2 ∨ ∠ A B C = Real.pi / 2 ∨ ∠ B C A = Real.pi / 2 := by
  -- side lengths
  set a := dist B C with ha_def
  set b := dist C A with hb_def
  set c := dist A B with hc_def
  have hAneB : A ≠ B := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hBneC : B ≠ C := hABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have hAneC : A ≠ C := hABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have ha : 0 < a := dist_pos.mpr hBneC
  have hb : 0 < b := dist_pos.mpr hAneC.symm
  have hc : 0 < c := dist_pos.mpr hAneB
  -- Ravi substitution x = s - a, y = s - b, z = s - c
  set x := (b + c - a) / 2 with hx_def
  set y := (a + c - b) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def
  have hyz_a : y + z = a := by rw [hy_def, hz_def]; ring
  have hzx_b : z + x = b := by rw [hz_def, hx_def]; ring
  have hxy_c : x + y = c := by rw [hx_def, hy_def]; ring
  -- strict triangle inequalities from non-collinearity
  have hncol := affineIndependent_iff_not_collinear.mp hABC
  -- Note: feeding `not_wbtw_of_injective` directly into `dist_lt_dist_add_dist_iff.mpr`
  -- sends unification into a `WithLp.equiv` unfold loop (the `![A, B, C] i =?= B`
  -- defeqs).  Reduce the matrix applications with `simp only` first instead.
  have hinj102 : Function.Injective (![1, 0, 2] : Fin 3 → Fin 3) := by decide
  have hinj210 : Function.Injective (![2, 1, 0] : Fin 3 → Fin 3) := by decide
  have hinj021 : Function.Injective (![0, 2, 1] : Fin 3 → Fin 3) := by decide
  have hnbac := AffineIndependent.not_wbtw_of_injective 1 0 2 hinj102 hABC
  have hncba := AffineIndependent.not_wbtw_of_injective 2 1 0 hinj210 hABC
  have hnacb := AffineIndependent.not_wbtw_of_injective 0 2 1 hinj021 hABC
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    at hnbac hncba hnacb
  have htr1 : dist B C < dist B A + dist A C := dist_lt_dist_add_dist_iff.mpr hnbac
  have htr2 : dist C A < dist C B + dist B A := dist_lt_dist_add_dist_iff.mpr hncba
  have htr3 : dist A B < dist A C + dist C B := dist_lt_dist_add_dist_iff.mpr hnacb
  rw [dist_comm B A, dist_comm A C] at htr1
  rw [dist_comm C B, dist_comm B A] at htr2
  rw [dist_comm A C, dist_comm C B] at htr3
  have hx : 0 < x := by rw [hx_def]; linarith
  have hy : 0 < y := by rw [hy_def]; linarith
  have hz : 0 < z := by rw [hz_def]; linarith
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hyz : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have hzx : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  -- orthonormal basis along AB
  set e1 : EuclideanSpace ℝ (Fin 2) := c⁻¹ • (B - A) with he1
  set e2 : EuclideanSpace ℝ (Fin 2) := !₂[-(e1 1), e1 0] with he2
  have hnorm_e1 : ⟪e1, e1⟫ = 1 := by
    rw [he1, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm B A, ← hc_def]
    field_simp [hc.ne']
  have he1sq : e1 0^2 + e1 1^2 = 1 := by
    have h := hnorm_e1
    rw [inner_fin2] at h
    linear_combination h
  -- coordinates of C
  set p := ⟪C - A, e1⟫ with hp_def
  set q := ⟪C - A, e2⟫ with hq_def
  have hq_ne : q ≠ 0 := by
    intro hq0
    have hrepr := onb_repr he2 he1sq (C - A)
    rw [← hp_def, ← hq_def, hq0, zero_smul, add_zero, he1, smul_smul] at hrepr
    -- C - A = (p * c⁻¹) • (B - A), so A, B, C are collinear
    have hcoll : Collinear ℝ (Set.range ![A, B, C]) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨A, B - A, ?_⟩
      intro P hP
      rcases hP with ⟨i, rfl⟩
      rcases fin3_cases i with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp [vadd_eq_add]⟩
      · exact ⟨p * c⁻¹, by rw [vadd_eq_add, ← hrepr]; simp⟩
    exact hncol hcoll
  have hTA : TOf A e1 e2 A = 0 := by
    ext i
    rcases fin2_cases i with rfl | rfl <;> simp [TOf]
  have hce1 : c • e1 = B - A := by
    rw [he1]
    exact smul_inv_smul₀ hc.ne' _
  have hTB : TOf A e1 e2 B = !₂[c, 0] := by
    ext i
    rcases fin2_cases i with rfl | rfl
    · simp only [TOf_apply_zero, Matrix.cons_val_zero]
      rw [he1, real_inner_smul_right, real_inner_self_eq_norm_sq,
        ← dist_eq_norm, dist_comm B A, ← hc_def]
      field_simp [hc.ne']
    · simp only [TOf_apply_one, Matrix.cons_val_one]
      rw [he2, inner_fin2 (B - A) !₂[-(e1 1), e1 0]]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [he1]
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
  have hTC : TOf A e1 e2 C = !₂[p, q] := by
    simp only [TOf, ← hp_def, ← hq_def]
  -- squared distance of C from A
  have hC : p^2 + q^2 = (z + x)^2 := by
    have h4 : dist (TOf A e1 e2 C) (TOf A e1 e2 A) = dist C A :=
      TOf_dist he2 he1sq C A
    have h4sq := congrArg (·^2) h4
    rw [dist_sq_fin2, hTC, hTA, ← hb_def] at h4sq
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, sub_zero] at h4sq
    rw [← hzx_b] at h4sq
    exact h4sq
  -- first moments of C along e1
  have hIA : ⟪C - A, B - A⟫ = x * (x + y + z) - y * z := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hsub : C - A - (B - A) = C - B := by abel
    rw [hsub]
    simp only [← dist_eq_norm]
    rw [dist_comm B A, dist_comm C B, ← ha_def, ← hb_def, ← hc_def,
      hx_def, hy_def, hz_def]
    ring
  have hp : (x + y) * p = x * (x + y + z) - y * z := by
    rw [hxy_c, hp_def, ← real_inner_smul_right, hce1, hIA, hxy_c]
  have hQ : q^2 * (x + y)^2 = 4 * x * y * z * (x + y + z) := by
    linear_combination (x + y)^2 * hC
      - ((x + y) * p + (x * (x + y + z) - y * z)) * hp
  -- circumcenter and circumradius of ABC
  set Tabc : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A, B, C], hABC⟩ with hTabc
  set O := Tabc.circumcenter with hO_def
  set R := Tabc.circumradius with hR_def
  have hO_oa : dist O A = R :=
    Affine.Simplex.dist_circumcenter_eq_circumradius' Tabc 0
  have hO_ob : dist O B = R :=
    Affine.Simplex.dist_circumcenter_eq_circumradius' Tabc 1
  have hO_oc : dist O C = R :=
    Affine.Simplex.dist_circumcenter_eq_circumradius' Tabc 2
  obtain ⟨W, hW1, hW2, hW3⟩ := hW
  -- image points and their coordinates
  set w0 := (TOf A e1 e2 W) 0 with hw0
  set w1 := (TOf A e1 e2 W) 1 with hw1
  set o0 := (TOf A e1 e2 O) 0 with ho0
  set o1 := (TOf A e1 e2 O) 1 with ho1
  have h5 : dist (TOf A e1 e2 O) (TOf A e1 e2 A) = dist (TOf A e1 e2 O) (TOf A e1 e2 B) := by
    rw [TOf_dist he2 he1sq, hO_oa, ← hO_ob, ← TOf_dist he2 he1sq]
  have h5sq := congrArg (·^2) h5
  rw [dist_sq_fin2, dist_sq_fin2, hTA, hTB] at h5sq
  simp only [PiLp.zero_apply, sub_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h5sq
  rw [← ho0, ← ho1] at h5sq
  have hO0c : c * (2 * o0) = c * c := by
    linear_combination h5sq
  have hO0 : 2 * o0 = x + y := by
    have h := mul_left_cancel₀ hc.ne' hO0c
    rw [hxy_c]
    exact h
  have h6 : dist (TOf A e1 e2 O) (TOf A e1 e2 A) = dist (TOf A e1 e2 O) (TOf A e1 e2 C) := by
    rw [TOf_dist he2 he1sq, hO_oa, ← hO_oc, ← TOf_dist he2 he1sq]
  have h6sq := congrArg (·^2) h6
  rw [dist_sq_fin2, dist_sq_fin2, hTA, hTC] at h6sq
  simp only [PiLp.zero_apply, sub_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h6sq
  rw [← ho0, ← ho1] at h6sq
  have h62 : 2 * o0 * p + 2 * o1 * q = (z + x)^2 := by
    have h : 2 * o0 * p + 2 * o1 * q = p^2 + q^2 := by
      linear_combination h6sq
    rw [hC] at h
    exact h
  have hO1 : 2 * q * o1 = z * (x + y + z) - x * y := by
    linear_combination h62 - p * hO0 - hp
  have h7 : dist (TOf A e1 e2 W) (TOf A e1 e2 O) = dist (TOf A e1 e2 O) (TOf A e1 e2 A) := by
    rw [TOf_dist he2 he1sq, hW3, ← hO_oa, ← TOf_dist he2 he1sq]
  have h7sq := congrArg (·^2) h7
  rw [dist_sq_fin2, dist_sq_fin2, hTA] at h7sq
  simp only [PiLp.zero_apply, sub_zero] at h7sq
  rw [← ho0, ← ho1, ← hw0, ← hw1] at h7sq
  have hcond : w0^2 - 2 * w0 * o0 + w1^2 - 2 * w1 * o1 = 0 := by
    linear_combination h7sq
  -- touch point coordinates after the rigid motion
  have hzA1 : ((a + b + c) / 2 - c) / a = z / (y + z) := by
    rw [div_eq_div_iff ha.ne' (ne_of_gt (add_pos hy hz)), hy_def, hz_def]
    ring
  have hxB1 : ((a + b + c) / 2 - a) / b = x / (z + x) := by
    rw [div_eq_div_iff hb.ne' (ne_of_gt (add_pos hz hx)), hx_def, hz_def]
    ring
  have hyC1 : ((a + b + c) / 2 - b) / c = y / (x + y) := by
    rw [div_eq_div_iff hc.ne' (ne_of_gt (add_pos hx hy)), hx_def, hy_def]
    ring
  rw [hzA1] at hA1
  rw [hxB1] at hB1
  rw [hyC1] at hC1
  have hA10 : (TOf A e1 e2 A1) 0
      = (x + y + z) * (x * y + x * z + y^2 - y * z) / ((x + y) * (y + z)) := by
    have hv : (TOf A e1 e2 A1) 0 = c + z / (y + z) * (p - c) := by
      rw [hA1, TOf_lineMap, hTB, hTC, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Matrix.cons_val_zero]
      ring
    rw [← hxy_c] at hv
    rw [hv]
    field_simp [hxy, hyz]
    linear_combination z * hp
  have hA11 : (TOf A e1 e2 A1) 1 = q * z / (y + z) := by
    have hv : (TOf A e1 e2 A1) 1 = z / (y + z) * q := by
      rw [hA1, TOf_lineMap, hTB, hTC, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [hv]
    ring
  have hB10 : (TOf A e1 e2 B1) 0
      = z * (x * (x + y + z) - y * z) / ((x + y) * (x + z)) := by
    have hv : (TOf A e1 e2 B1) 0 = p - x / (z + x) * p := by
      rw [hB1, TOf_lineMap, hTC, hTA, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Matrix.cons_val_zero,
        PiLp.zero_apply]
      ring
    rw [hv]
    have h1 : p - x / (z + x) * p = p * z / (z + x) := by
      field_simp [hzx]
      ring
    rw [h1]
    field_simp [hxy, hzx]
    linear_combination (x + z) * hp
  have hB11 : (TOf A e1 e2 B1) 1 = q * z / (x + z) := by
    have hv : (TOf A e1 e2 B1) 1 = q - x / (z + x) * q := by
      rw [hB1, TOf_lineMap, hTC, hTA, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.zero_apply]
      ring
    rw [hv]
    field_simp [hzx]
    ring
  have hC10 : (TOf A e1 e2 C1) 0 = y := by
    have hv : (TOf A e1 e2 C1) 0 = y / (x + y) * c := by
      rw [hC1, TOf_lineMap, hTA, hTB, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero,
        PiLp.zero_apply, sub_zero]
      ring
    rw [hv, ← hxy_c, div_mul_cancel₀ y (ne_of_gt (add_pos hx hy))]
  have hC11 : (TOf A e1 e2 C1) 1 = 0 := by
    have hv : (TOf A e1 e2 C1) 1 = y / (x + y) * (0 : ℝ) := by
      rw [hC1, TOf_lineMap, hTA, hTB, AffineMap.lineMap_apply_module']
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.zero_apply, sub_zero]
      ring
    rw [hv, mul_zero]
  -- the equidistance equations in coordinates
  have h8 : dist (TOf A e1 e2 W) (TOf A e1 e2 A1)
      = dist (TOf A e1 e2 W) (TOf A e1 e2 B1) := by
    rw [TOf_dist he2 he1sq, hW1, ← TOf_dist he2 he1sq]
  have h8sq := congrArg (·^2) h8
  rw [dist_sq_fin2, dist_sq_fin2, hA10, hA11, hB10, hB11, ← hw0, ← hw1] at h8sq
  have h9 : dist (TOf A e1 e2 W) (TOf A e1 e2 B1)
      = dist (TOf A e1 e2 W) (TOf A e1 e2 C1) := by
    rw [TOf_dist he2 he1sq, hW2, ← TOf_dist he2 he1sq]
  have h9sq := congrArg (·^2) h9
  rw [dist_sq_fin2, dist_sq_fin2, hB10, hB11, hC10, hC11, ← hw0, ← hw1] at h9sq
  rw [sub_zero] at h9sq
  -- apply the algebraic core
  have hprod := core x y z q w0 w1 o0 o1 hx hy hz hq_ne hQ hO0 hO1 hcond h8sq h9sq
  -- translate back to angles
  have hIB : ⟪A - B, C - B⟫ = y * (x + y + z) - x * z := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hsub : A - B - (C - B) = A - C := by abel
    rw [hsub]
    simp only [← dist_eq_norm]
    rw [dist_comm C B, dist_comm A C, ← ha_def, ← hb_def, ← hc_def,
      hx_def, hy_def, hz_def]
    ring
  have hIC : ⟪B - C, A - C⟫ = z * (x + y + z) - x * y := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hsub : B - C - (A - C) = B - A := by abel
    rw [hsub]
    simp only [← dist_eq_norm]
    rw [dist_comm B A, dist_comm A C, ← ha_def, ← hb_def, ← hc_def,
      hx_def, hy_def, hz_def]
    ring
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h1 | h2
    · left
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
        ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, hIA]
      exact h1
    · right
      left
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
        ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, hIB]
      exact h2
  · right
    right
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub,
      ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, hIC]
    exact h

end Imo2013P3
