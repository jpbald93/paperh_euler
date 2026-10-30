import EulerIneq.Main
import EulerIneq.Pedoe
import EulerIneq.Ptolemy
import EulerIneq.Kooi
import EulerIneq.Extremal

/-!
# Layer 14: Mathlib-only restatements and witnesses

Each `l14_*` theorem restates a main theorem of the development with a type that mentions only
Mathlib notions: the local `area` is unfolded to `½ · AB · AC · sin ∠BAC` and the local
`semiperimeter` to `(a + b + c) / 2`; everything else (`circumcenter`, `circumradius`, `incenter`,
`inradius`, `excenter`, `exradius`, `centroid`, `orthocenter`) is already Mathlib's. Each is proved
from the library theorem. The `l14w_*` theorems are explicit witnesses in
`EuclideanSpace ℝ (Fin 2)` (the 3-4-5 triangle `(0,0), (4,0), (0,3)` with `a, b, c = 5, 3, 4`,
`Δ = 6`, `s = 6`, `R = 5/2`, `r = 1`), showing that the hypotheses are satisfiable and that every
inequality with an equality case is strict for this non-equilateral triangle.
-/

open EuclideanGeometry

namespace EulerIneq

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
variable {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [MetricSpace P']
  [NormedAddTorsor V' P']

/-! ### Mathlib-only restatements -/

theorem l14_euler (t : Affine.Triangle ℝ P) :
    dist t.incenter t.circumcenter ^ 2 = t.circumradius ^ 2 - 2 * t.circumradius * t.inradius :=
  euler t

theorem l14_euler_inequality (t : Affine.Triangle ℝ P) :
    2 * t.inradius ≤ t.circumradius :=
  euler_inequality t

theorem l14_euler_inequality_eq_iff (t : Affine.Triangle ℝ P) :
    2 * t.inradius = t.circumradius ↔ dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧ dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) :=
  euler_inequality_eq_iff t

theorem l14_euler_excenter (t : Affine.Triangle ℝ P) (i : Fin 3) :
    dist (t.excenter {i}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {i} :=
  euler_excenter t i

theorem l14_dist_circumcenter_centroid_sq (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.centroid ^ 2 = t.circumradius ^ 2 - (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 9 :=
  dist_circumcenter_centroid_sq t

theorem l14_dist_circumcenter_orthocenter_sq (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.orthocenter ^ 2 = 9 * t.circumradius ^ 2 - (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) :=
  dist_circumcenter_orthocenter_sq t

theorem l14_dist_incenter_centroid_sq (t : Affine.Triangle ℝ P) :
    dist t.incenter t.centroid ^ 2 =
      (((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
      dist (t.points 0) (t.points 1)) / 2) ^ 2 + 5 * t.inradius ^ 2 - 16 * t.circumradius * t.inradius) / 9 :=
  dist_incenter_centroid_sq t

theorem l14_fundamental_quartic (t : Affine.Triangle ℝ P) :
    ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
      dist (t.points 0) (t.points 1)) / 2) ^ 4 - 2 * (2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2) * ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
      dist (t.points 0) (t.points 1)) / 2) ^ 2 +
      t.inradius * (4 * t.circumradius + t.inradius) ^ 3 ≤ 0 :=
  fundamental_quartic t

theorem l14_gerretsen (t : Affine.Triangle ℝ P) :
    16 * t.circumradius * t.inradius - 5 * t.inradius ^ 2 ≤ ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
      dist (t.points 0) (t.points 1)) / 2) ^ 2 ∧
      ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
      dist (t.points 0) (t.points 1)) / 2) ^ 2 ≤ 4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 :=
  gerretsen t

theorem l14_kooi (t : Affine.Triangle ℝ P) :
    ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
      dist (t.points 0) (t.points 1)) / 2) ^ 2 ≤ t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 / (2 * (2 * t.circumradius - t.inradius)) :=
  kooi t

theorem l14_kooi_le_gerretsen (t : Affine.Triangle ℝ P) :
    t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 / (2 * (2 * t.circumradius - t.inradius)) ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 :=
  kooi_le_gerretsen t

theorem l14_weitzenboeck (t : Affine.Triangle ℝ P) :
    4 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) ≤ dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 :=
  weitzenboeck t

theorem l14_weitzenboeck_eq_iff (t : Affine.Triangle ℝ P) :
    4 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) = dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 ↔ dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧ dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) :=
  weitzenboeck_eq_iff t

theorem l14_hadwiger_finsler (t : Affine.Triangle ℝ P) :
    4 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) + (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
      (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 + (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 ≤
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 :=
  hadwiger_finsler t

theorem l14_hadwiger_finsler_eq_iff (t : Affine.Triangle ℝ P) :
    4 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) + (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
      (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 + (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 =
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 ↔ dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧ dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) :=
  hadwiger_finsler_eq_iff t

theorem l14_isoperimetric (t : Affine.Triangle ℝ P) :
    12 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) ≤ (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) ^ 2 :=
  isoperimetric t

theorem l14_isoperimetric_eq_iff (t : Affine.Triangle ℝ P) :
    12 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) = (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) ^ 2 ↔
      dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) ∧ dist (t.points 2) (t.points 0) = dist (t.points 0) (t.points 1) :=
  isoperimetric_eq_iff t

theorem l14_leibniz_relation (t : Affine.Triangle ℝ P) (X : P) :
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
      3 * dist X t.centroid ^ 2 + (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 3 :=
  leibniz_relation t X

theorem l14_leibniz_min (t : Affine.Triangle ℝ P) (X : P) :
    (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 3 ≤
      dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 :=
  leibniz_min t X

theorem l14_leibniz_min_eq_iff (t : Affine.Triangle ℝ P) (X : P) :
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 = (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 3 ↔
      X = t.centroid :=
  leibniz_min_eq_iff t X

theorem l14_pedoe (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    16 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) * (1 / 2 * dist (t'.points 0) (t'.points 1) * dist (t'.points 0) (t'.points 2) *
      Real.sin (∠ (t'.points 1) (t'.points 0) (t'.points 2))) ≤
      dist (t'.points 1) (t'.points 2) ^ 2 * (dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 - dist (t.points 1) (t.points 2) ^ 2) +
      dist (t'.points 2) (t'.points 0) ^ 2 * (dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 - dist (t.points 2) (t.points 0) ^ 2) +
      dist (t'.points 0) (t'.points 1) ^ 2 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 - dist (t.points 0) (t.points 1) ^ 2) :=
  pedoe t t'

theorem l14_pedoe_eq_iff (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    dist (t'.points 1) (t'.points 2) ^ 2 * (dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 - dist (t.points 1) (t.points 2) ^ 2) +
      dist (t'.points 2) (t'.points 0) ^ 2 * (dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 - dist (t.points 2) (t.points 0) ^ 2) +
      dist (t'.points 0) (t'.points 1) ^ 2 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 - dist (t.points 0) (t.points 1) ^ 2) =
      16 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) * (1 / 2 * dist (t'.points 0) (t'.points 1) * dist (t'.points 0) (t'.points 2) *
      Real.sin (∠ (t'.points 1) (t'.points 0) (t'.points 2))) ↔
    ∃ k : ℝ, 0 < k ∧ dist (t'.points 1) (t'.points 2) = k * dist (t.points 1) (t.points 2) ∧ dist (t'.points 2) (t'.points 0) = k * dist (t.points 2) (t.points 0) ∧ dist (t'.points 0) (t'.points 1) = k * dist (t.points 0) (t.points 1) :=
  pedoe_eq_iff t t'

include V in
theorem l14_ptolemy_inequality (A B C D : P) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D :=
  ptolemy_inequality (V := V) A B C D

/-! ### Witnesses -/

theorem l14_dist_sq (x y : EuclideanSpace ℝ (Fin 2)) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem l14_dist (x y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = r ^ 2) : dist x y = r := by
  rw [← sq_eq_sq₀ dist_nonneg hr, l14_dist_sq, h]

theorem l14_not_collinear (X Y Z : EuclideanSpace ℝ (Fin 2))
    (h : (Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0) ≠ 0) :
    ¬ Collinear ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hc
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hc
  obtain ⟨v, hv⟩ := hc
  obtain ⟨r, hr⟩ := hv Y (by simp)
  obtain ⟨s, hs⟩ := hv Z (by simp)
  apply h
  have h0 := congrArg (· 0) hr; have h1 := congrArg (· 1) hr
  have h2 := congrArg (· 0) hs; have h3 := congrArg (· 1) hs
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]; ring

theorem l14_ne (X Y : EuclideanSpace ℝ (Fin 2)) (h : X 0 ≠ Y 0 ∨ X 1 ≠ Y 1) : X ≠ Y := by
  rintro rfl; tauto

/-- The 3-4-5 witness triangle `(0,0), (4,0), (0,3)`. -/
noncomputable def l14T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![!₂[0, 0], !₂[4, 0], !₂[0, 3]],
    affineIndependent_iff_not_collinear_set.2 (l14_not_collinear _ _ _ (by simp))⟩

/-- The right isosceles triangle `(0,0), (1,0), (0,1)` (not similar to `l14T`). -/
noncomputable def l14T' : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![!₂[0, 0], !₂[1, 0], !₂[0, 1]],
    affineIndependent_iff_not_collinear_set.2 (l14_not_collinear _ _ _ (by simp))⟩

theorem l14T_sides : dist (l14T.points 1) (l14T.points 2) = 5 ∧
    dist (l14T.points 2) (l14T.points 0) = 3 ∧ dist (l14T.points 0) (l14T.points 1) = 4 :=
  ⟨l14_dist _ _ _ (by norm_num) (by simp [l14T]; norm_num),
    l14_dist _ _ _ (by norm_num) (by simp [l14T]),
    l14_dist _ _ _ (by norm_num) (by simp [l14T])⟩

theorem l14T_area : area l14T = 6 := by
  have h := two_mul_area_sq l14T
  have h0 := area_nonneg l14T
  obtain ⟨ha, hb, hc⟩ := l14T_sides
  rw [ha, hb, hc, gram] at h
  nlinarith

theorem l14T_inradius : l14T.inradius = 1 := by
  obtain ⟨ha, hb, hc⟩ := l14T_sides
  rw [inradius_eq, ha, hb, hc, l14T_area]; norm_num

theorem l14T_circumradius : l14T.circumradius = 5 / 2 := by
  have h := four_mul_circumradius_mul_area l14T
  obtain ⟨ha, hb, hc⟩ := l14T_sides
  rw [ha, hb, hc, l14T_area] at h
  linarith

theorem l14T'_sides : dist (l14T'.points 1) (l14T'.points 2) ^ 2 = 2 ∧
    dist (l14T'.points 2) (l14T'.points 0) = 1 ∧ dist (l14T'.points 0) (l14T'.points 1) = 1 :=
  ⟨by rw [l14_dist_sq]; simp [l14T']; norm_num,
    l14_dist _ _ _ (by norm_num) (by simp [l14T']),
    l14_dist _ _ _ (by norm_num) (by simp [l14T'])⟩

theorem l14T'_area : area l14T' = 1 / 2 := by
  have h := two_mul_area_sq l14T'
  have h0 := area_nonneg l14T'
  obtain ⟨ha, hb, hc⟩ := l14T'_sides
  rw [hb, hc, gram] at h
  have h4 : dist (l14T'.points 1) (l14T'.points 2) ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha]; norm_num
  rw [h4, ha] at h
  nlinarith

theorem l14_sqrt3_lt : √3 < 7 / 4 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- Witness for the triangle theorems (Euler, Gerretsen, Kooi, Weitzenböck, Hadwiger–Finsler,
isoperimetric, the distance formulas): the 3-4-5 triangle, which is not equilateral; every
inequality with an equality case is strict, and `OI² = 5/4`, `OG² = 25/36`, `OH² = 25/4`,
`IG² = 1/9`. -/
theorem l14w_triangle : ∃ t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧
    dist (t.points 1) (t.points 2) = 5 ∧ dist (t.points 2) (t.points 0) = 3 ∧ dist (t.points 0) (t.points 1) = 4 ∧
    (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) = 6 ∧
    ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) / 2) = 6 ∧ t.circumradius = 5 / 2 ∧ t.inradius = 1 ∧
    dist t.incenter t.circumcenter ^ 2 = 5 / 4 ∧ dist t.circumcenter t.centroid ^ 2 = 25 / 36 ∧
    dist t.circumcenter t.orthocenter ^ 2 = 25 / 4 ∧ dist t.incenter t.centroid ^ 2 = 1 / 9 ∧
    2 * t.inradius < t.circumradius ∧
    ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) / 2) ^ 4 - 2 * (2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2) * ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) / 2) ^ 2 +
      t.inradius * (4 * t.circumradius + t.inradius) ^ 3 < 0 ∧
    16 * t.circumradius * t.inradius - 5 * t.inradius ^ 2 < ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) / 2) ^ 2 ∧
    ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) / 2) ^ 2 < t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 / (2 * (2 * t.circumradius - t.inradius)) ∧
    t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 / (2 * (2 * t.circumradius - t.inradius)) <
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 ∧
    4 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) < dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 ∧
    4 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) + (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 + (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 + (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 < dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 ∧
    12 * √3 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) < (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := l14T_sides
  have hA : (1 / 2 * dist (l14T.points 0) (l14T.points 1) * dist (l14T.points 0) (l14T.points 2) *
      Real.sin (∠ (l14T.points 1) (l14T.points 0) (l14T.points 2))) = 6 := l14T_area
  have hOI := l14_euler l14T
  have hOG := l14_dist_circumcenter_centroid_sq l14T
  have hOH := l14_dist_circumcenter_orthocenter_sq l14T
  have hIG := l14_dist_incenter_centroid_sq l14T
  have h3 := l14_sqrt3_lt
  refine ⟨l14T, rfl, ?_⟩
  rw [hOI, hOG, hOH, hIG, hA]
  rw [ha, hb, hc, l14T_circumradius, l14T_inradius]
  refine ⟨rfl, rfl, rfl, rfl, by norm_num, rfl, rfl, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    nlinarith

/-- Witness for Leibniz: for `X = A` in the 3-4-5 triangle, `X` is not the centroid and the
inequality is strict (`25 > 50/3`). -/
theorem l14w_leibniz : ∃ t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), ∃ X : EuclideanSpace ℝ (Fin 2), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧
    X = !₂[0, 0] ∧ X ≠ t.centroid ∧
    (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 3 < dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := l14T_sides
  have hX0 : dist (l14T.points 0) (l14T.points 0) = 0 := dist_self _
  have hX1 : dist (l14T.points 0) (l14T.points 1) = 4 := hc
  have hX2 : dist (l14T.points 0) (l14T.points 2) = 3 := by rw [dist_comm]; exact hb
  have hlt : (dist (l14T.points 1) (l14T.points 2) ^ 2 + dist (l14T.points 2) (l14T.points 0) ^ 2 + dist (l14T.points 0) (l14T.points 1) ^ 2) / 3 <
      dist (l14T.points 0) (l14T.points 0) ^ 2 + dist (l14T.points 0) (l14T.points 1) ^ 2 +
        dist (l14T.points 0) (l14T.points 2) ^ 2 := by
    rw [ha, hb, hX0, hX1, hX2]; norm_num
  refine ⟨l14T, l14T.points 0, rfl, rfl, ?_, hlt⟩
  intro h
  have := (l14_leibniz_min_eq_iff l14T (l14T.points 0)).2 h
  linarith

/-- Witness for Pedoe: the 3-4-5 triangle and the right isosceles triangle are not similar, and
the inequality is strict (`48 < 50`). -/
theorem l14w_pedoe : ∃ t t' : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] ∧
    t'.points = ![!₂[0, 0], !₂[1, 0], !₂[0, 1]] ∧
    (¬ ∃ k : ℝ, 0 < k ∧ dist (t'.points 1) (t'.points 2) = k * dist (t.points 1) (t.points 2) ∧ dist (t'.points 2) (t'.points 0) = k * dist (t.points 2) (t.points 0) ∧ dist (t'.points 0) (t'.points 1) = k * dist (t.points 0) (t.points 1)) ∧
    16 * (1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
      Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))) * (1 / 2 * dist (t'.points 0) (t'.points 1) * dist (t'.points 0) (t'.points 2) *
      Real.sin (∠ (t'.points 1) (t'.points 0) (t'.points 2))) <
      dist (t'.points 1) (t'.points 2) ^ 2 * (dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 - dist (t.points 1) (t.points 2) ^ 2) +
      dist (t'.points 2) (t'.points 0) ^ 2 * (dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 - dist (t.points 2) (t.points 0) ^ 2) +
      dist (t'.points 0) (t'.points 1) ^ 2 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 - dist (t.points 0) (t.points 1) ^ 2) := by
  obtain ⟨ha, hb, hc⟩ := l14T_sides
  obtain ⟨ha', hb', hc'⟩ := l14T'_sides
  have hA : (1 / 2 * dist (l14T.points 0) (l14T.points 1) * dist (l14T.points 0) (l14T.points 2) *
      Real.sin (∠ (l14T.points 1) (l14T.points 0) (l14T.points 2))) = 6 := l14T_area
  have hA' : (1 / 2 * dist (l14T'.points 0) (l14T'.points 1) *
      dist (l14T'.points 0) (l14T'.points 2) *
      Real.sin (∠ (l14T'.points 1) (l14T'.points 0) (l14T'.points 2))) = 1 / 2 := l14T'_area
  refine ⟨l14T, l14T', rfl, rfl, ?_, ?_⟩
  · rintro ⟨k, -, -, h2, h3⟩
    rw [hb, hb'] at h2; rw [hc, hc'] at h3; linarith
  · rw [hA, hA', ha', ha, hb, hc, hb', hc']; norm_num

/-- Witness for Ptolemy's inequality: the rectangle `(0,0), (4,0), (0,3), (4,3)` taken in the
non-cyclic order `A, B, C, D`, where the inequality is strict (`9 < 41`). -/
theorem l14w_ptolemy_inequality : ∃ A B C D : EuclideanSpace ℝ (Fin 2),
    A = !₂[0, 0] ∧ B = !₂[4, 0] ∧ C = !₂[0, 3] ∧ D = !₂[4, 3] ∧
    dist A C * dist B D < dist A B * dist C D + dist B C * dist A D := by
  refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_⟩
  rw [l14_dist _ _ 3 (by norm_num) (by simp), l14_dist _ _ 3 (by norm_num) (by simp),
    l14_dist _ _ 4 (by norm_num) (by simp), l14_dist _ _ 4 (by norm_num) (by simp),
    l14_dist _ _ 5 (by norm_num) (by simp; norm_num), l14_dist _ _ 5 (by norm_num) (by simp; norm_num)]
  norm_num

end EulerIneq
