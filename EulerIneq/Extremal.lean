import EulerIneq.Main

/-!
# Extremal problems (H3.4)

* the Leibniz minimum: `XA² + XB² + XC² ≥ (a² + b² + c²)/3`, with equality iff `X` is the
  centroid (from `XA² + XB² + XC² = 3 XG² + (a² + b² + c²)/3`, the barycentric distance formula
  with the centroid weights);
* the isoperimetric inequality for triangles `12√3 Δ ≤ (a + b + c)²`, equality iff equilateral
  (from `16Δ² = p (−a + b + c)(a − b + c)(a + b − c)` and AM–GM, with the certificate
  `(x + y + z)³ − 27xyz = ½(x + y + z)Σ(x − y)² + 3(x(y − z)² + y(z − x)² + z(x − y)²)`);
* a cross-check: Gerretsen's two bounds alone give `(R − r)(R − 2r) ≥ 0`.
-/

namespace EulerIneq

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Leibniz's relation: `XA² + XB² + XC² = 3 XG² + (a² + b² + c²)/3`. -/
theorem leibniz_relation (t : Affine.Triangle ℝ P) (X : P) :
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
      3 * dist X t.centroid ^ 2 + (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 3 := by
  have hw : ∑ _i : Fin 3, (1 / 3 : ℝ) = 1 := by rw [Fin.sum_univ_three]; norm_num
  have h := dist_affineCombination_sq t.points (fun _ => (1 / 3 : ℝ)) hw X
  rw [← centroid_eq_affineCombination] at h
  rw [dist_comm X t.centroid, h, dist_comm X (t.points 0), dist_comm X (t.points 1),
    dist_comm X (t.points 2)]
  ring

/-- **The Leibniz minimum** (H3.4 (i)): `XA² + XB² + XC² ≥ (a² + b² + c²)/3`. -/
theorem leibniz_min (t : Affine.Triangle ℝ P) (X : P) :
    (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2) / 3 ≤
      dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 := by
  linarith [leibniz_relation t X, sq_nonneg (dist X t.centroid)]

/-- **Equality in the Leibniz minimum** (H3.4 (i)): iff `X` is the centroid. -/
theorem leibniz_min_eq_iff (t : Affine.Triangle ℝ P) (X : P) :
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
        (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2) / 3 ↔
      X = t.centroid := by
  rw [leibniz_relation]
  constructor
  · intro h
    have h0 : dist X t.centroid ^ 2 = 0 := by linarith
    exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  · rintro rfl
    simp

/-- AM–GM for three positive reals with the explicit certificate. -/
theorem amgm_three {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
  have e : (x + y + z) ^ 3 - 27 * (x * y * z) = (x + y + z) / 2 * ((x - y) ^ 2 + (y - z) ^ 2 +
      (z - x) ^ 2) + 3 * (x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2) := by ring
  have : 0 ≤ (x + y + z) / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) +
      3 * (x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2) := by positivity
  linarith

/-- **The isoperimetric inequality for triangles** (H3.4 (ii)): `12√3 Δ ≤ (a + b + c)²`. -/
theorem isoperimetric (t : Affine.Triangle ℝ P) :
    12 * Real.sqrt 3 * area t ≤
      (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
        dist (t.points 0) (t.points 1)) ^ 2 := by
  have hA := two_mul_area_sq t
  unfold gram at hA
  have hD := area_nonneg t
  obtain ⟨hx, hy, hz⟩ := triangle_pos t
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set D := area t
  have h27 := amgm_three hx hy hz
  have hp : 0 < a + b + c := by linarith
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsq : (12 * Real.sqrt 3 * D) ^ 2 ≤ ((a + b + c) ^ 2) ^ 2 := by
    have e1 : (12 * Real.sqrt 3 * D) ^ 2 = 27 * ((a + b + c) *
        ((-a + b + c) * (a - b + c) * (a + b - c))) := by
      rw [mul_pow, mul_pow, h3]; linear_combination 108 * hA
    have e2 : ((a + b + c) ^ 2) ^ 2 = (a + b + c) * ((-a + b + c) + (a - b + c) + (a + b - c)) ^ 3 := by
      ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left h27 hp.le
    linarith
  exact (sq_le_sq₀ (mul_nonneg (by positivity) hD) (by positivity)).1 hsq

/-- **Equality in the isoperimetric inequality** (H3.4 (ii)): iff the triangle is equilateral. -/
theorem isoperimetric_eq_iff (t : Affine.Triangle ℝ P) :
    12 * Real.sqrt 3 * area t =
        (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
          dist (t.points 0) (t.points 1)) ^ 2 ↔
      dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) ∧
        dist (t.points 2) (t.points 0) = dist (t.points 0) (t.points 1) := by
  have hA := two_mul_area_sq t
  unfold gram at hA
  have hD := area_nonneg t
  obtain ⟨hx, hy, hz⟩ := triangle_pos t
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set D := area t
  have hp : 0 < a + b + c := by linarith
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  constructor
  · intro h
    have hsq : (12 * Real.sqrt 3 * D) ^ 2 = ((a + b + c) ^ 2) ^ 2 := by rw [h]
    set x := -a + b + c
    set y := a - b + c
    set z := a + b - c
    have hpx : a + b + c = x + y + z := by simp only [x, y, z]; ring
    have e1 : (12 * Real.sqrt 3 * D) ^ 2 = 27 * ((x + y + z) * (x * y * z)) := by
      rw [mul_pow, mul_pow, h3, ← hpx]; simp only [x, y, z]; linear_combination 108 * hA
    rw [e1, hpx] at hsq
    have hp' : 0 < x + y + z := by linarith
    have h27 : (x + y + z) ^ 3 - 27 * (x * y * z) = 0 := by
      have : (x + y + z) * ((x + y + z) ^ 3 - 27 * (x * y * z)) = 0 := by linear_combination -hsq
      exact (mul_eq_zero.1 this).resolve_left hp'.ne'
    have e : (x + y + z) ^ 3 - 27 * (x * y * z) = (1 / 2) * ((x + y + z) * (x - y) ^ 2) +
        (1 / 2) * ((x + y + z) * (y - z) ^ 2) + (1 / 2) * ((x + y + z) * (z - x) ^ 2) +
        3 * (x * (y - z) ^ 2) + 3 * (y * (z - x) ^ 2) + 3 * (z * (x - y) ^ 2) := by ring
    have t1 := mul_nonneg hp'.le (sq_nonneg (x - y))
    have t2 := mul_nonneg hp'.le (sq_nonneg (y - z))
    have t3 := mul_nonneg hp'.le (sq_nonneg (z - x))
    have t4 := mul_nonneg hx.le (sq_nonneg (y - z))
    have t5 := mul_nonneg hy.le (sq_nonneg (z - x))
    have t6 := mul_nonneg hz.le (sq_nonneg (x - y))
    have hxy : (x - y) ^ 2 = 0 :=
      (mul_eq_zero.1 (show (x + y + z) * (x - y) ^ 2 = 0 by linarith)).resolve_left hp'.ne'
    have hyz : (y - z) ^ 2 = 0 :=
      (mul_eq_zero.1 (show (x + y + z) * (y - z) ^ 2 = 0 by linarith)).resolve_left hp'.ne'
    have h1 := pow_eq_zero_iff two_ne_zero |>.1 hxy
    have h2 := pow_eq_zero_iff two_ne_zero |>.1 hyz
    simp only [x, y, z] at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [← h2, ← h1] at hA ⊢
    have ha : 0 < a := side_pos t (i := 1) (j := 2) (by decide)
    have e : (4 * D) ^ 2 = (Real.sqrt 3 * a ^ 2) ^ 2 := by
      linear_combination 4 * hA - a ^ 4 * h3
    have hD4 := (pow_left_inj₀ (by linarith) (by positivity) two_ne_zero).1 e
    have : 12 * Real.sqrt 3 * D = 3 * Real.sqrt 3 * (4 * D) := by ring
    rw [this, hD4]
    linear_combination 3 * a ^ 2 * h3

/-- Cross-check (H3.4 (iii), partial): Gerretsen's two bounds alone force
`(R − r)(R − 2r) ≥ 0`, i.e. `R ≤ r` or `R ≥ 2r`; they do not exclude `R ≤ r` by themselves. -/
theorem gerretsen_cross_check (t : Affine.Triangle ℝ P) :
    0 ≤ (t.circumradius - t.inradius) * (t.circumradius - 2 * t.inradius) := by
  have h := gerretsen t
  nlinarith [h.1, h.2]

end EulerIneq
