import EulerIneq.Basic

/-!
# Bridges between Mathlib's triangle centres and explicit barycentric weights

* `gram a b c = (2Δ)²` (Heron) and `hᵢ · aᵢ = 2Δ` for the heights;
* `4 R Δ = a b c`;
* the weights of Mathlib's incentre and excentres are `(± a : ± b : ± c)`, the inradius is
  `2Δ / (a + b + c)` and the exradius opposite vertex `i` is `2Δ / (−aᵢ + aⱼ + aₖ)`;
* the Leibniz (barycentric distance) formula
  `|Σ wᵢ Pᵢ − Q|² = Σ wᵢ |Pᵢ − Q|² − Σ_{i<j} wᵢ wⱼ |Pᵢ − Pⱼ|²` for `Σ wᵢ = 1`.

`height_sq_mul` and `circumradius_sq_mul` are adapted from the Blundon development (namespace
`Blundon`), with the same proofs.
-/

namespace EulerIneq

open EuclideanGeometry RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Four times the squared area of a triangle with sides `a, b, c` (Heron). -/
noncomputable def gram (a b c : ℝ) : ℝ :=
  (2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4) / 4

/-- The side length opposite vertex `i`: `a, b, c` for `i = 0, 1, 2`. -/
noncomputable def sideLen (t : Affine.Triangle ℝ P) (i : Fin 3) : ℝ :=
  ![dist (t.points 1) (t.points 2), dist (t.points 2) (t.points 0),
    dist (t.points 0) (t.points 1)] i

@[simp] lemma sideLen_zero (t : Affine.Triangle ℝ P) :
    sideLen t 0 = dist (t.points 1) (t.points 2) := rfl

@[simp] lemma sideLen_one (t : Affine.Triangle ℝ P) :
    sideLen t 1 = dist (t.points 2) (t.points 0) := rfl

@[simp] lemma sideLen_two (t : Affine.Triangle ℝ P) :
    sideLen t 2 = dist (t.points 0) (t.points 1) := rfl

lemma side_pos (t : Affine.Triangle ℝ P) {i j : Fin 3} (h : i ≠ j) :
    0 < dist (t.points i) (t.points j) :=
  dist_pos.2 (t.independent.injective.ne h)

/-- Bridge for heights: `h_i² · (opposite side)² = gram` (from the Blundon development). -/
theorem height_sq_mul (t : Affine.Triangle ℝ P) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    t.height i ^ 2 * dist (t.points j) (t.points k) ^ 2 =
      gram (dist (t.points i) (t.points j)) (dist (t.points i) (t.points k))
        (dist (t.points j) (t.points k)) := by
  have hc : ({i}ᶜ : Set (Fin 3)) = {j, k} := by ext l; simp; omega
  have hF : t.altitudeFoot i ∈ line[ℝ, t.points j, t.points k] := by
    have := t.altitudeFoot_mem_affineSpan_image_compl i
    rwa [hc, Set.image_insert_eq, Set.image_singleton] at this
  obtain ⟨τ, hτ⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hF
  have e1 := t.inner_vsub_vsub_altitudeFoot_eq_height_sq hij
  have e2 := t.inner_vsub_vsub_altitudeFoot_eq_height_sq hik
  set p := t.points i -ᵥ t.points j
  set q := t.points i -ᵥ t.points k
  have hw : t.points i -ᵥ t.altitudeFoot i = p - τ • (p - q) := by
    rw [← hτ, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub]
    simp only [p, q, vsub_sub_vsub_cancel_left]
  rw [hw] at e1 e2
  simp only [inner_sub_right, inner_smul_right, real_inner_comm p q] at e1 e2
  have hP : ⟪p, p⟫ = dist (t.points i) (t.points j) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm_vsub V]
  have hQ : ⟪q, q⟫ = dist (t.points i) (t.points k) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm_vsub V]
  have ha : dist (t.points j) (t.points k) ^ 2 = ⟪p, p⟫ - 2 * ⟪p, q⟫ + ⟪q, q⟫ := by
    rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_left (t.points j) (t.points k) (t.points i)]
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm]
    ring
  have hM : ⟪p, q⟫ = (dist (t.points i) (t.points j) ^ 2 + dist (t.points i) (t.points k) ^ 2
      - dist (t.points j) (t.points k) ^ 2) / 2 := by
    rw [ha, hP, hQ]; ring
  have core : t.height i ^ 2 * (⟪p, p⟫ - 2 * ⟪p, q⟫ + ⟪q, q⟫) = ⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2 := by
    linear_combination (⟪p, q⟫ - ⟪q, q⟫) * e1 + (⟪p, q⟫ - ⟪p, p⟫) * e2
  rw [ha, core, hM, hP, hQ, gram]
  ring

/-- Bridge for the circumradius: `4R² · gram = a²b²c²` (law of sines; from the Blundon
development). -/
theorem circumradius_sq_mul (t : Affine.Triangle ℝ P) :
    4 * t.circumradius ^ 2 * gram (dist (t.points 0) (t.points 1)) (dist (t.points 1) (t.points 2))
      (dist (t.points 0) (t.points 2)) =
      dist (t.points 0) (t.points 1) ^ 2 * dist (t.points 1) (t.points 2) ^ 2 *
        dist (t.points 0) (t.points 2) ^ 2 := by
  have hls := t.dist_div_sin_angle_eq_two_mul_circumradius (i₁ := 0) (i₂ := 1) (i₃ := 2)
    (by decide) (by decide) (by decide)
  have hR := t.circumradius_pos
  have hc : 0 < dist (t.points 0) (t.points 1) :=
    dist_pos.2 (t.independent.injective.ne (by decide))
  have ha : 0 < dist (t.points 1) (t.points 2) :=
    dist_pos.2 (t.independent.injective.ne (by decide))
  set B := ∠ (t.points 0) (t.points 1) (t.points 2)
  have hsin : Real.sin B ≠ 0 := by
    intro h0; rw [h0, div_zero] at hls; linarith
  have hb : dist (t.points 0) (t.points 2) = 2 * t.circumradius * Real.sin B := by
    field_simp at hls; linarith
  have hlaw := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (t.points 0) (t.points 1) (t.points 2)
  rw [dist_comm (t.points 2) (t.points 1)] at hlaw
  have hpy := Real.sin_sq_add_cos_sq B
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 0) (t.points 2)
  set c := dist (t.points 0) (t.points 1)
  have hg : gram c a b = c ^ 2 * a ^ 2 * Real.sin B ^ 2 := by
    unfold gram
    linear_combination (-(c ^ 2 * a ^ 2)) * hpy +
      (c * a * Real.cos B - (b * b - (c * c + a * a - 2 * c * a * Real.cos B)) / 4) * hlaw
  rw [hg, hb]
  ring

/-- Bridge for the area: `(2Δ)² = gram a b c` (Heron's formula). -/
theorem two_mul_area_sq (t : Affine.Triangle ℝ P) :
    (2 * area t) ^ 2 = gram (dist (t.points 1) (t.points 2)) (dist (t.points 2) (t.points 0))
      (dist (t.points 0) (t.points 1)) := by
  have hlaw := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (t.points 1) (t.points 0) (t.points 2)
  have hpy := Real.sin_sq_add_cos_sq (∠ (t.points 1) (t.points 0) (t.points 2))
  rw [dist_comm (t.points 1) (t.points 0)] at hlaw
  unfold area gram
  rw [dist_comm (t.points 0) (t.points 2)]
  set A := ∠ (t.points 1) (t.points 0) (t.points 2)
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  linear_combination (c ^ 2 * b ^ 2) * hpy -
    ((c ^ 2 + b ^ 2 - a ^ 2) + 2 * c * b * Real.cos A) / 4 * hlaw

lemma area_nonneg (t : Affine.Triangle ℝ P) : 0 ≤ area t := by
  unfold area
  have := Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg (t.points 1) (t.points 0) (t.points 2))
    (angle_le_pi _ _ _)
  have h1 := dist_nonneg (x := t.points 0) (y := t.points 1)
  have h2 := dist_nonneg (x := t.points 0) (y := t.points 2)
  positivity

/-- Bridge for heights: `h_i · a_i = 2Δ`. -/
theorem height_mul_sideLen (t : Affine.Triangle ℝ P) (i : Fin 3) :
    t.height i * sideLen t i = 2 * area t := by
  have hA := two_mul_area_sq t
  have hΔ := area_nonneg t
  have hh := t.height_pos i
  have key : (t.height i * sideLen t i) ^ 2 = (2 * area t) ^ 2 := by
    rw [hA, mul_pow]
    fin_cases i
    · have := height_sq_mul t (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
      simp only [sideLen, Fin.zero_eta, Matrix.cons_val_zero]
      rw [this, dist_comm (t.points 0) (t.points 2)]; unfold gram; ring
    · have := height_sq_mul t (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
      simp only [sideLen, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [this, dist_comm (t.points 1) (t.points 0)]; unfold gram; ring
    · have := height_sq_mul t (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)
      simp only [sideLen, Fin.reduceFinMk, Matrix.cons_val]
      rw [this, dist_comm (t.points 2) (t.points 1)]; unfold gram; ring
  have hs : 0 ≤ sideLen t i := by fin_cases i <;> simp [sideLen, dist_nonneg]
  exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 key

lemma area_pos (t : Affine.Triangle ℝ P) : 0 < area t := by
  have h := height_mul_sideLen t 0
  have hh := t.height_pos 0
  have hs : 0 < sideLen t 0 := by simpa [sideLen] using side_pos t (i := 1) (j := 2) (by decide)
  have : 0 < t.height 0 * sideLen t 0 := mul_pos hh hs
  linarith

/-- Bridge for the circumradius: `4 R Δ = a b c`. -/
theorem four_mul_circumradius_mul_area (t : Affine.Triangle ℝ P) :
    4 * t.circumradius * area t = dist (t.points 1) (t.points 2) *
      dist (t.points 2) (t.points 0) * dist (t.points 0) (t.points 1) := by
  have h := circumradius_sq_mul t
  have hA := two_mul_area_sq t
  have hR := t.circumradius_pos
  have hΔ := area_pos t
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have hb := side_pos t (i := 2) (j := 0) (by decide)
  have hc := side_pos t (i := 0) (j := 1) (by decide)
  rw [dist_comm (t.points 0) (t.points 2)] at h
  have hg : gram (dist (t.points 0) (t.points 1)) (dist (t.points 1) (t.points 2))
      (dist (t.points 2) (t.points 0)) = gram (dist (t.points 1) (t.points 2))
      (dist (t.points 2) (t.points 0)) (dist (t.points 0) (t.points 1)) := by unfold gram; ring
  rw [hg, ← hA] at h
  have key : (4 * t.circumradius * area t) ^ 2 = (dist (t.points 1) (t.points 2) *
      dist (t.points 2) (t.points 0) * dist (t.points 0) (t.points 1)) ^ 2 := by
    linear_combination h
  exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 key

/-- Bridge for the unnormalised excentre weights: `± a_i / (2Δ)`. -/
theorem excenterWeightsUnnorm_eq (t : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) (i : Fin 3) :
    t.excenterWeightsUnnorm signs i = (if i ∈ signs then -1 else 1) * sideLen t i / (2 * area t) := by
  have h := height_mul_sideLen t i
  have hh := (t.height_pos i).ne'
  have hΔ := (area_pos t).ne'
  rw [Affine.Simplex.excenterWeightsUnnorm, mul_div_assoc]
  congr 1
  field_simp
  linarith

/-- Bridge for the excentre weights: Mathlib's `excenterWeights signs` are
`(ε₀ a, ε₁ b, ε₂ c) / (ε₀ a + ε₁ b + ε₂ c)` with `εᵢ = -1` for `i ∈ signs` and `1` otherwise. -/
theorem excenterWeights_eq (t : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) (i : Fin 3) :
    t.excenterWeights signs i = (if i ∈ signs then -1 else 1) * sideLen t i /
      ∑ j, (if j ∈ signs then -1 else 1) * sideLen t j := by
  have hΔ := (area_pos t).ne'
  rw [Affine.Simplex.excenterWeights, Pi.smul_apply, smul_eq_mul]
  simp only [excenterWeightsUnnorm_eq]
  rw [← Finset.sum_div, inv_div, div_mul_div_comm, mul_comm (2 * area t), mul_div_mul_right _ _
    (by positivity)]

/-- Bridge for the exradii: `r_signs = |2Δ / (ε₀ a + ε₁ b + ε₂ c)|`. -/
theorem exradius_eq (t : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) :
    t.exradius signs = |2 * area t / ∑ j, (if j ∈ signs then -1 else 1) * sideLen t j| := by
  rw [Affine.Simplex.exradius_eq_abs_inv_sum]
  simp only [excenterWeightsUnnorm_eq]
  rw [← Finset.sum_div, inv_div]

/-- Bridge for the incentre: weights `(a, b, c) / (a + b + c)`. -/
theorem incenter_weights (t : Affine.Triangle ℝ P) (i : Fin 3) :
    t.excenterWeights ∅ i = sideLen t i /
      (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
        dist (t.points 0) (t.points 1)) := by
  rw [excenterWeights_eq]
  simp [Fin.sum_univ_three, sideLen]

/-- Bridge for the inradius: `r = 2Δ / (a + b + c)`. -/
theorem inradius_eq (t : Affine.Triangle ℝ P) :
    t.inradius = 2 * area t / (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
        dist (t.points 0) (t.points 1)) := by
  have h := exradius_eq t ∅
  simp only [Finset.notMem_empty, if_false, one_mul, Fin.sum_univ_three, sideLen] at h
  have hΔ := area_pos t
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have hb := side_pos t (i := 2) (j := 0) (by decide)
  have hc := side_pos t (i := 0) (j := 1) (by decide)
  rw [show t.inradius = t.exradius ∅ from rfl, h]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [abs_of_pos (by positivity)]
  simp

/-- The signed side sums `-aᵢ + aⱼ + aₖ` are positive (strict triangle inequality, from
Mathlib's existence of the excentres). -/
theorem sum_signed_sideLen_pos (t : Affine.Triangle ℝ P) (i : Fin 3) :
    0 < ∑ j, (if j ∈ ({i} : Finset (Fin 3)) then -1 else 1) * sideLen t j := by
  have h := t.sum_excenterWeightsUnnorm_singleton_pos i
  simp only [excenterWeightsUnnorm_eq] at h
  rw [← Finset.sum_div] at h
  exact (div_pos_iff_of_pos_right (by have := area_pos t; positivity)).1 h

/-- **Leibniz's (barycentric distance) formula** for three points: for `w₀ + w₁ + w₂ = 1`,
`|Σ wᵢ Pᵢ − Q|² = Σ wᵢ |Pᵢ − Q|² − Σ_{i<j} wᵢ wⱼ |Pᵢ − Pⱼ|²`. -/
theorem dist_affineCombination_sq (p : Fin 3 → P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (Q : P) :
    dist (Finset.univ.affineCombination ℝ p w) Q ^ 2 =
      w 0 * dist (p 0) Q ^ 2 + w 1 * dist (p 1) Q ^ 2 + w 2 * dist (p 2) Q ^ 2 -
        (w 0 * w 1 * dist (p 0) (p 1) ^ 2 + w 1 * w 2 * dist (p 1) (p 2) ^ 2 +
          w 2 * w 0 * dist (p 2) (p 0) ^ 2) := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw Q,
    dist_eq_norm_vsub V, vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  rw [Fin.sum_univ_three] at hw
  have e : ∀ i j, dist (p i) (p j) ^ 2 = ‖(p i -ᵥ Q) - (p j -ᵥ Q)‖ ^ 2 := fun i j => by
    rw [vsub_sub_vsub_cancel_right, dist_eq_norm_vsub V]
  rw [e 0 1, e 1 2, e 2 0, dist_eq_norm_vsub V (p 0) Q, dist_eq_norm_vsub V (p 1) Q,
    dist_eq_norm_vsub V (p 2) Q]
  set u0 := p 0 -ᵥ Q
  set u1 := p 1 -ᵥ Q
  set u2 := p 2 -ᵥ Q
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm u0 u1,
    real_inner_comm u0 u2, real_inner_comm u1 u2]
  linear_combination (w 0 * ⟪u0, u0⟫ + w 1 * ⟪u1, u1⟫ + w 2 * ⟪u2, u2⟫) * hw

/-- The barycentric distance formula with `Q` the circumcentre:
`|Σ wᵢ Pᵢ − O|² = R² − Σ_{i<j} wᵢ wⱼ |Pᵢ − Pⱼ|²`. -/
theorem dist_affineCombination_circumcenter_sq (t : Affine.Triangle ℝ P) (w : Fin 3 → ℝ)
    (hw : ∑ i, w i = 1) :
    dist (Finset.univ.affineCombination ℝ t.points w) t.circumcenter ^ 2 =
      t.circumradius ^ 2 - (w 0 * w 1 * dist (t.points 0) (t.points 1) ^ 2 +
        w 1 * w 2 * dist (t.points 1) (t.points 2) ^ 2 +
          w 2 * w 0 * dist (t.points 2) (t.points 0) ^ 2) := by
  rw [dist_affineCombination_sq t.points w hw, t.dist_circumcenter_eq_circumradius,
    t.dist_circumcenter_eq_circumradius, t.dist_circumcenter_eq_circumradius]
  rw [Fin.sum_univ_three] at hw
  linear_combination t.circumradius ^ 2 * hw

/-- The distance between two affine combinations of the vertices of a triangle: for
`Σ wᵢ = Σ vᵢ = 1` and `d = w − v`, `|Σ wᵢ Pᵢ − Σ vᵢ Pᵢ|² = −(d₀d₁ c² + d₁d₂ a² + d₂d₀ b²)`. -/
theorem dist_affineCombination_affineCombination_sq (p : Fin 3 → P) (w v : Fin 3 → ℝ)
    (hw : ∑ i, w i = 1) (hv : ∑ i, v i = 1) :
    dist (Finset.univ.affineCombination ℝ p w) (Finset.univ.affineCombination ℝ p v) ^ 2 =
      -((w 0 - v 0) * (w 1 - v 1) * dist (p 0) (p 1) ^ 2 +
        (w 1 - v 1) * (w 2 - v 2) * dist (p 1) (p 2) ^ 2 +
          (w 2 - v 2) * (w 0 - v 0) * dist (p 2) (p 0) ^ 2) := by
  rw [sq, dist_affineCombination p hw hv]
  simp only [Fin.sum_univ_three, dist_self, Pi.sub_apply, dist_comm (p 1) (p 0),
    dist_comm (p 2) (p 1), dist_comm (p 0) (p 2)]
  ring

/-- Bridge for the centroid: weights `(1/3, 1/3, 1/3)`. -/
theorem centroid_eq_affineCombination (t : Affine.Triangle ℝ P) :
    t.centroid = Finset.univ.affineCombination ℝ t.points (fun _ => (1 / 3 : ℝ)) := by
  rw [Affine.Simplex.centroid_eq_affineCombination]
  congr 1
  ext i
  simp [Finset.centroidWeights_apply]

/-- The strict triangle inequalities `-a + b + c > 0`, `a - b + c > 0`, `a + b - c > 0`. -/
theorem triangle_pos (t : Affine.Triangle ℝ P) :
    0 < -dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
        dist (t.points 0) (t.points 1) ∧
      0 < dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0) +
        dist (t.points 0) (t.points 1) ∧
      0 < dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) -
        dist (t.points 0) (t.points 1) := by
  have h0 := sum_signed_sideLen_pos t 0
  have h1 := sum_signed_sideLen_pos t 1
  have h2 := sum_signed_sideLen_pos t 2
  simp [Fin.sum_univ_three] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The inradius times the perimeter: `r (a + b + c) = 2Δ`. -/
theorem inradius_mul (t : Affine.Triangle ℝ P) :
    t.inradius * (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
        dist (t.points 0) (t.points 1)) = 2 * area t := by
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have hb := side_pos t (i := 2) (j := 0) (by decide)
  have hc := side_pos t (i := 0) (j := 1) (by decide)
  rw [inradius_eq]
  field_simp

end EulerIneq
