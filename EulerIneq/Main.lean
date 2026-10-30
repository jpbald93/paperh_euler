import EulerIneq.Bridges

/-!
# Euler's theorem and the inequalities around it: main theorems

`A = t.points 0`, `B = t.points 1`, `C = t.points 2`, `a = dist B C`, `b = dist C A`,
`c = dist A B`, `R = t.circumradius`, `r = t.inradius`, `s = semiperimeter t`, `Δ = area t`.

The distance formulas all come from the barycentric distance formulas of `EulerIneq.Bridges`
applied to the weights of the bridges; the inequalities reduce to polynomial identities in
`a, b, c` (and, for Gerretsen, to the quartic of the Blundon development).
-/

namespace EulerIneq

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Euler's theorem** (H1.1): `OI² = R² − 2Rr`. -/
theorem euler (t : Affine.Triangle ℝ P) :
    dist t.incenter t.circumcenter ^ 2 = t.circumradius ^ 2 - 2 * t.circumradius * t.inradius := by
  have hsum := t.excenterExists_empty.sum_excenterWeights_eq_one
  rw [t.incenter_eq_affineCombination, dist_affineCombination_circumcenter_sq t _ hsum,
    incenter_weights, incenter_weights, incenter_weights, inradius_eq]
  have h4 := four_mul_circumradius_mul_area t
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have hb := side_pos t (i := 2) (j := 0) (by decide)
  have hc := side_pos t (i := 0) (j := 1) (by decide)
  simp only [sideLen_zero, sideLen_one, sideLen_two]
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  have hp : a + b + c ≠ 0 := by positivity
  have e1 : a / (a + b + c) * (b / (a + b + c)) * c ^ 2 + b / (a + b + c) * (c / (a + b + c)) *
      a ^ 2 + c / (a + b + c) * (a / (a + b + c)) * b ^ 2 = a * b * c / (a + b + c) := by
    field_simp; ring
  linear_combination -e1 + h4 / (a + b + c)

/-- The key identity behind Euler's inequality:
`4Δ (R − 2r) = ½ ((−a+b+c)(b−c)² + (a−b+c)(c−a)² + (a+b−c)(a−b)²)`. -/
theorem four_mul_area_mul_circumradius_sub (t : Affine.Triangle ℝ P) :
    4 * area t * (t.circumradius - 2 * t.inradius) =
      ((-dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
          dist (t.points 0) (t.points 1)) *
          (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0) +
          dist (t.points 0) (t.points 1)) *
          (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 +
        (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) -
          dist (t.points 0) (t.points 1)) *
          (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2) / 2 := by
  have h4 := four_mul_circumradius_mul_area t
  have hrp := inradius_mul t
  have hA := two_mul_area_sq t
  unfold gram at hA
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have hb := side_pos t (i := 2) (j := 0) (by decide)
  have hc := side_pos t (i := 0) (j := 1) (by decide)
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set r := t.inradius
  set D := area t
  have h8 : 8 * D * r = (-a + b + c) * (a - b + c) * (a + b - c) := by
    have hp : a + b + c ≠ 0 := by positivity
    refine mul_left_cancel₀ hp ?_
    linear_combination 8 * D * hrp + 4 * hA
  linear_combination h4 - h8

/-- **Euler's inequality** (H1.2): `2r ≤ R`. -/
theorem euler_inequality (t : Affine.Triangle ℝ P) : 2 * t.inradius ≤ t.circumradius := by
  have h := four_mul_area_mul_circumradius_sub t
  obtain ⟨hx, hy, hz⟩ := triangle_pos t
  have hD := area_pos t
  have hnn : 0 ≤ 4 * area t * (t.circumradius - 2 * t.inradius) := by
    rw [h]; positivity
  have : 0 ≤ t.circumradius - 2 * t.inradius :=
    nonneg_of_mul_nonneg_right (by linarith) (by positivity : 0 < 4 * area t)
  linarith

lemma eq_zero_of_pos_mul_sq {x d : ℝ} (hx : 0 < x) (h : x * d ^ 2 = 0) : d = 0 :=
  pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 h).resolve_left hx.ne')

lemma sum_three_eq_zero {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (h : p + q + r = 0) :
    p = 0 ∧ q = 0 ∧ r = 0 :=
  ⟨by linarith, by linarith, by linarith⟩

/-- Equality in Euler's inequality (H1.2) holds exactly for equilateral triangles. -/
theorem euler_inequality_eq_iff (t : Affine.Triangle ℝ P) :
    2 * t.inradius = t.circumradius ↔
      dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
        dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) := by
  have h := four_mul_area_mul_circumradius_sub t
  obtain ⟨hx, hy, hz⟩ := triangle_pos t
  have hD := area_pos t
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  constructor
  · intro he
    rw [← he, sub_self, mul_zero] at h
    obtain ⟨h1, h2, h3⟩ := sum_three_eq_zero (by positivity) (by positivity) (by positivity)
      (by linarith : (-a + b + c) * (b - c) ^ 2 + (a - b + c) * (c - a) ^ 2 +
        (a + b - c) * (a - b) ^ 2 = 0)
    have := eq_zero_of_pos_mul_sq hz h3
    have := eq_zero_of_pos_mul_sq hx h1
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [h1, h2] at h
    have : 4 * area t * (t.circumradius - 2 * t.inradius) = 0 := by rw [h]; ring
    have := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith

/-- **Euler's theorem for an excircle** (H1.3): `OIᵢ² = R² + 2R rᵢ`. -/
theorem euler_excenter (t : Affine.Triangle ℝ P) (i : Fin 3) :
    dist (t.excenter {i}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {i} := by
  have hsum := (t.excenterExists {i}).sum_excenterWeights_eq_one
  have hS := sum_signed_sideLen_pos t i
  rw [t.excenter_eq_affineCombination, dist_affineCombination_circumcenter_sq t _ hsum,
    excenterWeights_eq, excenterWeights_eq, excenterWeights_eq, exradius_eq,
    abs_of_pos (div_pos (by have := area_pos t; positivity) hS)]
  have h4 := four_mul_circumradius_mul_area t
  set e0 : ℝ := if (0 : Fin 3) ∈ ({i} : Finset (Fin 3)) then -1 else 1
  set e1 : ℝ := if (1 : Fin 3) ∈ ({i} : Finset (Fin 3)) then -1 else 1
  set e2 : ℝ := if (2 : Fin 3) ∈ ({i} : Finset (Fin 3)) then -1 else 1
  set S := ∑ j, (if j ∈ ({i} : Finset (Fin 3)) then (-1 : ℝ) else 1) * sideLen t j with hSdef
  have hS3 : S = e0 * sideLen t 0 + e1 * sideLen t 1 + e2 * sideLen t 2 := by
    rw [hSdef, Fin.sum_univ_three]
  have hid : e0 * e1 * sideLen t 2 + e1 * e2 * sideLen t 0 + e2 * e0 * sideLen t 1 = -S := by
    rw [hS3]
    fin_cases i <;> simp [e0, e1, e2] <;> ring
  simp only [sideLen_zero, sideLen_one, sideLen_two] at hid h4 ⊢
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  have hS0 := hS.ne'
  have hsum' : e0 * a / S * (e1 * b / S) * c ^ 2 + e1 * b / S * (e2 * c / S) * a ^ 2 +
      e2 * c / S * (e0 * a / S) * b ^ 2 = -(a * b * c) / S := by
    have hx : e0 * a / S * (e1 * b / S) * c ^ 2 + e1 * b / S * (e2 * c / S) * a ^ 2 +
        e2 * c / S * (e0 * a / S) * b ^ 2 =
          a * b * c * (e0 * e1 * c + e1 * e2 * a + e2 * e0 * b) / S ^ 2 := by ring
    rw [hx, hid, div_eq_div_iff (pow_ne_zero 2 hS0) hS0]
    ring
  linear_combination -hsum' - h4 / S

/-- The algebra behind Weitzenböck and Hadwiger–Finsler:
`L² − 48Δ² = 8 Σ (y(c − a))²` with `L = 2(ab + bc + ca) − (a² + b² + c²)` and `x, y, z` the
tangent lengths. -/
lemma hf_identity (t : Affine.Triangle ℝ P) :
    (2 * (dist (t.points 1) (t.points 2) * dist (t.points 2) (t.points 0) +
          dist (t.points 2) (t.points 0) * dist (t.points 0) (t.points 1) +
          dist (t.points 0) (t.points 1) * dist (t.points 1) (t.points 2)) -
        (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2)) ^ 2 - (4 * √3 * area t) ^ 2 =
      2 * (((dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0) +
            dist (t.points 0) (t.points 1)) *
            (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2))) ^ 2 +
        ((dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) -
            dist (t.points 0) (t.points 1)) *
            (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0))) ^ 2 +
        ((-dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
            dist (t.points 0) (t.points 1)) *
            (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1))) ^ 2) := by
  have hA := two_mul_area_sq t
  unfold gram at hA
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (-12) * hA - 16 * area t ^ 2 * h3

lemma hf_L_nonneg (t : Affine.Triangle ℝ P) :
    0 ≤ 2 * (dist (t.points 1) (t.points 2) * dist (t.points 2) (t.points 0) +
          dist (t.points 2) (t.points 0) * dist (t.points 0) (t.points 1) +
          dist (t.points 0) (t.points 1) * dist (t.points 1) (t.points 2)) -
        (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2) := by
  obtain ⟨hx, hy, hz⟩ := triangle_pos t
  nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]

/-- **The Hadwiger–Finsler inequality** (H1.4):
`a² + b² + c² ≥ 4√3 Δ + (a − b)² + (b − c)² + (c − a)²`. -/
theorem hadwiger_finsler (t : Affine.Triangle ℝ P) :
    4 * √3 * area t + (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
        (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 ≤
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2 := by
  have hid := hf_identity t
  have hL := hf_L_nonneg t
  have hK : 0 ≤ 4 * √3 * area t := by have := area_pos t; positivity
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set K := 4 * √3 * area t
  set L := 2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2)
  have hsq : K ^ 2 ≤ L ^ 2 := by
    rw [← sub_nonneg, hid]; positivity
  have : K ≤ L := (pow_le_pow_iff_left₀ hK hL two_ne_zero).1 hsq
  linarith

/-- Equality in the Hadwiger–Finsler inequality holds exactly for equilateral triangles. -/
theorem hadwiger_finsler_eq_iff (t : Affine.Triangle ℝ P) :
    4 * √3 * area t + (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
        (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 =
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2 ↔
      dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
        dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) := by
  have hid := hf_identity t
  have hL := hf_L_nonneg t
  have hK : 0 ≤ 4 * √3 * area t := by have := area_pos t; positivity
  obtain ⟨hx, hy, hz⟩ := triangle_pos t
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set K := 4 * √3 * area t
  set L := 2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2)
  constructor
  · intro he
    have hKL : K = L := by linarith
    rw [hKL, sub_self] at hid
    obtain ⟨h1, h2, h3⟩ := sum_three_eq_zero (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
      (by linarith : ((a - b + c) * (c - a)) ^ 2 + ((a + b - c) * (a - b)) ^ 2 +
        ((-a + b + c) * (b - c)) ^ 2 = 0)
    have e1 := (mul_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)).resolve_left hy.ne'
    have e2 := (mul_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)).resolve_left hz.ne'
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have hsq : K ^ 2 = L ^ 2 := by rw [h1, h2] at hid; linarith
    have hKL : K = L := (pow_left_inj₀ hK hL two_ne_zero).1 hsq
    rw [hKL]; simp only [L]; rw [h1, h2]; ring

/-- **Weitzenböck's inequality** (H1.4): `a² + b² + c² ≥ 4√3 Δ`. -/
theorem weitzenboeck (t : Affine.Triangle ℝ P) :
    4 * √3 * area t ≤
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2 := by
  have := hadwiger_finsler t
  nlinarith [sq_nonneg (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)),
    sq_nonneg (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)),
    sq_nonneg (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2))]

/-- Equality in Weitzenböck's inequality holds exactly for equilateral triangles. -/
theorem weitzenboeck_eq_iff (t : Affine.Triangle ℝ P) :
    4 * √3 * area t =
        dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2 ↔
      dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
        dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) := by
  have hf := hadwiger_finsler t
  have hfe := hadwiger_finsler_eq_iff t
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  constructor
  · intro he
    obtain ⟨h1, h2, h3⟩ := sum_three_eq_zero (sq_nonneg (a - b)) (sq_nonneg (b - c))
      (sq_nonneg (c - a)) (by linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)])
    have := pow_eq_zero_iff two_ne_zero |>.1 h1
    have := pow_eq_zero_iff two_ne_zero |>.1 h2
    constructor <;> linarith
  · intro h
    have he := hfe.2 h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2] at he ⊢
    linarith

/-- The polynomial certificate behind Blundon's inequalities (copied from the Blundon
development, `Blundon.core_identity`; `s = x + y + z`). -/
theorem core_identity {r R x y z : ℝ} (h1 : r ^ 2 * (x + y + z) = x * y * z)
    (h2 : 4 * R * r * (x + y + z) = (y + z) * (z + x) * (x + y)) :
    (x + y + z) ^ 3 * (4 * r ^ 2 * ((x + y + z) ^ 4 - 2 * (2 * R ^ 2 + 10 * R * r - r ^ 2) *
      (x + y + z) ^ 2 + r * (4 * R + r) ^ 3) + ((y - x) * (z - y) * (x - z)) ^ 2) = 0 := by
  linear_combination (64*R^2*r^2*x^2 + 128*R^2*r^2*x*y + 128*R^2*r^2*x*z + 64*R^2*r^2*y^2 + 128*R^2*r^2*y*z + 64*R^2*r^2*z^2 + 48*R*r^3*x^2 + 96*R*r^3*x*y + 96*R*r^3*x*z + 48*R*r^3*y^2 + 96*R*r^3*y*z + 48*R*r^3*z^2 - 4*R*r*x^4 + 8*R*r*x^2*y^2 + 16*R*r*x^2*y*z + 8*R*r*x^2*z^2 + 16*R*r*x*y^2*z + 16*R*r*x*y*z^2 - 4*R*r*y^4 + 8*R*r*y^2*z^2 - 4*R*r*z^4 + 12*r^4*x^2 + 24*r^4*x*y + 24*r^4*x*z + 12*r^4*y^2 + 24*r^4*y*z + 12*r^4*z^2 - 20*r^2*x^4 - 68*r^2*x^3*y - 68*r^2*x^3*z - 96*r^2*x^2*y^2 - 192*r^2*x^2*y*z - 96*r^2*x^2*z^2 - 68*r^2*x*y^3 - 192*r^2*x*y^2*z - 192*r^2*x*y*z^2 - 68*r^2*x*z^3 - 20*r^2*y^4 - 68*r^2*y^3*z - 96*r^2*y^2*z^2 - 68*r^2*y*z^3 - 20*r^2*z^4 - x^5*y - x^5*z + 2*x^3*y^3 + 5*x^3*y^2*z + 5*x^3*y*z^2 + 2*x^3*z^3 + 5*x^2*y^3*z + 10*x^2*y^2*z^2 + 5*x^2*y*z^3 - x*y^5 + 5*x*y^3*z^2 + 5*x*y^2*z^3 - x*z^5 - y^5*z + 2*y^3*z^3 - y*z^5) * h2 + (4*r^4*x^2 + 8*r^4*x*y + 8*r^4*x*z + 4*r^4*y^2 + 8*r^4*y*z + 4*r^4*z^2 + 8*r^2*x^4 + 44*r^2*x^3*y + 44*r^2*x^3*z + 72*r^2*x^2*y^2 + 148*r^2*x^2*y*z + 72*r^2*x^2*z^2 + 44*r^2*x*y^3 + 148*r^2*x*y^2*z + 148*r^2*x*y*z^2 + 44*r^2*x*z^3 + 8*r^2*y^4 + 44*r^2*y^3*z + 72*r^2*y^2*z^2 + 44*r^2*y*z^3 + 8*r^2*z^4 + 4*x^6 + 4*x^5*y + 4*x^5*z - 8*x^4*y^2 - 8*x^4*y*z - 8*x^4*z^2 - 16*x^3*y^3 - 32*x^3*y^2*z - 32*x^3*y*z^2 - 16*x^3*z^3 - 8*x^2*y^4 - 32*x^2*y^3*z - 44*x^2*y^2*z^2 - 32*x^2*y*z^3 - 8*x^2*z^4 + 4*x*y^5 - 8*x*y^4*z - 32*x*y^3*z^2 - 32*x*y^2*z^3 - 8*x*y*z^4 + 4*x*z^5 + 4*y^6 + 4*y^5*z - 8*y^4*z^2 - 16*y^3*z^3 - 8*y^2*z^4 + 4*y*z^5 + 4*z^6) * h1

/-- The fundamental quartic `s⁴ − 2(2R² + 10Rr − r²)s² + r(4R + r)³ ≤ 0` (as in the Blundon
development). -/
theorem fundamental_quartic (t : Affine.Triangle ℝ P) :
    semiperimeter t ^ 4 - 2 * (2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius -
      t.inradius ^ 2) * semiperimeter t ^ 2 +
        t.inradius * (4 * t.circumradius + t.inradius) ^ 3 ≤ 0 := by
  have h4 := four_mul_circumradius_mul_area t
  have hrp := inradius_mul t
  have hA := two_mul_area_sq t
  unfold gram at hA
  have hD := area_pos t
  have hR := t.circumradius_pos
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have hb := side_pos t (i := 2) (j := 0) (by decide)
  have hc := side_pos t (i := 0) (j := 1) (by decide)
  unfold semiperimeter
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set r := t.inradius
  set R := t.circumradius
  set D := area t
  set x := (-a + b + c) / 2
  set y := (a - b + c) / 2
  set z := (a + b - c) / 2
  have hs : (a + b + c) / 2 = x + y + z := by simp only [x, y, z]; ring
  have hsp : 0 < x + y + z := by rw [← hs]; positivity
  have hr0 : 0 < r := by
    have : 0 < r * (a + b + c) := by rw [hrp]; positivity
    exact pos_of_mul_pos_left this (by positivity)
  have h1 : r ^ 2 * (x + y + z) = x * y * z := by
    refine mul_left_cancel₀ (show (4 : ℝ) * (x + y + z) ≠ 0 by positivity) ?_
    simp only [x, y, z]
    linear_combination (r * (a + b + c) + 2 * D) * hrp + hA
  have h2 : 4 * R * r * (x + y + z) = (y + z) * (z + x) * (x + y) := by
    have hy : y + z = a := by simp only [y, z]; ring
    have hz : z + x = b := by simp only [x, z]; ring
    have hx : x + y = c := by simp only [x, y]; ring
    rw [← hs, hy, hz, hx, ← h4]
    linear_combination 2 * R * hrp
  have key := core_identity h1 h2
  rw [hs]
  generalize x + y + z = s at key hsp
  have h4' := (mul_eq_zero.1 key).resolve_left (pow_pos hsp 3).ne'
  by_contra hneg
  push Not at hneg
  have : 0 < 4 * r ^ 2 * (s ^ 4 - 2 * (2 * R ^ 2 + 10 * R * r - r ^ 2) * s ^ 2 +
      r * (4 * R + r) ^ 3) := by positivity
  nlinarith [sq_nonneg ((y - x) * (z - y) * (x - z))]

/-- **Gerretsen's inequalities** (H1.5): `16Rr − 5r² ≤ s² ≤ 4R² + 4Rr + 3r²`. -/
theorem gerretsen (t : Affine.Triangle ℝ P) :
    16 * t.circumradius * t.inradius - 5 * t.inradius ^ 2 ≤ semiperimeter t ^ 2 ∧
      semiperimeter t ^ 2 ≤
        4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 := by
  have hq := fundamental_quartic t
  have he := euler_inequality t
  have hr := t.inradius_pos
  set R := t.circumradius
  set r := t.inradius
  set s := semiperimeter t
  have hB : 0 ≤ 2 * (R - r) * (R - 2 * r) := by
    have : 0 ≤ R - r := by linarith
    have : 0 ≤ R - 2 * r := by linarith
    positivity
  have hsq : (s ^ 2 - (2 * R ^ 2 + 10 * R * r - r ^ 2)) ^ 2 ≤ (2 * (R - r) * (R - 2 * r)) ^ 2 := by
    nlinarith [sq_nonneg (R - 2 * r), mul_nonneg (sq_nonneg (R - 2 * r)) (sq_nonneg r)]
  have := abs_le_of_sq_le_sq' hsq hB
  constructor <;> linarith [this.1, this.2]

/-- The circumcentre–centroid distance (H1.6): `OG² = R² − (a² + b² + c²)/9`. -/
theorem dist_circumcenter_centroid_sq (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.centroid ^ 2 =
      t.circumradius ^ 2 - (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) / 9 := by
  have hw : ∑ _i : Fin 3, (1 / 3 : ℝ) = 1 := by rw [Fin.sum_univ_three]; norm_num
  rw [dist_comm, centroid_eq_affineCombination, dist_affineCombination_circumcenter_sq t _ hw]
  ring

/-- The circumcentre–orthocentre distance (H1.6): `OH² = 9R² − (a² + b² + c²)`. -/
theorem dist_circumcenter_orthocenter_sq (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.orthocenter ^ 2 =
      9 * t.circumradius ^ 2 - (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2) := by
  have h := dist_circumcenter_centroid_sq t
  rw [t.orthocenter_eq_smul_vsub_vadd_circumcenter, dist_comm, dist_vadd_left, norm_smul,
    ← dist_eq_norm_vsub V, dist_comm, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3),
    mul_pow]
  rw [Affine.Simplex.univ_centroid_eq, h]
  ring

/-- The incentre–centroid distance (H1.6): `IG² = (s² + 5r² − 16Rr)/9`. -/
theorem dist_incenter_centroid_sq (t : Affine.Triangle ℝ P) :
    dist t.incenter t.centroid ^ 2 =
      (semiperimeter t ^ 2 + 5 * t.inradius ^ 2 - 16 * t.circumradius * t.inradius) / 9 := by
  have hsum := t.excenterExists_empty.sum_excenterWeights_eq_one
  have hw : ∑ _i : Fin 3, (1 / 3 : ℝ) = 1 := by rw [Fin.sum_univ_three]; norm_num
  rw [t.incenter_eq_affineCombination, centroid_eq_affineCombination,
    dist_affineCombination_affineCombination_sq t.points _ _ hsum hw,
    incenter_weights, incenter_weights, incenter_weights, inradius_eq]
  have h4 := four_mul_circumradius_mul_area t
  have hA := two_mul_area_sq t
  unfold gram at hA
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have hb := side_pos t (i := 2) (j := 0) (by decide)
  have hc := side_pos t (i := 0) (j := 1) (by decide)
  simp only [sideLen_zero, sideLen_one, sideLen_two]
  unfold semiperimeter
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set D := area t
  set R := t.circumradius
  have hp : a + b + c ≠ 0 := by positivity
  set u := (a + b + c)⁻¹ with hu_def
  have hu : (a + b + c) * u = 1 := mul_inv_cancel₀ hp
  simp only [div_eq_mul_inv _ (a + b + c), ← hu_def]
  linear_combination
    (-((-(5 * a ^ 2 + 2 * a * b + 2 * a * c + 5 * b ^ 2 + 2 * b * c + 5 * c ^ 2) / 36) *
        (1 + (a + b + c) * u) +
      (3 * a ^ 2 * b + 3 * a ^ 2 * c + 3 * a * b ^ 2 + 8 * a * b * c + 3 * a * c ^ 2 +
        3 * b ^ 2 * c + 3 * b * c ^ 2) / 9 * u)) * hu -
    (5 / 9) * u ^ 2 * hA + (8 / 9) * u * h4

end EulerIneq
