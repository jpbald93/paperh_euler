import EulerIneq.Bridges

/-!
# The Neuberg–Pedoe inequality (H3.1)

For triangles `t` (sides `a, b, c`, area `Δ`) and `t'` (sides `a', b', c'`, area `Δ'`), possibly in
different Euclidean spaces,
`a'²(b² + c² − a²) + b'²(c² + a² − b²) + c'²(a² + b² − c²) ≥ 16 Δ Δ'`,
with equality iff the triangles are similar.

Proof: with `x, y, z = a², b², c²`, `X, Y, Z = a'², b'², c'²`, `S = x + y + z`, `T = X + Y + Z`,
`L` the left-hand side and Heron's `16Δ² = 2(xy + yz + zx) − (x² + y² + z²)`, one has the
identity `2ST(L − 16ΔΔ') = (4TΔ − 4SΔ')² + 2((Tx − SX)² + (Ty − SY)² + (Tz − SZ)²)`.
-/

namespace EulerIneq

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
variable {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [MetricSpace P']
  [NormedAddTorsor V' P']

/-- The polynomial certificate: for `(2Δ)² = gram a b c`, `(2Δ')² = gram a' b' c'`,
`S = a² + b² + c²`, `T = a'² + b'² + c'²` and `L` the Neuberg–Pedoe form,
`2ST(L − 16ΔΔ') = (4TΔ − 4SΔ')² + 2((Ta² − Sa'²)² + (Tb² − Sb'²)² + (Tc² − Sc'²)²)`. -/
theorem pedoe_identity {a b c a' b' c' D D' : ℝ} (hD : (2 * D) ^ 2 = gram a b c)
    (hD' : (2 * D') ^ 2 = gram a' b' c') :
    2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a' ^ 2 + b' ^ 2 + c' ^ 2) *
        (a' ^ 2 * (b ^ 2 + c ^ 2 - a ^ 2) + b' ^ 2 * (c ^ 2 + a ^ 2 - b ^ 2) +
          c' ^ 2 * (a ^ 2 + b ^ 2 - c ^ 2) - 16 * D * D') =
      (4 * (a' ^ 2 + b' ^ 2 + c' ^ 2) * D - 4 * (a ^ 2 + b ^ 2 + c ^ 2) * D') ^ 2 +
        2 * (((a' ^ 2 + b' ^ 2 + c' ^ 2) * a ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2) * a' ^ 2) ^ 2 +
          ((a' ^ 2 + b' ^ 2 + c' ^ 2) * b ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2) * b' ^ 2) ^ 2 +
          ((a' ^ 2 + b' ^ 2 + c' ^ 2) * c ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2) * c' ^ 2) ^ 2) := by
  unfold gram at hD hD'
  linear_combination (-4 * (a' ^ 2 + b' ^ 2 + c' ^ 2) ^ 2) * hD +
    (-4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) * hD'

/-- **The Neuberg–Pedoe inequality** (H3.1):
`a'²(b² + c² − a²) + b'²(c² + a² − b²) + c'²(a² + b² − c²) ≥ 16 Δ Δ'`. -/
theorem pedoe (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    16 * area t * area t' ≤
      dist (t'.points 1) (t'.points 2) ^ 2 * (dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2 - dist (t.points 1) (t.points 2) ^ 2) +
        dist (t'.points 2) (t'.points 0) ^ 2 * (dist (t.points 0) (t.points 1) ^ 2 +
          dist (t.points 1) (t.points 2) ^ 2 - dist (t.points 2) (t.points 0) ^ 2) +
        dist (t'.points 0) (t'.points 1) ^ 2 * (dist (t.points 1) (t.points 2) ^ 2 +
          dist (t.points 2) (t.points 0) ^ 2 - dist (t.points 0) (t.points 1) ^ 2) := by
  have hA := two_mul_area_sq t
  have hA' := two_mul_area_sq t'
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have ha' := side_pos t' (i := 1) (j := 2) (by decide)
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set a' := dist (t'.points 1) (t'.points 2)
  set b' := dist (t'.points 2) (t'.points 0)
  set c' := dist (t'.points 0) (t'.points 1)
  have hS0 : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by nlinarith [sq_nonneg b, sq_nonneg c, pow_pos ha 2]
  have hT0 : 0 < a' ^ 2 + b' ^ 2 + c' ^ 2 := by
    nlinarith [sq_nonneg b', sq_nonneg c', pow_pos ha' 2]
  have hpos : 0 < 2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a' ^ 2 + b' ^ 2 + c' ^ 2) :=
    mul_pos (mul_pos two_pos hS0) hT0
  have h : 0 ≤ 2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a' ^ 2 + b' ^ 2 + c' ^ 2) *
      (a' ^ 2 * (b ^ 2 + c ^ 2 - a ^ 2) + b' ^ 2 * (c ^ 2 + a ^ 2 - b ^ 2) +
        c' ^ 2 * (a ^ 2 + b ^ 2 - c ^ 2) - 16 * area t * area t') := by
    rw [pedoe_identity hA hA']; positivity
  have := (mul_nonneg_iff_of_pos_left hpos).1 h
  linarith

/-- **Equality in Neuberg–Pedoe** (H3.1): equality holds iff the triangles are similar, i.e.
`a' = k a`, `b' = k b`, `c' = k c` for some `k > 0`. -/
theorem pedoe_eq_iff (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    dist (t'.points 1) (t'.points 2) ^ 2 * (dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2 - dist (t.points 1) (t.points 2) ^ 2) +
        dist (t'.points 2) (t'.points 0) ^ 2 * (dist (t.points 0) (t.points 1) ^ 2 +
          dist (t.points 1) (t.points 2) ^ 2 - dist (t.points 2) (t.points 0) ^ 2) +
        dist (t'.points 0) (t'.points 1) ^ 2 * (dist (t.points 1) (t.points 2) ^ 2 +
          dist (t.points 2) (t.points 0) ^ 2 - dist (t.points 0) (t.points 1) ^ 2) =
      16 * area t * area t' ↔
    ∃ k : ℝ, 0 < k ∧ dist (t'.points 1) (t'.points 2) = k * dist (t.points 1) (t.points 2) ∧
      dist (t'.points 2) (t'.points 0) = k * dist (t.points 2) (t.points 0) ∧
      dist (t'.points 0) (t'.points 1) = k * dist (t.points 0) (t.points 1) := by
  have hA := two_mul_area_sq t
  have hA' := two_mul_area_sq t'
  have hD := area_nonneg t
  have hD' := area_nonneg t'
  have ha := side_pos t (i := 1) (j := 2) (by decide)
  have hb := side_pos t (i := 2) (j := 0) (by decide)
  have hc := side_pos t (i := 0) (j := 1) (by decide)
  have ha' := side_pos t' (i := 1) (j := 2) (by decide)
  have hb' := side_pos t' (i := 2) (j := 0) (by decide)
  have hc' := side_pos t' (i := 0) (j := 1) (by decide)
  have hid := pedoe_identity hA hA'
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 2) (t.points 0)
  set c := dist (t.points 0) (t.points 1)
  set a' := dist (t'.points 1) (t'.points 2)
  set b' := dist (t'.points 2) (t'.points 0)
  set c' := dist (t'.points 0) (t'.points 1)
  set D := area t
  set D' := area t'
  set S := a ^ 2 + b ^ 2 + c ^ 2 with hS
  set T := a' ^ 2 + b' ^ 2 + c' ^ 2 with hT
  have hS0 : 0 < S := by nlinarith [sq_nonneg b, sq_nonneg c, pow_pos ha 2]
  have hT0 : 0 < T := by nlinarith [sq_nonneg b', sq_nonneg c', pow_pos ha' 2]
  have hSne := hS0.ne'
  constructor
  · intro heq
    rw [heq, sub_self, mul_zero] at hid
    have q0 := sq_nonneg (4 * T * D - 4 * S * D')
    have q1 := sq_nonneg (T * a ^ 2 - S * a' ^ 2)
    have q2 := sq_nonneg (T * b ^ 2 - S * b' ^ 2)
    have q3 := sq_nonneg (T * c ^ 2 - S * c' ^ 2)
    have h1 : (T * a ^ 2 - S * a' ^ 2) ^ 2 = 0 := by linarith
    have h2 : (T * b ^ 2 - S * b' ^ 2) ^ 2 = 0 := by linarith
    have h3 : (T * c ^ 2 - S * c' ^ 2) ^ 2 = 0 := by linarith
    have key : ∀ u u' : ℝ, 0 ≤ u → 0 ≤ u' → (T * u ^ 2 - S * u' ^ 2) ^ 2 = 0 →
        u' = Real.sqrt (T / S) * u := by
      intro u u' hu hu' h
      have h' : u' ^ 2 = T / S * u ^ 2 := by
        have := pow_eq_zero_iff (two_ne_zero) |>.1 h
        field_simp
        linarith
      rw [← Real.sqrt_sq hu', h', Real.sqrt_mul (div_nonneg hT0.le hS0.le), Real.sqrt_sq hu]
    exact ⟨Real.sqrt (T / S), Real.sqrt_pos.2 (div_pos hT0 hS0), key _ _ ha.le ha'.le h1,
      key _ _ hb.le hb'.le h2, key _ _ hc.le hc'.le h3⟩
  · rintro ⟨k, hk, h1, h2, h3⟩
    have hDD : D' = k ^ 2 * D := by
      have e : (2 * D') ^ 2 = (2 * (k ^ 2 * D)) ^ 2 := by
        rw [hA', h1, h2, h3]
        unfold gram at hA ⊢
        linear_combination (-k ^ 4) * hA
      have := (pow_left_inj₀ (by linarith) (by have := mul_nonneg (sq_nonneg k) hD; linarith)
        two_ne_zero).1 e
      linarith
    rw [h1, h2, h3, hDD]
    unfold gram at hA
    linear_combination (-4 * k ^ 2) * hA

end EulerIneq
