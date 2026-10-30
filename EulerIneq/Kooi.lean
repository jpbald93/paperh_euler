import EulerIneq.Main

/-!
# Kooi's inequality (H3.3)

`s² ≤ R (4R + r)² / (2 (2R − r))`, a strengthening of Gerretsen's upper bound
`s² ≤ 4R² + 4Rr + 3r²`. Equality holds exactly for the equilateral triangle.

Proof: write the fundamental quartic as `f(s²) ≤ 0` with `f(u) = (u − B)² − Q`,
`B = 2R² + 10Rr − r²`. With `K = R (4R + r)² / (2 (2R − r))` one has
`2(2R − r)(K − B) = (R − 2r)(8R² − 12Rr + r²) ≥ 0` and
`f(K) = r²(R − 2r)²(4R + r)² / (4 (2R − r)²) ≥ 0`, so `K` lies at or beyond the larger root of `f`,
hence `s² ≤ K`.
-/

namespace EulerIneq

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The real-number core of Kooi's inequality. -/
theorem kooi_of_quartic {R r u : ℝ} (hr : 0 < r) (hR : 2 * r ≤ R)
    (hq : u ^ 2 - 2 * (2 * R ^ 2 + 10 * R * r - r ^ 2) * u + r * (4 * R + r) ^ 3 ≤ 0) :
    u ≤ R * (4 * R + r) ^ 2 / (2 * (2 * R - r)) := by
  have hd : 0 < 2 * R - r := by linarith
  set B := 2 * R ^ 2 + 10 * R * r - r ^ 2
  set M := (R - 2 * r) * (8 * R ^ 2 - 12 * R * r + r ^ 2) with hM_def
  have hM : 0 ≤ M := by
    have h1 : 0 ≤ R - 2 * r := by linarith
    have h2 : 0 ≤ 8 * R ^ 2 - 12 * R * r + r ^ 2 := by
      nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ R)]
    exact mul_nonneg h1 h2
  have hid : M ^ 2 - (2 * (2 * R - r) * (u - B)) ^ 2 = (r * (R - 2 * r) * (4 * R + r)) ^ 2 -
      4 * (2 * R - r) ^ 2 * (u ^ 2 - 2 * B * u + r * (4 * R + r) ^ 3) := by
    simp only [hM_def, B]; ring
  have hsq : (2 * (2 * R - r) * (u - B)) ^ 2 ≤ M ^ 2 := by
    have : 0 ≤ 4 * (2 * R - r) ^ 2 * -(u ^ 2 - 2 * B * u + r * (4 * R + r) ^ 3) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [sq_nonneg (r * (R - 2 * r) * (4 * R + r))]
  have hw := (abs_le_of_sq_le_sq' hsq hM).2
  rw [le_div_iff₀ (by positivity)]
  have hMB : M = R * (4 * R + r) ^ 2 - 2 * (2 * R - r) * B := by simp only [hM_def, B]; ring
  nlinarith

/-- **Kooi's inequality** (H3.3): `s² ≤ R (4R + r)² / (2 (2R − r))`. -/
theorem kooi (t : Affine.Triangle ℝ P) :
    semiperimeter t ^ 2 ≤
      t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) := by
  have hq := fundamental_quartic t
  exact kooi_of_quartic t.inradius_pos (euler_inequality t) (by linarith [hq])

/-- Kooi's bound is at most Gerretsen's: `R (4R + r)² / (2 (2R − r)) ≤ 4R² + 4Rr + 3r²`. -/
theorem kooi_le_gerretsen (t : Affine.Triangle ℝ P) :
    t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 := by
  have hR := euler_inequality t
  have hr := t.inradius_pos
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sq_nonneg t.inradius) (show 0 ≤ t.circumradius - 2 * t.inradius by linarith)]

end EulerIneq
