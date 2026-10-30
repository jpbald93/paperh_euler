import Mathlib

/-!
# Euler's theorem and the inequalities around it: definitions

Throughout, `t : Affine.Triangle ℝ P` has vertices `A = t.points 0`, `B = t.points 1`,
`C = t.points 2` and side lengths `a = dist B C`, `b = dist C A`, `c = dist A B`.
The circumcentre, circumradius, incentre, inradius, excentres, exradii, centroid and orthocentre
are Mathlib's (`t.circumcenter`, `t.circumradius`, `t.incenter`, `t.inradius`, `t.excenter`,
`t.exradius`, `t.centroid`, `t.orthocenter`). Mathlib (at the pinned version) has no Euler
distance formula and no `R ≥ 2r`; we only add the area and the semiperimeter.
-/

namespace EulerIneq

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The area `Δ = ½ · AB · AC · sin ∠BAC` of a triangle (the same definition as in the Brocard
development). -/
noncomputable def area (t : Affine.Triangle ℝ P) : ℝ :=
  (1 / 2) * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
    Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))

/-- The semiperimeter `s = (a + b + c) / 2`. -/
noncomputable def semiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
    dist (t.points 0) (t.points 1)) / 2

end EulerIneq
