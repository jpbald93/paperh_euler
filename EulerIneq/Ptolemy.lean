import EulerIneq.Basic

/-!
# Ptolemy's inequality (H3.2)

Mathlib already proves Ptolemy's inequality in any real inner product space, by inversion:
`EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist` (file
`Mathlib/Geometry/Euclidean/Inversion/Basic.lean`). We restate it under the name of this
development; the proof is Mathlib's.
-/

namespace EulerIneq

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

include V in
/-- **Ptolemy's inequality** (H3.2): `AC · BD ≤ AB · CD + BC · AD` for any four points
(Mathlib's `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`). -/
theorem ptolemy_inequality (A B C D : P) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D :=
  EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist A B C D

end EulerIneq
