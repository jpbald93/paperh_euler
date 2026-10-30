import EulerIneq.Basic
import EulerIneq.Bridges
import EulerIneq.Main
import EulerIneq.Pedoe
import EulerIneq.Ptolemy
import EulerIneq.Kooi
import EulerIneq.Extremal
import EulerIneq.L14

/-!
# Layer 15: classical statements (EulerIneq)

An independent writer stated the classical theorems in the textbook form, using only Mathlib
and a few elementary definitions, in a separate file, `PaperHClassical.lean`
(sha256 begins 0ac73f94ec9efdb8). This file copies that file's `Classical*` definitions
verbatim (inside the namespace `EulerIneq.Classical`) and restates each classical statement with
its verbatim type as `cov_<name>`, proved from the library. Helper lemmas marked NEW PROOF are
arguments that are not in the rest of the library.
-/

open EuclideanGeometry Real

noncomputable section
namespace EulerIneq.Classical

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## Definitions not (directly) in Mathlib -/

/-- Side `a = BC`. -/
def ClassicalSideA (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 1) (t.points 2)
/-- Side `b = CA`. -/
def ClassicalSideB (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 2) (t.points 0)
/-- Side `c = AB`. -/
def ClassicalSideC (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 0) (t.points 1)

/-- Semiperimeter `s = (a+b+c)/2`. -/
def ClassicalSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (ClassicalSideA t + ClassicalSideB t + ClassicalSideC t) / 2

/-- Area of the triangle with vertices `A B C`: `Δ = ½·AB·AC·sin A`. -/
def ClassicalAreaPts (A B C : P) : ℝ :=
  1 / 2 * dist A B * dist A C * Real.sin (∠ B A C)

/-- Area `Δ` of a triangle. -/
def ClassicalArea (t : Affine.Triangle ℝ P) : ℝ :=
  ClassicalAreaPts (t.points 0) (t.points 1) (t.points 2)

/-- Centroid `G`. -/
def ClassicalCentroid (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ t.points

/-- Equilateral: `a = b = c`. -/
def ClassicalEquilateral (t : Affine.Triangle ℝ P) : Prop :=
  ClassicalSideA t = ClassicalSideB t ∧ ClassicalSideB t = ClassicalSideC t

/-- Sum of squared sides `a² + b² + c²`. -/
def ClassicalSumSq (t : Affine.Triangle ℝ P) : ℝ :=
  ClassicalSideA t ^ 2 + ClassicalSideB t ^ 2 + ClassicalSideC t ^ 2

/-- `X` lies inside or on the triangle (closed convex hull of the vertices):
all barycentric coordinates nonnegative. -/
def ClassicalInsideOrOn (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- `X` lies strictly inside the triangle: all barycentric coordinates positive
(works in any ambient dimension, i.e. relative interior). -/
def ClassicalStrictlyInside (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- Distance from `X` to the line through `Y` and `Z`. -/
def ClassicalDistToLine (X Y Z : P) : ℝ :=
  Metric.infDist X (affineSpan ℝ {Y, Z} : Set P)

/-- Fermat point: a point seeing each side under `120°`. -/
def ClassicalIsFermatPoint (t : Affine.Triangle ℝ P) (F : P) : Prop :=
  ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
  ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
  ∠ (t.points 0) F (t.points 1) = 2 * π / 3

/-- All angles of the triangle are less than `120°`. -/
def ClassicalAnglesLt120 (t : Affine.Triangle ℝ P) : Prop :=
  ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3 ∧
  ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3 ∧
  ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3

/-- `X'` is the apex of the equilateral triangle erected outward on side `YZ`
of a triangle whose third vertex is `X`: `X'Y = X'Z = YZ`, and `X'` lies on the
opposite side of line `YZ` from `X`. -/
def ClassicalOutwardEquilateralApex (X Y Z X' : P) : Prop :=
  dist X' Y = dist Y Z ∧ dist X' Z = dist Y Z ∧
  (affineSpan ℝ {Y, Z}).SOppSide X X'

/-- Sum of distances `XA + XB + XC`. -/
def ClassicalDistSum (t : Affine.Triangle ℝ P) (X : P) : ℝ :=
  dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)

/-- Sum of squared distances `XA² + XB² + XC²`. -/
def ClassicalDistSqSum (t : Affine.Triangle ℝ P) (X : P) : ℝ :=
  dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2

/-- Four distinct points lie "in this order" `A, B, C, D` on a circle or line:
either they are concyclic and the diagonals `AC`, `BD` meet (convex position in
the order `ABCD`), or they are collinear and the pair `{A, C}` separates
`{B, D}` (exactly one of `B, D` lies strictly between `A` and `C`). -/
def ClassicalInOrderOnCircleOrLine (A B C D : P) : Prop :=
  (Concyclic ({A, B, C, D} : Set P) ∧
      ∃ X : P, Wbtw ℝ A X C ∧ Wbtw ℝ B X D) ∨
  (Collinear ℝ ({A, B, C, D} : Set P) ∧ (Sbtw ℝ A B C ↔ ¬ Sbtw ℝ A D C))


open EulerIneq

/-! ## Classical statements (verbatim types) proved from the repository -/

/-- E1 (Euler). OI² = R² − 2Rr. -/
theorem cov_E1 (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.incenter ^ 2 =
      t.circumradius ^ 2 - 2 * t.circumradius * t.inradius := by
  rw [dist_comm]; exact l14_euler t

/-- E2 (Euler's inequality). R ≥ 2r. -/
theorem cov_E2a (t : Affine.Triangle ℝ P) :
    2 * t.inradius ≤ t.circumradius :=
  l14_euler_inequality t

/-- E2 (Euler's inequality). … with equality iff the triangle is equilateral. -/
theorem cov_E2b (t : Affine.Triangle ℝ P) :
    t.circumradius = 2 * t.inradius ↔ ClassicalEquilateral t := by
  unfold ClassicalEquilateral ClassicalSideA ClassicalSideB ClassicalSideC
  rw [eq_comm, l14_euler_inequality_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩

/-- E3. OI_A² = R² + 2R r_A. -/
theorem cov_E3 (t : Affine.Triangle ℝ P) (i : Fin 3) :
    dist t.circumcenter (t.excenter {i}) ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {i} := by
  rw [dist_comm]; exact l14_euler_excenter t i

/-- E4. OG² = R² − (a²+b²+c²)/9. -/
theorem cov_E4a (t : Affine.Triangle ℝ P) :
    dist t.circumcenter (ClassicalCentroid t) ^ 2 =
      t.circumradius ^ 2 - ClassicalSumSq t / 9 :=
  l14_dist_circumcenter_centroid_sq t

/-- E4. OH² = 9R² − (a²+b²+c²). -/
theorem cov_E4b (t : Affine.Triangle ℝ P) :
    dist t.circumcenter t.orthocenter ^ 2 =
      9 * t.circumradius ^ 2 - ClassicalSumSq t :=
  l14_dist_circumcenter_orthocenter_sq t

/-- E4. IG² = (s² + 5r² − 16Rr)/9. -/
theorem cov_E4c (t : Affine.Triangle ℝ P) :
    dist t.incenter (ClassicalCentroid t) ^ 2 =
      (ClassicalSemiperimeter t ^ 2 + 5 * t.inradius ^ 2
        - 16 * t.circumradius * t.inradius) / 9 :=
  l14_dist_incenter_centroid_sq t

/-- E5 (Fundamental inequality / Blundon's quartic). -/
theorem cov_E5 (t : Affine.Triangle ℝ P) :
    ClassicalSemiperimeter t ^ 4
      - 2 * (2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2)
        * ClassicalSemiperimeter t ^ 2
      + t.inradius * (4 * t.circumradius + t.inradius) ^ 3 ≤ 0 :=
  l14_fundamental_quartic t

/-- E6 (Gerretsen). 16Rr − 5r² ≤ s². -/
theorem cov_E6a (t : Affine.Triangle ℝ P) :
    16 * t.circumradius * t.inradius - 5 * t.inradius ^ 2 ≤
      ClassicalSemiperimeter t ^ 2 :=
  (l14_gerretsen t).1

/-- E6 (Gerretsen). s² ≤ 4R² + 4Rr + 3r². -/
theorem cov_E6b (t : Affine.Triangle ℝ P) :
    ClassicalSemiperimeter t ^ 2 ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2 :=
  (l14_gerretsen t).2

/-- E7 (Kooi). -/
theorem cov_E7 (t : Affine.Triangle ℝ P) :
    ClassicalSemiperimeter t ^ 2 ≤
      t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) :=
  l14_kooi t

/-- E8 (Weitzenböck). -/
theorem cov_E8a (t : Affine.Triangle ℝ P) :
    4 * √3 * ClassicalArea t ≤ ClassicalSumSq t :=
  l14_weitzenboeck t

/-- E8 (Weitzenböck). … equality iff equilateral. -/
theorem cov_E8b (t : Affine.Triangle ℝ P) :
    ClassicalSumSq t = 4 * √3 * ClassicalArea t ↔ ClassicalEquilateral t := by
  unfold ClassicalEquilateral ClassicalSideA ClassicalSideB ClassicalSideC
  rw [eq_comm]
  refine (l14_weitzenboeck_eq_iff t).trans ?_
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩

/-- E9 (Hadwiger–Finsler). -/
theorem cov_E9a (t : Affine.Triangle ℝ P) :
    4 * √3 * ClassicalArea t + (ClassicalSideA t - ClassicalSideB t) ^ 2
      + (ClassicalSideB t - ClassicalSideC t) ^ 2 + (ClassicalSideC t - ClassicalSideA t) ^ 2
      ≤ ClassicalSumSq t :=
  l14_hadwiger_finsler t

/-- E9 (Hadwiger–Finsler). … equality iff equilateral. -/
theorem cov_E9b (t : Affine.Triangle ℝ P) :
    ClassicalSumSq t = 4 * √3 * ClassicalArea t + (ClassicalSideA t - ClassicalSideB t) ^ 2
      + (ClassicalSideB t - ClassicalSideC t) ^ 2 + (ClassicalSideC t - ClassicalSideA t) ^ 2
      ↔ ClassicalEquilateral t := by
  unfold ClassicalEquilateral
  rw [eq_comm]
  refine (l14_hadwiger_finsler_eq_iff t).trans ?_
  unfold ClassicalSideA ClassicalSideB ClassicalSideC
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩

/-- E10 (Isoperimetric inequality for triangles). -/
theorem cov_E10a (t : Affine.Triangle ℝ P) :
    12 * √3 * ClassicalArea t ≤
      (ClassicalSideA t + ClassicalSideB t + ClassicalSideC t) ^ 2 :=
  l14_isoperimetric t

/-- E10. … equality iff equilateral. -/
theorem cov_E10b (t : Affine.Triangle ℝ P) :
    (ClassicalSideA t + ClassicalSideB t + ClassicalSideC t) ^ 2 = 12 * √3 * ClassicalArea t
      ↔ ClassicalEquilateral t := by
  rw [eq_comm]; exact l14_isoperimetric_eq_iff t

/-- E11 (Leibniz). -/
theorem cov_E11a (t : Affine.Triangle ℝ P) (X : P) :
    ClassicalDistSqSum t X =
      3 * dist X (ClassicalCentroid t) ^ 2 + ClassicalSumSq t / 3 :=
  l14_leibniz_relation t X

/-- E11 (Leibniz). … so the sum is minimised exactly at X = G. -/
theorem cov_E11b (t : Affine.Triangle ℝ P) :
    (∀ X : P, ClassicalDistSqSum t (ClassicalCentroid t) ≤ ClassicalDistSqSum t X) ∧
    (∀ X : P, ClassicalDistSqSum t X = ClassicalDistSqSum t (ClassicalCentroid t) →
      X = ClassicalCentroid t) := by
  have hG : ClassicalDistSqSum t (ClassicalCentroid t) = ClassicalSumSq t / 3 := by
    rw [cov_E11a, dist_self]; ring
  refine ⟨fun X => hG ▸ l14_leibniz_min t X, fun X hX => ?_⟩
  rw [hG] at hX
  exact (l14_leibniz_min_eq_iff t X).1 hX

/-- E12 (Neuberg–Pedoe). -/
theorem cov_E12a {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    [MetricSpace P'] [NormedAddTorsor V' P']
    (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    16 * ClassicalArea t * ClassicalArea t' ≤
      ClassicalSideA t' ^ 2 * (ClassicalSideB t ^ 2 + ClassicalSideC t ^ 2 - ClassicalSideA t ^ 2)
      + ClassicalSideB t' ^ 2 * (ClassicalSideC t ^ 2 + ClassicalSideA t ^ 2 - ClassicalSideB t ^ 2)
      + ClassicalSideC t' ^ 2 * (ClassicalSideA t ^ 2 + ClassicalSideB t ^ 2 - ClassicalSideC t ^ 2)
      :=
  l14_pedoe t t'

/-- E12 (Neuberg–Pedoe). … equality iff the triangles are similar. -/
theorem cov_E12b {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    [MetricSpace P'] [NormedAddTorsor V' P']
    (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P') :
    (ClassicalSideA t' ^ 2 * (ClassicalSideB t ^ 2 + ClassicalSideC t ^ 2 - ClassicalSideA t ^ 2)
      + ClassicalSideB t' ^ 2 * (ClassicalSideC t ^ 2 + ClassicalSideA t ^ 2 - ClassicalSideB t ^ 2)
      + ClassicalSideC t' ^ 2 * (ClassicalSideA t ^ 2 + ClassicalSideB t ^ 2 - ClassicalSideC t ^ 2)
      = 16 * ClassicalArea t * ClassicalArea t') ↔
    ∃ k : ℝ, 0 < k ∧ ClassicalSideA t' = k * ClassicalSideA t ∧
      ClassicalSideB t' = k * ClassicalSideB t ∧ ClassicalSideC t' = k * ClassicalSideC t :=
  l14_pedoe_eq_iff t t'

/-! ### P1 (Ptolemy's inequality)

The verbatim classical statement `classical_P1 (A B C D : P)` mentions neither `V` nor the
torsor structure, so Lean's variable inclusion drops `[NormedAddCommGroup V]
[InnerProductSpace ℝ V] [NormedAddTorsor V P]`: the statement is quantified over an
*arbitrary metric space* `P`.  In that generality it is false (`cov_P1_false`); the repository
proves exactly the Euclidean case (`cov_P1_part`). -/

include V in
/-- P1, Euclidean part (what the repository proves): the classical inequality for points of a
Euclidean affine space. -/
theorem cov_P1_part (A B C D : P) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D :=
  l14_ptolemy_inequality (V := V) A B C D

/-- The verbatim `classical_P1` (arbitrary metric space) is false: in `Fin 2 → ℝ` with the sup
metric, `A = (1,0)`, `B = (0,1)`, `C = (-1,0)`, `D = (0,-1)` give `AC·BD = 4 > 2 = AB·CD + BC·AD`. -/
theorem cov_P1_counterexample :
    ∃ A B C D : Fin 2 → ℝ,
      dist A B * dist C D + dist B C * dist A D < dist A C * dist B D := by
  refine ⟨![1, 0], ![0, 1], ![-1, 0], ![0, -1], ?_⟩
  have hAC : (2 : ℝ) ≤ dist (![1, 0] : Fin 2 → ℝ) ![-1, 0] := by
    have := dist_le_pi_dist (![1, 0] : Fin 2 → ℝ) ![-1, 0] 0
    simp [Real.dist_eq] at this; norm_num at this; linarith
  have hBD : (2 : ℝ) ≤ dist (![0, 1] : Fin 2 → ℝ) ![0, -1] := by
    have := dist_le_pi_dist (![0, 1] : Fin 2 → ℝ) ![0, -1] 1
    simp [Real.dist_eq] at this; norm_num at this; linarith
  have h1 : ∀ x y : Fin 2 → ℝ, (∀ i, |x i - y i| ≤ 1) → dist x y ≤ 1 := fun x y h =>
    (dist_pi_le_iff zero_le_one).2 fun i => by rw [Real.dist_eq]; exact h i
  have hAB := h1 ![1, 0] ![0, 1] (by simp [Fin.forall_fin_two])
  have hCD := h1 ![-1, 0] ![0, -1] (by simp [Fin.forall_fin_two])
  have hBC := h1 ![0, 1] ![-1, 0] (by simp [Fin.forall_fin_two])
  have hAD := h1 ![1, 0] ![0, -1] (by simp [Fin.forall_fin_two])
  have := dist_nonneg (x := (![1, 0] : Fin 2 → ℝ)) (y := ![0, 1])
  have := dist_nonneg (x := (![-1, 0] : Fin 2 → ℝ)) (y := ![0, -1])
  have := dist_nonneg (x := (![0, 1] : Fin 2 → ℝ)) (y := ![-1, 0])
  have := dist_nonneg (x := (![1, 0] : Fin 2 → ℝ)) (y := ![0, -1])
  nlinarith

/-- The verbatim statement of `classical_P1` (as Lean reads it, over an arbitrary metric
space) is refutable. -/
theorem cov_P1_false :
    ¬ ∀ (P : Type) [MetricSpace P] (A B C D : P),
      dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D := by
  intro h
  obtain ⟨A, B, C, D, hlt⟩ := cov_P1_counterexample
  exact absurd (h _ A B C D) (not_le.2 hlt)

end EulerIneq.Classical

end
