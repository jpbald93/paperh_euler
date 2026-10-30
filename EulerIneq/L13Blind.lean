import EulerIneq.Basic
import EulerIneq.Bridges
import EulerIneq.Main
import EulerIneq.Pedoe
import EulerIneq.Ptolemy
import EulerIneq.Kooi
import EulerIneq.Extremal
import EulerIneq.L14

/-!
# Layer 13: blind restatement (EulerIneq)

An independent writer, who saw only the plain-English text of the paper and not this library,
formalised its theorem statements in a separate file, `PaperHBlind.lean`
(sha256 begins e257c271479a928f). This file copies that file's `Blind*` definitions verbatim
(inside the namespace `EulerIneq.Blind`) and each blind statement verbatim as `blindK_stmt`.
For each statement it proves `rb_K` (library theorem → blind statement) and `br_K` (blind
statement → library theorem). Where the paper's statement was split by the blind writer into
several parts, the reverse direction is proved jointly (e.g. `br_456`). The `agree_*` lemmas
identify the blind definitions with the library's. No proof uses a library theorem other than
the one being compared and the definition-level agreement lemmas.
-/

namespace EulerIneq.Blind


/-!
Blind formalisation (Layer 13) of the theorem statements of the paper `paperh_blind.txt`.
Conventions (Section "Setting"): `A = t.points 0`, `B = t.points 1`, `C = t.points 2`,
`a = |BC|`, `b = |CA|`, `c = |AB|`, `O` circumcentre, `I` incentre, `G` centroid,
`H` orthocentre, `R` circumradius, `r` inradius.
-/

open EuclideanGeometry Real

noncomputable section

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Semiperimeter `s = (a+b+c)/2`. -/
def BlindSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
    dist (t.points 0) (t.points 1)) / 2

/-- Area `Δ = ½ |AB| |AC| sin ∠BAC`. -/
def BlindArea (t : Affine.Triangle ℝ P) : ℝ :=
  1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
    Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))

/-- Heron's polynomial `Γ(a,b,c) = ¼(2a²b²+2b²c²+2c²a²-a⁴-b⁴-c⁴)` (auxiliary definition). -/
def BlindHeronGamma (a b c : ℝ) : ℝ :=
  1 / 4 * (2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4)

/-- "Equilateral" is `|AB| = |BC| ∧ |BC| = |CA|`. -/
def BlindEquilateral (t : Affine.Triangle ℝ P) : Prop :=
  dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
    dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)

/-- `X` is in the closed triangle: `X = w₀A + w₁B + w₂C` with all `wᵢ ≥ 0`, `∑ wᵢ = 1`. -/
def BlindInClosedTriangle (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- `X` is strictly inside the triangle: as above with all `wᵢ > 0`. -/
def BlindStrictlyInside (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- Distance from `X` to the line `YZ`: `|X π_{YZ}(X)|`, `π_{YZ}` the orthogonal projection. -/
def BlindDistToLine (X Y Z : P) : ℝ :=
  dist X (EuclideanGeometry.orthogonalProjection line[ℝ, Y, Z] X : P)

/-! ### Oriented plane setting (Section "Fermat and Napoleon") -/

section Oriented

variable [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Orientation sign `σ ∈ {1,-1}` of `t`: `σ = 1` iff `ω(B-A, C-A) > 0`. -/
def BlindOrientationSign (t : Affine.Triangle ℝ P) : ℝ :=
  if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then 1 else -1

/-- Outer apex on `XY`: the image of `Y` under the rotation about `X` by `-σπ/3`. -/
def BlindOuterApex (t : Affine.Triangle ℝ P) (X Y : P) : P :=
  o.rotation ((-(BlindOrientationSign o t * π / 3) : ℝ) : Real.Angle) (Y -ᵥ X) +ᵥ X

/-- `A'`: outer apex on `BC`. -/
def BlindApexA (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 1) (t.points 2)
/-- `B'`: outer apex on `CA`. -/
def BlindApexB (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 2) (t.points 0)
/-- `C'`: outer apex on `AB`. -/
def BlindApexC (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 0) (t.points 1)

/-- `N_A`: centroid of `B C A'`. -/
def BlindNapoleonA (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 1, t.points 2, BlindApexA o t]
/-- `N_B`: centroid of `C A B'`. -/
def BlindNapoleonB (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 2, t.points 0, BlindApexB o t]
/-- `N_C`: centroid of `A B C'`. -/
def BlindNapoleonC (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 0, t.points 1, BlindApexC o t]

end Oriented

end

universe u v u' v'

open EuclideanGeometry Real

noncomputable section

/-! ## Blind statements (verbatim) -/

def blind1_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    dist t.incenter t.circumcenter ^ 2 =
      t.circumradius ^ 2 - 2 * t.circumradius * t.inradius

def blind2_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    2 * t.inradius ≤ t.circumradius

def blind3_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    2 * t.inradius = t.circumradius ↔ BlindEquilateral t

def blind4_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    dist (t.excenter {0}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {0}

def blind5_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    dist (t.excenter {1}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {1}

def blind6_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    dist (t.excenter {2}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {2}

def blind7_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    dist t.circumcenter (Finset.univ.centroid ℝ t.points) ^ 2 =
      t.circumradius ^ 2 - 1 / 9 * (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2)

def blind8_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    dist t.circumcenter t.orthocenter ^ 2 =
      9 * t.circumradius ^ 2 - (dist (t.points 1) (t.points 2) ^ 2 +
        dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2)

def blind9_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    dist t.incenter (Finset.univ.centroid ℝ t.points) ^ 2 =
      1 / 9 * (BlindSemiperimeter t ^ 2 + 5 * t.inradius ^ 2 -
        16 * t.circumradius * t.inradius)

def blind10_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    BlindSemiperimeter t ^ 4 -
      2 * (2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2) *
        BlindSemiperimeter t ^ 2 +
      t.inradius * (4 * t.circumradius + t.inradius) ^ 3 ≤ 0

def blind11_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    16 * t.circumradius * t.inradius - 5 * t.inradius ^ 2 ≤ BlindSemiperimeter t ^ 2

def blind12_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    BlindSemiperimeter t ^ 2 ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2

def blind13_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    0 ≤ (t.circumradius - t.inradius) * (t.circumradius - 2 * t.inradius)

def blind14_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    BlindSemiperimeter t ^ 2 ≤
      t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius))

def blind15_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    t.circumradius * (4 * t.circumradius + t.inradius) ^ 2 /
        (2 * (2 * t.circumradius - t.inradius)) ≤
      4 * t.circumradius ^ 2 + 4 * t.circumradius * t.inradius + 3 * t.inradius ^ 2

def blind16_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    4 * √3 * BlindArea t ≤ dist (t.points 1) (t.points 2) ^ 2 +
      dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2

def blind17_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    4 * √3 * BlindArea t = dist (t.points 1) (t.points 2) ^ 2 +
      dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 ↔
      BlindEquilateral t

def blind18_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    4 * √3 * BlindArea t +
        (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
        (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 ≤
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2

def blind19_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    4 * √3 * BlindArea t +
        (dist (t.points 1) (t.points 2) - dist (t.points 2) (t.points 0)) ^ 2 +
        (dist (t.points 2) (t.points 0) - dist (t.points 0) (t.points 1)) ^ 2 +
        (dist (t.points 0) (t.points 1) - dist (t.points 1) (t.points 2)) ^ 2 =
      dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2 ↔ BlindEquilateral t

def blind20_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    12 * √3 * BlindArea t ≤ (dist (t.points 1) (t.points 2) +
      dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) ^ 2

def blind21_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P),
    12 * √3 * BlindArea t = (dist (t.points 1) (t.points 2) +
      dist (t.points 2) (t.points 0) + dist (t.points 0) (t.points 1)) ^ 2 ↔
      BlindEquilateral t

def blind22_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P) (X : P),
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
      3 * dist X (Finset.univ.centroid ℝ t.points) ^ 2 +
        1 / 3 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2)

def blind23_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P) (X : P),
    1 / 3 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
        dist (t.points 0) (t.points 1) ^ 2) ≤
      dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2

def blind24_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (t : Affine.Triangle ℝ P) (X : P),
    dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2 =
        1 / 3 * (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2) ↔
      X = Finset.univ.centroid ℝ t.points

def blind25_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {V' : Type u'} {P' : Type v'} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    [MetricSpace P'] [NormedAddTorsor V' P'],
  ∀ (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P'),
    16 * BlindArea t * BlindArea t' ≤
      dist (t'.points 1) (t'.points 2) ^ 2 *
          (dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 -
            dist (t.points 1) (t.points 2) ^ 2) +
        dist (t'.points 2) (t'.points 0) ^ 2 *
          (dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 -
            dist (t.points 2) (t.points 0) ^ 2) +
        dist (t'.points 0) (t'.points 1) ^ 2 *
          (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 -
            dist (t.points 0) (t.points 1) ^ 2)

def blind26_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {V' : Type u'} {P' : Type v'} [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
    [MetricSpace P'] [NormedAddTorsor V' P'],
  ∀ (t : Affine.Triangle ℝ P) (t' : Affine.Triangle ℝ P'),
    dist (t'.points 1) (t'.points 2) ^ 2 *
          (dist (t.points 2) (t.points 0) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 -
            dist (t.points 1) (t.points 2) ^ 2) +
        dist (t'.points 2) (t'.points 0) ^ 2 *
          (dist (t.points 0) (t.points 1) ^ 2 + dist (t.points 1) (t.points 2) ^ 2 -
            dist (t.points 2) (t.points 0) ^ 2) +
        dist (t'.points 0) (t'.points 1) ^ 2 *
          (dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 2) (t.points 0) ^ 2 -
            dist (t.points 0) (t.points 1) ^ 2) = 16 * BlindArea t * BlindArea t' ↔
      ∃ k : ℝ, 0 < k ∧
        dist (t'.points 1) (t'.points 2) = k * dist (t.points 1) (t.points 2) ∧
        dist (t'.points 2) (t'.points 0) = k * dist (t.points 2) (t.points 0) ∧
        dist (t'.points 0) (t'.points 1) = k * dist (t.points 0) (t.points 1)

def blind27_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P],
  ∀ (A B C D : P),
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D

/-! ## Agreement lemmas (Blind notions ↔ repository notions) -/

section Agreement

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem agree_area (t : Affine.Triangle ℝ P) : BlindArea t = EulerIneq.area t := rfl

theorem agree_semiperimeter (t : Affine.Triangle ℝ P) :
    BlindSemiperimeter t = EulerIneq.semiperimeter t := rfl

theorem agree_centroid (t : Affine.Triangle ℝ P) :
    Finset.univ.centroid ℝ t.points = t.centroid := rfl

theorem agree_equilateral (t : Affine.Triangle ℝ P) :
    BlindEquilateral t ↔ dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
      dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) := Iff.rfl

/-- The repository's `isoperimetric_eq_iff` states equilaterality as `a = b ∧ b = c`. -/
theorem agree_equilateral' (t : Affine.Triangle ℝ P) :
    BlindEquilateral t ↔ dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0) ∧
      dist (t.points 2) (t.points 0) = dist (t.points 0) (t.points 1) := by
  unfold BlindEquilateral
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [h1, h2]⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rw [h1, h2], h1⟩

end Agreement

/-! ## Pairs -/

-- 1 euler
theorem rb_1 : (type_of% @EulerIneq.euler.{u, v}) → blind1_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => h t
theorem br_1 : blind1_stmt.{u, v} → (type_of% @EulerIneq.euler.{u, v}) :=
  fun h _ _ _ _ _ _ t => h t

-- 2 euler_inequality
theorem rb_2 : (type_of% @EulerIneq.euler_inequality.{u, v}) → blind2_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => h t
theorem br_2 : blind2_stmt.{u, v} → (type_of% @EulerIneq.euler_inequality.{u, v}) :=
  fun h _ _ _ _ _ _ t => h t

-- 3 euler_inequality_eq_iff
theorem rb_3 : (type_of% @EulerIneq.euler_inequality_eq_iff.{u, v}) → blind3_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => (h t).trans (agree_equilateral t).symm
theorem br_3 : blind3_stmt.{u, v} → (type_of% @EulerIneq.euler_inequality_eq_iff.{u, v}) :=
  fun h _ _ _ _ _ _ t => (h t).trans (agree_equilateral t)

-- 4,5,6 euler_excenter (i = 0,1,2).  R→B: specialise i.  B→R: needs all three blind statements.
theorem rb_4 : (type_of% @EulerIneq.euler_excenter.{u, v}) → blind4_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => h t 0
theorem rb_5 : (type_of% @EulerIneq.euler_excenter.{u, v}) → blind5_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => h t 1
theorem rb_6 : (type_of% @EulerIneq.euler_excenter.{u, v}) → blind6_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => h t 2
theorem br_456 : blind4_stmt.{u, v} ∧ blind5_stmt.{u, v} ∧ blind6_stmt.{u, v} →
    (type_of% @EulerIneq.euler_excenter.{u, v}) := by
  rintro ⟨h4, h5, h6⟩ V P _ _ _ _ t i
  fin_cases i
  · exact h4 t
  · exact h5 t
  · exact h6 t
/-- Single-statement B→R in the specialised form: blind_K is exactly `euler_excenter` at `i`. -/
theorem br_4 : blind4_stmt.{u, v} → ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
    dist (t.excenter {0}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {0} :=
  fun h _ _ _ _ _ _ t => h t
theorem br_5 : blind5_stmt.{u, v} → ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
    dist (t.excenter {1}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {1} :=
  fun h _ _ _ _ _ _ t => h t
theorem br_6 : blind6_stmt.{u, v} → ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (t : Affine.Triangle ℝ P),
    dist (t.excenter {2}) t.circumcenter ^ 2 =
      t.circumradius ^ 2 + 2 * t.circumradius * t.exradius {2} :=
  fun h _ _ _ _ _ _ t => h t

-- 7 dist_circumcenter_centroid_sq
theorem rb_7 : (type_of% @EulerIneq.dist_circumcenter_centroid_sq.{u, v}) → blind7_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_centroid, h t]; ring
theorem br_7 : blind7_stmt.{u, v} → (type_of% @EulerIneq.dist_circumcenter_centroid_sq.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_centroid] at this
  rw [this]; ring

-- 8 dist_circumcenter_orthocenter_sq
theorem rb_8 : (type_of% @EulerIneq.dist_circumcenter_orthocenter_sq.{u, v}) →
    blind8_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => h t
theorem br_8 : blind8_stmt.{u, v} →
    (type_of% @EulerIneq.dist_circumcenter_orthocenter_sq.{u, v}) :=
  fun h _ _ _ _ _ _ t => h t

-- 9 dist_incenter_centroid_sq
theorem rb_9 : (type_of% @EulerIneq.dist_incenter_centroid_sq.{u, v}) → blind9_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_centroid, agree_semiperimeter, h t]; ring
theorem br_9 : blind9_stmt.{u, v} → (type_of% @EulerIneq.dist_incenter_centroid_sq.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_centroid, agree_semiperimeter] at this
  rw [this]; ring

-- 10 fundamental_quartic
theorem rb_10 : (type_of% @EulerIneq.fundamental_quartic.{u, v}) → blind10_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_semiperimeter]; exact h t
theorem br_10 : blind10_stmt.{u, v} → (type_of% @EulerIneq.fundamental_quartic.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_semiperimeter] at this; exact this

-- 11, 12 gerretsen (two conjuncts).  R→B: projections.  B→R: needs both.
theorem rb_11 : (type_of% @EulerIneq.gerretsen.{u, v}) → blind11_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_semiperimeter]; exact (h t).1
theorem rb_12 : (type_of% @EulerIneq.gerretsen.{u, v}) → blind12_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_semiperimeter]; exact (h t).2
theorem br_11_12 : blind11_stmt.{u, v} ∧ blind12_stmt.{u, v} →
    (type_of% @EulerIneq.gerretsen.{u, v}) := by
  rintro ⟨h1, h2⟩ V P _ _ _ _ t
  have e1 := h1 t
  have e2 := h2 t
  rw [agree_semiperimeter] at e1 e2
  exact ⟨e1, e2⟩

-- 13 gerretsen_cross_check
theorem rb_13 : (type_of% @EulerIneq.gerretsen_cross_check.{u, v}) → blind13_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => h t
theorem br_13 : blind13_stmt.{u, v} → (type_of% @EulerIneq.gerretsen_cross_check.{u, v}) :=
  fun h _ _ _ _ _ _ t => h t

-- 14 kooi
theorem rb_14 : (type_of% @EulerIneq.kooi.{u, v}) → blind14_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_semiperimeter]; exact h t
theorem br_14 : blind14_stmt.{u, v} → (type_of% @EulerIneq.kooi.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_semiperimeter] at this; exact this

-- 15 kooi_le_gerretsen
theorem rb_15 : (type_of% @EulerIneq.kooi_le_gerretsen.{u, v}) → blind15_stmt.{u, v} :=
  fun h _ _ _ _ _ _ t => h t
theorem br_15 : blind15_stmt.{u, v} → (type_of% @EulerIneq.kooi_le_gerretsen.{u, v}) :=
  fun h _ _ _ _ _ _ t => h t

-- 16 weitzenboeck
theorem rb_16 : (type_of% @EulerIneq.weitzenboeck.{u, v}) → blind16_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_area]; exact h t
theorem br_16 : blind16_stmt.{u, v} → (type_of% @EulerIneq.weitzenboeck.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_area] at this; exact this

-- 17 weitzenboeck_eq_iff
theorem rb_17 : (type_of% @EulerIneq.weitzenboeck_eq_iff.{u, v}) → blind17_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_area, agree_equilateral]; exact h t
theorem br_17 : blind17_stmt.{u, v} → (type_of% @EulerIneq.weitzenboeck_eq_iff.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_area, agree_equilateral] at this; exact this

-- 18 hadwiger_finsler
theorem rb_18 : (type_of% @EulerIneq.hadwiger_finsler.{u, v}) → blind18_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_area]; exact h t
theorem br_18 : blind18_stmt.{u, v} → (type_of% @EulerIneq.hadwiger_finsler.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_area] at this; exact this

-- 19 hadwiger_finsler_eq_iff
theorem rb_19 : (type_of% @EulerIneq.hadwiger_finsler_eq_iff.{u, v}) → blind19_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_area, agree_equilateral]; exact h t
theorem br_19 : blind19_stmt.{u, v} → (type_of% @EulerIneq.hadwiger_finsler_eq_iff.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_area, agree_equilateral] at this; exact this

-- 20 isoperimetric
theorem rb_20 : (type_of% @EulerIneq.isoperimetric.{u, v}) → blind20_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_area]; exact h t
theorem br_20 : blind20_stmt.{u, v} → (type_of% @EulerIneq.isoperimetric.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_area] at this; exact this

-- 21 isoperimetric_eq_iff (repository states equilaterality as a = b ∧ b = c)
theorem rb_21 : (type_of% @EulerIneq.isoperimetric_eq_iff.{u, v}) → blind21_stmt.{u, v} := by
  intro h V P _ _ _ _ t
  rw [agree_area, agree_equilateral']; exact h t
theorem br_21 : blind21_stmt.{u, v} → (type_of% @EulerIneq.isoperimetric_eq_iff.{u, v}) := by
  intro h V P _ _ _ _ t
  have := h t
  rw [agree_area, agree_equilateral'] at this; exact this

-- 22 leibniz_relation
theorem rb_22 : (type_of% @EulerIneq.leibniz_relation.{u, v}) → blind22_stmt.{u, v} := by
  intro h V P _ _ _ _ t X
  rw [agree_centroid, h t X]; ring
theorem br_22 : blind22_stmt.{u, v} → (type_of% @EulerIneq.leibniz_relation.{u, v}) := by
  intro h V P _ _ _ _ t X
  rw [h t X, agree_centroid]; ring

-- 23 leibniz_min
theorem rb_23 : (type_of% @EulerIneq.leibniz_min.{u, v}) → blind23_stmt.{u, v} := by
  intro h V P _ _ _ _ t X
  have := h t X
  linarith
theorem br_23 : blind23_stmt.{u, v} → (type_of% @EulerIneq.leibniz_min.{u, v}) := by
  intro h V P _ _ _ _ t X
  have := h t X
  linarith

-- 24 leibniz_min_eq_iff
theorem rb_24 : (type_of% @EulerIneq.leibniz_min_eq_iff.{u, v}) → blind24_stmt.{u, v} := by
  intro h V P _ _ _ _ t X
  rw [agree_centroid, ← h t X]
  constructor <;> intro e <;> linarith
theorem br_24 : blind24_stmt.{u, v} → (type_of% @EulerIneq.leibniz_min_eq_iff.{u, v}) := by
  intro h V P _ _ _ _ t X
  rw [← agree_centroid, ← h t X]
  constructor <;> intro e <;> linarith

-- 25 pedoe
theorem rb_25 : (type_of% @EulerIneq.pedoe.{u, v, u', v'}) → blind25_stmt.{u, v, u', v'} := by
  intro h V P _ _ _ _ V' P' _ _ _ _ t t'
  rw [agree_area, agree_area]; exact h t t'
theorem br_25 : blind25_stmt.{u, v, u', v'} → (type_of% @EulerIneq.pedoe.{u, v, u', v'}) := by
  intro h V P _ _ _ _ V' P' _ _ _ _ t t'
  have := h t t'
  rw [agree_area, agree_area] at this; exact this

-- 26 pedoe_eq_iff
theorem rb_26 : (type_of% @EulerIneq.pedoe_eq_iff.{u, v, u', v'}) → blind26_stmt.{u, v, u', v'} := by
  intro h V P _ _ _ _ V' P' _ _ _ _ t t'
  rw [agree_area, agree_area]; exact h t t'
theorem br_26 : blind26_stmt.{u, v, u', v'} → (type_of% @EulerIneq.pedoe_eq_iff.{u, v, u', v'}) := by
  intro h V P _ _ _ _ V' P' _ _ _ _ t t'
  have := h t t'
  rw [agree_area, agree_area] at this; exact this

-- 27 ptolemy_inequality
theorem rb_27 : (type_of% @EulerIneq.ptolemy_inequality.{u, v}) → blind27_stmt.{u, v} :=
  fun h _ _ _ _ _ _ A B C D => h A B C D
theorem br_27 : blind27_stmt.{u, v} → (type_of% @EulerIneq.ptolemy_inequality.{u, v}) :=
  fun h _ _ _ _ _ _ A B C D => h A B C D

end

end EulerIneq.Blind
