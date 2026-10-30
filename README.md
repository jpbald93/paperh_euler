# Euler's theorem and the inequalities around it — Lean 4 / Mathlib

**Paper:** J. Bald, *Classical triangle inequalities and the Fermat–Napoleon configuration in Lean 4* (2026), Zenodo, https://doi.org/10.5281/zenodo.23813097. Companion repositories: https://github.com/jpbald93/paperh_fermat, https://github.com/jpbald93/paperh_mordell.

**Toolchain:** Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (see `lake-manifest.json`).
**Check:** `lake build && bash gate.sh`, then `bash tests/tamper.sh`. **Licence:** Apache-2.0.

The setting is any real inner
product space (no dimension hypothesis). The triangle is `t : Affine.Triangle ℝ P` with vertices
`A, B, C = t.points 0, 1, 2` and sides `a = BC`, `b = CA`, `c = AB` (as `dist`). `R`, `r`, `O`, `I`,
`Iᵢ`, `rᵢ`, `G`, `H` are Mathlib's `t.circumradius`, `t.inradius`, `t.circumcenter`, `t.incenter`,
`t.excenter {i}`, `t.exradius {i}`, `t.centroid` and `t.orthocenter`. `Δ = EulerIneq.area t` and
`s = EulerIneq.semiperimeter t` are defined in `EulerIneq/Basic.lean`.

| Statement (plain English) | Lean name | Location |
|---|---|---|
| Euler: `OI² = R² − 2Rr` | `EulerIneq.euler` | EulerIneq/Main.lean:22 |
| Euler's inequality `2r ≤ R` | `EulerIneq.euler_inequality` | EulerIneq/Main.lean:73 |
| `2r = R` iff the triangle is equilateral | `EulerIneq.euler_inequality_eq_iff` | EulerIneq/Main.lean:91 |
| Excircle Euler: `OIᵢ² = R² + 2R rᵢ` for each `i` | `EulerIneq.euler_excenter` | EulerIneq/Main.lean:117 |
| Hadwiger–Finsler: `a²+b²+c² ≥ 4√3Δ + (a−b)²+(b−c)²+(c−a)²` | `EulerIneq.hadwiger_finsler` | EulerIneq/Main.lean:183 |
| … with equality iff the triangle is equilateral | `EulerIneq.hadwiger_finsler_eq_iff` | EulerIneq/Main.lean:203 |
| Weitzenböck: `a²+b²+c² ≥ 4√3Δ` | `EulerIneq.weitzenboeck` | EulerIneq/Main.lean:236 |
| … with equality iff the triangle is equilateral | `EulerIneq.weitzenboeck_eq_iff` | EulerIneq/Main.lean:246 |
| Gerretsen: `16Rr − 5r² ≤ s² ≤ 4R² + 4Rr + 3r²` | `EulerIneq.gerretsen` | EulerIneq/Main.lean:329 |
| `OG² = R² − (a²+b²+c²)/9` | `EulerIneq.dist_circumcenter_centroid_sq` | EulerIneq/Main.lean:349 |
| `OH² = 9R² − (a²+b²+c²)` | `EulerIneq.dist_circumcenter_orthocenter_sq` | EulerIneq/Main.lean:358 |
| `IG² = (s² + 5r² − 16Rr)/9` | `EulerIneq.dist_incenter_centroid_sq` | EulerIneq/Main.lean:370 |

The proofs rest on bridges in `EulerIneq/Bridges.lean`:
* Mathlib's incentre and excentres are affine combinations with weights `(±a : ±b : ±c)`.
* `r = 2Δ/(a+b+c)` and `rᵢ = 2Δ/(−aᵢ+aⱼ+aₖ)`.
* `4RΔ = abc`, and Heron's formula.
* The barycentric distance formula `|ΣwᵢPᵢ − O|² = R² − Σ_{i<j} wᵢwⱼ|PᵢPⱼ|²` (`Σwᵢ = 1`).

The inequalities then reduce to explicit polynomial identities. Gerretsen comes from the fundamental
quartic, using the polynomial certificate of the Blundon development.

## Group H3: Pedoe, Ptolemy, Kooi and the extremal problems

| Statement (plain English) | Lean name | Location |
|---|---|---|
| Neuberg–Pedoe: for triangles `t` in `P` and `t'` in `P'`, `a'²(b²+c²−a²) + b'²(c²+a²−b²) + c'²(a²+b²−c²) ≥ 16ΔΔ'` | `EulerIneq.pedoe` | EulerIneq/Pedoe.lean:43 |
| … with equality iff the sides are proportional (`a' = ka`, `b' = kb`, `c' = kc`, `k > 0`) | `EulerIneq.pedoe_eq_iff` | EulerIneq/Pedoe.lean:75 |
| The sum-of-squares certificate behind Pedoe | `EulerIneq.pedoe_identity` | EulerIneq/Pedoe.lean:28 |
| Ptolemy's inequality `AC·BD ≤ AB·CD + BC·AD` for any four points (this is Mathlib's `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`, restated) | `EulerIneq.ptolemy_inequality` | EulerIneq/Ptolemy.lean:20 |
| Kooi: `s² ≤ R(4R+r)² / (2(2R−r))` | `EulerIneq.kooi` | EulerIneq/Kooi.lean:46 |
| Kooi's bound is at most Gerretsen's upper bound | `EulerIneq.kooi_le_gerretsen` | EulerIneq/Kooi.lean:54 |
| Real-number core of Kooi (from the fundamental quartic) | `EulerIneq.kooi_of_quartic` | EulerIneq/Kooi.lean:22 |
| Leibniz: `XA²+XB²+XC² = 3XG² + (a²+b²+c²)/3` | `EulerIneq.leibniz_relation` | EulerIneq/Extremal.lean:23 |
| Leibniz minimum: `XA²+XB²+XC² ≥ (a²+b²+c²)/3` | `EulerIneq.leibniz_min` | EulerIneq/Extremal.lean:35 |
| … with equality iff `X = t.centroid` | `EulerIneq.leibniz_min_eq_iff` | EulerIneq/Extremal.lean:42 |
| AM–GM for three positive reals | `EulerIneq.amgm_three` | EulerIneq/Extremal.lean:56 |
| Isoperimetric inequality for triangles `12√3Δ ≤ (a+b+c)²` | `EulerIneq.isoperimetric` | EulerIneq/Extremal.lean:65 |
| … with equality iff the triangle is equilateral | `EulerIneq.isoperimetric_eq_iff` | EulerIneq/Extremal.lean:93 |
| Cross-check: Gerretsen's two bounds give `(R−r)(R−2r) ≥ 0` | `EulerIneq.gerretsen_cross_check` | EulerIneq/Extremal.lean:153 |

`scripts/numerics_h3.py` is the numerical check for H3, and `scripts/certs_h3.py` checks the Pedoe and
Kooi certificates with sympy.

## Layer 13 (blind restatement)

An independent writer, who saw only the plain-English statements of the paper and not this library,
wrote the theorem statements in Lean on their own (`PaperHBlind.lean`, sha256 beginning
`e257c271479a928f`). `EulerIneq/L13Blind.lean` (namespace `EulerIneq.Blind`) copies the writer's
definitions and statements 1–27 verbatim. For each one it proves both directions against the library
theorem: `rb_K` (library → blind) and `br_K` (blind → library).

* All 27 blind statements are proved equivalent to the library in both directions (5 of them jointly).
  The writer split two library theorems into parts: the excentre version of Euler's theorem (one
  statement per excentre, 4–6) and Gerretsen's two bounds (11–12). Each part follows from the library
  theorem, and together the parts give it back (`br_456`, `br_11_12`).
* The agreement lemmas (`agree_area`, `agree_semiperimeter`, `agree_centroid`, `agree_equilateral`,
  `agree_equilateral'`) show that the writer's area, semiperimeter, centroid and "equilateral" are the
  library's, either by definition or by a trivial rewrite.
* No difference in meaning was found.

## Layer 14 (Mathlib-only restatements and witnesses)

`EulerIneq/L14.lean` restates every main theorem with the library's own definitions unfolded (area as
½·AB·AC·sin A, semiperimeter as (a+b+c)/2). The statements therefore mention only Mathlib notions.
All 23 restatements (`l14_*`) are proved from the library. Four witness theorems (`l14w_*`) show on
explicit triangles that the hypotheses can be satisfied and that the inequalities are not trivially
equalities: the 3-4-5 triangle (R = 5/2, r = 1), a non-similar second triangle for Pedoe, a point
other than the centroid for Leibniz, and four points in non-cyclic order for Ptolemy.

## Layer 15 (classical statements)

An independent writer also stated the classical theorems in textbook form, using only Mathlib and a few
elementary definitions (`PaperHClassical.lean`, sha256 beginning `0ac73f94ec9efdb8`).
`EulerIneq/L15Classical.lean` (namespace `EulerIneq.Classical`) copies these definitions verbatim and
restates each assigned classical statement with its verbatim type as `cov_<name>`.

* All 21 classical statements E1–E12 (Euler, the excentre version, the centre distances, the
  fundamental quartic, Gerretsen, Kooi, Weitzenböck, Hadwiger–Finsler, the isoperimetric inequality,
  Leibniz, Neuberg–Pedoe, with their equality cases) are proved from the library.
* P1 (Ptolemy's inequality): the classical file has a slip. As written, the statement never mentions
  the vector space, so Lean drops the Euclidean structure and reads it as a claim about an arbitrary
  metric space, where it is false. `cov_P1_counterexample` gives four points of the plane with the
  maximum metric where it fails, and `cov_P1_false` refutes the statement as written.
  `cov_P1_part` proves the intended Euclidean statement.
* NEW PROOFS: none were needed. Every classical statement follows directly from a library theorem.

## Build and check
Mathlib is expected under `.lake/packages` (do not run `lake update`).
```
lake build                 # build the library
bash gate.sh               # forbidden-token scan + build + axiom report for every declaration
bash tests/tamper.sh       # gate must reject 9 planted defects
```
Expected output: `PASS (243 declarations, standard axioms only)` and `ALL TAMPERING TESTS REJECTED`.
`scripts/numerics.py` (mpmath) is the numerical sanity check of every statement.
`scripts/ig_cofactor.py` derives the cofactor used for `IG²`.
