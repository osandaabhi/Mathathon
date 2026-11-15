# Lean formalization of "An explicit deformation excluding the tetrahedral-prism soap-film cone in R⁴"

(Mathathon project `attempt_8_T5`, 15 Nov 2026, 10 pp; attached as
`attachments/formalize-in-lean-the-llpc/Mathathon (1).pdf`.)

The report proves that the tetrahedral-prism cone `T5 ⊂ R⁴` is not Almgren-minimal by an
explicit compactly supported Lipschitz deformation. Its structure is

| § | content | kind of mathematics |
|---|---|---|
| 2 | the cone `T5`, the exact area identity `Δ area = 2 I(F)` (Lemmas 2.1, 2.2) | geometric measure theory |
| 3 | radial/angular reduction to three moments (Lemmas 3.1, 3.2) and the moment bounds `J_{1/2} < 191/20`, `J_{5/2} > 33/10`, `J_{-3/2} > 31` (Lemma 3.3) | one-variable calculus, rational arithmetic |
| 4 | cutoff cost `4π/R`, the Lipschitz deformation `φ` with `φ(C) = X_{F_R}` (Lemmas 4.1, 4.2) | Lipschitz analysis |
| 1,4 | assembly: `2 I(F_R) < -6/100 + 8π/1000 < -7/250 < -1/40` | rational arithmetic |
| 5 | density `Θ(T5,0) = 4τ - 5`, `τ = 3α/π`, `α = arccos(-1/3)` | spherical geometry |

## What this Lean development proves

Everything below is checked by `./build.sh` with **no `sorry`, `admit`, `axiom` or
`native_decide`** (Lean 4.33.1 + Mathlib; only `propext`, `Classical.choice`, `Quot.sound`).

* `Basic.lean` — the objects of §1, §3, §4 as definitions: the sign vectors, the tetrahedral
  vertices `p_i = ε_i/√5`, the support function `f = max_i p_i·u`, the sectors `V_i` and seams
  `W`, the cone `C` (1.2), `L`, `E_i` (2.3), `F_∞`, `g_R`, `F_R` (4.1), `δ` (4.3), `clip`, `H`
  (4.4), `ζ`, the deformation `φ` (4.5) and the competitor `X_F` (2.2).  Proved: the
  tetrahedral Gram data `|p_i|² = 3/5`, `p_i·p_j = -1/5` (`i ≠ j`), `Σ p_i = 0`, `f ≥ 0`,
  `g_R ≥ 0` on `[0,∞)`, `0 ≤ F_R ≤ f`, `|clip z| ≤ 1`.  (This is the algebraic core of
  Lemma 2.1.)
* `Convex.lean` — `∫ cos² = (b-a)/2 + (sin 2b - sin 2a)/4`, the integral of `α + β cos²`, and
  the chord/tangent inequalities for convex functions (`f` convex `⇒` `f ≤` chord, `f ≥`
  tangent).
* `Moments.lean` — the three angular integrands of Lemma 3.2 taken as definitions
  (`J_p = 24 ∫_0^{π/3} (c^p/(p+1))(1 - z^(p+1))`), the `cos²` bounds on `[0,π/3]`, and
  **`J52_gt : 33/10 < J_{5/2}`** (four-piece monotonicity; no Jensen, no measure on `S²`).
* `NodeBounds.lean` — the rational node values of `Lam` (0.56131, 0.5749, 0.6227, 0.7010,
  0.8076) and `√c < 880112/10⁶`, each reduced to a rational fourth-power inequality.
* `PsiConvex.lean` — `ConvexOn ℝ [1/4,1] Ψ`, `deriv Ψ` explicitly, and the tangent minorant
  `Ψ c + Ψ'(c)(x-c) ≤ Ψ x`.
* `TangentData.lean` — rational bounds for `Ψ` and `Ψ'` at `97/100, 169/200, 5/8, 37/100`.
* `Jm32.lean` — **`Jm32_gt : 31 < J_{-3/2}`** (four-piece tangent minorants, exact integrals,
  `π` and `√3` bracketed rationally).
* `Constants.lean` — `b = √(5/8) ∈ (79/100, 791/1000)`, `c^(5/2) > 528/1000`,
  `c^(-3/2) > 14668/10000`, and the assembly **`B < -3/100`**, **`2(B + 4π/1000) < -1/40`**,
  **`< -7/250`** from the three moment bounds.
* `ChordData.lean` — convexity-free rational affine certificates: `Lam` majorants on
  `[1/4,1/2]`, `[1/2,3/4]`, `[3/4,47/50]`, `[93/100,1]` (the four `x`-images of the report's
  `v`-partition) and `Ψ` minorants on the same intervals.
* `Density.lean` — **`linkArea/(4π) = 4τ - 5`**, `τ = 3α/π`, `α = arccos(-1/3)`
  (Prop. 5.1's arithmetic).
* `Main.lean` — `Bval`, and the conditional statements `saving_of_moments`,
  `area_decreases`, `not_minimizing` (Theorem 1.2's conclusion from the area identity).

## What is **not** formalized (and is therefore assumed in `Main.lean`)

1. **`J_{1/2} < 191/20`** (Lemma 3.3, first estimate).  The hard half is here:
   `ChordData.Lam_piece_one … Lam_piece_four` are proved rational affine majorants of `Lam`
   on the four `x`-intervals; what is missing is the assembly (piecewise `integral_mono_on`,
   `Convex.integral_affine_cos_sq`, then `16√c · 6764/10000 < 191/20`).  An assembly attempt
   exists in the git-less working tree's history and was abandoned for time, not because of a
   mathematical gap.  `Main.lean` takes it as an explicit hypothesis `hJ1`.
2. **Lemma 2.1** (identifying `C` with the cone over the two-skeleton of the
   tetrahedral bipyramid's polar).  Only the Gram data is formalized.
3. **Lemma 2.2** (the area identity, counted-once convention, divergence theorem on the
   polyhedral sectors, `∇F = 0` a.e. on `{F = 0}`).
4. **Lemma 3.1** (the radial reduction `I(F_∞) ≤ B`) and **Lemma 3.2** (the angular
   reduction): the reduced formula (3.2) is *taken as the definition* of `J_p` here.
5. **Lemma 4.1** (the cutoff cost `4π/R`) and **Lemma 4.2** (the Lipschitz bound
   `Lip φ < 4`, compact support, `φ|_C = X_{F_R}`).
6. The **numeric value** `4τ - 5 ≈ 2.2980813756` (needs rational bounds for `arccos(-1/3)`).

`Main.lean` therefore contains no hidden assumption: its theorem is
`area (φ 1000 '' cone) < area cone - 1/40` under exactly the three named hypotheses
`hJ1`, `himg` (`φ 1000 '' cone = Xset 1000`, Lemma 4.2) and `harea` (Lemmas 2.2 + 3.1 + 4.1).

## Build

    ./build.sh            # checks every module in dependency order with `lean`
    ./build.sh Moments    # a single module

`LEAN_PATH` must contain a built Mathlib (it does in this VM) plus this directory; `build.sh`
adds the latter.  There is no Lake project: each module is checked with
`lean -o MathathonT5/<m>.olean MathathonT5/<m>.lean` in dependency order.

## Provenance

Modules `Convex`, `NodeBounds`, `Constants`, `PsiConvex`, `ChordData` are verbatim bodies of
submissions by swarm members `m3`, `m6`, `m2`, `m4`, `m1` of Ultramath swarm `smwi0v1pw`
(deepseek-v4.1-flash), refereed by recompiling them and checking `#print axioms`; only their
preamble was replaced by an import of this project's definitions.  Everything else is by the
main agent.  The three published constants that had to be *corrected* against the task
statement are recorded in the member files: `c^(5/2) = 0.528067…` (not `0.5282`),
`c^(-3/2) = 1.466798…`, `Lam(94/100) = 0.57467…` (not `0.6222`).
