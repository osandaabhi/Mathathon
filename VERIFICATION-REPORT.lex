================================================================================
LEAN VERIFICATION REPORT
Target: "An explicit deformation excluding the tetrahedral-prism soap-film cone
in R^4", Mathathon project attempt_8_T5, 15 November 2026, 10 pp.
Artifact: results/t5-formalization/  (11 Lean modules, 2358 lines)
Toolchain: leanprover/lean4:v4.33.1 (commit 819816b2e0a3bf405af45ae5c7af2498f8b5bee6)
           with the prebuilt Mathlib installed at /opt/mathlib in this image.
Report written by the agent that produced the artifact. Every claim below is
either (a) a machine-checked fact with the command that checks it, or (b)
explicitly marked as unverified or author-computed.
================================================================================

0. VERDICT IN ONE PARAGRAPH
--------------------------------------------------------------------------------
The report's Theorem 1.2 ("the tetrahedral-prism cone T5 is not Almgren-minimal")
is NOT Lean-verified. The Lean development verifies: (i) the algebraic core of the
report's tetrahedral geometry (the Gram data of the four vertices); (ii) two of the
three moment estimates of Lemma 3.3, namely J_{5/2} > 33/10 and J_{-3/2} > 31, both
proved for the report's REDUCED one-dimensional integrands of Lemma 3.2; (iii) the
arithmetic identity of Proposition 5.1, link area / 4*pi = 4*tau - 5; (iv) every
rational one-variable certificate that the numerical scheme uses (node values,
chords, tangents, constants). It does not verify: the area identity (Lemma 2.2),
the Lipschitz/admissibility lemmas (4.1, 4.2), the identification of the cone
(Lemma 2.1), the radial and angular reductions (Lemmas 3.1, 3.2), the remaining
moment estimate J_{1/2} < 191/20, or the numerical value of the density. In Lean
the theorem exists only in conditional form, with three named hypotheses; there is
no unconditional Lean theorem asserting that this cone is not minimizing.

1. WHAT "VERIFIED" MEANS HERE
--------------------------------------------------------------------------------
Definition used throughout: a declaration is VERIFIED iff it is elaborated by Lean
with no `sorry`, `admit`, `axiom` or `native_decide`, and `#print axioms` reports
only `propext`, `Classical.choice`, `Quot.sound` (the standard axioms of Mathlib;
none of them is a mathematical assumption about the problem).

Checks performed on the tree as delivered:

  $ cd results/t5-formalization && ./build.sh
    == checking MathathonT5/Basic.lean          ... (11 modules) ...
    == all modules checked                     exit status 0

  $ grep -rn "\bsorry\b\|\badmit\b\|^axiom\|native_decide" MathathonT5/*.lean
    (no matches)

  $ lean .axcheck.lean     # imports MathathonT5.Main and MathathonT5.Density
    'MathathonT5.J52_gt'                  depends on axioms: [propext,
                                           Classical.choice, Quot.sound]
    'MathathonT5.Jm32_gt'                 depends on axioms: [propext,
                                           Classical.choice, Quot.sound]
    'MathathonT5.saving_of_moments'       depends on axioms: [propext,
                                           Classical.choice, Quot.sound]
    'MathathonT5.saving_of_moments_sharp' depends on axioms: [propext,
                                           Classical.choice, Quot.sound]
    'MathathonT5.not_minimizing'          depends on axioms: [propext,
                                           Classical.choice, Quot.sound]
    'MathathonT5.density_eq'              depends on axioms: [propext,
                                           Classical.choice, Quot.sound]
    'MathathonT5.dot3_p_off'              depends on axioms: [propext,
                                           Classical.choice, Quot.sound]
    same for D6.B_neg, D6.saving, D5.Lam_piece_one, D5.Lam_piece_four,
    D4.Lam_14_lt, D4.sqrtc_lt, D4.Lam_antitone, D1.convex_chord,
    D1.convex_tangent, D1.integral_cos_sq.

  Note that `not_minimizing` having only standard axioms does NOT make it a proof
  of the theorem: it is a conditional implication (see Section 5).

Three linter warnings remain (unused `ring` in Basic.lean line 72, unused variable
name in TangentData.lean line 21, unused simp argument in Jm32.lean line 34). They
concern style only, not correctness.

2. STATUS VOCABULARY USED IN THE TABLES
--------------------------------------------------------------------------------
  [PROVED]        elaborated, no sorry, standard axioms only.
  [PROVED-RED]    as [PROVED], but about a definition that already incorporates a
                  reduction the report proves separately (here: the reduced
                  integrands (3.2) replace the sphere integrals) -- so the report's
                  reduction step itself is not covered.
  [CONDITIONAL]   a Lean theorem that assumes the missing pieces as explicit
                  hypotheses. No hidden assumptions, but not a proof of the claim.
  [DEF ONLY]      the objects are defined faithfully; no theorem about them.
  [NOT FORMALIZED] nothing in Lean.

3. ITEM-BY-ITEM STATUS OF THE REPORT
--------------------------------------------------------------------------------
  Def. 1.1 (Almgren comparison, admissible endpoint, counted-once H^3)
    [NOT FORMALIZED]. There is no use of Hausdorff measure anywhere in the tree.
  Section 1 (eps_i, q_i, b, c, f = max_i q_i.u / b, V_i, W, the cone C of (1.2))
    [DEF ONLY] for V_i, W, C, and the cone is a set of points of R^4 written with
    coordinate functions; [PROVED] for the four-vertex Gram data, see Section 4.
  Lemma 2.1 ("C is the cone over the two-skeleton of Q = conv{-8q_i} x [-1/b,1/b]";
             "m|u| <= f(u) <= c|u|", "Lip f <= c")
    [NOT FORMALIZED] as a statement. What is formalized and proved:
      dot3_p_self : |p_i|^2 = 3/5,       p_i = q_i/b = eps_i/sqrt 5
      dot3_p_off  : p_i . p_j = -1/5     (i != j)
      sum_pvec    : sum_i p_i = 0
      fsup_nonneg : 0 <= f(u)
    The polar/two-skeleton identification, the bounds m|u| <= f(u) <= c|u| and
    Lip f <= c are not formalized.
  Lemma 2.2 (exact area identity, "area counted once": area difference = 2 I(F))
    [NOT FORMALIZED]. Nothing in the tree mentions the area of a set in R^4.
  Lemma 3.1 (I(F_infinity) <= B = (b/2)J_{1/2} - (b^3/2)J_{5/2} - ((b-1/2)/3)J_{-3/2})
    [NOT FORMALIZED]. Neither the inequality nor the radial/angular integration
    that produces it. In Lean the quantities J_p are DEFINED by the reduced formula
    (3.2) of Lemma 3.2 (see Section 7, deviation D1).
  Lemma 3.2 (angular reduction: J_p = 24 * integral_0^{pi/3} of the one-dimensional
             integrand)
    [NOT FORMALIZED] as a theorem; it is used as a definition. Consequently the
    results of Section 4 marked [PROVED-RED] do not cover the step from
    integral_{S^2} k^p dH^2 to the one-dimensional integral.
  Lemma 3.3, first estimate  J_{1/2} < 191/20
    [NOT FORMALIZED] as a theorem. The hard half is done: four rational affine
    majorants of the profile are proved (Section 4, D5.Lam_piece_one..four); the
    piecewise assembly is missing (Section 6).
  Lemma 3.3, second estimate  J_{5/2} > 33/10
    [PROVED-RED]  MathathonT5.J52_gt : (33/10 : R) < J52
    by a different argument than the report's (monotonicity on four pieces; the
    report uses Jensen's inequality on S^2 together with J_2 > 87/20).
  Lemma 3.3, third estimate  J_{-3/2} > 31
    [PROVED-RED]  MathathonT5.Jm32_gt : (31 : R) < Jm32
    by a different argument than the report's (convexity of the profile in
    x = cos^2 v plus tangent lines; the report uses convexity in v plus the
    midpoint rule).
  Lemma 3.3, the intermediate estimate (3.6)  J_2 = 4pi/5 + 16 sqrt 3/15 > 87/20
    [NOT FORMALIZED]. It is not needed by the route used here.
  Lemma 3.3, the arithmetic step  B < -1989361/60000000 < -3/100
    [PROVED] as an implication, from the three moment bounds as hypotheses:
      D6.B_neg   : J1 < 191/20 -> 33/10 < J5 -> 31 < Jm
                   -> (b/2)J1 - (b^3/2)J5 - ((b-1/2)/3)Jm < -3/100
      D6.B_lt    : the same with the sharper -39/1000
      D6.B_neg_exact : the same with the report's exact -1989361/60000000
  Lemma 4.1 (cutoff cost I(F_R) <= I(F_infinity) + 4 pi / R)
    [NOT FORMALIZED]. The functions gR, FR are defined; no estimate about them.
  Lemma 4.2 (phi is globally Lipschitz with constant < 4, support inside B_{4R},
             preserves the ball, and phi(C) = X_{F_R})
    [DEF ONLY] for phi, Hmap, zeta, deltaR, clip, Xset; the Lipschitz bound,
    the support statement, ball preservation and the image identity are not proved.
  Theorem 1.2 (there is phi with Lip phi < 4, identity outside B_4000, and
               H^3(phi(C) cap B_4000) < H^3(C cap B_4000) - 1/40)
    [NOT FORMALIZED]. Available only as the conditional statement of Section 5.
  Proposition 5.1 (link area = 48 alpha - 20 pi, density = 4 tau - 5)
    [PROVED] for the arithmetic identity only:
      density_eq  : linkArea / (4*pi) = 4*tau - 5, with alpha := arccos(-1/3),
                    tau := 3*alpha/pi, linkArea := 48*alpha - 20*pi.
      density_eq' : the same written as linkArea/(4*pi/3)/3 = 4*tau - 5.
    [NOT FORMALIZED]: the spherical-excess computation 8(3alpha-pi)+6(4alpha-2pi),
    and the numerical value 4*tau - 5 = 2.2980813756... (that would need rational
    bounds for arccos(-1/3)).
  Remark 4.3 (rescaling the comparison ball), Remark 5.2, Section 6 (talk outline),
  Appendix A (t5_certificate.py)
    [NOT FORMALIZED]. The certificate script of Appendix A is not part of the
    supplied attachment and was not reproduced or checked here.

4. THE DECLARATIONS THAT ARE PROVED (verbatim)
--------------------------------------------------------------------------------
Unless stated otherwise these are unconditional.

4.1 Tetrahedral geometry (Basic.lean)
  dot3_p_self (i : Fin 4) : dot3 (pvec i) (pvec i) = 3 / 5
  dot3_p_off  (i j : Fin 4) (h : i != j) : dot3 (pvec i) (pvec j) = -1 / 5
  sum_pvec    (k : Fin 3) : (sum i : Fin 4, pvec i k) = 0
  sum_dot3_pvec (u : V3) : (sum i : Fin 4, dot3 (pvec i) u) = 0
  fsup_nonneg (u : V3) : 0 <= fsup u
  clip_mem, abs_clip_le, gR_nonneg, deltaR_nonneg, FR_nonneg, FR_le_fsup
    (bookkeeping for the cut-off objects: |clip z| <= 1, gR >= 0 on [0,inf),
     0 <= F_R <= f)

4.2 One-variable calculus (Convex.lean)
  integral_cos_sq (a b : R) :
      integral v in a..b, cos v ^ 2 = (b-a)/2 + (sin (2b) - sin (2a))/4
  integral_cos_sq_zero_pi_div_twelve :
      integral v in 0..(pi/12), cos v ^ 2 = pi/24 + 1/8
  integral_affine_cos_sq (alpha beta a b : R) :
      integral v in a..b, (alpha + beta * cos v ^ 2)
        = alpha*(b-a) + beta*((b-a)/2 + (sin (2b) - sin (2a))/4)
  convex_chord (h12 : x1 < x2) (hf : ConvexOn R (Icc x1 x2) f)
      (hx : x in Icc x1 x2) : f x <= f x1 + (f x2 - f x1)/(x2 - x1)*(x - x1)
  convex_tangent (h12) (hf) (hc : c in Icc x1 x2) (hm : HasDerivAt f m c) :
      forall x in Icc x1 x2, f c + m*(x - c) <= f x

4.3 Rational data for the J_{1/2} profile (NodeBounds.lean, namespace D4)
  Lam_antitone : AntitoneOn Lam (Icc (1/4) 1)
  Lam_one_lt'   : Lam 1 < 5614/10000            (true value 0.56130866)
  Lam_94_lt'    : Lam (94/100) < 5749/10000     (true value 0.57480770)
  Lam_34_lt     : Lam (3/4) < 6227/10000        (true value 0.62260475)
  Lam_12_lt     : Lam (1/2) < 7010/10000        (true value 0.70093024)
  Lam_14_lt     : Lam (1/4) < 8076/10000        (true value 0.80754991)
  sqrtc_lt      : Real.sqrt cc < 880112/1000000 (i.e. (3/5)^(1/4) < 0.880112)

4.4 Rational affine majorants of the J_{1/2} profile (ChordData.lean, D5)
  Lam_piece_one   : forall x in Icc (1/4) (1/2),   Lam x <=  148975379/163008765
                                                     -  69014176/163008765 * x
  Lam_piece_two   : forall x in Icc (1/2) (3/4),   Lam x <=   52257/60950
                                                     -   9528/30475 * x
  Lam_piece_three : forall x in Icc (3/4) (47/50), Lam x <= 5510230771/6802361181
                                                     - 62959200/251939303 * x
  Lam_piece_four  : forall x in Icc (93/100) (1),  Lam x <=  236202671/300106715
                                                     - 13548640/60021343 * x
  supporting machinery: rpow_chord_le, rpow_chord_ge, Lam_le_affine,
  h7_le_affine (majorants for the 7/4 profile), inv_ge_tangent,
  rpow_quarter_le_of_le_fourth, Psi_ge_affine, plus Psi_piece_one..four.
  NOTE. These are pointwise statements about Lam (and Psi). They are NOT yet
  integrated into an integral bound; see Section 6.

4.5 Convexity of the J_{-3/2} profile (PsiConvex.lean, D3)
  convexOn_Psi  : ConvexOn R (Icc (1/4) 1) Psi
  strictConvexOn_Psi, antitoneOn_Psi
  deriv_Psi (x) (hx : 0 < x) :
      deriv Psi x = -1 / (2 * x^2 * (((2 + x) / x) ^ (3/4)))
  deriv2_Psi (x) (hx : 0 < x) :
      deriv (deriv Psi) x = (4x+5) / (4 * x^(9/4) * (x+2)^(7/4))
  tangent_le_Psi (hc : c in Icc (1/4) 1) (hx : x in Icc (1/4) 1) :
      Psi c + deriv Psi c * (x - c) <= Psi x

4.6 Rational data for the tangent argument (TangentData.lean, Tangent namespace)
  for q in {97/100, 169/200, 5/8, 37/100}:
    Psi_{q}_lo     : p <= Psi q          with p = 3228,3545,4315,5908 / 10000
    derivPsi_{q}_lo : -M <= deriv Psi q  with M = 2296,2818,4363,9072 / 10000
  plus le_rpow_quarter, le_rpow_three_quarters'.

4.7 Constants and final arithmetic (Constants.lean, D6)
  b_bounds : 79/100 < bb < 791/1000           (bb = sqrt (5/8))
  c_bounds : 7745/10000 < cc < 7746/10000     (cc = sqrt (3/5))
  c_pow52_lo   : 5280/10000 < cc^(5/2)        (true value 0.5280670)
  c_pow_m32_lo : 14668/10000 < cc^(-3/2)      (true value 1.4668529)
  nine_pow_lo  : (1/9)^(7/4) < 214/10000      (true value 0.0213833)
  cc_pow52_eq  : cc^(5/2) = (3/5) * sqrt cc
  c_pow52_lo_false : NOT (5282/10000 < cc^(5/2))   [machine-checked refutation
                     of a constant that appeared in an earlier draft of the plan]
  B_neg, B_lt, B_neg_exact, saving, saving_sharp  (all with the three moment
      bounds as hypotheses; conclusions -3/100, -39/1000, -1989361/60000000,
      and 2*(B + 4 pi/1000) < -1/40 resp. < -7/250)

4.8 The two moment estimates (Moments.lean, Jm32.lean)
  J52_gt : (33/10 : R) < J52     [PROVED-RED]  J52 := 24 * integral_0^{pi/3}
           of (c^(5/2)/(7/2)) * (1 - (cos^2 v/(2+cos^2 v))^(7/4)) dv
  Jm32_gt : (31 : R) < Jm32      [PROVED-RED]  Jm32 := 24 * integral_0^{pi/3}
           of 2 * c^(-3/2) * (((2+cos^2 v)/cos^2 v)^(1/4) - 1) dv
  Numerical content of the two proofs (exact rational bounds, machine-checked):
    J52  > 24 * (528/1000/(7/2)) * (157/600) * (35537/10000) = 3.3670...
    Jm32 > 24 * 2 * (14668/10000) * 0.4430                   = 31.1900...
    (true values 3.4280819 and 31.4496160; targets 3.3 and 31.)

4.9 Density (Density.lean)
  alpha := arccos (-(1/3)),  tau := 3*alpha/pi,  linkArea := 48*alpha - 20*pi
  density_eq  : linkArea / (4*pi) = 4*tau - 5
  density_eq' : linkArea / (4*pi/3) / 3 = 4*tau - 5

5. THE CONDITIONAL FORM OF THE MAIN THEOREM (verbatim, Main.lean)
--------------------------------------------------------------------------------
  def Bval : R := (bb/2)*J12 - (bb^3/2)*J52 - ((bb - 1/2)/3)*Jm32

  theorem saving_of_moments (hJ1 : J12 < 191/20) :
      2 * (Bval + 4 * Real.pi / 1000) < -1/40

  theorem saving_of_moments_sharp (hJ1 : J12 < 191/20) :
      2 * (Bval + 4 * Real.pi / 1000) < -7/250

  theorem area_decreases (area : Set V4 -> R) (hJ1 : J12 < 191/20)
      (harea : area (Xset 1000) <= area cone + 2 * (Bval + 4*Real.pi/1000)) :
      1/40 < area cone - area (Xset 1000)

  theorem not_minimizing (area : Set V4 -> R) (hJ1 : J12 < 191/20)
      (himg : phi 1000 '' cone = Xset 1000)
      (harea : area (Xset 1000) <= area cone + 2 * (Bval + 4*Real.pi/1000)) :
      area (phi 1000 '' cone) < area cone - 1/40

  Interpretation of the three hypotheses (all unproved in Lean):
    hJ1   : the report's first moment bound, Lemma 3.3 (see Section 6).
    himg  : the image identity of Lemma 4.2.
    harea : the area identity of Lemma 2.2 combined with Lemma 3.1 (I(F_inf) <= B)
            and Lemma 4.1 (I(F_R) <= I(F_inf) + 4 pi/R), R = 1000.
  Note that `area` is an arbitrary function Set R^4 -> R: no property of Hausdorff
  measure is used, so even the conclusion is only as strong as the hypothesis
  `harea`. In particular nothing in Lean shows that the area of the competitor is
  finite or that it equals the number `area (Xset 1000)`.

6. THE ONE MISSING ARITHMETIC ESTIMATE, IN DETAIL
--------------------------------------------------------------------------------
Claim missing:  J12 < 191/20, where
  J12 = 24 * integral_0^{pi/3} (2/3)*sqrt c * Lam (cos^2 v) dv,
  Lam x = 1 - (x/(2+x))^(3/4),  c = sqrt (3/5).

Present in the tree and proved:
  * the four rational affine majorants D5.Lam_piece_one..four (Section 4.4);
  * monotonicity of cos^2 on [0,pi/2] (Moments.cos_sq_le_cos_sq) and the exact
    values cos^2(pi/12) = (2+sqrt 3)/4, cos^2(pi/6) = 3/4, cos^2(pi/4) = 1/2,
    cos^2(pi/3) = 1/4 (Moments.cos_sq_pi_div_twelve, cos_sq_pi_div_three/four/six
    from Mathlib);
  * integral_affine_cos_sq (Section 4.2) and the values sin(pi/6), sin(pi/3),
    sin(pi/2), sin(2pi/3) (Jm32.sin_pi_div_six' etc.);
  * the two-fold technique of splitting an interval integral over
    0 < pi/12 < pi/6 < pi/4 < pi/3 (used twice already, in J52_gt and Jm32_gt);
  * sqrt c < 880112/1000000 (D4.sqrtc_lt).

Missing: the five-step assembly
  (1) continuity of v |- Lam (cos^2 v) and hence IntervalIntegrable on each piece
      (a one-line proof was found: Continuous.div with positive denominator, then
      Continuous.rpow_const at exponent 3/4 >= 0);
  (2) integral_mono_on against each of the four majorants, on the v-pieces
      [0,pi/12], [pi/12,pi/6], [pi/6,pi/4], [pi/4,pi/3], whose x = cos^2 v ranges
      are [93/100,1], [3/4,47/50], [1/2,3/4], [1/4,1/2] respectively;
  (3) evaluating the four integrals of affine functions of cos^2;
  (4) summing with integral_add_adjacent_intervals;
  (5) the final comparison 16 * (880112/10^6) * (6764/10000) < 191/20.

Why it is missing: steps (1)-(5) are mathematically routine, but applying the
majorant D5.Lam_piece_* inside the piecewise argument produces deterministic
elaboration timeouts (isDefEq / whnf, at 800000 heartbeats), i.e. a performance
problem in checking large rational certificate terms, not a mathematical gap.
No counterexample or numerical obstruction is known; see the numbers below.

Numbers (AUTHOR-COMPUTED, NOT machine-checked; treat as indicative only):
  * with the four majorants and pi <= 22/7, sqrt 3 <= 1.732051 the four piece
    integrals sum to at most 0.6764, giving J12 <= 16*0.880112*0.6764 = 9.5249;
  * an independent computation by the member that produced the majorants, using
    the chord values at the four decimal node bounds, gives J12 <= 9.5174;
  * target 9.55, true value 9.4917.
So the plan closes with roughly 0.3% to 0.6% margin; the assembly is expected to
succeed but has not been carried out.

7. DEVIATIONS FROM THE REPORT'S OWN ARGUMENT (accuracy-critical)
--------------------------------------------------------------------------------
D1. In Lean the moments are DEFINED by the reduced one-dimensional formula, i.e.
    J12, J52, Jm32 are defined as 24 * integral_0^{pi/3} of, respectively,
      (2/3) sqrt c * (1 - (x/(2+x))^(3/4)),
      (c^(5/2)/(7/2)) * (1 - (x/(2+x))^(7/4)),
      2 c^(-3/2) * (((2+x)/x)^(1/4) - 1),   where x = cos^2 v.
    These are the report's (3.2) integrands after the substitution
    z = cos v / sqrt(2+cos^2 v), i.e. z^(p+1) = (x/(2+x))^((p+1)/2).
    That substitution is NOT formalized; it is a one-line calculation on paper.
    Consequently J52_gt and Jm32_gt are statements about these definitions, not
    about integral_{S^2} f(u)^p dH^2(u).
D2. J_{5/2} > 33/10 is proved WITHOUT Jensen's inequality and WITHOUT J_2 > 87/20:
    the integrand is bounded below on four subintervals by monotonicity of
    v |- 1 - (cos^2 v/(2+cos^2 v))^(7/4), using the four rational bounds
    1463/10000, 137/1000, 103/1000, 60/1000 for that function at the left
    endpoints (sum 35537/10000), and c^(5/2) > 528/1000.
D3. J_{-3/2} > 31 is proved by convexity of Psi in x = cos^2 v and TANGENT lines at
    the four rational points 97/100, 169/200, 5/8, 37/100, not by convexity in v
    and the midpoint rule. The report's midpoint-rule numbers (0.938, 1.033, 1.260,
    1.731) are therefore not used; the report's claim that the integral average of
    a convex function is at least its midpoint value is not formalized.
D4. For J_{1/2} the plan uses rational chords in x = cos^2 v (the majorants of
    ChordData.lean) instead of the report's trapezoid rule in v. The report's
    table (0.330, 0.339, 0.366, 0.412, 0.474) is not used, although it was
    checked numerically and is correct.
D5. The report's Prop. 5.1 is formalized only as the final algebraic identity.
D6. No classification or regularity theorem about minimal sets is imported
    anywhere in the tree, in agreement with the report's claim about its own proof.
    Mathlib's standard axioms only: propext, Classical.choice, Quot.sound.

8. NUMERICAL CORRECTIONS OF THE PLAN, NOT OF THE REPORT
--------------------------------------------------------------------------------
The following constants appeared in the task specification issued to the
formalization effort and are FALSE; the tree contains the corrected values
(and, for one of them, a machine-checked refutation):
    (3/5)^(5/4) = 0.5280670421   (a bound 5282/10000 is false; 5280/10000 works)
    (5/3)^(3/4) = 1.4668528947
    (1/9)^(7/4) = 0.0213833...   (a bound 214/10000 works)
    Lam 1       = 0.5613086623   (a bound 5613/10000 is false; 56131/100000 works)
    Lam(94/100) = 0.5748076987   (a bound 6222/10000 is true but far too loose:
                                  with it the chord bound gives J12 <= 9.586 > 9.55)
The REPORT's own table entries (.330/.339/.366/.412/.474 and
.938/1.033/1.260/1.731) were checked numerically and are correct as bounds.
The report's density 4*tau - 5 = 2.2980813756 was checked numerically;
tau = 1.8245203439.

9. PROVENANCE AND DEPTH OF REVIEW
--------------------------------------------------------------------------------
* Modules Convex.lean, NodeBounds.lean, Constants.lean, PsiConvex.lean and
  ChordData.lean are the verbatim bodies of five submissions by members of an
  internal agent swarm (model: deepseek-v4.1-flash); only their preamble was
  replaced by an import of this project's definitions. They were refereed by the
  author of this report by (i) recompiling them independently, (ii) grepping for
  forbidden tokens, (iii) #print axioms on their main theorems. They have NOT been
  reviewed by a human, and the model family that produced them is not independent
  of the model that wrote the rest of the tree.
* Modules Basic.lean, Moments.lean, Convex.lean's consumer Jm32.lean, Density.lean
  and Main.lean were written by the author of this report.
* Nothing in the tree was produced by an automated theorem prover other than Lean
  itself checking the given proof terms.

10. WHAT MAY AND MAY NOT BE CLAIMED IN A SUBMISSION
--------------------------------------------------------------------------------
MAY be claimed:
  "The following parts of the report are machine-checked in Lean 4 with Mathlib:
   the tetrahedral Gram data; the two moment bounds J_{5/2} > 33/10 and
   J_{-3/2} > 31 for the reduced integrands of Lemma 3.2; the arithmetic step
   B < -3/100 and 2(B + 4 pi/1000) < -1/40 and < -7/250, given the three moment
   bounds; the density identity link area / 4 pi = 4 tau - 5; and all rational
   one-variable certificates (node values, chords, tangent data, constants) used
   by the numerical scheme. Every module compiles with no sorry, admit, axiom or
   native_decide and uses only the standard axioms propext, Classical.choice,
   Quot.sound."
MAY NOT be claimed:
  - that Theorem 1.2 is Lean-verified, or that the cone is proved in Lean not to
    be area-minimizing;
  - that the moment bounds are verified for the SPHERE integrals (only for the
    reduced one-dimensional integrals);
  - that Lemma 3.3 as a whole is verified (J_{1/2} < 191/20 is missing);
  - that the area identity, the cut-off cost, the Lipschitz estimates or the image
    identity of the deformation are verified;
  - that the numerical value of the density 4 tau - 5 is verified.

11. FILES, SIZES, REPRODUCTION
--------------------------------------------------------------------------------
  results/t5-formalization/build.sh                      build driver (lean -o, in
                                                          dependency order)
  results/t5-formalization/README.md                     module inventory + status
  results/t5-formalization/VERIFICATION-REPORT.lex       this file
  results/t5-formalization/MathathonT5/ Basic.lean            185 lines
                                        Moments.lean          294
                                        Convex.lean            91
                                        NodeBounds.lean       131
                                        Constants.lean        211
                                        PsiConvex.lean        283
                                        TangentData.lean      145
                                        Jm32.lean             217
                                        ChordData.lean        700
                                        Density.lean           37
                                        Main.lean              64
                                                              ---- total 2358

  Reproduction:
    cd results/t5-formalization && ./build.sh          # exit 0, "all modules checked"
    ./build.sh Moments                                  # a single module
  Requirements: lean 4.33.1 on PATH and LEAN_PATH containing a built Mathlib;
  build.sh prepends its own directory to LEAN_PATH. No Lake project is used.
  `lean -o MathathonT5/<m>.olean MathathonT5/<m>.lean` in the order Basic, Moments,
  Convex, NodeBounds, Constants, PsiConvex, TangentData, Jm32, ChordData, Density,
  Main.
================================================================================
END OF REPORT
================================================================================
