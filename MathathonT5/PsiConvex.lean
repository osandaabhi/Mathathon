/-
Convexity of `Psi x = ((2+x)/x)^(1/4) - 1` on `[1/4,1]`, the explicit derivative, and the
resulting tangent-line minorant on `[1/4,1]`.  This is what turns the rational lower bounds
on `Psi` and `deriv Psi` at four rational points into the lower bound for `J_{-3/2}`.

Proved by swarm member `m4` (direction d3), integrated verbatim.
-/
import MathathonT5.Moments

noncomputable section
open scoped BigOperators

namespace MathathonT5.D3

open Filter Set
open scoped Topology

theorem hasDerivAt_quo (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (2 + y) / y) (-2 / x ^ 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 2
  have h3 := h1.div (hasDerivAt_id x) hx.ne'
  refine h3.congr_deriv ?_
  simp only [id]
  ring_nf

/-- The pointwise derivative of `Psi`. -/
theorem hasDerivAt_Psi (x : ℝ) (hx : 0 < x) :
    HasDerivAt Psi (-1 / (2 * x ^ 2 * (((2 + x) / x) ^ ((3 : ℝ) / 4)))) x := by
  have hq := hasDerivAt_quo x hx
  have hqpos : 0 < (2 + x) / x := by positivity
  have _hbase : HasDerivAt (fun y : ℝ => y ^ ((1 : ℝ) / 4))
      (((1 : ℝ) / 4) * ((2 + x) / x) ^ ((1 : ℝ) / 4 - 1)) ((2 + x) / x) :=
    Real.hasDerivAt_rpow_const (Or.inl hqpos.ne')
  have hcomp : HasDerivAt (fun y : ℝ => ((2 + y) / y) ^ ((1 : ℝ) / 4))
      ((-2 / x ^ 2) * ((1 : ℝ) / 4) * ((2 + x) / x) ^ ((1 : ℝ) / 4 - 1)) x :=
    hq.rpow_const (Or.inl hqpos.ne')
  have hPsi : HasDerivAt Psi
      ((-2 / x ^ 2) * ((1 : ℝ) / 4) * ((2 + x) / x) ^ ((1 : ℝ) / 4 - 1)) x :=
    hcomp.sub_const 1
  refine hPsi.congr_deriv ?_
  rw [show ((1 : ℝ) / 4 - 1) = -(3 / 4) by norm_num, Real.rpow_neg hqpos.le]
  field_simp
  ring

/-- The pointwise value of the derivative, in monomial form (positive `x`). -/
theorem deriv_alt (x : ℝ) (hx : 0 < x) :
    -1 / (2 * x ^ 2 * (((2 + x) / x) ^ ((3 : ℝ) / 4)))
      = -(1 / 2) * (x ^ (-(5 / 4 : ℝ)) * (2 + x) ^ (-(3 / 4 : ℝ))) := by
  have hY : (0 : ℝ) < 2 + x := by linarith
  have hkey : x ^ 2 * ((2 + x) / x) ^ ((3 : ℝ) / 4)
      = x ^ ((5 : ℝ) / 4) * (2 + x) ^ ((3 : ℝ) / 4) := by
    rw [Real.div_rpow (le_of_lt hY) (le_of_lt hx)]
    have h3 : x ^ ((5 : ℝ) / 4) = x ^ 2 / x ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_natCast (x := x) 2, ← Real.rpow_sub hx]
      norm_num
    rw [h3]
    ring
  have h2 : 2 * x ^ 2 * ((2 + x) / x) ^ ((3 : ℝ) / 4)
      = 2 * (x ^ ((5 : ℝ) / 4) * (2 + x) ^ ((3 : ℝ) / 4)) := by
    rw [mul_assoc, hkey]
  have hx5 : x ^ ((5 : ℝ) / 4) ≠ 0 :=
    (Real.rpow_ne_zero (le_of_lt hx) (by norm_num)).2 hx.ne'
  have hY3 : (2 + x) ^ ((3 : ℝ) / 4) ≠ 0 :=
    (Real.rpow_ne_zero (le_of_lt hY) (by norm_num)).2 hY.ne'
  rw [h2, Real.rpow_neg (le_of_lt hx) (5 / 4), Real.rpow_neg (le_of_lt hY) (3 / 4)]
  field_simp

/-- Derivative of the monomial form of `deriv Psi`. -/
theorem hasDerivAt_derivPsi_mono (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(1 / 2) * (y ^ (-(5 / 4 : ℝ)) * (2 + y) ^ (-(3 / 4 : ℝ))))
      (-(1 / 2) * ((-(5 / 4 : ℝ)) * x ^ (-(9 / 4 : ℝ)) * (2 + x) ^ (-(3 / 4 : ℝ))
        + x ^ (-(5 / 4 : ℝ)) * (-(3 / 4 : ℝ)) * (2 + x) ^ (-(7 / 4 : ℝ)))) x := by
  have hY : (0 : ℝ) < 2 + x := by linarith
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / 4 : ℝ)))
      ((-(5 / 4 : ℝ)) * x ^ (-(9 / 4 : ℝ))) x := by
    have h := (hasDerivAt_id x).rpow_const (p := (-(5 / 4 : ℝ))) (Or.inl hx.ne')
    rw [show (-(5 / 4 : ℝ)) - 1 = -(9 / 4 : ℝ) by norm_num] at h
    simpa using h
  have hq : HasDerivAt (fun y : ℝ => (2 + y) ^ (-(3 / 4 : ℝ)))
      ((-(3 / 4 : ℝ)) * (2 + x) ^ (-(7 / 4 : ℝ))) x := by
    have h2 : HasDerivAt (fun y : ℝ => 2 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add 2
    have h := h2.rpow_const (p := (-(3 / 4 : ℝ))) (Or.inl hY.ne')
    rw [show (-(3 / 4 : ℝ)) - 1 = -(7 / 4 : ℝ) by norm_num] at h
    simpa using h
  have h := (hp.mul hq).const_mul (-(1 / 2))
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- The stated formula for `deriv Psi`. -/
theorem deriv_Psi (x : ℝ) (hx : 0 < x) :
    deriv Psi x = -1 / (2 * x ^ 2 * (((2 + x) / x) ^ ((3 : ℝ) / 4))) :=
  (hasDerivAt_Psi x hx).deriv

/-- The stated formula for the derivative of `deriv Psi`. -/
theorem hasDerivAt_derivPsi (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -1 / (2 * y ^ 2 * (((2 + y) / y) ^ ((3 : ℝ) / 4))))
      ((4 * x + 5) / (4 * x ^ ((9 : ℝ) / 4) * (x + 2) ^ ((7 : ℝ) / 4))) x := by
  have hY : (0 : ℝ) < 2 + x := by linarith
  have hmono := hasDerivAt_derivPsi_mono x hx
  have heq : (fun y : ℝ => -1 / (2 * y ^ 2 * (((2 + y) / y) ^ ((3 : ℝ) / 4))))
      =ᶠ[𝓝 x] fun y => -(1 / 2) * (y ^ (-(5 / 4 : ℝ)) * (2 + y) ^ (-(3 / 4 : ℝ))) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact deriv_alt y hy
  refine (hmono.congr_of_eventuallyEq heq).congr_deriv ?_
  have hxA : x ^ (-(5 / 4 : ℝ)) = x ^ (-(9 / 4 : ℝ)) * x := by
    rw [show (-(5 / 4 : ℝ)) = (-(9 / 4 : ℝ)) + 1 by norm_num, Real.rpow_add hx,
      Real.rpow_one]
  have hYB : (2 + x) ^ (-(3 / 4 : ℝ)) = (2 + x) ^ (-(7 / 4 : ℝ)) * (2 + x) := by
    rw [show (-(3 / 4 : ℝ)) = (-(7 / 4 : ℝ)) + 1 by norm_num, Real.rpow_add hY,
      Real.rpow_one]
  have hxA' : (x ^ ((9 : ℝ) / 4))⁻¹ = x ^ (-(9 / 4 : ℝ)) :=
    (Real.rpow_neg (le_of_lt hx) (9 / 4)).symm
  have hYC' : ((2 + x) ^ ((7 : ℝ) / 4))⁻¹ = (2 + x) ^ (-(7 / 4 : ℝ)) :=
    (Real.rpow_neg (le_of_lt hY) (7 / 4)).symm
  have hxp : x ^ ((9 : ℝ) / 4) ≠ 0 :=
    (Real.rpow_ne_zero (le_of_lt hx) (by norm_num)).2 hx.ne'
  have hYq : (2 + x) ^ ((7 : ℝ) / 4) ≠ 0 :=
    (Real.rpow_ne_zero (le_of_lt hY) (by norm_num)).2 hY.ne'
  rw [hxA, hYB, ← hxA', ← hYC']
  field_simp
  ring_nf

theorem deriv2_Psi (x : ℝ) (hx : 0 < x) :
    deriv (deriv Psi) x = (4 * x + 5) / (4 * x ^ ((9 : ℝ) / 4) * (x + 2) ^ ((7 : ℝ) / 4)) := by
  have hev : deriv Psi =ᶠ[𝓝 x]
      fun y => -1 / (2 * y ^ 2 * (((2 + y) / y) ^ ((3 : ℝ) / 4))) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact deriv_Psi y hy
  rw [hev.deriv_eq]
  exact (hasDerivAt_derivPsi x hx).deriv

end MathathonT5.D3

namespace MathathonT5.D3

open Filter Set
open scoped Topology

/-- `Psi` is convex on `[1/4, 1]`. -/
theorem convexOn_Psi : ConvexOn ℝ (Set.Icc (1/4 : ℝ) 1) Psi := by
  have hD : Convex ℝ (Set.Icc (1/4 : ℝ) 1) := convex_Icc _ _
  have hpos : ∀ x ∈ Set.Icc (1/4 : ℝ) 1, (0 : ℝ) < x := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    linarith [hx.1]
  refine convexOn_of_deriv2_nonneg hD ?_ ?_ ?_ ?_
  · -- continuity
    intro x hx
    exact (hasDerivAt_Psi x (hpos x hx)).continuousAt.continuousWithinAt
  · -- differentiability
    intro x hx
    exact (hasDerivAt_Psi x (hpos x (interior_subset hx))).differentiableAt.differentiableWithinAt
  · -- differentiability of the derivative
    intro x hx
    have hx' : (0 : ℝ) < x := hpos x (interior_subset hx)
    have hev : deriv Psi =ᶠ[𝓝 x]
        fun y => -1 / (2 * y ^ 2 * (((2 + y) / y) ^ ((3 : ℝ) / 4))) := by
      filter_upwards [eventually_gt_nhds hx'] with y hy
      exact deriv_Psi y hy
    exact (DifferentiableAt.congr_of_eventuallyEq
      (hasDerivAt_derivPsi x hx').differentiableAt hev).differentiableWithinAt
  · -- second derivative nonnegative
    intro x hx
    have hx' : (0 : ℝ) < x := hpos x (interior_subset hx)
    have h2 : deriv^[2] Psi = deriv (deriv Psi) := rfl
    rw [h2, deriv2_Psi x hx']
    have h1 : (0 : ℝ) < 4 * x + 5 := by linarith
    have h2' : (0 : ℝ) < x ^ ((9 : ℝ) / 4) := Real.rpow_pos_of_pos hx' _
    have h3 : (0 : ℝ) < (x + 2) ^ ((7 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
    positivity

end MathathonT5.D3

namespace MathathonT5.D3

/-- `Psi` is strictly convex on `[1/4, 1]` (its second derivative is positive there). -/
theorem strictConvexOn_Psi : StrictConvexOn ℝ (Set.Icc (1/4 : ℝ) 1) Psi := by
  have hD : Convex ℝ (Set.Icc (1/4 : ℝ) 1) := convex_Icc _ _
  have hpos : ∀ x ∈ Set.Icc (1/4 : ℝ) 1, (0 : ℝ) < x := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    linarith [hx.1]
  refine strictConvexOn_of_deriv2_pos hD ?_ ?_
  · intro x hx
    exact (hasDerivAt_Psi x (hpos x hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : (0 : ℝ) < x := hpos x (interior_subset hx)
    have h2 : deriv^[2] Psi = deriv (deriv Psi) := rfl
    rw [h2, deriv2_Psi x hx']
    have h1 : (0 : ℝ) < 4 * x + 5 := by linarith
    have h2' : (0 : ℝ) < x ^ ((9 : ℝ) / 4) := Real.rpow_pos_of_pos hx' _
    have h3 : (0 : ℝ) < (x + 2) ^ ((7 : ℝ) / 4) := Real.rpow_pos_of_pos (by linarith) _
    positivity

/-- The tangent line to `Psi` at `c ∈ [1/4,1]` lies below `Psi` on all of `[1/4,1]`.
This is the affine minorant consumed by the lower bound for `J_{-3/2}`. -/
theorem tangent_le_Psi {c x : ℝ} (hc : c ∈ Set.Icc (1/4 : ℝ) 1)
    (hx : x ∈ Set.Icc (1/4 : ℝ) 1) :
    Psi c + deriv Psi c * (x - c) ≤ Psi x := by
  have hpos : ∀ y ∈ Set.Icc (1/4 : ℝ) 1, (0 : ℝ) < y := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    linarith [hy.1]
  have hdc : DifferentiableAt ℝ Psi c := (hasDerivAt_Psi c (hpos c hc)).differentiableAt
  rcases lt_trichotomy c x with hlt | heq | hgt
  · have hs := convexOn_Psi.deriv_le_slope hc hx hlt hdc
    rw [slope_def_field] at hs
    have hxc : (0 : ℝ) < x - c := by linarith
    rw [le_div_iff₀ hxc] at hs
    linarith
  · subst heq; simp
  · have hs := convexOn_Psi.slope_le_deriv hx hc hgt hdc
    rw [slope_def_field] at hs
    have hcx : (0 : ℝ) < c - x := by linarith
    rw [div_le_iff₀ hcx] at hs
    linarith

/-! ### The derivative at the four rational nodes used by the tangent argument -/

theorem hasDerivAt_Psi_97 : HasDerivAt Psi (deriv Psi (97/100)) (97/100) :=
  (hasDerivAt_Psi (97/100) (by norm_num)).congr_deriv (deriv_Psi (97/100) (by norm_num)).symm

theorem hasDerivAt_Psi_169 : HasDerivAt Psi (deriv Psi (169/200)) (169/200) :=
  (hasDerivAt_Psi (169/200) (by norm_num)).congr_deriv
    (deriv_Psi (169/200) (by norm_num)).symm

theorem hasDerivAt_Psi_58 : HasDerivAt Psi (deriv Psi (5/8)) (5/8) :=
  (hasDerivAt_Psi (5/8) (by norm_num)).congr_deriv (deriv_Psi (5/8) (by norm_num)).symm

theorem hasDerivAt_Psi_37 : HasDerivAt Psi (deriv Psi (37/100)) (37/100) :=
  (hasDerivAt_Psi (37/100) (by norm_num)).congr_deriv
    (deriv_Psi (37/100) (by norm_num)).symm

end MathathonT5.D3

namespace MathathonT5.D3

/-- `deriv Psi` is negative at every positive point. -/
theorem deriv_Psi_neg {x : ℝ} (hx : 0 < x) : deriv Psi x < 0 := by
  rw [deriv_Psi x hx]
  have h2 : (0 : ℝ) < (2 + x) / x := by positivity
  have h3 : (0 : ℝ) < ((2 + x) / x) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos h2 _
  have h4 : (0 : ℝ) < 2 * x ^ 2 * (((2 + x) / x) ^ ((3 : ℝ) / 4)) := by positivity
  exact div_neg_of_neg_of_pos (by norm_num) h4

/-- `Psi` is antitone on `[1/4,1]`. -/
theorem antitoneOn_Psi : AntitoneOn Psi (Set.Icc (1/4 : ℝ) 1) := by
  have hD : Convex ℝ (Set.Icc (1/4 : ℝ) 1) := convex_Icc _ _
  have hpos : ∀ x ∈ Set.Icc (1/4 : ℝ) 1, (0 : ℝ) < x := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    linarith [hx.1]
  refine antitoneOn_of_deriv_nonpos hD ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_Psi x (hpos x hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_Psi x (hpos x (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    exact le_of_lt (deriv_Psi_neg (hpos x (interior_subset hx)))

/-- Rational-data form of the tangent minorant, to the **right** of the node:
if `l ≤ Psi q` and `m ≤ deriv Psi q` then `l + m*(x-q) ≤ Psi x` for `q ≤ x` in `[1/4,1]`. -/
theorem tangent_le_Psi_right {q x l m : ℝ} (hq : q ∈ Set.Icc (1/4 : ℝ) 1)
    (hx : x ∈ Set.Icc (1/4 : ℝ) 1) (hxq : q ≤ x) (hl : l ≤ Psi q)
    (hm : m ≤ deriv Psi q) : l + m * (x - q) ≤ Psi x := by
  have h1 := tangent_le_Psi hq hx
  have h2 : m * (x - q) ≤ deriv Psi q * (x - q) :=
    mul_le_mul_of_nonneg_right hm (by linarith)
  linarith

/-- Rational-data form of the tangent minorant, to the **left** of the node:
if `l ≤ Psi q` and `deriv Psi q ≤ m` then `l + m*(x-q) ≤ Psi x` for `x ≤ q` in `[1/4,1]`. -/
theorem tangent_le_Psi_left {q x l m : ℝ} (hq : q ∈ Set.Icc (1/4 : ℝ) 1)
    (hx : x ∈ Set.Icc (1/4 : ℝ) 1) (hxq : x ≤ q) (hl : l ≤ Psi q)
    (hm : deriv Psi q ≤ m) : l + m * (x - q) ≤ Psi x := by
  have h1 := tangent_le_Psi hq hx
  have h2 : m * (x - q) ≤ deriv Psi q * (x - q) := by
    have := mul_le_mul_of_nonneg_right hm (by linarith : (0 : ℝ) ≤ -(x - q))
    nlinarith
  linarith

end MathathonT5.D3
