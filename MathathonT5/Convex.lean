/-
Interval-integral and convexity lemmas used by the numerical certificate
(Mathathon report `attempt_8_T5`, §3.1 and §4).

* `integral_cos_sq` and `integral_affine_cos_sq` evaluate the integrals of
  `cos²` and of an affine function of `cos²`; these are what every chord or
  tangent majorant below integrates to.
* `convex_chord` is the statement "a convex function lies below its chord",
  `convex_tangent` is "a convex function lies above its tangent".

Proved by swarm member `m3` (direction d1), integrated verbatim.
-/
import MathathonT5.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral

namespace MathathonT5.D1

theorem integral_cos_sq (a b : ℝ) :
    ∫ v in a..b, Real.cos v ^ 2 = (b - a) / 2 + (Real.sin (2 * b) - Real.sin (2 * a)) / 4 := by
  rw [_root_.integral_cos_sq, Real.sin_two_mul, Real.sin_two_mul]
  ring

theorem integral_cos_sq_zero_pi_div_twelve :
    ∫ v in (0 : ℝ)..(Real.pi / 12), Real.cos v ^ 2 = Real.pi / 24 + 1 / 8 := by
  have h : (2 : ℝ) * (Real.pi / 12) = Real.pi / 6 := by ring
  have h0 : (2 : ℝ) * 0 = 0 := by ring
  rw [integral_cos_sq, h, h0, Real.sin_pi_div_six, Real.sin_zero]
  ring

theorem convex_chord {f : ℝ → ℝ} {x1 x2 : ℝ} (h12 : x1 < x2)
    (hf : ConvexOn ℝ (Set.Icc x1 x2) f) {x : ℝ} (hx : x ∈ Set.Icc x1 x2) :
    f x ≤ f x1 + (f x2 - f x1) / (x2 - x1) * (x - x1) := by
  have hx1 : x1 ∈ Set.Icc x1 x2 := ⟨le_rfl, le_of_lt h12⟩
  have hx2 : x2 ∈ Set.Icc x1 x2 := ⟨le_of_lt h12, le_rfl⟩
  obtain ⟨hxl, hxr⟩ := hx
  have hd : 0 < x2 - x1 := sub_pos.mpr h12
  set a : ℝ := (x2 - x) / (x2 - x1) with ha
  set b : ℝ := (x - x1) / (x2 - x1) with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have hax : a * x1 + b * x2 = x := by
    rw [ha, hb]; field_simp; ring
  have h := hf.2 hx1 hx2 ha0 hb0 hab
  have h' : f x ≤ a * f x1 + b * f x2 := by
    simpa only [hax, smul_eq_mul] using h
  have heq : a * f x1 + b * f x2 = f x1 + (f x2 - f x1) / (x2 - x1) * (x - x1) := by
    rw [ha, hb]; field_simp; ring
  linarith [h', heq]

theorem convex_tangent {f : ℝ → ℝ} {x1 x2 : ℝ} (h12 : x1 < x2)
    (hf : ConvexOn ℝ (Set.Icc x1 x2) f) {c : ℝ} (hc : c ∈ Set.Icc x1 x2) {m : ℝ}
    (hm : HasDerivAt f m c) :
    ∀ x ∈ Set.Icc x1 x2, f c + m * (x - c) ≤ f x := by
  -- `x1 < x2` is not needed below: `Set.Icc x1 x2` is convex for any endpoints,
  -- and the slope lemmas only need `c` and `x` in the interval. We keep the
  -- hypothesis for compatibility with the project statement.
  have : x1 < x2 := h12
  intro x hx
  rcases lt_trichotomy x c with hxc | hxc | hxc
  · have h := hf.slope_le_of_hasDerivAt hx hc hxc hm
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxc)] at h
    nlinarith
  · subst hxc; simp
  · have h := hf.le_slope_of_hasDerivAt hc hx hxc hm
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxc)] at h
    nlinarith

/-- Integral of an affine function of `cos²`: the object every majorant/minorant in the
numerical certificate integrates to. -/
theorem integral_affine_cos_sq (α β a b : ℝ) :
    ∫ v in a..b, (α + β * Real.cos v ^ 2) =
      α * (b - a) + β * ((b - a) / 2 + (Real.sin (2 * b) - Real.sin (2 * a)) / 4) := by
  have hcont : Continuous fun v : ℝ => β * Real.cos v ^ 2 := by fun_prop
  conv_lhs =>
    rw [intervalIntegral.integral_add intervalIntegrable_const (hcont.intervalIntegrable a b)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos_sq]
  ring_nf

/-- Tangent-line (affine minorant) form of `convex_tangent` stated with `deriv`, which is the
form used when the tangent slope is known at a rational node. -/
theorem convex_tangent_deriv {f : ℝ → ℝ} {x1 x2 : ℝ} (h12 : x1 < x2)
    (hf : ConvexOn ℝ (Set.Icc x1 x2) f) {c : ℝ} (hc : c ∈ Set.Icc x1 x2)
    (hfd : DifferentiableAt ℝ f c) :
    ∀ x ∈ Set.Icc x1 x2, f c + deriv f c * (x - c) ≤ f x :=
  convex_tangent h12 hf hc hfd.hasDerivAt

end MathathonT5.D1
