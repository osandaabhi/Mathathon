/-
The angular moments of the tetrahedral-prism cone and their numerical bounds
(Mathathon report `attempt_8_T5`, Lemmas 3.1 -- 3.3).

With `z v = cos v / sqrt (2 + cos v ^ 2)` and `x = cos ^ 2 v` the report's reduced
one-dimensional formula (Lemma 3.2) is

  `J p = 24 * ∫_0^(π/3) (c^p/(p+1)) * (1 - z v ^ (p+1)) dv`,  `c = √(3/5)`,

and `(z v)^2 = x/(2+x)`.  We therefore define

  `G12 v = (2/3) √c · Lam (cos²v)`   with  `Lam x = 1 - (x/(2+x))^(3/4)`,
  `G52 v = (c^(5/2)/(7/2)) · g52 v`  with  `g52 v = 1 - (x/(2+x))^(7/4)`,
  `Gm32 v = 2 c^(-3/2) · Psi (cos²v)` with `Psi x = ((2+x)/x)^(1/4) - 1`,

which is the same integrand as the report's `z^(p+1)`.  The bounds proved here are
the report's (3.3) with the constant improvements recorded in the docstrings.
-/
import MathathonT5.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral

namespace MathathonT5

/-! ### The three angular integrands -/

/-- `1 - (x/(2+x))^(3/4)`, the shape of the `p = 1/2` integrand. -/
def Lam (x : ℝ) : ℝ := 1 - (x / (2 + x)) ^ ((3 : ℝ) / 4)

/-- `((2+x)/x)^(1/4) - 1`, the shape of the `p = -3/2` integrand. -/
def Psi (x : ℝ) : ℝ := ((2 + x) / x) ^ ((1 : ℝ) / 4) - 1

/-- The `p = 5/2` integrand without its constant factor. -/
def g52 (v : ℝ) : ℝ := 1 - (Real.cos v ^ 2 / (2 + Real.cos v ^ 2)) ^ ((7 : ℝ) / 4)

/-- The `p = 1/2` integrand of the report. -/
def G12 (v : ℝ) : ℝ := (2 / 3) * Real.sqrt cc * Lam (Real.cos v ^ 2)

/-- The `p = 5/2` integrand of the report. -/
def G52 (v : ℝ) : ℝ := cc ^ ((5 : ℝ) / 2) / ((7 : ℝ) / 2) * g52 v

/-- The `p = -3/2` integrand of the report. -/
def Gm32 (v : ℝ) : ℝ := 2 * cc ^ (-((3 : ℝ) / 2)) * Psi (Real.cos v ^ 2)

/-- `J_{1/2} = 24 ∫_0^{π/3} G12`. -/
def J12 : ℝ := 24 * ∫ v in (0 : ℝ)..(Real.pi / 3), G12 v

/-- `J_{5/2} = 24 ∫_0^{π/3} G52`. -/
def J52 : ℝ := 24 * ∫ v in (0 : ℝ)..(Real.pi / 3), G52 v

/-- `J_{-3/2} = 24 ∫_0^{π/3} Gm32`. -/
def Jm32 : ℝ := 24 * ∫ v in (0 : ℝ)..(Real.pi / 3), Gm32 v

/-! ### Elementary monotonicity -/

lemma frac_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x / (2 + x) ≤ y / (2 + y) := by
  have hy : 0 ≤ y := le_trans hx hxy
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma rpow_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (r : ℝ) (hr : 0 ≤ r) :
    x ^ r ≤ y ^ r := Real.rpow_le_rpow hx hxy hr

/-- `x ↦ (x/(2+x))^(7/4)` is monotone on `[0,∞)`. -/
lemma g52_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (x / (2 + x)) ^ ((7 : ℝ) / 4) ≤ (y / (2 + y)) ^ ((7 : ℝ) / 4) :=
  Real.rpow_le_rpow (by positivity) (frac_mono hx hxy) (by norm_num)

/-- `x ↦ 1 - (x/(2+x))^(7/4)` is antitone on `[0,∞)`. -/
lemma g52_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    1 - (y / (2 + y)) ^ ((7 : ℝ) / 4) ≤ 1 - (x / (2 + x)) ^ ((7 : ℝ) / 4) := by
  linarith [g52_mono hx hxy]

/-- A seventh-power test for fourth roots: `(q/(2+q))^(7/4) ≤ A` follows from
`(q/(2+q))^7 ≤ A^4`. -/
lemma pow75_le_of_pow7_le {q A : ℝ} (hq : 0 ≤ q) (hA : 0 ≤ A)
    (h : (q / (2 + q)) ^ 7 ≤ A ^ 4) : (q / (2 + q)) ^ ((7 : ℝ) / 4) ≤ A := by
  have hb : (0:ℝ) ≤ q / (2 + q) := by positivity
  have e1 : ((q / (2 + q)) ^ 7) ^ ((1 : ℝ) / 4) = (q / (2 + q)) ^ ((7 : ℝ) / 4) := by
    rw [← Real.rpow_natCast (q / (2 + q)) 7, ← Real.rpow_mul hb]
    norm_num
  have e2 : (A ^ 4) ^ ((1 : ℝ) / 4) = A := by
    rw [← Real.rpow_natCast A 4, ← Real.rpow_mul hA]
    norm_num
  rw [← e1, ← e2]
  exact Real.rpow_le_rpow (by positivity) h (by norm_num)



/-! ### The `p = 5/2` moment: `J_{5/2} > 33/10`

Here the report uses Jensen's inequality on the sphere.  Instead we use only
monotonicity of `v ↦ 1 - (cos²v/(2+cos²v))^(7/4)` on the four pieces of
`[0,π/3]` cut at `π/12`, `π/6`, `π/4`, which needs no measure theory on `S²`:
on the `j`-th piece the integrand is at least `1 - A_j` for explicit rational
`A_j` with `(q_j/(2+q_j))^7 ≤ A_j^4`, where `q_j` is a rational upper bound for
`cos²v` on that piece. -/

lemma cos_sq_le_cos_sq {a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v) (hv : v ≤ Real.pi / 2) :
    Real.cos v ^ 2 ≤ Real.cos a ^ 2 := by
  have hpihalf : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hle : Real.cos v ≤ Real.cos a :=
    Real.cos_le_cos_of_nonneg_of_le_pi ha (le_trans hv hpihalf) hav
  have hv0 : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hv⟩
  have ha0 : 0 ≤ Real.cos a :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], le_trans hav hv⟩
  nlinarith [hle, hv0, ha0]

lemma cos_sq_pi_div_twelve : Real.cos (Real.pi / 12) ^ 2 = (2 + Real.sqrt 3) / 4 := by
  rw [Real.cos_sq, show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.cos_pi_div_six]
  ring

lemma cos_sq_pi_div_twelve_le : Real.cos (Real.pi / 12) ^ 2 ≤ 94 / 100 := by
  rw [cos_sq_pi_div_twelve]
  have h3 : Real.sqrt 3 < 176 / 100 := by
    rw [show (176:ℝ)/100 = Real.sqrt ((176/100)^2) from by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma g52_ge_of {v q A : ℝ} (_hv0 : 0 ≤ Real.cos v) (hxq : Real.cos v ^ 2 ≤ q)
    (hqA : (q / (2 + q)) ^ ((7 : ℝ) / 4) ≤ A) : 1 - A ≤ g52 v := by
  have hx0 : 0 ≤ Real.cos v ^ 2 := by positivity
  have h := g52_mono hx0 hxq
  simp only [g52]
  linarith

lemma g52_p1 {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) (Real.pi / 12)) :
    (1 - 1463 / 10000 : ℝ) ≤ g52 v := by
  refine g52_ge_of (q := 1) (A := 1463/10000) ?_ ?_ ?_
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hv.1], by linarith [Real.pi_pos, hv.2]⟩
  · have := Real.cos_sq_le_one v; linarith
  · exact pow75_le_of_pow7_le (by norm_num) (by norm_num) (by norm_num)

lemma g52_p2 {v : ℝ} (hv : v ∈ Set.Icc (Real.pi / 12) (Real.pi / 6)) :
    (1 - 137 / 1000 : ℝ) ≤ g52 v := by
  refine g52_ge_of (q := 94/100) (A := 137/1000) ?_ ?_ ?_
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hv.1], by linarith [Real.pi_pos, hv.2]⟩
  · have h1 : Real.cos v ^ 2 ≤ Real.cos (Real.pi / 12) ^ 2 :=
      cos_sq_le_cos_sq (by positivity) hv.1 (by linarith [Real.pi_pos, hv.2])
    have h2 := cos_sq_pi_div_twelve_le
    linarith
  · exact pow75_le_of_pow7_le (by norm_num) (by norm_num) (by norm_num)

lemma g52_p3 {v : ℝ} (hv : v ∈ Set.Icc (Real.pi / 6) (Real.pi / 4)) :
    (1 - 103 / 1000 : ℝ) ≤ g52 v := by
  refine g52_ge_of (q := 3/4) (A := 103/1000) ?_ ?_ ?_
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hv.1], by linarith [Real.pi_pos, hv.2]⟩
  · have h1 : Real.cos v ^ 2 ≤ Real.cos (Real.pi / 6) ^ 2 :=
      cos_sq_le_cos_sq (by positivity) hv.1 (by linarith [Real.pi_pos, hv.2])
    rw [Real.cos_pi_div_six] at h1
    have h3 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [h3] at h1
    linarith
  · exact pow75_le_of_pow7_le (by norm_num) (by norm_num) (by norm_num)

lemma g52_p4 {v : ℝ} (hv : v ∈ Set.Icc (Real.pi / 4) (Real.pi / 3)) :
    (1 - 60 / 1000 : ℝ) ≤ g52 v := by
  refine g52_ge_of (q := 1/2) (A := 60/1000) ?_ ?_ ?_
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hv.1], by linarith [Real.pi_pos, hv.2]⟩
  · have h1 : Real.cos v ^ 2 ≤ Real.cos (Real.pi / 4) ^ 2 :=
      cos_sq_le_cos_sq (by positivity) hv.1 (by linarith [Real.pi_pos, hv.2])
    rw [Real.cos_pi_div_four] at h1
    have h3 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [h3] at h1
    linarith
  · exact pow75_le_of_pow7_le (by norm_num) (by norm_num) (by norm_num)

lemma continuous_g52 : Continuous g52 := by
  have h1 : Continuous fun v : ℝ => Real.cos v ^ 2 / (2 + Real.cos v ^ 2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x; positivity
  have h2 : Continuous fun v : ℝ => (Real.cos v ^ 2 / (2 + Real.cos v ^ 2)) ^ ((7:ℝ)/4) :=
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 7/4)).comp h1
  exact continuous_const.sub h2

lemma c52_nonneg : (0:ℝ) ≤ cc ^ ((5 : ℝ) / 2) / ((7 : ℝ) / 2) := by
  have : (0:ℝ) < cc := by rw [cc]; positivity
  positivity

lemma g52_integral_lower :
    (Real.pi / 12) * ((1 - 1463/10000) + (1 - 137/1000) + (1 - 103/1000) + (1 - 60/1000))
      ≤ ∫ v in (0 : ℝ)..(Real.pi / 3), g52 v := by
  have hi : ∀ a b : ℝ, IntervalIntegrable g52 volume a b := fun a b =>
    continuous_g52.intervalIntegrable a b
  have hstep : ∀ a b A : ℝ, a ≤ b → (∀ v ∈ Set.Icc a b, A ≤ g52 v) →
      (b - a) * A ≤ ∫ v in a..b, g52 v := by
    intro a b A hab hAB
    have := intervalIntegral.integral_mono_on (μ := volume) hab
      intervalIntegrable_const (hi a b) hAB
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have b1 : (Real.pi / 12 - 0) * (1 - 1463/10000) ≤ ∫ v in (0:ℝ)..(Real.pi/12), g52 v :=
    hstep _ _ _ (by positivity) (fun v hv => g52_p1 hv)
  have b2 : (Real.pi / 6 - Real.pi / 12) * (1 - 137/1000) ≤
      ∫ v in (Real.pi/12)..(Real.pi/6), g52 v :=
    hstep _ _ _ (by linarith [Real.pi_pos]) (fun v hv => g52_p2 hv)
  have b3 : (Real.pi / 4 - Real.pi / 6) * (1 - 103/1000) ≤
      ∫ v in (Real.pi/6)..(Real.pi/4), g52 v :=
    hstep _ _ _ (by linarith [Real.pi_pos]) (fun v hv => g52_p3 hv)
  have b4 : (Real.pi / 3 - Real.pi / 4) * (1 - 60/1000) ≤
      ∫ v in (Real.pi/4)..(Real.pi/3), g52 v :=
    hstep _ _ _ (by linarith [Real.pi_pos]) (fun v hv => g52_p4 hv)
  have e1 : (∫ v in (0:ℝ)..(Real.pi/12), g52 v) + (∫ v in (Real.pi/12)..(Real.pi/6), g52 v)
      = ∫ v in (0:ℝ)..(Real.pi/6), g52 v :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
  have e2 : (∫ v in (0:ℝ)..(Real.pi/6), g52 v) + (∫ v in (Real.pi/6)..(Real.pi/4), g52 v)
      = ∫ v in (0:ℝ)..(Real.pi/4), g52 v :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
  have e3 : (∫ v in (0:ℝ)..(Real.pi/4), g52 v) + (∫ v in (Real.pi/4)..(Real.pi/3), g52 v)
      = ∫ v in (0:ℝ)..(Real.pi/3), g52 v :=
    intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
  have h12 : Real.pi / 12 - 0 = Real.pi / 12 := by ring
  have h23 : Real.pi / 6 - Real.pi / 12 = Real.pi / 12 := by ring
  have h34 : Real.pi / 4 - Real.pi / 6 = Real.pi / 12 := by ring
  have h45 : Real.pi / 3 - Real.pi / 4 = Real.pi / 12 := by ring
  rw [h12] at b1
  rw [h23] at b2
  rw [h34] at b3
  rw [h45] at b4
  linarith [b1, b2, b3, b4, e1, e2, e3]

/-- `c^(5/2) = (3/5)·√c ≥ (3/5)·(88/100) = 528/1000`. -/
lemma c52_lower : (528 / 1000 : ℝ) ≤ cc ^ ((5 : ℝ) / 2) := by
  have hc : (0:ℝ) < cc := by rw [cc]; positivity
  have hc2 : cc ^ 2 = 3 / 5 := by rw [cc]; exact Real.sq_sqrt (by norm_num)
  have hsq : (88/100 : ℝ) ≤ Real.sqrt cc := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hc)]
    rw [cc, Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
  have hpow : cc ^ ((5 : ℝ) / 2) = cc ^ 2 * Real.sqrt cc := by
    have h5 : ((5:ℝ)/2) = 2 + 1/2 := by norm_num
    rw [h5, Real.rpow_add hc, Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [hpow, hc2]
  nlinarith [hsq]

/-- **The `p = 5/2` moment bound.**  (The report obtains `J_{5/2} > 33/10` from
Jensen's inequality on `S²` together with `J_2 > 87/20`; the monotonicity
argument used here needs neither the sphere measure nor `J_2`.) -/
theorem J52_gt : (33 / 10 : ℝ) < J52 := by
  have hpi : (157/50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hS : (1 - 1463/10000) + (1 - 137/1000) + (1 - 103/1000) + (1 - 60/1000 : ℝ)
      = 35537/10000 := by norm_num
  have hg := g52_integral_lower
  rw [hS] at hg
  have hconst : ∫ v in (0 : ℝ)..(Real.pi / 3), G52 v
      = cc ^ ((5 : ℝ) / 2) / ((7 : ℝ) / 2) * ∫ v in (0 : ℝ)..(Real.pi / 3), g52 v := by
    simp only [G52]
    rw [intervalIntegral.integral_const_mul]
  have hc52' : (528/1000 : ℝ) / ((7:ℝ)/2) ≤ cc ^ ((5 : ℝ)/2) / ((7:ℝ)/2) :=
    div_le_div_of_nonneg_right c52_lower (by norm_num)
  have hc52nn : (0:ℝ) ≤ cc ^ ((5 : ℝ)/2) / ((7:ℝ)/2) := by
    have : (0:ℝ) < cc := by rw [cc]; positivity
    positivity
  have hpi' : (157/50 : ℝ) / 12 ≤ Real.pi / 12 := by linarith
  have hstep : ((528/1000)/((7:ℝ)/2)) * ((157/50)/12) ≤
      (cc ^ ((5:ℝ)/2) / ((7:ℝ)/2)) * (Real.pi/12) :=
    mul_le_mul hc52' hpi' (by norm_num) hc52nn
  have hstep2 : ((528/1000)/((7:ℝ)/2) * ((157/50)/12)) * (35537/10000) ≤
      (cc ^ ((5:ℝ)/2) / ((7:ℝ)/2) * (Real.pi/12)) * (35537/10000) :=
    mul_le_mul_of_nonneg_right hstep (by norm_num)
  have hchain : (cc ^ ((5:ℝ)/2) / ((7:ℝ)/2) * (Real.pi/12)) * (35537/10000)
      ≤ cc ^ ((5 : ℝ)/2) / ((7 : ℝ) / 2) * ∫ v in (0 : ℝ)..(Real.pi / 3), g52 v := by
    have h2 := mul_le_mul_of_nonneg_left hg hc52nn
    calc (cc ^ ((5:ℝ)/2) / ((7:ℝ)/2) * (Real.pi/12)) * (35537/10000)
        = cc ^ ((5:ℝ)/2) / ((7:ℝ)/2) * (Real.pi/12 * (35537/10000)) := by ring
      _ = cc ^ ((5:ℝ)/2) / ((7:ℝ)/2) * (Real.pi/12 * (35537/10000)) := by ring
      _ ≤ cc ^ ((5:ℝ)/2) / ((7:ℝ)/2) * ∫ v in (0:ℝ)..(Real.pi/3), g52 v := h2
  simp only [J52]
  rw [hconst]
  have hfin : (33/10 : ℝ) < 24 * (((528/1000)/((7:ℝ)/2) * ((157/50)/12)) * (35537/10000)) := by
    norm_num
  nlinarith [hfin, hstep2, hchain]

/-! ### `cos²` on `[0,π/3]` -/

lemma cos_sq_ge_quarter {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) (Real.pi / 3)) :
    (1/4 : ℝ) ≤ Real.cos v ^ 2 := by
  have hc1 : Real.cos (Real.pi/3) ≤ Real.cos v :=
    Real.cos_le_cos_of_nonneg_of_le_pi hv.1 (by linarith [Real.pi_pos]) hv.2
  have hc0 : 0 ≤ Real.cos v :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hv.1], by linarith [Real.pi_pos, hv.2]⟩
  rw [Real.cos_pi_div_three] at hc1
  nlinarith

lemma cos_sq_mem {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) (Real.pi / 3)) :
    Real.cos v ^ 2 ∈ Set.Icc (1/4 : ℝ) 1 :=
  ⟨cos_sq_ge_quarter hv, Real.cos_sq_le_one v⟩


end MathathonT5
