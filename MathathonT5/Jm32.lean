/-
The lower bound `J_{-3/2} > 31` (Mathathon report `attempt_8_T5`, Lemma 3.3).

The report uses convexity of `v ↦ Psi (cos²v)` on `[0,π/3]` and the midpoint rule.  Here we
use convexity of `Psi` in the variable `x = cos²v` (`MathathonT5.D3.convexOn_Psi`): on each
piece of the partition `0, π/12, π/6, π/4, π/3` the integrand is minorised by the tangent
line of `Psi` at one rational point `c_j` inside the corresponding `x`-range.  The integrals
of those affine functions of `cos²` are evaluated exactly (`D1.integral_affine_cos_sq`), and
what is left is rational arithmetic once `π` and `√3` are bracketed.
-/
import MathathonT5.TangentData
import MathathonT5.Convex
import MathathonT5.Constants

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral

namespace MathathonT5

lemma continuousOn_psi_cos_sq :
    ContinuousOn (fun v : ℝ => Psi (Real.cos v ^ 2)) (Set.Icc 0 (Real.pi/3)) := by
  have hbase : ContinuousOn (fun v : ℝ => (2 + Real.cos v ^ 2) / (Real.cos v ^ 2))
      (Set.Icc 0 (Real.pi/3)) := by
    apply ContinuousOn.div
    · exact (continuous_const.add (by fun_prop : Continuous fun v : ℝ => Real.cos v ^ 2)).continuousOn
    · exact (by fun_prop : Continuous fun v : ℝ => Real.cos v ^ 2).continuousOn
    · intro v hv
      have := cos_sq_ge_quarter hv
      positivity
  have hr : ContinuousOn (fun v : ℝ => ((2 + Real.cos v ^ 2) / (Real.cos v ^ 2)) ^ ((1:ℝ)/4))
      (Set.Icc 0 (Real.pi/3)) :=
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/4)).comp_continuousOn hbase
  simp only [Pi.sub_apply, Psi]
  exact hr.sub continuousOn_const

lemma intervalIntegrable_psi_cos_sq {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ Real.pi/3) :
    IntervalIntegrable (fun v : ℝ => Psi (Real.cos v ^ 2)) volume a b := by
  have hb0 : (0:ℝ) ≤ b := le_trans ha hab
  have ha3 : a ≤ Real.pi/3 := le_trans hab hb
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_psi_cos_sq.mono
    (fun x hx => ⟨le_trans (le_min ha hb0) hx.1, le_trans hx.2 (max_le ha3 hb)⟩)

/-- **One piece of the tangent argument.**  If on `[a,b] ⊂ [0,π/3]` the tangent to `Psi` at
`c ∈ [1/4,1]` is used, if `p ≤ Psi c` and `-M ≤ deriv Psi c`, and if the "moment defect"
`S = ∫ cos² - c (b-a)` satisfies `0 ≤ S ≤ Shi`, then the piece integral of `Psi (cos²·)`
is at least `p (b-a) - M Shi`. -/
lemma piece_lower_Psi {a b c p M Shi : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ Real.pi/3)
    (hc : c ∈ Set.Icc (1/4 : ℝ) 1) (hp : p ≤ Psi c) (hM : -M ≤ deriv Psi c) (hM0 : 0 ≤ M)
    (hS0 : 0 ≤ (b - a) / 2 + (Real.sin (2 * b) - Real.sin (2 * a)) / 4 - c * (b - a))
    (hS1 : (b - a) / 2 + (Real.sin (2 * b) - Real.sin (2 * a)) / 4 - c * (b - a) ≤ Shi) :
    p * (b - a) - M * Shi ≤ ∫ v in a..b, Psi (Real.cos v ^ 2) := by
  have hcont : IntervalIntegrable (fun v : ℝ => Psi (Real.cos v ^ 2)) volume a b :=
    intervalIntegrable_psi_cos_sq hab ha hb
  have haff : Continuous fun v : ℝ => Psi c + deriv Psi c * (Real.cos v ^ 2 - c) := by fun_prop
  have ht : ∀ v ∈ Set.Icc a b,
      Psi c + deriv Psi c * (Real.cos v ^ 2 - c) ≤ Psi (Real.cos v ^ 2) := by
    intro v hv
    exact D3.tangent_le_Psi hc (cos_sq_mem ⟨le_trans ha hv.1, le_trans hv.2 hb⟩)
  have hint : ∫ v in a..b, (Psi c + deriv Psi c * (Real.cos v ^ 2 - c))
      ≤ ∫ v in a..b, Psi (Real.cos v ^ 2) :=
    intervalIntegral.integral_mono_on hab (haff.intervalIntegrable a b) hcont ht
  have hval : ∫ v in a..b, (Psi c + deriv Psi c * (Real.cos v ^ 2 - c))
      = Psi c * (b - a) + deriv Psi c * ((b - a) / 2
          + (Real.sin (2 * b) - Real.sin (2 * a)) / 4 - c * (b - a)) := by
    have e : ∀ v : ℝ, Psi c + deriv Psi c * (Real.cos v ^ 2 - c)
        = (Psi c - deriv Psi c * c) + deriv Psi c * Real.cos v ^ 2 := fun v => by ring
    simp only [e]
    rw [D1.integral_affine_cos_sq]
    ring
  have hba : (0:ℝ) ≤ b - a := by linarith
  nlinarith [hint, hval, hp, hM, hS0, hS1, hM0, hba,
    mul_nonneg (sub_nonneg.mpr hp) hba, mul_nonneg hM0 (sub_nonneg.mpr hS1)]

/-! ### The four pieces -/

lemma sin_pi_div_six' : Real.sin (2 * (Real.pi/12)) = 1/2 := by
  have h : 2 * (Real.pi/12) = Real.pi/6 := by ring
  rw [h, Real.sin_pi_div_six]

lemma sin_pi_div_three' : Real.sin (2 * (Real.pi/6)) = Real.sqrt 3 / 2 := by
  have h : 2 * (Real.pi/6) = Real.pi/3 := by ring
  rw [h, Real.sin_pi_div_three]

lemma sin_pi_div_two' : Real.sin (2 * (Real.pi/4)) = 1 := by
  have h : 2 * (Real.pi/4) = Real.pi/2 := by ring
  rw [h, Real.sin_pi_div_two]

lemma sin_two_pi_div_three' : Real.sin (2 * (Real.pi/3)) = Real.sqrt 3 / 2 := by
  have h : 2 * (Real.pi/3) = Real.pi - Real.pi/3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

lemma psi_pieces :
    (3228/10000) * (Real.pi/12) - (2296/10000) * (2017/1000000)
        + ((3545/10000) * (Real.pi/12) - (2818/10000) * (1232/1000000))
        + ((4315/10000) * (Real.pi/12) - (4363/10000) * (786/1000000))
        + ((5908/10000) * (Real.pi/12) - (9072/10000) * (554/1000000))
      ≤ ∫ v in (0 : ℝ)..(Real.pi / 3), Psi (Real.cos v ^ 2) := by
  have hpi_lo : (157/50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hpi_hi : Real.pi < 22/7 := by
    have h := Real.pi_lt_d4
    norm_num at h
    linarith
  have h3lo : (1732050/1000000 : ℝ) < Real.sqrt 3 := by
    rw [show (1732050/1000000 : ℝ) = Real.sqrt ((1732050/1000000)^2) from by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h3hi : Real.sqrt 3 < 1732051/1000000 := by
    rw [show (1732051/1000000 : ℝ) = Real.sqrt ((1732051/1000000)^2) from by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have b1 : (3228/10000) * (Real.pi/12) - (2296/10000) * (2017/1000000)
      ≤ ∫ v in (0:ℝ)..(Real.pi/12), Psi (Real.cos v ^ 2) := by
    have := piece_lower_Psi (a := 0) (b := Real.pi/12) (c := 97/100) (p := 3228/10000)
      (M := 2296/10000) (Shi := 2017/1000000) (by positivity) (le_refl 0)
      (by linarith [Real.pi_pos]) (by norm_num) Tangent.Psi_97_100_lo Tangent.derivPsi_97_100_lo
      (by norm_num) ?_ ?_
    · simpa using this
    · rw [sin_pi_div_six', show Real.sin (2 * (0:ℝ)) = 0 from by simp]
      nlinarith
    · rw [sin_pi_div_six', show Real.sin (2 * (0:ℝ)) = 0 from by simp]
      nlinarith
  have b2 : (3545/10000) * (Real.pi/12) - (2818/10000) * (1232/1000000)
      ≤ ∫ v in (Real.pi/12)..(Real.pi/6), Psi (Real.cos v ^ 2) := by
    have hba : Real.pi/6 - Real.pi/12 = Real.pi/12 := by ring
    have := piece_lower_Psi (a := Real.pi/12) (b := Real.pi/6) (c := 169/200) (p := 3545/10000)
      (M := 2818/10000) (Shi := 1232/1000000) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by norm_num) Tangent.Psi_169_200_lo Tangent.derivPsi_169_200_lo
      (by norm_num) ?_ ?_
    · rw [hba] at this; exact this
    · rw [sin_pi_div_three', sin_pi_div_six']
      nlinarith
    · rw [sin_pi_div_three', sin_pi_div_six']
      nlinarith
  have b3 : (4315/10000) * (Real.pi/12) - (4363/10000) * (786/1000000)
      ≤ ∫ v in (Real.pi/6)..(Real.pi/4), Psi (Real.cos v ^ 2) := by
    have hba : Real.pi/4 - Real.pi/6 = Real.pi/12 := by ring
    have := piece_lower_Psi (a := Real.pi/6) (b := Real.pi/4) (c := 5/8) (p := 4315/10000)
      (M := 4363/10000) (Shi := 786/1000000) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by norm_num) Tangent.Psi_5_8_lo Tangent.derivPsi_5_8_lo
      (by norm_num) ?_ ?_
    · rw [hba] at this; exact this
    · rw [sin_pi_div_two', sin_pi_div_three']
      nlinarith
    · rw [sin_pi_div_two', sin_pi_div_three']
      nlinarith
  have b4 : (5908/10000) * (Real.pi/12) - (9072/10000) * (554/1000000)
      ≤ ∫ v in (Real.pi/4)..(Real.pi/3), Psi (Real.cos v ^ 2) := by
    have hba : Real.pi/3 - Real.pi/4 = Real.pi/12 := by ring
    have := piece_lower_Psi (a := Real.pi/4) (b := Real.pi/3) (c := 37/100) (p := 5908/10000)
      (M := 9072/10000) (Shi := 554/1000000) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      (le_refl _) (by norm_num) Tangent.Psi_37_100_lo Tangent.derivPsi_37_100_lo
      (by norm_num) ?_ ?_
    · rw [hba] at this; exact this
    · rw [sin_two_pi_div_three', sin_pi_div_two']
      nlinarith
    · rw [sin_two_pi_div_three', sin_pi_div_two']
      nlinarith
  have hi0 : IntervalIntegrable (fun v : ℝ => Psi (Real.cos v ^ 2)) volume 0 (Real.pi/12) :=
    intervalIntegrable_psi_cos_sq (by linarith [Real.pi_pos]) (le_refl 0) (by linarith [Real.pi_pos])
  have hi1 : IntervalIntegrable (fun v : ℝ => Psi (Real.cos v ^ 2)) volume (Real.pi/12) (Real.pi/6) :=
    intervalIntegrable_psi_cos_sq (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hi2 : IntervalIntegrable (fun v : ℝ => Psi (Real.cos v ^ 2)) volume (Real.pi/6) (Real.pi/4) :=
    intervalIntegrable_psi_cos_sq (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hi3 : IntervalIntegrable (fun v : ℝ => Psi (Real.cos v ^ 2)) volume (Real.pi/4) (Real.pi/3) :=
    intervalIntegrable_psi_cos_sq (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (le_refl _)
  have hi4 : IntervalIntegrable (fun v : ℝ => Psi (Real.cos v ^ 2)) volume 0 (Real.pi/6) :=
    intervalIntegrable_psi_cos_sq (by linarith [Real.pi_pos]) (le_refl 0) (by linarith [Real.pi_pos])
  have hi5 : IntervalIntegrable (fun v : ℝ => Psi (Real.cos v ^ 2)) volume 0 (Real.pi/4) :=
    intervalIntegrable_psi_cos_sq (by linarith [Real.pi_pos]) (le_refl 0) (by linarith [Real.pi_pos])
  have e1 : (∫ v in (0:ℝ)..(Real.pi/12), Psi (Real.cos v ^ 2))
      + (∫ v in (Real.pi/12)..(Real.pi/6), Psi (Real.cos v ^ 2))
      = ∫ v in (0:ℝ)..(Real.pi/6), Psi (Real.cos v ^ 2) :=
    intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  have e2 : (∫ v in (0:ℝ)..(Real.pi/6), Psi (Real.cos v ^ 2))
      + (∫ v in (Real.pi/6)..(Real.pi/4), Psi (Real.cos v ^ 2))
      = ∫ v in (0:ℝ)..(Real.pi/4), Psi (Real.cos v ^ 2) :=
    intervalIntegral.integral_add_adjacent_intervals hi4 hi2
  have e3 : (∫ v in (0:ℝ)..(Real.pi/4), Psi (Real.cos v ^ 2))
      + (∫ v in (Real.pi/4)..(Real.pi/3), Psi (Real.cos v ^ 2))
      = ∫ v in (0:ℝ)..(Real.pi/3), Psi (Real.cos v ^ 2) :=
    intervalIntegral.integral_add_adjacent_intervals hi5 hi3
  linarith [b1, b2, b3, b4, e1, e2, e3]

/-- **The `p = -3/2` moment bound.** -/
theorem Jm32_gt : (31 : ℝ) < Jm32 := by
  have hg := psi_pieces
  have hpi_lo : (157/50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hlow : (0.4430 : ℝ) ≤ ∫ v in (0 : ℝ)..(Real.pi / 3), Psi (Real.cos v ^ 2) := by
    linarith [hg, hpi_lo]
  have hc : (14668/10000 : ℝ) < cc ^ (-((3 : ℝ)/2)) := by
    simpa only [neg_div] using D6.c_pow_m32_lo
  have hccpos : (0:ℝ) < cc ^ (-((3 : ℝ)/2)) := by
    have : (0:ℝ) < cc := by rw [cc]; positivity
    positivity
  have hconst : ∫ v in (0 : ℝ)..(Real.pi / 3), Gm32 v
      = 2 * cc ^ (-((3 : ℝ) / 2)) * ∫ v in (0 : ℝ)..(Real.pi / 3), Psi (Real.cos v ^ 2) := by
    simp only [Gm32]
    rw [intervalIntegral.integral_const_mul]
  have hmono : 2 * (14668/10000 : ℝ) ≤ 2 * cc ^ (-((3 : ℝ)/2)) := by linarith
  have hbig : 24 * (2 * (14668/10000 : ℝ)) * 0.4430
      ≤ 24 * (2 * cc ^ (-((3 : ℝ)/2))) * ∫ v in (0 : ℝ)..(Real.pi / 3), Psi (Real.cos v ^ 2) := by
    have h2 : (0:ℝ) ≤ 2 * (14668/10000) := by norm_num
    calc 24 * (2 * (14668/10000 : ℝ)) * 0.4430
        = 24 * ((2 * (14668/10000 : ℝ)) * 0.4430) := by ring
      _ ≤ 24 * ((2 * cc ^ (-((3 : ℝ)/2))) * ∫ v in (0 : ℝ)..(Real.pi / 3), Psi (Real.cos v ^ 2)) := by
          apply mul_le_mul (le_refl 24) _ (by norm_num) (by norm_num)
          exact mul_le_mul hmono hlow (by norm_num) (by linarith)
      _ = 24 * (2 * cc ^ (-((3 : ℝ)/2))) * ∫ v in (0 : ℝ)..(Real.pi / 3), Psi (Real.cos v ^ 2) := by
          ring
  simp only [Jm32]
  rw [hconst]
  have hfin : (31:ℝ) < 24 * (2 * (14668/10000 : ℝ)) * 0.4430 := by norm_num
  linarith [hbig, hfin]

end MathathonT5
