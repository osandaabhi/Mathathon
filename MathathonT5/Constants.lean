/-
The constants `b = √(5/8)`, `c = √(3/5)` and the final scalar arithmetic of the
report's Theorem 1.2 (`B < -3/100`, `2(B + 4π/1000) < -1/40`).

Proved by swarm member `m2` (direction d4), integrated verbatim.
-/
import MathathonT5.Moments

noncomputable section
open scoped BigOperators

namespace MathathonT5.D6

/-! ## Elementary facts about `bb = √(5/8)` and `cc = √(3/5)` -/

theorem bb_nonneg : (0 : ℝ) ≤ bb := by
  rw [bb]; positivity

theorem bb_pos : (0 : ℝ) < bb := by
  rw [bb]; positivity

theorem bb_sq : bb ^ 2 = 5 / 8 := by
  rw [bb, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 8)]

theorem bb_rpow_three : bb ^ (3 : ℝ) = bb ^ 3 := Real.rpow_natCast bb 3

theorem cc_nonneg : (0 : ℝ) ≤ cc := by
  rw [cc]; positivity

theorem cc_pos : (0 : ℝ) < cc := by
  rw [cc]; positivity

theorem cc_sq : cc ^ 2 = 3 / 5 := by
  rw [cc, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 5)]

theorem cc_rpow_three : cc ^ (3 : ℝ) = cc ^ 3 := Real.rpow_natCast cc 3

/-! ## Square-root bounds -/

theorem b_bounds : 79 / 100 < bb ∧ bb < 791 / 1000 := by
  constructor
  · rw [bb, Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 79 / 100)]
    norm_num
  · rw [bb, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 791 / 1000)]
    norm_num

theorem c_bounds : 7745 / 10000 < cc ∧ cc < 7746 / 10000 := by
  constructor
  · rw [cc, Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 7745 / 10000)]
    norm_num
  · rw [cc, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7746 / 10000)]
    norm_num

/-! ## Helpers for fourth-root (`rpow` at `1/4`) comparisons -/

theorem rpow_quarter_pow_four {t : ℝ} (ht : 0 ≤ t) : (t ^ ((1 : ℝ) / 4)) ^ 4 = t := by
  simpa using Real.rpow_inv_natCast_pow ht (n := 4) (by norm_num)

/-- `t^(n/4) = (t^n)^(1/4)`: turn a quarter power of a natural power into a quarter power. -/
theorem rpow_nat_div_four {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    t ^ ((n : ℝ) / 4) = (t ^ n) ^ ((1 : ℝ) / 4) := by
  rw [show ((n : ℝ) / 4) = (n : ℝ) * ((1 : ℝ) / 4) by ring, Real.rpow_mul ht,
    Real.rpow_natCast]

/-- `(t^(-n/4))^4 = (t^n)⁻¹`. -/
theorem rpow_neg_nat_div_four {t : ℝ} (n : ℕ) (ht : 0 ≤ t) :
    (t ^ (-(n : ℝ) / 4)) ^ 4 = (t ^ n)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht,
    show (-(n : ℝ) / 4) * ((4 : ℕ) : ℝ) = -(n : ℝ) by ring,
    Real.rpow_neg ht, Real.rpow_natCast]

theorem rpow_quarter_lt_iff {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    t ^ ((1 : ℝ) / 4) < u ↔ t < u ^ 4 := by
  have h4 : (t ^ ((1 : ℝ) / 4)) ^ 4 = t := rpow_quarter_pow_four ht
  constructor
  · intro h
    have h' : (t ^ ((1 : ℝ) / 4)) ^ 4 < u ^ 4 :=
      (pow_lt_pow_iff_left₀ (Real.rpow_nonneg ht _) hu (by norm_num : (4 : ℕ) ≠ 0)).mpr h
    rwa [h4] at h'
  · intro h
    rw [← h4] at h
    exact (pow_lt_pow_iff_left₀ (Real.rpow_nonneg ht _) hu (by norm_num : (4 : ℕ) ≠ 0)).mp h

/-! ## Constant bounds as stated in the paper, with the one correction

The paper's `c_pow52_lo` claims `5282/10000 < cc^(5/2)`, but
`cc^(5/2) = (3/5)^(5/4) = 0.52806704...`, so that bound is **false**.
The corrected (true) bound below is `5280/10000 = 0.528 < 0.52806704`. -/

theorem c_pow52_lo : (5280 / 10000 : ℝ) < cc ^ ((5 : ℝ) / 2) := by
  have hsqrt : (88 / 100 : ℝ) < Real.sqrt cc := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 88 / 100)]
    nlinarith [c_bounds.1]
  have hsplit : cc ^ ((5 : ℝ) / 2) = (3 / 5 : ℝ) * Real.sqrt cc := by
    rw [show ((5 : ℝ) / 2) = 2 + 1 / 2 by norm_num, Real.rpow_add cc_pos,
      Real.rpow_two, ← Real.sqrt_eq_rpow, cc_sq]
  rw [hsplit]
  calc (5280 / 10000 : ℝ) = 3 / 5 * (88 / 100) := by norm_num
    _ < 3 / 5 * Real.sqrt cc := by
        linarith [mul_lt_mul_of_pos_left hsqrt (by norm_num : (0 : ℝ) < 3 / 5)]

theorem c_pow_m32_lo : (14668 / 10000 : ℝ) < cc ^ (-(3 : ℝ) / 2) := by
  have hcc : cc ^ (-(3 : ℝ) / 2) = (3 / 5 : ℝ) ^ (-(3 : ℝ) / 4) := by
    rw [show (-(3 : ℝ) / 2) = 2 * (-(3 : ℝ) / 4) by norm_num,
      Real.rpow_mul cc_nonneg, Real.rpow_two, cc_sq]
  rw [hcc]
  have hpow : ((3 / 5 : ℝ) ^ (-(3 : ℝ) / 4)) ^ 4 = ((3 / 5 : ℝ) ^ 3)⁻¹ :=
    rpow_neg_nat_div_four 3 (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hpos : (0 : ℝ) < (3 / 5 : ℝ) ^ (-(3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h4 : (14668 / 10000 : ℝ) ^ 4 < ((3 / 5 : ℝ) ^ (-(3 : ℝ) / 4)) ^ 4 := by
    rw [hpow]
    norm_num
  exact (pow_lt_pow_iff_left₀ (by norm_num) hpos.le (by norm_num : (4 : ℕ) ≠ 0)).mp h4

theorem nine_pow_lo : ((1 / 9 : ℝ)) ^ ((7 : ℝ) / 4) < 214 / 10000 := by
  have h : (1 / 9 : ℝ) ^ ((7 : ℝ) / 4) = ((1 / 9 : ℝ) ^ 7) ^ ((1 : ℝ) / 4) :=
    rpow_nat_div_four (by norm_num : (0 : ℝ) ≤ 1 / 9) 7
  rw [h, rpow_quarter_lt_iff (by positivity) (by norm_num : (0 : ℝ) ≤ 214 / 10000)]
  norm_num

/-! ## The final arithmetic -/

theorem bb_cube : bb ^ 3 = bb * (5 / 8) := by
  have h : bb ^ 3 = bb * bb ^ 2 := by ring
  rw [h, bb_sq]

/-- `cc^(5/2) = (3/5) * √cc`. -/
theorem cc_pow52_eq : cc ^ ((5 : ℝ) / 2) = (3 / 5 : ℝ) * Real.sqrt cc := by
  rw [show ((5 : ℝ) / 2) = 2 + 1 / 2 by norm_num, Real.rpow_add cc_pos,
    Real.rpow_two, ← Real.sqrt_eq_rpow, cc_sq]

/-- Upper bound for `cc^(5/2)`, enough to refute the paper's stated `5282/10000`. -/
theorem cc_pow52_upper : cc ^ ((5 : ℝ) / 2) < 264099 / 500000 := by
  rw [cc_pow52_eq]
  have hs : Real.sqrt cc < 88033 / 100000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 88033 / 100000)]
    nlinarith [c_bounds.2]
  nlinarith [hs]

/-- The `c_pow52_lo` bound exactly as stated in the paper is **false**:
`cc^(5/2) = (3/5)^(5/4) = 0.528067042...`, while `5282/10000 = 0.5282`. -/
theorem c_pow52_lo_false : ¬ ((5282 / 10000 : ℝ) < cc ^ ((5 : ℝ) / 2)) := by
  intro h
  linarith [cc_pow52_upper, h]

/-! ## `b` at `rpow` exponents -/

theorem bb_pow52_eq : bb ^ ((5 : ℝ) / 2) = (5 / 8 : ℝ) * Real.sqrt bb := by
  rw [show ((5 : ℝ) / 2) = 2 + 1 / 2 by norm_num, Real.rpow_add bb_pos,
    Real.rpow_two, ← Real.sqrt_eq_rpow, bb_sq]

theorem bb_pow52_bounds : (555 / 1000 : ℝ) < bb ^ ((5 : ℝ) / 2) ∧
    bb ^ ((5 : ℝ) / 2) < 556 / 1000 := by
  have hlo : (888 / 1000 : ℝ) < Real.sqrt bb := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 888 / 1000)]
    nlinarith [b_bounds.1]
  have hhi : Real.sqrt bb < 8895 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 8895 / 10000)]
    nlinarith [b_bounds.2]
  constructor
  · rw [bb_pow52_eq]
    nlinarith [hlo]
  · rw [bb_pow52_eq]
    nlinarith [hhi]

theorem bb_rpow_three_bounds : (4937 / 10000 : ℝ) < bb ^ (3 : ℝ) ∧
    bb ^ (3 : ℝ) < 4944 / 10000 := by
  rw [bb_rpow_three, bb_cube]
  constructor <;> nlinarith [b_bounds.1, b_bounds.2]

/-- Quantitative form: with the stated moment bounds the paper's `B` is below `-39/1000`
(the actual value at the corner is `-0.0428564...`). -/
theorem B_lt (J1 J5 Jm : ℝ) (h1 : J1 < 191 / 20) (h5 : 33 / 10 < J5) (hm : 31 < Jm) :
    (bb / 2) * J1 - (bb ^ 3 / 2) * J5 - ((bb - 1 / 2) / 3) * Jm < -39 / 1000 := by
  rw [bb_cube]
  have hb79 : (79 / 100 : ℝ) < bb := b_bounds.1
  have hc1 : (0 : ℝ) < bb / 2 := by linarith [bb_pos]
  have hc2 : (0 : ℝ) < bb * (5 / 8) / 2 := by linarith [bb_pos]
  have hc3 : (0 : ℝ) < (bb - 1 / 2) / 3 := by linarith [bb_pos]
  have e1 : (bb / 2) * J1 < (bb / 2) * (191 / 20) := mul_lt_mul_of_pos_left h1 hc1
  have e2 : (bb * (5 / 8) / 2) * (33 / 10) < (bb * (5 / 8) / 2) * J5 :=
    mul_lt_mul_of_pos_left h5 hc2
  have e3 : ((bb - 1 / 2) / 3) * 31 < ((bb - 1 / 2) / 3) * Jm := mul_lt_mul_of_pos_left hm hc3
  nlinarith [e1, e2, e3, hb79]

theorem B_neg (J1 J5 Jm : ℝ) (h1 : J1 < 191 / 20) (h5 : 33 / 10 < J5) (hm : 31 < Jm) :
    (bb / 2) * J1 - (bb ^ 3 / 2) * J5 - ((bb - 1 / 2) / 3) * Jm < -3 / 100 := by
  have h := B_lt J1 J5 Jm h1 h5 hm
  linarith

/-- The paper's exact rational for `B`. -/
theorem B_neg_exact (J1 J5 Jm : ℝ) (h1 : J1 < 191 / 20) (h5 : 33 / 10 < J5) (hm : 31 < Jm) :
    (bb / 2) * J1 - (bb ^ 3 / 2) * J5 - ((bb - 1 / 2) / 3) * Jm < -1989361 / 60000000 := by
  have h := B_lt J1 J5 Jm h1 h5 hm
  linarith

theorem saving (J1 J5 Jm : ℝ) (h1 : J1 < 191 / 20) (h5 : 33 / 10 < J5) (hm : 31 < Jm) :
    2 * ((bb / 2) * J1 - (bb ^ 3 / 2) * J5 - ((bb - 1 / 2) / 3) * Jm +
        4 * Real.pi / 1000) < -1 / 40 := by
  have hB := B_neg J1 J5 Jm h1 h5 hm
  nlinarith [hB, Real.pi_lt_four]

/-- Sharper form of `saving`, at the paper's stated threshold `-7/250`. -/
theorem saving_sharp (J1 J5 Jm : ℝ) (h1 : J1 < 191 / 20) (h5 : 33 / 10 < J5) (hm : 31 < Jm) :
    2 * ((bb / 2) * J1 - (bb ^ 3 / 2) * J5 - ((bb - 1 / 2) / 3) * Jm +
        4 * Real.pi / 1000) < -7 / 250 := by
  have hB := B_neg_exact J1 J5 Jm h1 h5 hm
  nlinarith [hB, Real.pi_lt_four]

end MathathonT5.D6
