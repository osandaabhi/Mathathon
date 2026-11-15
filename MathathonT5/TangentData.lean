/-
Rational two-sided data for the tangent argument at the four points
`97/100, 169/200, 5/8, 37/100` of `[1/4,1]` used to bound `J_{-3/2}` from below.

For `c` one of these points put `t = (2+c)/c` (rational).  Then

  `Psi c = t^(1/4) - 1`  and  `deriv Psi c = -1/(2 c^2 t^(3/4))`,

so a rational lower bound `p ≤ Psi c` is the rational inequality `(p+1)^4 ≤ t`, and a
rational lower bound `-M ≤ deriv Psi c` is the rational inequality `(1/(2 c^2 M))^4 ≤ t^3`.
Every constant below is checked by exact integer arithmetic.
-/
import MathathonT5.PsiConvex

noncomputable section
open scoped BigOperators

namespace MathathonT5

/-- `a ≤ t^(1/4)` from `a^4 ≤ t`. -/
lemma le_rpow_quarter {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (h : a ^ 4 ≤ t) :
    a ≤ t ^ ((1 : ℝ) / 4) := by
  have e : a = (a ^ 4) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast a 4, ← Real.rpow_mul ha]
    norm_num
  rw [e]
  exact Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- `a ≤ t^(3/4)` from `a^4 ≤ t^3`. -/
lemma le_rpow_three_quarters' {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (h : a ^ 4 ≤ t ^ 3) :
    a ≤ t ^ ((3 : ℝ) / 4) := by
  have e : a = (a ^ 4) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast a 4, ← Real.rpow_mul ha]
    norm_num
  have e2 : (t ^ 3) ^ ((1 : ℝ) / 4) = t ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast t 3, ← Real.rpow_mul ht]
    norm_num
  rw [e, ← e2]
  exact Real.rpow_le_rpow (by positivity) h (by norm_num)

namespace Tangent

/-- `Psi (97/100) ≥ 3228/10000`. -/
lemma Psi_97_100_lo : (3228/10000 : ℝ) ≤ Psi (97/100) := by
  have ht : ((2 + (97 : ℝ)/100) / ((97 : ℝ)/100)) = (297/97 : ℝ) := by norm_num
  have h : (3228/10000 + 1) ^ 4 ≤ (297/97 : ℝ) := by norm_num
  have hq := le_rpow_quarter (t := (297/97 : ℝ)) (a := 3228/10000 + 1) (by norm_num) (by norm_num) h
  simp only [Psi, ht]
  linarith

/-- `deriv Psi (97/100) ≥ -2296/10000`. -/
lemma derivPsi_97_100_lo : -(2296/10000 : ℝ) ≤ deriv Psi (97/100) := by
  have ht : ((2 + (97 : ℝ)/100) / ((97 : ℝ)/100)) = (297/97 : ℝ) := by norm_num
  rw [D3.deriv_Psi (97/100 : ℝ) (by norm_num), ht]
  have hq : (6250000/2700383 : ℝ) ≤ (297/97 : ℝ) ^ ((3 : ℝ)/4) :=
    le_rpow_three_quarters' (t := (297/97 : ℝ)) (a := (6250000/2700383 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hmono : 2 * ((97 : ℝ)/100) ^ 2 * (6250000/2700383 : ℝ) ≤
      2 * ((97 : ℝ)/100) ^ 2 * ((297/97 : ℝ) ^ ((3 : ℝ)/4)) := by
    apply mul_le_mul_of_nonneg_left hq
    positivity
  have h1 : (1 : ℝ) / (2 * ((97 : ℝ)/100) ^ 2 * ((297/97 : ℝ) ^ ((3 : ℝ)/4)))
      ≤ 1 / (2 * ((97 : ℝ)/100) ^ 2 * (6250000/2700383 : ℝ)) :=
    one_div_le_one_div_of_le (by norm_num) hmono
  have h2 : (1 : ℝ) / (2 * ((97 : ℝ)/100) ^ 2 * (6250000/2700383 : ℝ)) ≤ 2296/10000 := by norm_num
  rw [neg_div]
  linarith

/-- `Psi (169/200) ≥ 3545/10000`. -/
lemma Psi_169_200_lo : (3545/10000 : ℝ) ≤ Psi (169/200) := by
  have ht : ((2 + (169 : ℝ)/200) / ((169 : ℝ)/200)) = (569/169 : ℝ) := by norm_num
  have h : (3545/10000 + 1) ^ 4 ≤ (569/169 : ℝ) := by norm_num
  have hq := le_rpow_quarter (t := (569/169 : ℝ)) (a := 3545/10000 + 1) (by norm_num) (by norm_num) h
  simp only [Psi, ht]
  linarith

/-- `deriv Psi (169/200) ≥ -2818/10000`. -/
lemma derivPsi_169_200_lo : -(2818/10000 : ℝ) ≤ deriv Psi (169/200) := by
  have ht : ((2 + (169 : ℝ)/200) / ((169 : ℝ)/200)) = (569/169 : ℝ) := by norm_num
  rw [D3.deriv_Psi (169/200 : ℝ) (by norm_num), ht]
  have hq : (100000000/40242449 : ℝ) ≤ (569/169 : ℝ) ^ ((3 : ℝ)/4) :=
    le_rpow_three_quarters' (t := (569/169 : ℝ)) (a := (100000000/40242449 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hmono : 2 * ((169 : ℝ)/200) ^ 2 * (100000000/40242449 : ℝ) ≤
      2 * ((169 : ℝ)/200) ^ 2 * ((569/169 : ℝ) ^ ((3 : ℝ)/4)) := by
    apply mul_le_mul_of_nonneg_left hq
    positivity
  have h1 : (1 : ℝ) / (2 * ((169 : ℝ)/200) ^ 2 * ((569/169 : ℝ) ^ ((3 : ℝ)/4)))
      ≤ 1 / (2 * ((169 : ℝ)/200) ^ 2 * (100000000/40242449 : ℝ)) :=
    one_div_le_one_div_of_le (by norm_num) hmono
  have h2 : (1 : ℝ) / (2 * ((169 : ℝ)/200) ^ 2 * (100000000/40242449 : ℝ)) ≤ 2818/10000 := by norm_num
  rw [neg_div]
  linarith

/-- `Psi (5/8) ≥ 4315/10000`. -/
lemma Psi_5_8_lo : (4315/10000 : ℝ) ≤ Psi (5/8) := by
  have ht : ((2 + (5 : ℝ)/8) / ((5 : ℝ)/8)) = (21/5 : ℝ) := by norm_num
  have h : (4315/10000 + 1) ^ 4 ≤ (21/5 : ℝ) := by norm_num
  have hq := le_rpow_quarter (t := (21/5 : ℝ)) (a := 4315/10000 + 1) (by norm_num) (by norm_num) h
  simp only [Psi, ht]
  linarith

/-- `deriv Psi (5/8) ≥ -4363/10000`. -/
lemma derivPsi_5_8_lo : -(4363/10000 : ℝ) ≤ deriv Psi (5/8) := by
  have ht : ((2 + (5 : ℝ)/8) / ((5 : ℝ)/8)) = (21/5 : ℝ) := by norm_num
  rw [D3.deriv_Psi (5/8 : ℝ) (by norm_num), ht]
  have hq : (12800/4363 : ℝ) ≤ (21/5 : ℝ) ^ ((3 : ℝ)/4) :=
    le_rpow_three_quarters' (t := (21/5 : ℝ)) (a := (12800/4363 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hmono : 2 * ((5 : ℝ)/8) ^ 2 * (12800/4363 : ℝ) ≤
      2 * ((5 : ℝ)/8) ^ 2 * ((21/5 : ℝ) ^ ((3 : ℝ)/4)) := by
    apply mul_le_mul_of_nonneg_left hq
    positivity
  have h1 : (1 : ℝ) / (2 * ((5 : ℝ)/8) ^ 2 * ((21/5 : ℝ) ^ ((3 : ℝ)/4)))
      ≤ 1 / (2 * ((5 : ℝ)/8) ^ 2 * (12800/4363 : ℝ)) :=
    one_div_le_one_div_of_le (by norm_num) hmono
  have h2 : (1 : ℝ) / (2 * ((5 : ℝ)/8) ^ 2 * (12800/4363 : ℝ)) ≤ 4363/10000 := by norm_num
  rw [neg_div]
  linarith

/-- `Psi (37/100) ≥ 5908/10000`. -/
lemma Psi_37_100_lo : (5908/10000 : ℝ) ≤ Psi (37/100) := by
  have ht : ((2 + (37 : ℝ)/100) / ((37 : ℝ)/100)) = (237/37 : ℝ) := by norm_num
  have h : (5908/10000 + 1) ^ 4 ≤ (237/37 : ℝ) := by norm_num
  have hq := le_rpow_quarter (t := (237/37 : ℝ)) (a := 5908/10000 + 1) (by norm_num) (by norm_num) h
  simp only [Psi, ht]
  linarith

/-- `deriv Psi (37/100) ≥ -9072/10000`. -/
lemma derivPsi_37_100_lo : -(9072/10000 : ℝ) ≤ deriv Psi (37/100) := by
  have ht : ((2 + (37 : ℝ)/100) / ((37 : ℝ)/100)) = (237/37 : ℝ) := by norm_num
  rw [D3.deriv_Psi (37/100 : ℝ) (by norm_num), ht]
  have hq : (3125000/776223 : ℝ) ≤ (237/37 : ℝ) ^ ((3 : ℝ)/4) :=
    le_rpow_three_quarters' (t := (237/37 : ℝ)) (a := (3125000/776223 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hmono : 2 * ((37 : ℝ)/100) ^ 2 * (3125000/776223 : ℝ) ≤
      2 * ((37 : ℝ)/100) ^ 2 * ((237/37 : ℝ) ^ ((3 : ℝ)/4)) := by
    apply mul_le_mul_of_nonneg_left hq
    positivity
  have h1 : (1 : ℝ) / (2 * ((37 : ℝ)/100) ^ 2 * ((237/37 : ℝ) ^ ((3 : ℝ)/4)))
      ≤ 1 / (2 * ((37 : ℝ)/100) ^ 2 * (3125000/776223 : ℝ)) :=
    one_div_le_one_div_of_le (by norm_num) hmono
  have h2 : (1 : ℝ) / (2 * ((37 : ℝ)/100) ^ 2 * (3125000/776223 : ℝ)) ≤ 9072/10000 := by norm_num
  rw [neg_div]
  linarith

end Tangent

end MathathonT5
