/-
Rational node bounds for `Lam` (Mathathon report `attempt_8_T5`, Lemma 3.3's tables,
in exact rational form).

Every bound is reduced to a polynomial inequality over `ℚ` by clearing the fourth
root: `Lam p < A` ⟺ `(1-A)^4 * (2+p)^3 < p^3`.

Proved by swarm member `m6` (direction d2), integrated verbatim.
-/
import MathathonT5.Moments

noncomputable section
open scoped BigOperators

namespace MathathonT5.D4

open MathathonT5

/-! ## Clearing the fourth root -/

/-- `t^(3/4) = (t^3)^(1/4)` for `t ≥ 0`. -/
lemma rpow_three_quarters {t : ℝ} (ht : 0 ≤ t) :
    t ^ ((3 : ℝ) / 4) = (t ^ 3) ^ ((1 : ℝ) / 4) := by
  have h : (3 : ℝ) / 4 = ((3 : ℕ) : ℝ) * ((1 : ℝ) / 4) := by norm_num
  rw [h, Real.rpow_mul ht, Real.rpow_natCast]

/-- `(t^(3/4))^(4:ℝ) = t^3` for `t ≥ 0`: the identity that clears the fourth root. -/
lemma rpow_three_quarters_rpow_four {t : ℝ} (ht : 0 ≤ t) :
    (t ^ ((3 : ℝ) / 4)) ^ (4 : ℝ) = t ^ 3 := by
  rw [← Real.rpow_mul ht, show (3 : ℝ) / 4 * (4 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- `r^(4:ℝ) = r^4`. -/
lemma rpow_four_eq {r : ℝ} : r ^ (4 : ℝ) = r ^ 4 := Real.rpow_natCast r 4

/-- **Key reduction**: for `t, r ≥ 0`, `r < t^(3/4) ↔ r^4 < t^3`. -/
lemma lt_rpow_three_quarters_iff {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    r < t ^ ((3 : ℝ) / 4) ↔ r ^ 4 < t ^ 3 := by
  have hiff : r ^ (4 : ℝ) < (t ^ ((3 : ℝ) / 4)) ^ (4 : ℝ) ↔ r < t ^ ((3 : ℝ) / 4) :=
    Real.rpow_lt_rpow_iff (x := r) (y := t ^ ((3 : ℝ) / 4)) (z := 4) hr (by positivity)
      (by norm_num)
  rw [rpow_three_quarters_rpow_four ht, rpow_four_eq] at hiff
  exact hiff.symm

/-- **Key reduction**, the other way round: for `t, r ≥ 0`, `t^(3/4) < r ↔ t^3 < r^4`. -/
lemma rpow_three_quarters_lt_iff {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    t ^ ((3 : ℝ) / 4) < r ↔ t ^ 3 < r ^ 4 := by
  have hiff : (t ^ ((3 : ℝ) / 4)) ^ (4 : ℝ) < r ^ (4 : ℝ) ↔ t ^ ((3 : ℝ) / 4) < r :=
    Real.rpow_lt_rpow_iff (x := t ^ ((3 : ℝ) / 4)) (y := r) (z := 4) (by positivity) hr
      (by norm_num)
  rw [rpow_three_quarters_rpow_four ht, rpow_four_eq] at hiff
  exact hiff.symm

/-! ## Bounding `Lam` by clearing the fourth root -/

/-- If `0 < 2 + p`, `A ≤ 1` and `(1-A)^4 * (2+p)^3 < p^3`, then `Lam p < A`. -/
lemma Lam_lt_of {p A : ℝ} (h2p : 0 < 2 + p) (hA : A ≤ 1)
    (h : (1 - A) ^ 4 * (2 + p) ^ 3 < p ^ 3) : Lam p < A := by
  have hp : 0 ≤ p := by
    have hp3 : 0 < p ^ 3 := lt_of_le_of_lt (by positivity) h
    rcases le_or_gt 0 p with h' | h'
    · exact h'
    · nlinarith [sq_nonneg p]
  have h1A : 0 ≤ 1 - A := by linarith
  have ht : 0 ≤ p / (2 + p) := by positivity
  have key : 1 - A < (p / (2 + p)) ^ ((3 : ℝ) / 4) := by
    rw [lt_rpow_three_quarters_iff ht h1A, div_pow,
      lt_div_iff₀ (by positivity : (0 : ℝ) < (2 + p) ^ 3)]
    linarith
  unfold Lam
  linarith

/-! ## The table

The four bounds below are stated exactly as in the task; all four are true (three of them
with little room to spare, one -- `Lam (94/100)` -- very loosely).  The fifth requested
bound, `Lam 1 < 5613/10000`, is **false**, see `Lam_one_lt` and `Lam_one_lt'`. -/

theorem Lam_94_lt : Lam (94 / 100) < 6222 / 10000 := by
  refine Lam_lt_of (p := 94 / 100) (A := 6222 / 10000) (by norm_num) (by norm_num) (by norm_num)

theorem Lam_34_lt : Lam (3 / 4) < 6227 / 10000 := by
  refine Lam_lt_of (p := 3 / 4) (A := 6227 / 10000) (by norm_num) (by norm_num) (by norm_num)

theorem Lam_12_lt : Lam (1 / 2) < 7010 / 10000 := by
  refine Lam_lt_of (p := 1 / 2) (A := 7010 / 10000) (by norm_num) (by norm_num) (by norm_num)

theorem Lam_14_lt : Lam (1 / 4) < 8076 / 10000 := by
  refine Lam_lt_of (p := 1 / 4) (A := 8076 / 10000) (by norm_num) (by norm_num) (by norm_num)

/-- **CORRECTED BOUND.**  `Lam 1 < 5613/10000` is *false*:
`Lam 1 = 1 - (1/3)^(3/4) = 0.5613086623... > 0.5613`.  Here is the true value, rounded up
to five decimals. -/
theorem Lam_one_lt : Lam 1 < 56131 / 100000 := by
  refine Lam_lt_of (p := 1) (A := 56131 / 100000) (by norm_num) (by norm_num) (by norm_num)

/-- The corrected first entry of the table, rounded up to four decimals. -/
theorem Lam_one_lt' : Lam 1 < 5614 / 10000 := by
  refine Lam_lt_of (p := 1) (A := 5614 / 10000) (by norm_num) (by norm_num) (by norm_num)

/-- **USE THIS ONE for the chord argument.**  The requested bound `6222/10000` on
`Lam (94/100)` is true but far too loose: with it the `v`-piece chord bound for `J_{1/2}`
comes out as `9.586 > 191/20`, whereas the true value `Lam (94/100) = 0.5748076987...`
gives `9.4951 < 191/20`. -/
theorem Lam_94_lt' : Lam (94 / 100) < 5749 / 10000 := by
  refine Lam_lt_of (p := 94 / 100) (A := 5749 / 10000) (by norm_num) (by norm_num) (by norm_num)

/-! ## The remaining two targets -/

/-- `√cc = (3/5)^(1/4) < 0.880112` (true value `0.8801117368...`). -/
theorem sqrtc_lt : Real.sqrt cc < 880112 / 1000000 := by
  unfold cc
  rw [Real.sqrt_lt (by positivity) (by norm_num),
    Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

/-- `Lam` is antitone on `[1/4, 1]`: `x ↦ x/(2+x)` is increasing there and `t ↦ t^(3/4)`
is increasing on `t ≥ 0`, so `1 - (x/(2+x))^(3/4)` is decreasing. -/
theorem Lam_antitone : AntitoneOn Lam (Set.Icc (1 / 4 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  unfold Lam
  have hmono : x / (2 + x) ≤ y / (2 + y) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h0 : (0 : ℝ) ≤ x / (2 + x) := by positivity
  have := Real.rpow_le_rpow h0 hmono (by norm_num : (0 : ℝ) ≤ 3 / 4)
  linarith

end MathathonT5.D4
