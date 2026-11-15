/-
Rational affine majorants for `Lam x = 1 - (x/(2+x))^(3/4)` on the four `x`-intervals
`[1/4,1/2]`, `[1/2,3/4]`, `[3/4,47/50]`, `[93/100,1]`, and rational affine minorants for
`Psi`, obtained without convexity: a chord of the concave map `s ↦ s^r` composed with the
exact chord of the Möbius map `x ↦ x/(x+2)`, reduced in each case to a rational polynomial
inequality.

Proved by swarm member `m1` (direction d5), integrated verbatim.
-/
import MathathonT5.Moments

noncomputable section
open scoped BigOperators

namespace MathathonT5.D5

open Set

/-! ## rpow algebra helpers -/

theorem rpow_fourth_three_quarters (y : ℝ) (hy : 0 ≤ y) :
    (y ^ 4) ^ ((3 : ℝ) / 4) = y ^ 3 := by
  rw [← Real.rpow_natCast y 4, ← Real.rpow_mul hy ((4 : ℕ) : ℝ) ((3 : ℝ) / 4),
    show (((4 : ℕ) : ℝ) * ((3 : ℝ) / 4)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem rpow_fourth_one_quarter (y : ℝ) (hy : 0 ≤ y) :
    (y ^ 4) ^ ((1 : ℝ) / 4) = y := by
  rw [← Real.rpow_natCast y 4, ← Real.rpow_mul hy ((4 : ℕ) : ℝ) ((1 : ℝ) / 4),
    show (((4 : ℕ) : ℝ) * ((1 : ℝ) / 4)) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

theorem rpow_fourth_seven_quarters (y : ℝ) (hy : 0 ≤ y) :
    (y ^ 4) ^ ((7 : ℝ) / 4) = y ^ 7 := by
  rw [← Real.rpow_natCast y 4, ← Real.rpow_mul hy ((4 : ℕ) : ℝ) ((7 : ℝ) / 4),
    show (((4 : ℕ) : ℝ) * ((7 : ℝ) / 4)) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ## The general chord inequality for a concave power map -/

/-- For `0 ≤ r ≤ 1` the map `s ↦ s ^ r` is concave on `[0,∞)`, hence lies above its chords. -/
theorem rpow_chord_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {c1 c2 : ℝ} (hc1 : 0 ≤ c1)
    (h12 : c1 < c2) {s : ℝ} (hs : s ∈ Icc c1 c2) :
    c1 ^ r + (c2 ^ r - c1 ^ r) / (c2 - c1) * (s - c1) ≤ s ^ r := by
  have hconc : ConcaveOn ℝ (Ici (0 : ℝ)) fun t : ℝ => t ^ r := Real.concaveOn_rpow hr0 hr1
  obtain ⟨hs1, hs2⟩ := hs
  have hw : 0 < c2 - c1 := by linarith
  have hc2 : 0 ≤ c2 := le_trans hc1 h12.le
  set a : ℝ := (c2 - s) / (c2 - c1) with ha
  set b : ℝ := (s - c1) / (c2 - c1) with hb
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (by linarith) hw.le
  have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg (by linarith) hw.le
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have hkey := hconc.2 (mem_Ici.2 hc1) (mem_Ici.2 hc2) ha0 hb0 hab
  simp only [smul_eq_mul] at hkey
  have hax : a * c1 + b * c2 = s := by rw [ha, hb]; field_simp; ring
  rw [hax] at hkey
  have heq : a * c1 ^ r + b * c2 ^ r = c1 ^ r + (c2 ^ r - c1 ^ r) / (c2 - c1) * (s - c1) := by
    rw [ha, hb]; field_simp; ring
  rw [heq] at hkey
  exact hkey

/-! ## Affine majorants for `Lam` from an rpow chord plus the Möbius chord -/

/-- If `P + Q s ≤ s^(3/4)` holds on an interval containing the range of `x ↦ x/(x+2)` on
`[x1,x2]`, then `Lam` is below an explicit affine function on `[x1,x2]`. -/
theorem Lam_le_affine {x1 x2 P Q : ℝ} (hx1 : 0 < x1) (hx12 : x1 ≤ x2) (hQ : 0 < Q)
    (hP : ∀ s ∈ Icc (x1 / (x1 + 2)) (x2 / (x2 + 2)), P + Q * s ≤ s ^ ((3 : ℝ) / 4)) :
    ∀ x ∈ Icc x1 x2,
      MathathonT5.Lam x ≤
        1 - P - Q * (x1 / (x1 + 2) + 2 / ((x1 + 2) * (x2 + 2)) * (x - x1)) := by
  intro x hx
  obtain ⟨hxa, hxb⟩ := hx
  have hx2 : 0 < x2 := lt_of_lt_of_le hx1 hx12
  have hxm : 0 < x + 2 := by linarith
  have hu_mem : x / (x + 2) ∈ Icc (x1 / (x1 + 2)) (x2 / (x2 + 2)) := by
    constructor
    · rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < x1 + 2) hxm]
      nlinarith
    · rw [div_le_div_iff₀ hxm (by linarith : (0 : ℝ) < x2 + 2)]
      nlinarith
  have hchord :
      x1 / (x1 + 2) + 2 / ((x1 + 2) * (x2 + 2)) * (x - x1) ≤ x / (x + 2) := by
    have hpos : 0 < (x1 + 2) * (x2 + 2) * (x + 2) := by positivity
    have hid : x / (x + 2) - (x1 / (x1 + 2) + 2 / ((x1 + 2) * (x2 + 2)) * (x - x1))
        = (x - x1) * (x2 - x) * 2 / ((x1 + 2) * (x2 + 2) * (x + 2)) := by
      field_simp
      ring
    rw [← sub_nonneg, hid]
    apply div_nonneg _ hpos.le
    have h1 : 0 ≤ x - x1 := by linarith
    have h2 : 0 ≤ x2 - x := by linarith
    nlinarith
  have h1 := hP _ hu_mem
  have h2 : MathathonT5.Lam x = 1 - (x / (x + 2)) ^ ((3 : ℝ) / 4) := by
    simp only [MathathonT5.Lam, add_comm]
  rw [h2]
  have h3 : Q * (x1 / (x1 + 2) + 2 / ((x1 + 2) * (x2 + 2)) * (x - x1)) ≤ Q * (x / (x + 2)) :=
    mul_le_mul_of_nonneg_left hchord hQ.le
  linarith


/-- `Lam` is below an explicit rational affine function on `[1/4, 1/2]`
(convexity-free certificate: a chord of the concave map `s ↦ s^(3/4)` composed with
the exact chord of the Möbius map `x ↦ x/(x+2)`).  Knots `4/7`, `15/22`. -/
theorem Lam_piece_one :
    ∀ x ∈ Icc (1/4 : ℝ) (1/2),
      MathathonT5.Lam x ≤ 148975379/163008765 + (-69014176/163008765) * x := by
  set Q : ℝ := (3375/10648 - 64/343) / (50625/234256 - 256/2401) with hQ
  set P : ℝ := 64/343 - Q * (256/2401) with hP
  have hQpos : 0 < Q := by rw [hQ]; norm_num
  have hkey : ∀ x ∈ Icc (1/4 : ℝ) (1/2),
      MathathonT5.Lam x ≤ 1 - P - Q * (1/4 / (1/4 + 2) +
        2 / ((1/4 + 2) * (1/2 + 2)) * (x - 1/4)) :=
    Lam_le_affine (x1 := 1/4) (x2 := 1/2) (P := P) (Q := Q)
      (by norm_num) (by norm_num) hQpos (by
        intro s hs
        have hu1 : (1/4 : ℝ) / (1/4 + 2) = 1/9 := by norm_num
        have hu2 : (1/2 : ℝ) / (1/2 + 2) = 1/5 := by norm_num
        rw [hu1, hu2] at hs
        have hs' : s ∈ Icc (256/2401 : ℝ) (50625/234256) := by
          refine ⟨?_, ?_⟩
          · linarith [hs.1, (by norm_num : (256/2401 : ℝ) ≤ 1/9)]
          · linarith [hs.2, (by norm_num : (1/5 : ℝ) ≤ 50625/234256)]
        have hch := rpow_chord_le (r := (3 : ℝ) / 4) (by norm_num) (by norm_num)
          (c1 := (256/2401 : ℝ)) (c2 := (50625/234256 : ℝ)) (by norm_num) (by norm_num) hs'
        have hc1 : ((256/2401 : ℝ)) ^ ((3 : ℝ) / 4) = 64/343 := by
          have h := rpow_fourth_three_quarters (4/7 : ℝ) (by norm_num)
          norm_num at h ⊢
        have hc2 : ((50625/234256 : ℝ)) ^ ((3 : ℝ) / 4) = 3375/10648 := by
          have h := rpow_fourth_three_quarters (15/22 : ℝ) (by norm_num)
          norm_num at h ⊢
        rw [hc1, hc2] at hch
        have hsplit : P + Q * s = 64/343 + (3375/10648 - 64/343) / (50625/234256 - 256/2401) *
            (s - 256/2401) := by
          rw [hP, hQ]; ring
        rw [hsplit]; exact hch)
  intro x hx
  have h1 := hkey x hx
  have h2 : (1 : ℝ) - P - Q * (1/4 / (1/4 + 2) +
      2 / ((1/4 + 2) * (1/2 + 2)) * (x - 1/4))
      = 148975379/163008765 + (-69014176/163008765) * x := by
    rw [hP, hQ]; field_simp; ring
  rw [h2] at h1
  exact h1

/-- `Lam` is below an explicit rational affine function on `[1/2, 3/4]`
(convexity-free certificate: a chord of the concave map `s ↦ s^(3/4)` composed with
the exact chord of the Möbius map `x ↦ x/(x+2)`).  Knots `2/3`, `8/11`. -/
theorem Lam_piece_two :
    ∀ x ∈ Icc (1/2 : ℝ) (3/4),
      MathathonT5.Lam x ≤ 52257/60950 + (-9528/30475) * x := by
  set Q : ℝ := (512/1331 - 8/27) / (4096/14641 - 16/81) with hQ
  set P : ℝ := 8/27 - Q * (16/81) with hP
  have hQpos : 0 < Q := by rw [hQ]; norm_num
  have hkey : ∀ x ∈ Icc (1/2 : ℝ) (3/4),
      MathathonT5.Lam x ≤ 1 - P - Q * (1/2 / (1/2 + 2) +
        2 / ((1/2 + 2) * (3/4 + 2)) * (x - 1/2)) :=
    Lam_le_affine (x1 := 1/2) (x2 := 3/4) (P := P) (Q := Q)
      (by norm_num) (by norm_num) hQpos (by
        intro s hs
        have hu1 : (1/2 : ℝ) / (1/2 + 2) = 1/5 := by norm_num
        have hu2 : (3/4 : ℝ) / (3/4 + 2) = 3/11 := by norm_num
        rw [hu1, hu2] at hs
        have hs' : s ∈ Icc (16/81 : ℝ) (4096/14641) := by
          refine ⟨?_, ?_⟩
          · linarith [hs.1, (by norm_num : (16/81 : ℝ) ≤ 1/5)]
          · linarith [hs.2, (by norm_num : (3/11 : ℝ) ≤ 4096/14641)]
        have hch := rpow_chord_le (r := (3 : ℝ) / 4) (by norm_num) (by norm_num)
          (c1 := (16/81 : ℝ)) (c2 := (4096/14641 : ℝ)) (by norm_num) (by norm_num) hs'
        have hc1 : ((16/81 : ℝ)) ^ ((3 : ℝ) / 4) = 8/27 := by
          have h := rpow_fourth_three_quarters (2/3 : ℝ) (by norm_num)
          norm_num at h ⊢
        have hc2 : ((4096/14641 : ℝ)) ^ ((3 : ℝ) / 4) = 512/1331 := by
          have h := rpow_fourth_three_quarters (8/11 : ℝ) (by norm_num)
          norm_num at h ⊢
        rw [hc1, hc2] at hch
        have hsplit : P + Q * s = 8/27 + (512/1331 - 8/27) / (4096/14641 - 16/81) *
            (s - 16/81) := by
          rw [hP, hQ]; ring
        rw [hsplit]; exact hch)
  intro x hx
  have h1 := hkey x hx
  have h2 : (1 : ℝ) - P - Q * (1/2 / (1/2 + 2) +
      2 / ((1/2 + 2) * (3/4 + 2)) * (x - 1/2))
      = 52257/60950 + (-9528/30475) * x := by
    rw [hP, hQ]; field_simp; ring
  rw [h2] at h1
  exact h1

/-- `Lam` is below an explicit rational affine function on `[3/4, 47/50]`
(convexity-free certificate: a chord of the concave map `s ↦ s^(3/4)` composed with
the exact chord of the Möbius map `x ↦ x/(x+2)`).  Knots `13/18`, `16/21`. -/
theorem Lam_piece_three :
    ∀ x ∈ Icc (3/4 : ℝ) (47/50),
      MathathonT5.Lam x ≤ 5510230771/6802361181 + (-62959200/251939303) * x := by
  set Q : ℝ := (4096/9261 - 2197/5832) / (65536/194481 - 28561/104976) with hQ
  set P : ℝ := 2197/5832 - Q * (28561/104976) with hP
  have hQpos : 0 < Q := by rw [hQ]; norm_num
  have hkey : ∀ x ∈ Icc (3/4 : ℝ) (47/50),
      MathathonT5.Lam x ≤ 1 - P - Q * (3/4 / (3/4 + 2) +
        2 / ((3/4 + 2) * (47/50 + 2)) * (x - 3/4)) :=
    Lam_le_affine (x1 := 3/4) (x2 := 47/50) (P := P) (Q := Q)
      (by norm_num) (by norm_num) hQpos (by
        intro s hs
        have hu1 : (3/4 : ℝ) / (3/4 + 2) = 3/11 := by norm_num
        have hu2 : (47/50 : ℝ) / (47/50 + 2) = 47/147 := by norm_num
        rw [hu1, hu2] at hs
        have hs' : s ∈ Icc (28561/104976 : ℝ) (65536/194481) := by
          refine ⟨?_, ?_⟩
          · linarith [hs.1, (by norm_num : (28561/104976 : ℝ) ≤ 3/11)]
          · linarith [hs.2, (by norm_num : (47/147 : ℝ) ≤ 65536/194481)]
        have hch := rpow_chord_le (r := (3 : ℝ) / 4) (by norm_num) (by norm_num)
          (c1 := (28561/104976 : ℝ)) (c2 := (65536/194481 : ℝ)) (by norm_num) (by norm_num) hs'
        have hc1 : ((28561/104976 : ℝ)) ^ ((3 : ℝ) / 4) = 2197/5832 := by
          have h := rpow_fourth_three_quarters (13/18 : ℝ) (by norm_num)
          norm_num at h ⊢
        have hc2 : ((65536/194481 : ℝ)) ^ ((3 : ℝ) / 4) = 4096/9261 := by
          have h := rpow_fourth_three_quarters (16/21 : ℝ) (by norm_num)
          norm_num at h ⊢
        rw [hc1, hc2] at hch
        have hsplit : P + Q * s = 2197/5832 + (4096/9261 - 2197/5832) / (65536/194481 - 28561/104976) *
            (s - 28561/104976) := by
          rw [hP, hQ]; ring
        rw [hsplit]; exact hch)
  intro x hx
  have h1 := hkey x hx
  have h2 : (1 : ℝ) - P - Q * (3/4 / (3/4 + 2) +
      2 / ((3/4 + 2) * (47/50 + 2)) * (x - 3/4))
      = 5510230771/6802361181 + (-62959200/251939303) * x := by
    rw [hP, hQ]; field_simp; ring
  rw [h2] at h1
  exact h1

/-- `Lam` is below an explicit rational affine function on `[93/100, 1]`
(convexity-free certificate: a chord of the concave map `s ↦ s^(3/4)` composed with
the exact chord of the Möbius map `x ↦ x/(x+2)`).  Knots `3/4`, `16/21`. -/
theorem Lam_piece_four :
    ∀ x ∈ Icc (93/100 : ℝ) (1),
      MathathonT5.Lam x ≤ 236202671/300106715 + (-13548640/60021343) * x := by
  set Q : ℝ := (4096/9261 - 27/64) / (65536/194481 - 81/256) with hQ
  set P : ℝ := 27/64 - Q * (81/256) with hP
  have hQpos : 0 < Q := by rw [hQ]; norm_num
  have hkey : ∀ x ∈ Icc (93/100 : ℝ) (1),
      MathathonT5.Lam x ≤ 1 - P - Q * (93/100 / (93/100 + 2) +
        2 / ((93/100 + 2) * (1 + 2)) * (x - 93/100)) :=
    Lam_le_affine (x1 := 93/100) (x2 := 1) (P := P) (Q := Q)
      (by norm_num) (by norm_num) hQpos (by
        intro s hs
        have hu1 : (93/100 : ℝ) / (93/100 + 2) = 93/293 := by norm_num
        have hu2 : (1 : ℝ) / (1 + 2) = 1/3 := by norm_num
        rw [hu1, hu2] at hs
        have hs' : s ∈ Icc (81/256 : ℝ) (65536/194481) := by
          refine ⟨?_, ?_⟩
          · linarith [hs.1, (by norm_num : (81/256 : ℝ) ≤ 93/293)]
          · linarith [hs.2, (by norm_num : (1/3 : ℝ) ≤ 65536/194481)]
        have hch := rpow_chord_le (r := (3 : ℝ) / 4) (by norm_num) (by norm_num)
          (c1 := (81/256 : ℝ)) (c2 := (65536/194481 : ℝ)) (by norm_num) (by norm_num) hs'
        have hc1 : ((81/256 : ℝ)) ^ ((3 : ℝ) / 4) = 27/64 := by
          have h := rpow_fourth_three_quarters (3/4 : ℝ) (by norm_num)
          norm_num at h ⊢
        have hc2 : ((65536/194481 : ℝ)) ^ ((3 : ℝ) / 4) = 4096/9261 := by
          have h := rpow_fourth_three_quarters (16/21 : ℝ) (by norm_num)
          norm_num at h ⊢
        rw [hc1, hc2] at hch
        have hsplit : P + Q * s = 27/64 + (4096/9261 - 27/64) / (65536/194481 - 81/256) *
            (s - 81/256) := by
          rw [hP, hQ]; ring
        rw [hsplit]; exact hch)
  intro x hx
  have h1 := hkey x hx
  have h2 : (1 : ℝ) - P - Q * (93/100 / (93/100 + 2) +
      2 / ((93/100 + 2) * (1 + 2)) * (x - 93/100))
      = 236202671/300106715 + (-13548640/60021343) * x := by
    rw [hP, hQ]; field_simp; ring
  rw [h2] at h1
  exact h1


/-! ## Affine majorants for `x ↦ (x/(x+2))^(7/4)` (J_{5/2} needs an upper bound) -/

/-- For `p ≥ 1` the map `s ↦ s ^ p` is convex, hence lies below its chords. -/
theorem rpow_chord_ge {p : ℝ} (hp : 1 ≤ p) {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (h12 : c1 < c2)
    {s : ℝ} (hs : s ∈ Icc c1 c2) :
    s ^ p ≤ c1 ^ p + (c2 ^ p - c1 ^ p) / (c2 - c1) * (s - c1) := by
  have hcv : ConvexOn ℝ (Ici (0 : ℝ)) fun t : ℝ => t ^ p := convexOn_rpow hp
  obtain ⟨hs1, hs2⟩ := hs
  have hw : 0 < c2 - c1 := by linarith
  have hc2 : 0 ≤ c2 := le_trans hc1 h12.le
  set a : ℝ := (c2 - s) / (c2 - c1) with ha
  set b : ℝ := (s - c1) / (c2 - c1) with hb
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (by linarith) hw.le
  have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg (by linarith) hw.le
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have hkey := hcv.2 (mem_Ici.2 hc1) (mem_Ici.2 hc2) ha0 hb0 hab
  simp only [smul_eq_mul] at hkey
  have hax : a * c1 + b * c2 = s := by rw [ha, hb]; field_simp; ring
  rw [hax] at hkey
  have heq : a * c1 ^ p + b * c2 ^ p = c1 ^ p + (c2 ^ p - c1 ^ p) / (c2 - c1) * (s - c1) := by
    rw [ha, hb]; field_simp; ring
  rw [heq] at hkey
  exact hkey

/-- If `s ↦ s^(7/4)` is below `P + Q s` on an interval `[c1,c2]` containing the range of
`x ↦ x/(x+2)` on `[x1,x2]`, then it is below an explicit affine function on `[x1,x2]`. -/
theorem h7_le_affine {x1 x2 c1 c2 P Q : ℝ} (hx1 : 0 < x1) (hx12 : x1 ≤ x2)
    (hc1 : c1 ≤ x1 / (x1 + 2)) (hc2 : x2 / (x2 + 2) ≤ c2) (hQ : 0 < Q)
    (hP : ∀ s ∈ Icc c1 c2, s ^ ((7 : ℝ) / 4) ≤ P + Q * s) :
    ∀ x ∈ Icc x1 x2,
      (x / (x + 2)) ^ ((7 : ℝ) / 4) ≤ P + Q * (x2 / (x2 + 2) + 2 / (x2 + 2) ^ 2 * (x - x2)) := by
  intro x hx
  obtain ⟨hxa, hxb⟩ := hx
  have hx2 : 0 < x2 := lt_of_lt_of_le hx1 hx12
  have hxm : 0 < x + 2 := by linarith
  have hu1 : x1 / (x1 + 2) ≤ x / (x + 2) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < x1 + 2) hxm]
    nlinarith
  have hu2 : x / (x + 2) ≤ x2 / (x2 + 2) := by
    rw [div_le_div_iff₀ hxm (by linarith : (0 : ℝ) < x2 + 2)]
    nlinarith
  have humem : x / (x + 2) ∈ Icc c1 c2 := ⟨le_trans hc1 hu1, le_trans hu2 hc2⟩
  have htangent : x / (x + 2) ≤ x2 / (x2 + 2) + 2 / (x2 + 2) ^ 2 * (x - x2) := by
    have hpos : 0 < (x + 2) * (x2 + 2) ^ 2 := by positivity
    have hid : x2 / (x2 + 2) + 2 / (x2 + 2) ^ 2 * (x - x2) - x / (x + 2)
        = 2 * (x - x2) ^ 2 / ((x + 2) * (x2 + 2) ^ 2) := by
      field_simp
      ring
    have : 0 ≤ 2 * (x - x2) ^ 2 / ((x + 2) * (x2 + 2) ^ 2) := by positivity
    linarith [hid ▸ this]
  have h1 := hP _ humem
  have h2 : Q * (x / (x + 2)) ≤ Q * (x2 / (x2 + 2) + 2 / (x2 + 2) ^ 2 * (x - x2)) :=
    mul_le_mul_of_nonneg_left htangent hQ.le
  linarith

theorem h7_piece_one :
    ∀ x ∈ Icc (1/4 : ℝ) (1/2),
      (x / (x + 2)) ^ ((7 : ℝ) / 4) ≤ -3201828786551/330750580052200 + 5873087213449/41343822506525 * x := by
  set Q : ℝ := (170859375/2494357888 - 16384/823543) / (50625/234256 - 256/2401) with hQ
  set P : ℝ := 16384/823543 - Q * (256/2401) with hP
  have hQpos : 0 < Q := by rw [hQ]; norm_num
  have hkey := h7_le_affine (x1 := 1/4) (x2 := 1/2) (c1 := (256/2401 : ℝ))
      (c2 := (50625/234256 : ℝ)) (P := P) (Q := Q) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hQpos (by
        intro s hs
        have hch := rpow_chord_ge (p := (7 : ℝ) / 4) (by norm_num)
          (c1 := (256/2401 : ℝ)) (c2 := (50625/234256 : ℝ)) (by norm_num) (by norm_num) hs
        have hc1 : ((256/2401 : ℝ)) ^ ((7 : ℝ) / 4) = 16384/823543 := by
          have h := rpow_fourth_seven_quarters (4/7 : ℝ) (by norm_num)
          norm_num at h ⊢
        have hc2 : ((50625/234256 : ℝ)) ^ ((7 : ℝ) / 4) = 170859375/2494357888 := by
          have h := rpow_fourth_seven_quarters (15/22 : ℝ) (by norm_num)
          norm_num at h ⊢
        rw [hc1, hc2] at hch
        have hsplit : P + Q * s = 16384/823543 + (170859375/2494357888 - 16384/823543) / (50625/234256 - 256/2401) *
            (s - 256/2401) := by
          rw [hP, hQ]; ring
        rw [hsplit]; exact hch)
  intro x hx
  have h1 := hkey x hx
  have h2 : P + Q * (1/2 / (1/2 + 2) + 2 / (1/2 + 2) ^ 2 * (x - 1/2))
      = -3201828786551/330750580052200 + 5873087213449/41343822506525 * x := by
    rw [hP, hQ]; field_simp; ring
  rw [h2] at h1
  exact h1

theorem h7_piece_two :
    ∀ x ∈ Icc (1/2 : ℝ) (3/4),
      (x / (x + 2)) ^ ((7 : ℝ) / 4) ≤ -397262552/26503357815 + 4184227072/26503357815 * x := by
  set Q : ℝ := (2097152/19487171 - 128/2187) / (4096/14641 - 16/81) with hQ
  set P : ℝ := 128/2187 - Q * (16/81) with hP
  have hQpos : 0 < Q := by rw [hQ]; norm_num
  have hkey := h7_le_affine (x1 := 1/2) (x2 := 3/4) (c1 := (16/81 : ℝ))
      (c2 := (4096/14641 : ℝ)) (P := P) (Q := Q) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hQpos (by
        intro s hs
        have hch := rpow_chord_ge (p := (7 : ℝ) / 4) (by norm_num)
          (c1 := (16/81 : ℝ)) (c2 := (4096/14641 : ℝ)) (by norm_num) (by norm_num) hs
        have hc1 : ((16/81 : ℝ)) ^ ((7 : ℝ) / 4) = 128/2187 := by
          have h := rpow_fourth_seven_quarters (2/3 : ℝ) (by norm_num)
          norm_num at h ⊢
        have hc2 : ((4096/14641 : ℝ)) ^ ((7 : ℝ) / 4) = 2097152/19487171 := by
          have h := rpow_fourth_seven_quarters (8/11 : ℝ) (by norm_num)
          norm_num at h ⊢
        rw [hc1, hc2] at hch
        have hsplit : P + Q * s = 128/2187 + (2097152/19487171 - 128/2187) / (4096/14641 - 16/81) *
            (s - 16/81) := by
          rw [hP, hQ]; ring
        rw [hsplit]; exact hch)
  intro x hx
  have h1 := hkey x hx
  have h2 : P + Q * (3/4 / (3/4 + 2) + 2 / (3/4 + 2) ^ 2 * (x - 3/4))
      = -397262552/26503357815 + 4184227072/26503357815 * x := by
    rw [hP, hQ]; field_simp; ring
  rw [h2] at h1
  exact h1

theorem h7_piece_three :
    ∀ x ∈ Icc (3/4 : ℝ) (47/50),
      (x / (x + 2)) ^ ((7 : ℝ) / 4) ≤ -24578446992057391/1272899197386215784 + 2933580734385625/17679155519252997 * x := by
  set Q : ℝ := (268435456/1801088541 - 62748517/612220032) / (65536/194481 - 28561/104976) with hQ
  set P : ℝ := 62748517/612220032 - Q * (28561/104976) with hP
  have hQpos : 0 < Q := by rw [hQ]; norm_num
  have hkey := h7_le_affine (x1 := 3/4) (x2 := 47/50) (c1 := (28561/104976 : ℝ))
      (c2 := (65536/194481 : ℝ)) (P := P) (Q := Q) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hQpos (by
        intro s hs
        have hch := rpow_chord_ge (p := (7 : ℝ) / 4) (by norm_num)
          (c1 := (28561/104976 : ℝ)) (c2 := (65536/194481 : ℝ)) (by norm_num) (by norm_num) hs
        have hc1 : ((28561/104976 : ℝ)) ^ ((7 : ℝ) / 4) = 62748517/612220032 := by
          have h := rpow_fourth_seven_quarters (13/18 : ℝ) (by norm_num)
          norm_num at h ⊢
        have hc2 : ((65536/194481 : ℝ)) ^ ((7 : ℝ) / 4) = 268435456/1801088541 := by
          have h := rpow_fourth_seven_quarters (16/21 : ℝ) (by norm_num)
          norm_num at h ⊢
        rw [hc1, hc2] at hch
        have hsplit : P + Q * s = 62748517/612220032 + (268435456/1801088541 - 62748517/612220032) / (65536/194481 - 28561/104976) *
            (s - 28561/104976) := by
          rw [hP, hQ]; ring
        rw [hsplit]; exact hch)
  intro x hx
  have h1 := hkey x hx
  have h2 : P + Q * (47/50 / (47/50 + 2) + 2 / (47/50 + 2) ^ 2 * (x - 47/50))
      = -24578446992057391/1272899197386215784 + 2933580734385625/17679155519252997 * x := by
    rw [hP, hQ]; field_simp; ring
  rw [h2] at h1
  exact h1

theorem h7_piece_four :
    ∀ x ∈ Icc (93/100 : ℝ) (1),
      (x / (x + 2)) ^ ((7 : ℝ) / 4) ≤ -118877303231/5463720319680 + 459065871937/2731860159840 * x := by
  set Q : ℝ := (268435456/1801088541 - 2187/16384) / (65536/194481 - 81/256) with hQ
  set P : ℝ := 2187/16384 - Q * (81/256) with hP
  have hQpos : 0 < Q := by rw [hQ]; norm_num
  have hkey := h7_le_affine (x1 := 93/100) (x2 := 1) (c1 := (81/256 : ℝ))
      (c2 := (65536/194481 : ℝ)) (P := P) (Q := Q) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hQpos (by
        intro s hs
        have hch := rpow_chord_ge (p := (7 : ℝ) / 4) (by norm_num)
          (c1 := (81/256 : ℝ)) (c2 := (65536/194481 : ℝ)) (by norm_num) (by norm_num) hs
        have hc1 : ((81/256 : ℝ)) ^ ((7 : ℝ) / 4) = 2187/16384 := by
          have h := rpow_fourth_seven_quarters (3/4 : ℝ) (by norm_num)
          norm_num at h ⊢
        have hc2 : ((65536/194481 : ℝ)) ^ ((7 : ℝ) / 4) = 268435456/1801088541 := by
          have h := rpow_fourth_seven_quarters (16/21 : ℝ) (by norm_num)
          norm_num at h ⊢
        rw [hc1, hc2] at hch
        have hsplit : P + Q * s = 2187/16384 + (268435456/1801088541 - 2187/16384) / (65536/194481 - 81/256) *
            (s - 81/256) := by
          rw [hP, hQ]; ring
        rw [hsplit]; exact hch)
  intro x hx
  have h1 := hkey x hx
  have h2 : P + Q * (1 / (1 + 2) + 2 / (1 + 2) ^ 2 * (x - 1))
      = -118877303231/5463720319680 + 459065871937/2731860159840 * x := by
    rw [hP, hQ]; field_simp; ring
  rw [h2] at h1
  exact h1


/-! ## Affine minorants for `Psi` (J_{-3/2} needs a lower bound) -/

/-- The tangent line at `y0` of the convex map `w ↦ 1/w` lies below it. -/
theorem inv_ge_tangent {y y0 : ℝ} (hy : 0 < y) (hy0 : 0 < y0) :
    1 / y0 - (1 / y0 ^ 2) * (y - y0) ≤ 1 / y := by
  have hpos : 0 < y * y0 ^ 2 := by positivity
  have h : 1 / y - (1 / y0 - (1 / y0 ^ 2) * (y - y0)) = (y - y0) ^ 2 / (y * y0 ^ 2) := by
    field_simp
    ring
  have hnn : 0 ≤ (y - y0) ^ 2 / (y * y0 ^ 2) := div_nonneg (sq_nonneg _) hpos.le
  linarith [h ▸ hnn]

/-- `(x/(x+2))^(1/4) ≤ Y` follows from `x ≤ Y^4 (x+2)` for `Y ≥ 0`. -/
theorem rpow_quarter_le_of_le_fourth {x Y : ℝ} (hx : 0 < x) (hY : 0 ≤ Y)
    (h : x / (x + 2) ≤ Y ^ 4) : (x / (x + 2)) ^ ((1 : ℝ) / 4) ≤ Y := by
  have ha : (0 : ℝ) < x / (x + 2) := by positivity
  have hy4 : ((x / (x + 2)) ^ ((1 : ℝ) / 4)) ^ 4 = x / (x + 2) := by
    rw [← Real.rpow_natCast ((x / (x + 2)) ^ ((1 : ℝ) / 4)) 4,
      ← Real.rpow_mul ha.le ((1 : ℝ) / 4) ((4 : ℕ) : ℝ),
      show ((1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have step : (((x / (x + 2)) ^ ((1 : ℝ) / 4)) ^ 4) ^ ((1 : ℝ) / 4) ≤ (Y ^ 4) ^ ((1 : ℝ) / 4) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [hy4]; exact h
  calc (x / (x + 2)) ^ ((1 : ℝ) / 4)
      = (((x / (x + 2)) ^ ((1 : ℝ) / 4)) ^ 4) ^ ((1 : ℝ) / 4) := by
        rw [hy4]
    _ ≤ (Y ^ 4) ^ ((1 : ℝ) / 4) := step
    _ = Y := rpow_fourth_one_quarter Y hY

/-- A rational affine minorant of `Psi` from an affine upper bound of `x ↦ (x/(x+2))^(1/4)`. -/
theorem Psi_ge_affine {x1 x2 y0 m x0 : ℝ} (hx1 : 0 < x1) (_hx12 : x1 ≤ x2) (hy0 : 0 < y0)
    (htan : ∀ x ∈ Icc x1 x2, (x / (x + 2)) ^ ((1 : ℝ) / 4) ≤ y0 + m * (x - x0)) :
    ∀ x ∈ Icc x1 x2, 1 / y0 - 1 - (1 / y0 ^ 2) * (m * (x - x0)) ≤ MathathonT5.Psi x := by
  intro x hx
  have hxp : 0 < x := lt_of_lt_of_le hx1 hx.1
  have hx2p : 0 < x + 2 := by linarith
  have ha : 0 < x / (x + 2) := by positivity
  set y : ℝ := (x / (x + 2)) ^ ((1 : ℝ) / 4) with hy
  have hypos : 0 < y := Real.rpow_pos_of_pos ha _
  have h1 : 1 / y0 - (1 / y0 ^ 2) * (y - y0) ≤ 1 / y := inv_ge_tangent hypos hy0
  have h2 : y ≤ y0 + m * (x - x0) := htan x hx
  have hcoef : (0 : ℝ) < 1 / y0 ^ 2 := by positivity
  have h3 : 1 / y0 - (1 / y0 ^ 2) * (y0 + m * (x - x0) - y0) ≤
      1 / y0 - (1 / y0 ^ 2) * (y - y0) := by
    have h4 := mul_le_mul_of_nonneg_left h2 hcoef.le
    linarith
  have hPsi : MathathonT5.Psi x = 1 / y - 1 := by
    have h5 : (2 + x) / x = (x / (x + 2))⁻¹ := by
      field_simp
      ring
    rw [hy, MathathonT5.Psi, h5, Real.inv_rpow ha.le, inv_eq_one_div]
  rw [hPsi]
  linarith [h1, h3]

/-- `Psi` is above an explicit rational affine function on `[1/4, 1/2]`
(convexity-free: tangent of the convex map `w ↦ 1/w` at `5/8` composed with a rational
tangent line of the concave map `x ↦ (x/(x+2))^(1/4)` at `x0 = 1250/3471`). -/
theorem Psi_piece_one :
    ∀ x ∈ Icc (1/4 : ℝ) (1/2),
      (1923/2048 : ℝ) + (-12047841/12800000) * x ≤ MathathonT5.Psi x := by
  have hy0 : (0 : ℝ) < 5/8 := by norm_num
  have hmain := Psi_ge_affine (x1 := 1/4) (x2 := 1/2) (y0 := 5/8) (m := 12047841/32768000)
    (x0 := 1250/3471) (by norm_num) (by norm_num) hy0 (by
      intro x hx
      obtain ⟨hxa, hxb⟩ := hx
      have hxp : (0 : ℝ) < x := by linarith
      have hYpos : 0 < 5/8 + (12047841/32768000) * (x - 1250/3471) := by nlinarith
      have hquart : x ≤ (5/8 + (12047841/32768000) * (x - 1250/3471)) ^ 4 * (x + 2) := by
        have hid : (5/8 + (12047841/32768000) * (x - 1250/3471)) ^ 4 * (x + 2) - x
            = (x - 1250/3471) ^ 2 * (76859232058697630110934050178649/73786976294838206464000000000000 + 10586411371259990474074701158259/18446744073709551616000000000000 * (x - 1/4) +
              744086491029054192669663740571/4611686018427387904000000000000 * (x - 1/4) ^ 2 + 21068659742823377528812760961/1152921504606846976000000000000 * (x - 1/4) ^ 3) := by
          field_simp
          ring
        have hnn : 0 ≤ (x - 1250/3471) ^ 2 * (76859232058697630110934050178649/73786976294838206464000000000000 + 10586411371259990474074701158259/18446744073709551616000000000000 * (x - 1/4) +
            744086491029054192669663740571/4611686018427387904000000000000 * (x - 1/4) ^ 2 + 21068659742823377528812760961/1152921504606846976000000000000 * (x - 1/4) ^ 3) := by
          have h0 : (0:ℝ) ≤ 76859232058697630110934050178649/73786976294838206464000000000000 := by norm_num
          have h1 : (0:ℝ) ≤ 10586411371259990474074701158259/18446744073709551616000000000000 * (x - 1/4) := by
            have : (0:ℝ) ≤ x - 1/4 := by linarith
            positivity
          have h2 : (0:ℝ) ≤ 744086491029054192669663740571/4611686018427387904000000000000 * (x - 1/4) ^ 2 := by positivity
          have h3 : (0:ℝ) ≤ 21068659742823377528812760961/1152921504606846976000000000000 * (x - 1/4) ^ 3 := by
            have : (0:ℝ) ≤ x - 1/4 := by linarith
            positivity
          have := mul_nonneg (sq_nonneg (x - 1250/3471))
            (by linarith : (0:ℝ) ≤ 76859232058697630110934050178649/73786976294838206464000000000000 + 10586411371259990474074701158259/18446744073709551616000000000000 * (x - 1/4) +
              744086491029054192669663740571/4611686018427387904000000000000 * (x - 1/4) ^ 2 + 21068659742823377528812760961/1152921504606846976000000000000 * (x - 1/4) ^ 3)
          linarith
        linarith
      have hq : x / (x + 2) ≤ (5/8 + (12047841/32768000) * (x - 1250/3471)) ^ 4 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < x + 2)]
        nlinarith
      exact rpow_quarter_le_of_le_fourth hxp (le_of_lt hYpos) hq)
  intro x hx
  have h1 := hmain x hx
  have h2 : 1 / (5/8:ℝ) - 1 - (1 / (5/8:ℝ) ^ 2) * ((12047841/32768000) * (x - 1250/3471))
      = (1923/2048 : ℝ) + (-12047841/12800000) * x := by
    field_simp
    ring
  rw [h2] at h1
  exact h1

/-- `Psi` is above an explicit rational affine function on `[1/2, 3/4]`
(convexity-free: tangent of the convex map `w ↦ 1/w` at `7/10` composed with a rational
tangent line of the concave map `x ↦ (x/(x+2))^(1/4)` at `x0 = 4802/7599`). -/
theorem Psi_piece_two :
    ∀ x ∈ Icc (1/2 : ℝ) (3/4),
      (19599/28000 : ℝ) + (-57744801/134456000) * x ≤ MathathonT5.Psi x := by
  have hy0 : (0 : ℝ) < 7/10 := by norm_num
  have hmain := Psi_ge_affine (x1 := 1/2) (x2 := 3/4) (y0 := 7/10) (m := 57744801/274400000)
    (x0 := 4802/7599) (by norm_num) (by norm_num) hy0 (by
      intro x hx
      obtain ⟨hxa, hxb⟩ := hx
      have hxp : (0 : ℝ) < x := by linarith
      have hYpos : 0 < 7/10 + (57744801/274400000) * (x - 4802/7599) := by nlinarith
      have hquart : x ≤ (7/10 + (57744801/274400000) * (x - 4802/7599)) ^ 4 * (x + 2) := by
        have hid : (7/10 + (57744801/274400000) * (x - 4802/7599)) ^ 4 * (x + 2) - x
            = (x - 4802/7599) ^ 2 * (219772293124760051724562852563201/362841039201894400000000000000000 + 173013256643668059758924634345603/907102598004736000000000000000000 * (x - 1/2) +
              9874359806958805916789249000229/323965213573120000000000000000000 * (x - 1/2) ^ 2 + 11118637113070678628090961219201/5669391237529600000000000000000000 * (x - 1/2) ^ 3) := by
          field_simp
          ring
        have hnn : 0 ≤ (x - 4802/7599) ^ 2 * (219772293124760051724562852563201/362841039201894400000000000000000 + 173013256643668059758924634345603/907102598004736000000000000000000 * (x - 1/2) +
            9874359806958805916789249000229/323965213573120000000000000000000 * (x - 1/2) ^ 2 + 11118637113070678628090961219201/5669391237529600000000000000000000 * (x - 1/2) ^ 3) := by
          have h0 : (0:ℝ) ≤ 219772293124760051724562852563201/362841039201894400000000000000000 := by norm_num
          have h1 : (0:ℝ) ≤ 173013256643668059758924634345603/907102598004736000000000000000000 * (x - 1/2) := by
            have : (0:ℝ) ≤ x - 1/2 := by linarith
            positivity
          have h2 : (0:ℝ) ≤ 9874359806958805916789249000229/323965213573120000000000000000000 * (x - 1/2) ^ 2 := by positivity
          have h3 : (0:ℝ) ≤ 11118637113070678628090961219201/5669391237529600000000000000000000 * (x - 1/2) ^ 3 := by
            have : (0:ℝ) ≤ x - 1/2 := by linarith
            positivity
          have := mul_nonneg (sq_nonneg (x - 4802/7599))
            (by linarith : (0:ℝ) ≤ 219772293124760051724562852563201/362841039201894400000000000000000 + 173013256643668059758924634345603/907102598004736000000000000000000 * (x - 1/2) +
              9874359806958805916789249000229/323965213573120000000000000000000 * (x - 1/2) ^ 2 + 11118637113070678628090961219201/5669391237529600000000000000000000 * (x - 1/2) ^ 3)
          linarith
        linarith
      have hq : x / (x + 2) ≤ (7/10 + (57744801/274400000) * (x - 4802/7599)) ^ 4 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < x + 2)]
        nlinarith
      exact rpow_quarter_le_of_le_fourth hxp (le_of_lt hYpos) hq)
  intro x hx
  have h1 := hmain x hx
  have h2 : 1 / (7/10:ℝ) - 1 - (1 / (7/10:ℝ) ^ 2) * ((57744801/274400000) * (x - 4802/7599))
      = (19599/28000 : ℝ) + (-57744801/134456000) * x := by
    field_simp
    ring
  rw [h2] at h1
  exact h1

/-- `Psi` is above an explicit rational affine function on `[3/4, 47/50]`
(convexity-free: tangent of the convex map `w ↦ 1/w` at `11/15` composed with a rational
tangent line of the concave map `x ↦ (x/(x+2))^(1/4)` at `x0 = 14641/17992`). -/
theorem Psi_piece_three :
    ∀ x ∈ Icc (3/4 : ℝ) (47/50),
      (22496/37125 : ℝ) + (-161856032/543547125) * x ≤ MathathonT5.Psi x := by
  have hy0 : (0 : ℝ) < 11/15 := by norm_num
  have hmain := Psi_ge_affine (x1 := 3/4) (x2 := 47/50) (y0 := 11/15) (m := 161856032/1010728125)
    (x0 := 14641/17992) (by norm_num) (by norm_num) hy0 (by
      intro x hx
      obtain ⟨hxa, hxb⟩ := hx
      have hxp : (0 : ℝ) < x := by linarith
      have hYpos : 0 < 11/15 + (161856032/1010728125) * (x - 14641/17992) := by nlinarith
      have hquart : x ≤ (11/15 + (161856032/1010728125) * (x - 14641/17992)) ^ 4 * (x + 2) := by
        have hid : (11/15 + (161856032/1010728125) * (x - 14641/17992)) ^ 4 * (x + 2) - x
            = (x - 14641/17992) ^ 2 * (45355186004857334421842837134190464/94873455286949628735637664794921875 + 39961867123219597465752583410681856/347869336052148638697338104248046875 * (x - 3/4) +
              4790397478936152879585429703491584/347869336052148638697338104248046875 * (x - 3/4) ^ 2 + 686302461856862645208200774680576/1043608008156445916092014312744140625 * (x - 3/4) ^ 3) := by
          field_simp
          ring
        have hnn : 0 ≤ (x - 14641/17992) ^ 2 * (45355186004857334421842837134190464/94873455286949628735637664794921875 + 39961867123219597465752583410681856/347869336052148638697338104248046875 * (x - 3/4) +
            4790397478936152879585429703491584/347869336052148638697338104248046875 * (x - 3/4) ^ 2 + 686302461856862645208200774680576/1043608008156445916092014312744140625 * (x - 3/4) ^ 3) := by
          have h0 : (0:ℝ) ≤ 45355186004857334421842837134190464/94873455286949628735637664794921875 := by norm_num
          have h1 : (0:ℝ) ≤ 39961867123219597465752583410681856/347869336052148638697338104248046875 * (x - 3/4) := by
            have : (0:ℝ) ≤ x - 3/4 := by linarith
            positivity
          have h2 : (0:ℝ) ≤ 4790397478936152879585429703491584/347869336052148638697338104248046875 * (x - 3/4) ^ 2 := by positivity
          have h3 : (0:ℝ) ≤ 686302461856862645208200774680576/1043608008156445916092014312744140625 * (x - 3/4) ^ 3 := by
            have : (0:ℝ) ≤ x - 3/4 := by linarith
            positivity
          have := mul_nonneg (sq_nonneg (x - 14641/17992))
            (by linarith : (0:ℝ) ≤ 45355186004857334421842837134190464/94873455286949628735637664794921875 + 39961867123219597465752583410681856/347869336052148638697338104248046875 * (x - 3/4) +
              4790397478936152879585429703491584/347869336052148638697338104248046875 * (x - 3/4) ^ 2 + 686302461856862645208200774680576/1043608008156445916092014312744140625 * (x - 3/4) ^ 3)
          linarith
        linarith
      have hq : x / (x + 2) ≤ (11/15 + (161856032/1010728125) * (x - 14641/17992)) ^ 4 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < x + 2)]
        nlinarith
      exact rpow_quarter_le_of_le_fourth hxp (le_of_lt hYpos) hq)
  intro x hx
  have h1 := hmain x hx
  have h2 : 1 / (11/15:ℝ) - 1 - (1 / (11/15:ℝ) ^ 2) * ((161856032/1010728125) * (x - 14641/17992))
      = (22496/37125 : ℝ) + (-161856032/543547125) * x := by
    field_simp
    ring
  rw [h2] at h1
  exact h1

/-- `Psi` is above an explicit rational affine function on `[93/100, 1]`
(convexity-free: tangent of the convex map `w ↦ 1/w` at `3/4` composed with a rational
tangent line of the concave map `x ↦ (x/(x+2))^(1/4)` at `x0 = 162/175`). -/
theorem Psi_piece_four :
    ∀ x ∈ Icc (93/100 : ℝ) (1),
      (431/768 : ℝ) + (-30625/124416) * x ≤ MathathonT5.Psi x := by
  have hy0 : (0 : ℝ) < 3/4 := by norm_num
  have hmain := Psi_ge_affine (x1 := 93/100) (x2 := 1) (y0 := 3/4) (m := 30625/221184)
    (x0 := 162/175) (by norm_num) (by norm_num) hy0 (by
      intro x hx
      obtain ⟨hxa, hxb⟩ := hx
      have hxp : (0 : ℝ) < x := by linarith
      have hYpos : 0 < 3/4 + (30625/221184) * (x - 162/175) := by nlinarith
      have hquart : x ≤ (3/4 + (30625/221184) * (x - 162/175)) ^ 4 * (x + 2) := by
        have hid : (3/4 + (30625/221184) * (x - 162/175)) ^ 4 * (x + 2) - x
            = (x - 162/175) ^ 2 * (7204912822530407298125/17019715481382426771456 + 1124293183102903515625/12764786611036820078592 * (x - 93/100) +
              86576078068115234375/9573589958277615058944 * (x - 93/100) ^ 2 + 879638824462890625/2393397489569403764736 * (x - 93/100) ^ 3) := by
          field_simp
          ring
        have hnn : 0 ≤ (x - 162/175) ^ 2 * (7204912822530407298125/17019715481382426771456 + 1124293183102903515625/12764786611036820078592 * (x - 93/100) +
            86576078068115234375/9573589958277615058944 * (x - 93/100) ^ 2 + 879638824462890625/2393397489569403764736 * (x - 93/100) ^ 3) := by
          have h0 : (0:ℝ) ≤ 7204912822530407298125/17019715481382426771456 := by norm_num
          have h1 : (0:ℝ) ≤ 1124293183102903515625/12764786611036820078592 * (x - 93/100) := by
            have : (0:ℝ) ≤ x - 93/100 := by linarith
            positivity
          have h2 : (0:ℝ) ≤ 86576078068115234375/9573589958277615058944 * (x - 93/100) ^ 2 := by positivity
          have h3 : (0:ℝ) ≤ 879638824462890625/2393397489569403764736 * (x - 93/100) ^ 3 := by
            have : (0:ℝ) ≤ x - 93/100 := by linarith
            positivity
          have := mul_nonneg (sq_nonneg (x - 162/175))
            (by linarith : (0:ℝ) ≤ 7204912822530407298125/17019715481382426771456 + 1124293183102903515625/12764786611036820078592 * (x - 93/100) +
              86576078068115234375/9573589958277615058944 * (x - 93/100) ^ 2 + 879638824462890625/2393397489569403764736 * (x - 93/100) ^ 3)
          linarith
        linarith
      have hq : x / (x + 2) ≤ (3/4 + (30625/221184) * (x - 162/175)) ^ 4 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < x + 2)]
        nlinarith
      exact rpow_quarter_le_of_le_fourth hxp (le_of_lt hYpos) hq)
  intro x hx
  have h1 := hmain x hx
  have h2 : 1 / (3/4:ℝ) - 1 - (1 / (3/4:ℝ) ^ 2) * ((30625/221184) * (x - 162/175))
      = (431/768 : ℝ) + (-30625/124416) * x := by
    field_simp
    ring
  rw [h2] at h1
  exact h1

end MathathonT5.D5
