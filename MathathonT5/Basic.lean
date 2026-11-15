/-
The tetrahedral-prism cone T5 in R^4, its support function, and the explicit
cut-off deformation of Mathathon report `attempt_8_T5` (§1, §3, §4).

Everything here is a definition plus elementary bookkeeping; the analytic and
numerical content lives in `Moments.lean` and `Main.lean`.
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace MathathonT5

/-- Points of `R^3`, as coordinate functions. -/
abbrev V3 := Fin 3 → ℝ

/-- Points of `R^4`, as coordinate functions. -/
abbrev V4 := Fin 4 → ℝ

/-- The Euclidean inner product on `R^3`. -/
def dot3 (x y : V3) : ℝ := ∑ k, x k * y k

/-- The Euclidean norm on `R^3`. -/
def nrm3 (x : V3) : ℝ := Real.sqrt (dot3 x x)

/-- The sign matrix of the four tetrahedral vertices:
`i = 0` gives `(1,1,1)`, and `i ≥ 1` has its single plus in coordinate `i-1`. -/
def sg : Fin 3 → Fin 4 → ℝ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

/-- `ε_i`, the `i`-th sign vector. -/
def epsv (i : Fin 4) : V3 := fun k => sg k i

/-- `b = √(5/8)`, the half-height of the prism. -/
def bb : ℝ := Real.sqrt (5 / 8)

/-- `c = √(3/5)`, the circumradius of the tetrahedron `conv {p_i}`. -/
def cc : ℝ := Real.sqrt (3 / 5)

/-- `p_i = ε_i/√5`: the four vertices of the regular tetrahedron of circumradius `c`
whose support function is `f`. (The report's `q_i/(2√2)` equals `b · p_i`.) -/
def pvec (i : Fin 4) : V3 := (Real.sqrt 5)⁻¹ • epsv i

lemma dot3_smul_smul (a b : ℝ) (x y : V3) : dot3 (a • x) (b • y) = a * b * dot3 x y := by
  simp only [dot3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring_nf

lemma inv_sqrt5_sq : (Real.sqrt 5)⁻¹ * (Real.sqrt 5)⁻¹ = 1 / 5 := by
  have h : Real.sqrt 5 * Real.sqrt 5 = 5 := by
    rw [← pow_two]; exact Real.sq_sqrt (by norm_num)
  field_simp
  linarith

lemma dot3_eps_self (i : Fin 4) : dot3 (epsv i) (epsv i) = 3 := by
  fin_cases i <;> simp [dot3, epsv, sg, Fin.sum_univ_three] <;> norm_num

lemma dot3_eps_off (i j : Fin 4) (h : i ≠ j) : dot3 (epsv i) (epsv j) = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all [dot3, epsv, sg, Fin.sum_univ_three]

/-- `|p_i|^2 = 3/5`: the circumradius of the tetrahedron `conv {p_i}` is `c`. -/
lemma dot3_p_self (i : Fin 4) : dot3 (pvec i) (pvec i) = 3 / 5 := by
  simp only [pvec, dot3_smul_smul, dot3_eps_self, inv_sqrt5_sq]
  norm_num

/-- `p_i · p_j = -1/5` for `i ≠ j`: all pairwise angles are equal. -/
lemma dot3_p_off (i j : Fin 4) (h : i ≠ j) : dot3 (pvec i) (pvec j) = -1 / 5 := by
  simp only [pvec, dot3_smul_smul, dot3_eps_off i j h, inv_sqrt5_sq]
  norm_num

/-- `∑ p_i = 0`: zero is the centre of the tetrahedron. -/
lemma sum_pvec (k : Fin 3) : (∑ i : Fin 4, pvec i k) = 0 := by
  fin_cases k <;> simp [pvec, epsv, sg, Fin.sum_univ_four] <;> ring

/-- The support function `f(u) = max_i p_i · u` of the tetrahedron `conv {p_i}`. -/
def fsup (u : V3) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => dot3 (pvec i) u)

lemma sum_dot3_pvec (u : V3) : (∑ i : Fin 4, dot3 (pvec i) u) = 0 := by
  simp only [dot3]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Finset.sum_mul, sum_pvec, zero_mul]

/-- `f ≥ 0`: the tetrahedron contains the origin. -/
lemma nrm3_nonneg (x : V3) : 0 ≤ nrm3 x := by
  simp only [nrm3]; positivity

lemma fsup_nonneg (u : V3) : 0 ≤ fsup u := by
  by_contra h
  rw [not_le] at h
  have hall : ∀ i : Fin 4, dot3 (pvec i) u < 0 := fun i =>
    lt_of_le_of_lt (Finset.le_sup' (fun i => dot3 (pvec i) u) (Finset.mem_univ i)) h
  have hneg : (∑ i : Fin 4, dot3 (pvec i) u) < 0 :=
    Finset.sum_neg (fun i _ => hall i) Finset.univ_nonempty
  rw [sum_dot3_pvec] at hneg
  exact lt_irrefl _ hneg

/-- The sector `V_i = {u : p_i · u ≥ p_j · u for all j}`. -/
def sector (i : Fin 4) : Set V3 := {u | ∀ j, dot3 (pvec j) u ≤ dot3 (pvec i) u}

/-- The union `W = ⋃_{i<j} (V_i ∩ V_j)` of the seams of the roof `f`. -/
def seam : Set V3 := ⋃ i : Fin 4, ⋃ j ∈ {j : Fin 4 | j ≠ i}, (sector i ∩ sector j)

/-- The first three coordinates of a point of `R^4`. -/
def fst3 (x : V4) : V3 := fun k => x (Fin.castSucc k)

/-- The fourth coordinate of a point of `R^4`. -/
def lst (x : V4) : ℝ := x 3

/-- The tetrahedral-prism cone `T5` defined by (1.2) of the report. -/
def cone : Set V4 :=
  {x | lst x = fsup (fst3 x)} ∪ {x | lst x = -fsup (fst3 x)}
    ∪ {x | fst3 x ∈ seam ∧ |lst x| ≤ fsup (fst3 x)}

/-- `L(p) = √(1+|p|^2)`, the area element of a graph. -/
def Lof (p : V3) : ℝ := Real.sqrt (1 + dot3 p p)

/-- `E_i(p) = L(p) - L(p_i) - p_i · (p - p_i)`, the bending cost of (2.3). -/
def Efun (i : Fin 4) (p : V3) : ℝ := Lof p - Lof (pvec i) - dot3 (pvec i) (p - pvec i)

/-- The non-compact decaying profile `F_∞ = (f - 1/|u|)^+`. -/
def Finf (u : V3) : ℝ := max 0 (fsup u - (nrm3 u)⁻¹)

/-- `g_R` of (4.1). -/
def gR (R r : ℝ) : ℝ := if r ≤ R then r⁻¹ else if r < 2 * R then 2 * r⁻¹ - R⁻¹ else 0

/-- The compactly supported profile `F_R = (f - g_R(|u|))^+` of (4.1). -/
def FR (R : ℝ) (u : V3) : ℝ := max 0 (fsup u - gR R (nrm3 u))

/-- `g̃_R = min (1, g_R)`, the 1-Lipschitz modification. -/
def gR' (R r : ℝ) : ℝ := min 1 (gR R r)

/-- The displacement bound `δ = min (f, g̃_R) = f - F_R` of (4.3). -/
def deltaR (R : ℝ) (u : V3) : ℝ := min (fsup u) (gR' R (nrm3 u))

/-- Clamping to `[-1,1]`. -/
def clip (z : ℝ) : ℝ := max (-1) (min 1 z)

/-- The vertical displacement field `H` of (4.4). -/
def Hmap (R : ℝ) (u : V3) (t : ℝ) : ℝ := deltaR R u * clip (t / fsup u)

/-- The vertical cutoff `ζ` of §4. -/
def zeta (R : ℝ) (t : ℝ) : ℝ := if |t| ≤ 2 * R then 1 else max 0 (2 * R + 1 - |t|)

/-- The ambient deformation `φ` of (4.5). -/
def phi (R : ℝ) (x : V4) : V4 :=
  Function.update x 3 (lst x - zeta R (lst x) * Hmap R (fst3 x) (lst x))

/-- The competitor `X_F` of (2.2). -/
def Xset (R : ℝ) : Set V4 :=
  {x | lst x = FR R (fst3 x)} ∪ {x | lst x = -FR R (fst3 x)}
    ∪ {x | fst3 x ∈ seam ∧ |lst x| ≤ FR R (fst3 x)}

/-! ### Elementary bookkeeping -/

lemma clip_mem (z : ℝ) : clip z ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma abs_clip_le (z : ℝ) : |clip z| ≤ 1 := by
  have := clip_mem z
  rw [abs_le]
  exact this

/-- `g_R ≥ 0` on `[0,∞)`. -/
lemma gR_nonneg {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) : 0 ≤ gR R r := by
  unfold gR
  split_ifs with h1 h2
  · exact inv_nonneg.mpr hr
  · have hrpos : 0 < r := lt_trans hR (not_le.mp h1)
    have hEq : 2 * r⁻¹ - R⁻¹ = (2 * R - r) / (r * R) := by
      field_simp
    rw [hEq]
    exact div_nonneg (by linarith) (by positivity)
  · exact le_refl 0

lemma deltaR_nonneg (R : ℝ) (hR : 0 < R) (u : V3) : 0 ≤ deltaR R u := by
  refine le_min (fsup_nonneg u) ?_
  exact le_min (by norm_num) (gR_nonneg hR (nrm3_nonneg u))

lemma FR_nonneg (R : ℝ) (u : V3) : 0 ≤ FR R u := le_max_left _ _

lemma FR_le_fsup (R : ℝ) (hR : 0 < R) (u : V3) : FR R u ≤ fsup u := by
  refine max_le (fsup_nonneg u) ?_
  exact sub_le_self _ (gR_nonneg hR (nrm3_nonneg u))

end MathathonT5
