/-
The density of the tetrahedral-prism cone (Mathathon report `attempt_8_T5`, Prop. 5.1).

The report computes the area of the link of `T5` as `8 (3α - π) + 6 (4α - 2π) = 48α - 20π`
with `α = arccos(-1/3)` (eight triangles and six quadrilaterals, each spherical polygon
contributing its excess), and then divides by `4π` to get the density.  Only the final
algebraic identity is formalized here; the spherical-excess computation itself is not.
-/
import MathathonT5.Basic

noncomputable section
namespace MathathonT5

/-- `α = arccos(-1/3)`, the spherical edge angle of the tetrahedral link. -/
def alpha : ℝ := Real.arccos (-(1/3))

/-- `τ = 3α/π`. -/
def tau : ℝ := 3 * alpha / Real.pi

/-- The link area `48α - 20π`. -/
def linkArea : ℝ := 48 * alpha - 20 * Real.pi

/-- **Prop. 5.1, arithmetic part**: `Θ(T5,0) = linkArea/(4π) = 4τ - 5`. -/
theorem density_eq : linkArea / (4 * Real.pi) = 4 * tau - 5 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  simp only [linkArea, tau]
  field_simp
  ring

/-- The same identity in the report's form `Θ = (48α - 20π)/(4π/3) / 3`. -/
theorem density_eq' : linkArea / (4 * Real.pi / 3) / 3 = 4 * tau - 5 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  simp only [linkArea, tau]
  field_simp
  ring

end MathathonT5
