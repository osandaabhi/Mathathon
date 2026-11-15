/-
The main conditional statement: the tetrahedral-prism cone `T5` is not area-minimizing
(Mathathon report `attempt_8_T5`, Theorem 1.2), reduced to its scalar core.

What is *proved* here: the whole numerical chain
`J_{5/2} > 33/10` and `J_{-3/2} > 31` (both fully proved in `MathathonT5`), hence
`B < -3/100`, hence a saving `2 (B + 4π/1000) < -1/40`.

What is *assumed* (explicitly, as hypotheses, never as axioms):
* `J_{1/2} < 191/20` — the report's first moment bound, not yet formalized (see README.md);
* the area identity of the report's Lemma 2.2 together with the cutoff cost of Lemma 4.1,
  packaged as `area (Xset 1000) ≤ area cone + 2 (B + 4π/1000)`;
* the image identity `φ '' cone = Xset 1000` of Lemma 4.2.
-/
import MathathonT5.Basic
import MathathonT5.Moments
import MathathonT5.Jm32
import MathathonT5.NodeBounds
import MathathonT5.Constants

noncomputable section
open scoped BigOperators

namespace MathathonT5

/-- The report's scalar `B` of Lemma 3.1: `(b/2) J_{1/2} - (b^3/2) J_{5/2} - ((b-1/2)/3) J_{-3/2}`. -/
def Bval : ℝ := (bb/2) * J12 - (bb^3/2) * J52 - ((bb - 1/2)/3) * Jm32

theorem Bval_eq : Bval = (bb/2) * J12 - (bb^3/2) * J52 - ((bb - 1/2)/3) * Jm32 := rfl

/-- **The saving beats `1/40`** once the three moment bounds are available.  Here the
`p = 1/2` bound is a hypothesis; the other two are proved. -/
theorem saving_of_moments (hJ1 : J12 < 191/20) :
    2 * (Bval + 4 * Real.pi / 1000) < -1/40 := by
  have h := D6.saving J12 J52 Jm32 hJ1 J52_gt Jm32_gt
  simpa only [Bval] using h

/-- The same with the report's sharper threshold `-7/250`. -/
theorem saving_of_moments_sharp (hJ1 : J12 < 191/20) :
    2 * (Bval + 4 * Real.pi / 1000) < -7/250 := by
  have h := D6.saving_sharp J12 J52 Jm32 hJ1 J52_gt Jm32_gt
  simpa only [Bval] using h

/-- **Area strictly decreases.**  If the finite area difference between the cone and the
competitor `X_{F_R}` is what the report's Lemmas 2.2, 3.1 and 4.1 compute it to be, i.e.
at most `2 (B + 4π/R)` with `R = 1000`, then the deformation reduces the area by more
than `1/40`. -/
theorem area_decreases (area : Set V4 → ℝ) (hJ1 : J12 < 191/20)
    (harea : area (Xset 1000) ≤ area cone + 2 * (Bval + 4 * Real.pi / 1000)) :
    1/40 < area cone - area (Xset 1000) := by
  have h := saving_of_moments hJ1
  linarith

/-- **Failure of Almgren minimality** (report Theorem 1.2), conditional form: the image of
the cone under the explicit deformation `φ` of (4.5) has strictly smaller area. -/
theorem not_minimizing (area : Set V4 → ℝ) (hJ1 : J12 < 191/20)
    (himg : phi 1000 '' cone = Xset 1000)
    (harea : area (Xset 1000) ≤ area cone + 2 * (Bval + 4 * Real.pi / 1000)) :
    area (phi 1000 '' cone) < area cone - 1/40 := by
  have h := area_decreases area hJ1 harea
  rw [himg]
  linarith

end MathathonT5
