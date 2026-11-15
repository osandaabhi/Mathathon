import Mathlib
open Set
namespace TestLam
noncomputable section

def Lam (x : ℝ) : ℝ := 1 - (x / (2 + x)) ^ ((3 : ℝ) / 4)
def gg (x : ℝ) : ℝ := (x / (2 + x)) ^ ((3 : ℝ) / 4)

example : ConvexOn ℝ (Set.Icc (1/4:ℝ) 1) (fun x => 1 / (2 + x)) := by
  have h : ConvexOn ℝ (Set.Ioi (-2:ℝ)) (fun x => (2 + x)⁻¹) := by
    sorry
  sorry

example : ConcaveOn ℝ (Set.Icc (1/4:ℝ) 1) gg := by
  sorry

end
end TestLam
