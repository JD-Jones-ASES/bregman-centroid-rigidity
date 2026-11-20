module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import CentroidRigidity.Definitions
public import Mathlib.Tactic.Module

/-! # Local quasi-arithmetic pooling

The balance law uses the two generator equations for nearby centroids. This
formulation permits generators with only a local inverse and open images
which need not be convex.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology InnerProductSpace ContDiff

namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem mix_self (w : ℝ) (x : E) : mix w x x = x := by
  unfold mix
  module

theorem mix_swap (w : ℝ) (x y : E) : mix (1-w) x y = mix w y x := by
  unfold mix
  module

theorem LocalBalance.swap {Ω : Set E} {F G : E → E} {w : ℝ}
    (h : LocalBalance Ω w F G) : LocalBalance Ω (1-w) F G := by
  intro p hp
  obtain ⟨U, hU, h⟩ := h p hp
  exact ⟨U, hU, fun x hx y hy u hu v hv hF hG ↦ by
    rw [mix_swap] at hF hG ⊢
    exact h y hy x hx u hu v hv hF hG⟩

end CentroidRigidity
