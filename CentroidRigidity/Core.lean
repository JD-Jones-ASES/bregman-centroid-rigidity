module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
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

/-- Weighted arithmetic interpolation, with weight `w` on the second argument. -/
def mix (w : ℝ) (x y : E) : E := (1 - w) • x + w • y

/-- A generator with the indicated smoothness and invertible derivative at each domain point. -/
def RegularOn (n : ℕ∞ω) (Ω : Set E) (F : E → E) : Prop :=
  ∀ p ∈ Ω, ContDiffAt ℝ n F p ∧ (fderiv ℝ F p).IsInvertible

/-- The two locally defined pooling rules average to the arithmetic rule.
The four points are the inputs and their respective centroids. -/
def LocalBalance (Ω : Set E) (w : ℝ) (F G : E → E) : Prop :=
  ∀ p ∈ Ω, ∃ U ∈ 𝓝 p, ∀ x ∈ U, ∀ y ∈ U, ∀ u ∈ U, ∀ v ∈ U,
    F u = mix w (F x) (F y) → G v = mix w (G x) (G y) →
    u + v = (2 : ℝ) • mix w x y

/-- The restriction of a continuous affine map. -/
def AffineOn (Ω : Set E) (F : E → E) : Prop :=
  ∃ (L : E →L[ℝ] E) (b : E), ∀ x ∈ Ω, F x = L x + b

/-- Positive definiteness and symmetry of the Jacobian of the first generator. -/
def PositiveJacobian {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : Set H) (F : H → H) : Prop :=
  ∀ p ∈ Ω, (∀ a b, ⟪fderiv ℝ F p a, b⟫_ℝ = ⟪a, fderiv ℝ F p b⟫_ℝ) ∧
    ∀ a ≠ 0, 0 < ⟪fderiv ℝ F p a, a⟫_ℝ

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
