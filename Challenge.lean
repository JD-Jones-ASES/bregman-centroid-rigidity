module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! # Complementary quasi-arithmetic centroids

Local balance constrains two actual centroids of the same inputs.
Gradients of Bregman potentials with positive-definite Hessian generate such means.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology InnerProductSpace BigOperators ContDiff
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


variable {ι : Type*} [Fintype ι]

/-- Balance of two generator centroids of an actual finite family of inputs. -/
def FamilyBalance (Ω : Set E) (w : ι → ℝ) (F G : E → E) : Prop :=
  ∀ p ∈ Ω, ∃ U ∈ 𝓝 p, ∀ x : ι → E, (∀ i, x i ∈ U) →
    ∀ u ∈ U, ∀ v ∈ U,
    F u = ∑ i, w i • F (x i) → G v = ∑ i, w i • G (x i) →
    u + v = (2 : ℝ) • ∑ i, w i • x i

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H} {F G : H → H}

/-- One fixed unequal input weight forces affine generators on a connected
open subset of a real Hilbert space. -/
theorem complementary_unequal_weight {w : ℝ} (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (hw : 0 < w) (hw' : w < 1) (hne : w ≠ 1/2) (bal : LocalBalance Ω w F G) :
    AffineOn Ω F ∧ AffineOn Ω G := by
  sorry

/-- The equal-weight three-input balance law alone characterizes affine generators. -/
theorem three_input_centroids (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G) :
    AffineOn Ω F ∧ AffineOn Ω G := by
  sorry

/-- The same conclusion holds for every fixed family of at least three positive weights. -/
theorem weighted_family_centroids {n : ℕ} (hn : 3 ≤ n) (w : Fin n → ℝ)
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (bal : FamilyBalance Ω w F G) : AffineOn Ω F ∧ AffineOn Ω G := by
  sorry

end CentroidRigidity
