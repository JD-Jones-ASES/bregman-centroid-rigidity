module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! # Complementary centroid rules

The two generator equations specify the actual nearby centroids. The
arithmetic, exponential and loss formulas use the same input coordinates.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped BigOperators Topology InnerProductSpace ContDiff
namespace CentroidRigidity

section Pooling

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

end Pooling

section Coordinates

/-- The exponential generator with value zero and derivative one at the origin.
The parameter zero gives the arithmetic generator. -/
def sExp (l t : ℝ) : ℝ := if l = 0 then t else (Real.exp (l*t) - 1) / l

variable {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]

/-- Apply a normalized scalar generator on each axis of a single basis. -/
def axisMap (B : Module.Basis ι ℝ H) (l : ι → ℝ) (z : H) : H :=
  ∑ i, sExp (l i) (B.repr z i) • B i

/-- The generator itself in common input coordinates, with its output affine freedom fixed at p. -/
def RepresentsOn (Ω : Set H) (F : H → H) (p : H) (B : Module.Basis ι ℝ H) (l : ι → ℝ) : Prop :=
  ∀ x ∈ Ω, F x = F p + fderiv ℝ F p (axisMap B l (x-p))

end Coordinates

/-- The arithmetic or log-mean-exp prediction of two scalar inputs. -/
def pairPool (l a b : ℝ) :=
  if l = 0 then (a+b)/2 else Real.log ((Real.exp (l*a)+Real.exp (l*b))/2)/l

/-- Logarithm of the arithmetic mean of three exponentials. -/
def logMeanThree (a b c : ℝ) := Real.log ((Real.exp a + Real.exp b + Real.exp c)/3)

/-- The scalar three-input quasi-arithmetic pool with signed parameter. -/
def triplePool (l a b c : ℝ) := if l = 0 then (a+b+c)/3 else logMeanThree (l*a) (l*b) (l*c)/l

section Losses

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The divergence has the candidate prediction in its first argument. -/
def divergence (φ : H → ℝ) (F : H → H) (z x : H) : ℝ :=
  φ z - φ x - ⟪F x,z-x⟫_ℝ

/-- A single fixed positive quadratic form represents the entire divergence. -/
def QuadraticLossOn (Ω : Set H) (φ : H → ℝ) (F : H → H) : Prop :=
  ∃ L : H →L[ℝ] H, (∀ a b, ⟪L a,b⟫_ℝ = ⟪a,L b⟫_ℝ) ∧
    (∀ a ≠ 0, 0 < ⟪L a,a⟫_ℝ) ∧ ∀ z ∈ Ω, ∀ x ∈ Ω,
      divergence φ F z x = (1/2:ℝ) * ⟪L (z-x),z-x⟫_ℝ

end Losses

/-- Okamura’s shear generator for a scalar function. -/
def shear (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1,x.2 + f x.1)

end CentroidRigidity
