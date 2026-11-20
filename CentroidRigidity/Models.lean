module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # Canonical scalar generators and their products -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace CentroidRigidity

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

end CentroidRigidity
