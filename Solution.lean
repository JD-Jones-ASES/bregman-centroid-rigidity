module

public import CentroidRigidity

/-! # Complementary quasi-arithmetic centroids

Local balance constrains two actual centroids of the same inputs.
Gradients of Bregman potentials with positive-definite Hessian generate such means.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology InnerProductSpace BigOperators ContDiff
namespace CentroidRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H} {F G : H → H}

/-- One fixed unequal input weight forces affine generators on a connected
open subset of a real Hilbert space. -/
theorem complementary_unequal_weight {w : ℝ} (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (hw : 0 < w) (hw' : w < 1) (hne : w ≠ 1/2) (bal : LocalBalance Ω w F G) :
    AffineOn Ω F ∧ AffineOn Ω G := by
  exact unequal_weight_rigidity ho hc rF rG hF hw hw' hne bal

/-- The equal-weight three-input balance law alone characterizes affine generators. -/
theorem three_input_centroids (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G) :
    AffineOn Ω F ∧ AffineOn Ω G := by
  exact ternary_rigidity ho hc rF rG hF bal

/-- The same conclusion holds for every fixed family of at least three positive weights. -/
theorem weighted_family_centroids {n : ℕ} (hn : 3 ≤ n) (w : Fin n → ℝ)
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (bal : FamilyBalance Ω w F G) : AffineOn Ω F ∧ AffineOn Ω G := by
  exact family_rigidity hn w hw hpos ho hc rF rG hF bal

end CentroidRigidity
