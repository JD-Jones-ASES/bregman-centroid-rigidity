module

public import CentroidRigidity.Integration
public import CentroidRigidity.Complement

/-! # Classification of complementary binary means -/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CentroidRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H] {Ω : Set H} {F G : H → H} {p : H}

/-- One basis works simultaneously for both generators at every point
of the connected domain, including repeated eigenvalues and linear axes. -/
theorem equal_weight_classification (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F) :
    LocalBalance Ω (1/2) F G ↔
    ∃ (B : Module.Basis (Fin (Module.finrank ℝ H)) ℝ H) (l : Fin (Module.finrank ℝ H) → ℝ),
      RepresentsOn Ω F p B l ∧ RepresentsOn Ω G p B (fun i ↦ -l i) := by
  constructor
  · intro bal
    obtain ⟨B,l,h⟩ := common_axes ho hc hp rF rG pos bal
    refine ⟨B,l,integrate_axes ho hc hp (rF.lower (by decide)) B l h,?_⟩
    apply integrate_axes ho hc hp (rG.lower (by decide))
    intro x hx a i
    have e := eq_neg_of_add_eq_zero_right (opposite_logJac ho hx
      (rF.lower (by decide)) (rG.lower (by decide)) bal (by norm_num) (by norm_num) a)
    rw [e]
    simp [h x hx a i,neg_smul]
  · rintro ⟨B,l,hF,hG⟩
    exact balance_of_representation ho B l hF hG (rF p hp).2 (rG p hp).2

end CentroidRigidity
