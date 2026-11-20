module

public import CentroidRigidity.Loss

/-! # The arithmetic predictions of an affine generator -/

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace CentroidRigidity
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [Fintype ι] {Ω : Set E} {F G : E → E}

theorem affine_weighted_prediction {w : ι → ℝ} (hw : ∑ i, w i = 1) (ho : IsOpen Ω)
    (rF : RegularOn 2 Ω F) (aff : AffineOn Ω F) (x : ι → E) (hx : ∀ i, x i ∈ Ω)
    {u : E} (hu : u ∈ Ω) (he : F u = ∑ i, w i • F (x i)) : u = ∑ i, w i • x i := by
  obtain ⟨L,b,hL⟩ := aff
  have hj := affine_jacobian ho hu hL
  have hi : L.IsInvertible := hj ▸ (rF u hu).2
  simp only [hL u hu,fun i ↦ hL (x i) (hx i),smul_add,Finset.sum_add_distrib,← Finset.sum_smul,
    hw,one_smul, add_right_cancel_iff] at he
  have eqn : L u = L (∑ i, w i • x i) := by simpa only [map_sum,map_smul] using he
  exact (inv_apply_apply hi u).symm.trans
    ((congrArg (fun z : E ↦ L.inverse z) eqn).trans (inv_apply_apply hi _))

theorem all_weights_of_affine (ho : IsOpen Ω) (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G)
    (aF : AffineOn Ω F) (aG : AffineOn Ω G) (w : ι → ℝ) (hw : ∑ i, w i = 1) :
    FamilyBalance Ω w F G := by
  intro p hp
  refine ⟨Ω,ho.mem_nhds hp,?_⟩
  intro x hx u hu v hv hF hG
  rw [affine_weighted_prediction hw ho rF aF x hx hu hF,
    affine_weighted_prediction hw ho rG aG x hx hv hG,two_smul]

end CentroidRigidity
