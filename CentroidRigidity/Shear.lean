module

public import CentroidRigidity.Core

/-! # Complementary shears without the gradient hypothesis

These real-plane maps implement the shear construction in Okamura, Theorem 4.2.
The algebraic cancellation holds for every scalar function.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace CentroidRigidity

theorem shear_family_balance {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (w : ι → ℝ) :
    FamilyBalance (Set.univ : Set (ℝ × ℝ)) w (shear f) (shear (fun s ↦ -f s)) := by
  intro p _
  refine ⟨Set.univ,Filter.univ_mem,?_⟩
  intro x _ u _ v _ hF hG
  let fst := LinearMap.fst ℝ ℝ ℝ
  let snd := LinearMap.snd ℝ ℝ ℝ
  have ef := congrArg fst hF
  have eg := congrArg fst hG
  have eu := congrArg snd hF
  have ev := congrArg snd hG
  simp only [map_sum,map_smul] at ef eg eu ev
  change u.1 = ∑ i, w i * (x i).1 at ef
  change v.1 = ∑ i, w i * (x i).1 at eg
  change u.2 + f u.1 = ∑ i, w i * ((x i).2+f (x i).1) at eu
  change v.2 + -f v.1 = ∑ i, w i * ((x i).2+-f (x i).1) at ev
  rw [ef] at eu
  rw [eg] at ev
  simp only [mul_add,Finset.sum_add_distrib,mul_neg,Finset.sum_neg_distrib] at eu ev
  apply Prod.ext
  · change u.1+v.1 = fst ((2:ℝ) • ∑ i, w i • x i)
    simp only [map_smul,map_sum]
    change u.1+v.1 = 2 * ∑ i, w i*(x i).1
    linarith
  · change u.2+v.2 = snd ((2:ℝ) • ∑ i, w i • x i)
    simp only [map_smul,map_sum]
    change u.2+v.2 = 2 * ∑ i, w i*(x i).2
    linarith

end CentroidRigidity
