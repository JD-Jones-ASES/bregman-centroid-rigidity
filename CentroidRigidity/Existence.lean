module

public import CentroidRigidity.Charts

/-! # Existence of both actual predictions near the diagonal -/

@[expose] public section
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω : Set E} {F G : E → E} {p : E}

theorem local_pools_exist (hp : p ∈ Ω) (rF : RegularOn 1 Ω F) (rG : RegularOn 1 Ω G)
    (w : ℝ) {U : Set E} (hU : U ∈ 𝓝 p) :
    ∀ᶠ q : E × E in 𝓝 (p,p), ∃ u ∈ U, ∃ v ∈ U,
      F u = mix w (F q.1) (F q.2) ∧ G v = mix w (G q.1) (G q.2) := by
  obtain ⟨c⟩ := exists_chartAt (by decide) (rF p hp).1 (rF p hp).2
  obtain ⟨d⟩ := exists_chartAt (by decide) (rG p hp).1 (rG p hp).2
  have hf := (rF p hp).1.continuousAt
  have hg := (rG p hp).1.continuousAt
  filter_upwards [c.pool_tendsto w hf hU,d.pool_tendsto w hg hU,
    c.pool_eq w hf,d.pool_eq w hg] with q hu hv eu ev
  exact ⟨_,hu,_,hv,eu,ev⟩

end CentroidRigidity
