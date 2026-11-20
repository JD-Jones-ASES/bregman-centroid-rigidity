module

public import CentroidRigidity.Core

/-! # Inverse charts and endpoint differentiation -/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff
namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
abbrev Endo (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E
abbrev jac (F : E → E) := fderiv ℝ F

/-- An inverse function theorem chart at one base point. -/
structure ChartAt (F : E → E) (p : E) where
  e : OpenPartialHomeomorph E E
  forward : (e : E → E) = F
  mem_source : p ∈ e.source

theorem exists_chartAt {n : ℕ∞ω} {F : E → E} {p : E} (hn : 1 ≤ n)
    (hF : ContDiffAt ℝ n F p) (hi : (jac F p).IsInvertible) :
    Nonempty (ChartAt F p) := by
  obtain ⟨L, hL⟩ := hi
  have hn' : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞ω) < 1) hn)
  have hd : HasFDerivAt F (L : Endo E) p := hL ▸ (hF.differentiableAt hn').hasFDerivAt
  exact ⟨⟨hF.toOpenPartialHomeomorph F hd hn', hF.toOpenPartialHomeomorph_coe hd hn',
    hF.mem_toOpenPartialHomeomorph_source hd hn'⟩⟩

variable {F G : E → E} {p : E} (c : ChartAt F p)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem ChartAt.base_target : F p ∈ c.e.target := by
  simpa [← c.forward] using c.e.map_source c.mem_source

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem ChartAt.inv_base : c.e.symm (F p) = p := by
  rw [← congrFun c.forward p]
  exact c.e.left_inv c.mem_source

def ChartAt.pool (w : ℝ) (z : E × E) : E := c.e.symm (mix w (F z.1) (F z.2))

omit [CompleteSpace E] in
@[simp] theorem ChartAt.pool_base (w : ℝ) : c.pool w (p,p) = p := by simp [ChartAt.pool]

omit [CompleteSpace E] in
theorem ChartAt.mix_tendsto (w : ℝ) (hc : ContinuousAt F p) :
    Tendsto (fun z : E × E ↦ mix w (F z.1) (F z.2)) (𝓝 (p,p)) (𝓝 (F p)) := by
  have h : ContinuousAt (fun z : E × E ↦ mix w (F z.1) (F z.2)) (p,p) :=
    ((hc.comp continuous_fst.continuousAt).const_smul _).add
      ((hc.comp continuous_snd.continuousAt).const_smul _)
  simpa using h.tendsto

omit [CompleteSpace E] in
theorem ChartAt.pool_tendsto (w : ℝ) (hc : ContinuousAt F p) :
    Tendsto (c.pool w) (𝓝 (p,p)) (𝓝 p) := by
  change Tendsto (fun z : E × E ↦ c.e.symm (mix w (F z.1) (F z.2))) _ _
  simpa only [ChartAt.inv_base, Function.comp_def] using
    (c.e.symm.continuousAt c.base_target).tendsto.comp (ChartAt.mix_tendsto w hc)

omit [CompleteSpace E] in
theorem ChartAt.pool_eq (w : ℝ) (hc : ContinuousAt F p) :
    ∀ᶠ z in 𝓝 (p,p), F (c.pool w z) = mix w (F z.1) (F z.2) := by
  filter_upwards [(ChartAt.mix_tendsto w hc) (c.e.open_target.mem_nhds c.base_target)] with z hz
  exact (congrFun c.forward _).symm.trans (c.e.right_inv hz)

omit [CompleteSpace E] in
theorem balance_pool {Ω : Set E} {w : ℝ} (hp : p ∈ Ω) (bal : LocalBalance Ω w F G)
    (c : ChartAt F p) (d : ChartAt G p) (hF : ContinuousAt F p) (hG : ContinuousAt G p) :
    (fun z ↦ c.pool w z + d.pool w z) =ᶠ[𝓝 (p,p)] fun z ↦ (2 : ℝ) • mix w z.1 z.2 := by
  obtain ⟨U,hU,h⟩ := bal p hp
  filter_upwards [continuous_fst.continuousAt.tendsto hU, continuous_snd.continuousAt.tendsto hU,
    c.pool_tendsto w hF hU, d.pool_tendsto w hG hU,
    c.pool_eq w hF, d.pool_eq w hG] with z hx hy hu hv hf hg
  exact h _ hx _ hy _ hu _ hv hf hg

end CentroidRigidity
