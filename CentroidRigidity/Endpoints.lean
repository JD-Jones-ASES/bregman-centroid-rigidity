module

public import CentroidRigidity.Operator
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! # The equation obtained by differentiating the two endpoints -/

@[expose] public section
noncomputable section

open Filter Set ContinuousLinearMap
open scoped Topology ContDiff
namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω : Set E} {F G : E → E} {p : E} {w : ℝ}

def blendJac (w : ℝ) (a b : Endo E) : E × E →L[ℝ] E :=
  (1-w) • a.comp (fst ℝ E E) + w • b.comp (snd ℝ E E)

theorem ChartAt.inv_derivative (c : ChartAt F p) {y : E} (hy : y ∈ c.e.target)
    (hd : DifferentiableAt ℝ F (c.e.symm y)) (hi : (jac F (c.e.symm y)).IsInvertible) :
    HasFDerivAt c.e.symm (jac F (c.e.symm y)).inverse y := by
  obtain ⟨L,hL⟩ := hi
  rw [← hL, ContinuousLinearMap.inverse_equiv]
  apply c.e.hasFDerivAt_symm hy
  exact (hd.hasFDerivAt.congr_fderiv hL.symm).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ congrFun c.forward x)

theorem ChartAt.pool_derivative (c : ChartAt F p) (w : ℝ) {z : E × E}
    (hx : DifferentiableAt ℝ F z.1) (hy : DifferentiableAt ℝ F z.2)
    (ht : mix w (F z.1) (F z.2) ∈ c.e.target)
    (hu : DifferentiableAt ℝ F (c.pool w z))
    (hi : (jac F (c.pool w z)).IsInvertible) :
    HasFDerivAt (c.pool w)
      ((jac F (c.pool w z)).inverse.comp (blendJac w (jac F z.1) (jac F z.2))) z := by
  have h : HasFDerivAt (fun z : E × E ↦ mix w (F z.1) (F z.2))
      (blendJac w (jac F z.1) (jac F z.2)) z :=
    ((hx.hasFDerivAt.comp z (hasFDerivAt_fst)).const_smul _).add
      ((hy.hasFDerivAt.comp z (hasFDerivAt_snd)).const_smul _)
  exact (c.inv_derivative ht hu hi).comp z h

theorem ChartAt.eventually_pool_derivative {n : ℕ∞ω} (hn : n ≠ 0) (ho : IsOpen Ω)
    (hp : p ∈ Ω) (rF : RegularOn n Ω F) (c : ChartAt F p) (w : ℝ) :
    ∀ᶠ z in 𝓝 (p,p), HasFDerivAt (c.pool w)
      ((jac F (c.pool w z)).inverse.comp (blendJac w (jac F z.1) (jac F z.2))) z := by
  have hc := (rF p hp).1.continuousAt
  filter_upwards [continuous_fst.continuousAt.tendsto (ho.mem_nhds hp),
    continuous_snd.continuousAt.tendsto (ho.mem_nhds hp),
    c.pool_tendsto w hc (ho.mem_nhds hp),
    ChartAt.mix_tendsto w hc (c.e.open_target.mem_nhds c.base_target)] with z hx hy hu ht
  exact c.pool_derivative w ((rF _ hx).1.differentiableAt hn)
    ((rF _ hy).1.differentiableAt hn) ht ((rF _ hu).1.differentiableAt hn) (rF _ hu).2

set_option backward.isDefEq.respectTransparency false in
theorem mix_hasFDerivAt (w : ℝ) (z : E × E) :
    HasFDerivAt (fun z : E × E ↦ mix w z.1 z.2) (blendJac w 1 1) z := by
  simpa [blendJac, mix, ContinuousLinearMap.one_def, Pi.add_def, Pi.smul_def] using
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_smul (1-w)).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_smul w)

/-- Endpoint differences weighted by the two inverse Jacobians sum to zero. -/
theorem endpoint_equation {n : ℕ∞ω} (hn : n ≠ 0) (ho : IsOpen Ω) (hp : p ∈ Ω)
    (rF : RegularOn n Ω F) (rG : RegularOn n Ω G) (bal : LocalBalance Ω w F G)
    (hw : 0 < w) (hw' : w < 1) (c : ChartAt F p) (d : ChartAt G p) :
    ∀ᶠ z in 𝓝 (p,p),
      (jac F (c.pool w z)).inverse * (jac F z.2 - jac F z.1) +
      (jac G (d.pool w z)).inverse * (jac G z.2 - jac G z.1) = 0 := by
  have he := balance_pool hp bal c d (rF p hp).1.continuousAt (rG p hp).1.continuousAt
  filter_upwards [he.eventuallyEq_nhds, c.eventually_pool_derivative hn ho hp rF w,
    d.eventually_pool_derivative hn ho hp rG w] with z hab hF hG
  have lhs := hF.add hG
  have rhs := (mix_hasFDerivAt (E := E) w z).const_smul (2:ℝ)
  have hd := lhs.unique (rhs.congr_of_eventuallyEq hab)
  ext b
  have hx := congrArg (fun L : E × E →L[ℝ] E ↦ L (b,0)) hd
  have hy := congrArg (fun L : E × E →L[ℝ] E ↦ L (0,b)) hd
  simp [blendJac, ← smul_add] at hx hy
  have cancel {a : ℝ} (ha : a ≠ 0) {x y : E} (h : a • x = (2:ℝ) • a • y) : x = (2:ℝ) • y := by
    rw [smul_comm] at h
    exact (smul_right_injective E ha) h
  have hx' := cancel (sub_ne_zero.mpr (ne_of_gt hw')) hx
  have hy' := cancel (ne_of_gt hw) hy
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, sub_apply, map_sub,
    zero_apply]
  rw [sub_add_sub_comm, hx', hy', sub_self]

end CentroidRigidity
