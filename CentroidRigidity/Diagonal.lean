module

public import CentroidRigidity.Endpoints
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Limits on a line through the diagonal -/

@[expose] public section
noncomputable section

open Filter Set ContinuousLinearMap
open scoped Topology ContDiff
namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω : Set E} {F G : E → E} {p : E} {w : ℝ}

def ray (p h : E) (t : ℝ) := p + t • h
def ends (p h : E) (t : ℝ) := (p, ray p h t)

omit [CompleteSpace E] in
@[simp] theorem ray_zero (p h : E) : ray p h 0 = p := by simp [ray]
omit [CompleteSpace E] in
@[simp] theorem ends_zero (p h : E) : ends p h 0 = (p,p) := by simp [ends]

omit [CompleteSpace E] in
theorem ray_hasDerivAt (p h : E) (t : ℝ) : HasDerivAt (ray p h) h t := by
  change HasDerivAt (fun s : ℝ ↦ p + s • h) h t
  simpa [Pi.add_def] using (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const h)

omit [CompleteSpace E] in
theorem ends_hasDerivAt (p h : E) (t : ℝ) : HasDerivAt (ends p h) (0,h) t :=
  (hasDerivAt_const t p).prodMk (ray_hasDerivAt p h t)

omit [CompleteSpace E] in
theorem jac_diff {F : E → E} {p : E} (hF : ContDiffAt ℝ 2 F p) :
    DifferentiableAt ℝ (jac F) p :=
  (hF.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)

def jacDelta (F : E → E) (p h : E) (t : ℝ) := jac F (ray p h t) - jac F p

omit [CompleteSpace E] in
@[simp] theorem jacDelta_zero (F : E → E) (p h : E) : jacDelta F p h 0 = 0 := by simp [jacDelta]

omit [CompleteSpace E] in
theorem jacDelta_derivative (hF : ContDiffAt ℝ 2 F p) (h : E) :
    HasDerivAt (jacDelta F p h) (fderiv ℝ (jac F) p h) 0 := by
  exact ((jac_diff hF).hasFDerivAt.comp_hasDerivAt_of_eq 0 (ray_hasDerivAt p h 0)
    (ray_zero _ _).symm).sub_const _

def centerInv (c : ChartAt F p) (w : ℝ) (h : E) (t : ℝ) :=
  (jac F (c.pool w (ends p h t))).inverse

omit [CompleteSpace E] in
@[simp] theorem centerInv_zero (c : ChartAt F p) (w : ℝ) (h : E) :
    centerInv c w h 0 = (jac F p).inverse := by simp [centerInv]

omit [CompleteSpace E] in
theorem center_derivative (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F)
    (c : ChartAt F p) (w : ℝ) (h : E) :
    HasDerivAt (fun t ↦ c.pool w (ends p h t)) (w • h) 0 := by
  have he := (c.eventually_pool_derivative (by decide) ho hp rF w).self_of_nhds
  have hd := he.comp_hasDerivAt_of_eq 0 (ends_hasDerivAt p h 0) (ends_zero p h).symm
  simpa [blendJac, Function.comp_def, inv_apply_apply (rF p hp).2] using hd

theorem centerInv_derivative (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F)
    (c : ChartAt F p) (w : ℝ) (h : E) :
    HasDerivAt (centerInv c w h) ((-w) • (logJac F p h * (jac F p).inverse)) 0 := by
  have hc := center_derivative ho hp rF c w h
  have hd := (jac_diff (rF p hp).1).hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)
  have hct : Tendsto (fun t ↦ c.pool w (ends p h t)) (𝓝 0) (𝓝 p) := by
    simpa using hc.continuousAt.tendsto
  have hi : ∀ᶠ t in 𝓝 (0 : ℝ), (jac F (c.pool w (ends p h t))).IsInvertible :=
    by
      filter_upwards [hct (ho.mem_nhds hp)] with s hs
      exact (rF _ hs).2
  have hh := inverse_curve hd hi
  change HasDerivAt (fun t ↦ (jac F (c.pool w (ends p h t))).inverse) _ _
  simpa [Function.comp_def, logJac, neg_smul, smul_mul_assoc, mul_smul_comm] using hh

omit [CompleteSpace E] in
theorem endpoint_line (ho : IsOpen Ω) (hp : p ∈ Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (bal : LocalBalance Ω w F G)
    (hw : 0 < w) (hw' : w < 1) (c : ChartAt F p) (d : ChartAt G p) (h : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ), centerInv c w h t * jacDelta F p h t +
      centerInv d w h t * jacDelta G p h t = 0 := by
  have ht : Tendsto (ends p h) (𝓝 0) (𝓝 (p,p)) := by
    simpa using (ends_hasDerivAt p h 0).continuousAt.tendsto
  exact ht (endpoint_equation (by decide) ho hp rF rG bal hw hw' c d)

/-- Complementarity forces opposite logarithmic Jacobian derivatives for every input weight. -/
theorem opposite_logJac (ho : IsOpen Ω) (hp : p ∈ Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (bal : LocalBalance Ω w F G)
    (hw : 0 < w) (hw' : w < 1) (h : E) :
    logJac F p h + logJac G p h = 0 := by
  obtain ⟨c⟩ := exists_chartAt (by decide : (1 : ℕ∞ω) ≤ 2) (rF p hp).1 (rF p hp).2
  obtain ⟨d⟩ := exists_chartAt (by decide : (1 : ℕ∞ω) ≤ 2) (rG p hp).1 (rG p hp).2
  have hf := (centerInv_derivative ho hp rF c w h).mul (jacDelta_derivative (rF p hp).1 h)
  have hg := (centerInv_derivative ho hp rG d w h).mul (jacDelta_derivative (rG p hp).1 h)
  have he := endpoint_line ho hp rF rG bal hw hw' c d h
  have hz := (hasDerivAt_const (0:ℝ) (0 : Endo E)).congr_of_eventuallyEq he
  simpa [logJac] using (hf.add hg).unique hz

end CentroidRigidity
