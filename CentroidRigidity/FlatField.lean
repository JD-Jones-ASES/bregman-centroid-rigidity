module

public import CentroidRigidity.Stationarity
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Commuting mixed derivatives and constancy on the whole domain -/

@[expose] public section
noncomputable section
open Filter Set
open scoped Topology InnerProductSpace ContDiff
namespace CentroidRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H} {F G : H → H} {p : H}

theorem logJac_comm_arguments (hf : ContDiffAt ℝ 2 F p) (a b : H) :
    logJac F p a b = logJac F p b a := by
  change (jac F p).inverse (fderiv ℝ (jac F) p a b) = _
  rw [hf.isSymmSndFDerivAt (by simp) a b]
  rfl

theorem derivative_jac_product (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F) (a b : H) :
    fderiv ℝ (fderiv ℝ (jac F)) p a b =
    jac F p * (logJac F p a * logJac F p b + logDeriv F p a b) := by
  have ha : ContDiffAt ℝ 2 (jac F) p := (rF p hp).1.fderiv_right (by decide)
  have h2 := ((ha.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 (ray_hasDerivAt p a 0) (ray_zero p a).symm
  have hd := h2.clm_apply (hasDerivAt_const 0 b)
  have h1 := (ha.differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (ray_hasDerivAt p a 0) (ray_zero p a).symm
  have hl := (logJac_diff (rF p hp).1 (rF p hp).2 b).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (ray_hasDerivAt p a 0) (ray_zero p a).symm
  have ht : Tendsto (ray p a) (𝓝 0) (𝓝 p) := by simpa using (ray_hasDerivAt p a 0).continuousAt.tendsto
  have he : (fun t ↦ fderiv ℝ (jac F) (ray p a t) b) =ᶠ[𝓝 (0:ℝ)]
      fun t ↦ jac F (ray p a t) * logJac F (ray p a t) b := by
    filter_upwards [ht (ho.mem_nhds hp)] with t hx
    exact (jac_mul_logJac (rF _ hx).2 b).symm
  have eqn := hd.unique ((h1.mul hl).congr_of_eventuallyEq he)
  simp only [Function.comp_apply, ray_zero, map_zero, add_zero, zero_add] at eqn
  rw [eqn, ← jac_mul_logJac (rF p hp).2 a, mul_add,mul_assoc]
  rfl

theorem flat_equation (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F) (a b : H) :
    logJac F p a * logJac F p b + logDeriv F p a b =
    logJac F p b * logJac F p a + logDeriv F p b a := by
  have hJ : ContDiffAt ℝ 2 (jac F) p := (rF p hp).1.fderiv_right (by decide)
  have he := hJ.isSymmSndFDerivAt (by simp) a b
  rw [derivative_jac_product ho hp rF,derivative_jac_product ho hp rF] at he
  have e := congrArg (fun z : Endo H ↦ (jac F p).inverse * z) he
  simpa only [← mul_assoc, inv_mul (rF p hp).2, one_mul] using e

theorem opposite_field_derivative (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F)
    (rG : RegularOn 3 Ω G) {w : ℝ} (bal : LocalBalance Ω w F G) (hw : 0 < w) (hw' : w < 1)
    (a b : H) : logDeriv G p a b = -logDeriv F p a b := by
  have e : (fun x ↦ logJac G x b) =ᶠ[𝓝 p] fun x ↦ -logJac F x b := by
    filter_upwards [ho.mem_nhds hp] with x hx
    exact eq_neg_of_add_eq_zero_right
      (opposite_logJac ho hx (rF.lower (by decide)) (rG.lower (by decide)) bal hw hw' b)
  have he := (logJac_diff (rG p hp).1 (rG p hp).2 b).hasFDerivAt.unique
    (((logJac_diff (rF p hp).1 (rF p hp).2 b).hasFDerivAt.neg).congr_of_eventuallyEq e)
  exact congrArg (fun T : H →L[ℝ] Endo H ↦ T a) he

theorem mixed_commute (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F)
    (rG : RegularOn 3 Ω G) {w : ℝ} (bal : LocalBalance Ω w F G) (hw : 0 < w) (hw' : w < 1)
    (a b : H) :
    Commute (logJac F p a) (logJac F p b) ∧ logDeriv F p a b = logDeriv F p b a := by
  have f := flat_equation ho hp rF a b
  have g := flat_equation ho hp rG a b
  have opp (v : H) := eq_neg_of_add_eq_zero_right
    (opposite_logJac ho hp (rF.lower (by decide)) (rG.lower (by decide)) bal hw hw' v)
  simp only [opp,neg_mul_neg,opposite_field_derivative ho hp rF rG bal hw hw'] at g
  have e : (2:ℝ) • (logDeriv F p a b - logDeriv F p b a) = 0 := by
    calc
      _ = ((logJac F p a * logJac F p b + logDeriv F p a b) -
        (logJac F p b * logJac F p a + logDeriv F p b a)) -
        ((logJac F p a * logJac F p b + -logDeriv F p a b) -
        (logJac F p b * logJac F p a + -logDeriv F p b a)) := by module
      _ = 0 := by rw [f,g]; simp
  have he := sub_eq_zero.mp ((smul_eq_zero.mp e).resolve_left (by norm_num))
  rw [he] at f
  exact ⟨add_right_cancel f,he⟩

theorem logDeriv_add_right (rF : RegularOn 3 Ω F) (hp : p ∈ Ω) (a b c : H) :
    logDeriv F p a (b+c) = logDeriv F p a b + logDeriv F p a c := by
  have he : (fun x ↦ logJac F x (b+c)) = (fun x ↦ logJac F x b) + (fun x ↦ logJac F x c) := by
    funext x
    simp [logJac,mul_add]
  unfold logDeriv
  rw [he, fderiv_add (logJac_diff (rF p hp).1 (rF p hp).2 b)
    (logJac_diff (rF p hp).1 (rF p hp).2 c)]
  rfl

/-- Both directional slots of the logarithmic Jacobian field have zero spatial derivative. -/
theorem field_stationary (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F)
    (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F) (bal : LocalBalance Ω (1/2) F G)
    (a b : H) : logDeriv F p a b = 0 := by
  have h := directional_stationarity ho hp rF rG pos bal (a+b)
  rw [logDeriv_add_right rF hp] at h
  have hlin (v : H) : logDeriv F p (a+b) v = logDeriv F p a v + logDeriv F p b v :=
    map_add _ _ _
  simp only [hlin,directional_stationarity ho hp rF rG pos bal,zero_add,add_zero] at h
  rw [(mixed_commute ho hp rF rG bal (by norm_num) (by norm_num) b a).2] at h
  have e : (2:ℝ) • logDeriv F p a b = 0 := by simpa only [two_smul] using h
  exact (smul_eq_zero.mp e).resolve_left (by norm_num)

/-- In a real Hilbert space the common logarithmic Jacobian is spatially constant
even when no discrete spectral decomposition is available. -/
theorem constant_logJac (ho : IsOpen Ω) (hc : IsPreconnected Ω) (rF : RegularOn 3 Ω F)
    (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F) (bal : LocalBalance Ω (1/2) F G)
    {x y : H} (hx : x ∈ Ω) (hy : y ∈ Ω) (b : H) : logJac F x b = logJac F y b :=
  ho.is_const_of_fderiv_eq_zero hc
    (fun p hp ↦ (logJac_diff (rF p hp).1 (rF p hp).2 b).differentiableWithinAt)
    (fun p hp ↦ ContinuousLinearMap.ext (fun a ↦ field_stationary ho hp rF rG pos bal a b)) hx hy

end CentroidRigidity
