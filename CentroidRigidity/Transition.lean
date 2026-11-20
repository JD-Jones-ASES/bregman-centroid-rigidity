module

public import CentroidRigidity.Unequal
public import CentroidRigidity.Peano

/-! # A stationary transition between the two Jacobian charts -/

@[expose] public section
noncomputable section
open Filter Set Asymptotics
open scoped Topology ContDiff
namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω : Set E} {F G : E → E} {p : E}

def normalJac (F : E → E) (p x : E) : Endo E := (jac F p).inverse * jac F x
def invNormal (F : E → E) (p x : E) : Endo E := (jac F x).inverse * jac F p
def reflect (p x : E) := p + (p-x)
def transition (F G : E → E) (p x : E) := normalJac G p (reflect p x) * invNormal F p x

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem reflect_base (p : E) : reflect p p = p := by simp [reflect]
omit [CompleteSpace E] in
@[simp] theorem reflect_ray (p h : E) (t : ℝ) : reflect p (ray p h t) = ray p (-h) t := by
  simp [reflect, ray]

omit [CompleteSpace E] in
theorem normal_base (hi : (jac F p).IsInvertible) : normalJac F p p = 1 := inv_mul hi
omit [CompleteSpace E] in
theorem invNormal_base (hi : (jac F p).IsInvertible) : invNormal F p p = 1 := inv_mul hi
omit [CompleteSpace E] in
theorem transition_base (hi : (jac F p).IsInvertible) (hj : (jac G p).IsInvertible) :
    transition F G p p = 1 := by simp [transition, normal_base hj, invNormal_base hi]

omit [CompleteSpace E] in
theorem normal_curve (hF : ContDiffAt ℝ 2 F p) (h : E) :
    HasDerivAt (fun t ↦ normalJac F p (ray p h t)) (logJac F p h) 0 := by
  have hd := (jac_diff hF).hasFDerivAt.comp_hasDerivAt_of_eq 0 (ray_hasDerivAt p h 0) (ray_zero _ _).symm
  simpa [normalJac,logJac,Function.comp_def] using hd.const_mul (jac F p).inverse

theorem invNormal_curve (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F) (h : E) :
    HasDerivAt (fun t ↦ invNormal F p (ray p h t)) (-logJac F p h) 0 := by
  have hd := (jac_diff (rF p hp).1).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (ray_hasDerivAt p h 0) (ray_zero _ _).symm
  have ht : Tendsto (ray p h) (𝓝 0) (𝓝 p) := by simpa using (ray_hasDerivAt p h 0).continuousAt.tendsto
  have hi : ∀ᶠ t in 𝓝 (0:ℝ), (jac F (ray p h t)).IsInvertible := by
    filter_upwards [ht (ho.mem_nhds hp)] with t hx
    exact (rF _ hx).2
  have hh := (inverse_curve hd hi).mul_const (jac F p)
  simpa [invNormal,Function.comp_def, logJac, mul_assoc, inv_mul (rF p hp).2] using hh

theorem transition_stationary (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F)
    (rG : RegularOn 2 Ω G) (opp : ∀ h, logJac F p h + logJac G p h = 0) :
    HasFDerivAt (transition F G p) (0 : E →L[ℝ] Endo E) p := by
  have href : DifferentiableAt ℝ (reflect p) p :=
    (differentiableAt_const _).add ((differentiableAt_const _).sub differentiableAt_id)
  have hdG : DifferentiableAt ℝ (jac G) (reflect p p) := by simpa using jac_diff (rG p hp).1
  have hdF := (((rF p hp).2.contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)).differentiableAt
    (by decide)).comp p (jac_diff (rF p hp).1)
  have hd : DifferentiableAt ℝ (transition F G p) p :=
    (((hdG.comp p href).const_mul (jac G p).inverse)).mul (hdF.mul_const (jac F p))
  apply hd.hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  have h1 := normal_curve (rG p hp).1 (-h)
  have h2 := invNormal_curve ho hp rF h
  have dz := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (ray_hasDerivAt p h 0) (ray_zero _ _).symm
  have dh : HasDerivAt (fun t ↦ transition F G p (ray p h t))
      (-logJac G p h - logJac F p h) 0 := by
    simpa [transition, Pi.mul_def, normal_base (rG p hp).2, invNormal_base (rF p hp).2,
      logJac,sub_eq_add_neg] using h1.mul h2
  have hz := dz.unique dh
  have he := opp h
  change fderiv ℝ (transition F G p) p h = 0
  rw [hz, eq_neg_of_add_eq_zero_right he, neg_neg, sub_self]

theorem ChartAt.pool_smooth {n : ℕ∞ω} (hn : n ≠ 0) (c : ChartAt F p)
    (hF : ContDiffAt ℝ n F p) (hi : (jac F p).IsInvertible) (w : ℝ) :
    ContDiffAt ℝ n (c.pool w) (p,p) := by
  obtain ⟨L,hL⟩ := hi
  have hd : HasFDerivAt F (L : Endo E) p := hL ▸ (hF.differentiableAt hn).hasFDerivAt
  have hinv : ContDiffAt ℝ n c.e.symm (F p) :=
    c.e.contDiffAt_symm c.base_target (f₀' := L)
      (by simpa only [c.inv_base, c.forward] using hd)
      (by simpa only [c.inv_base, c.forward] using hF)
  have harg : ContDiffAt ℝ n (fun z : E × E ↦ mix w (F z.1) (F z.2)) (p,p) :=
    ((hF.comp _ contDiffAt_fst).const_smul _).add ((hF.comp _ contDiffAt_snd).const_smul _)
  apply ContDiffAt.comp (g := (c.e.symm : E → E)) _ _ harg
  simpa using hinv

def chord (p h : E) (t : ℝ) := (ray p (-h) t, ray p h t)
omit [CompleteSpace E] in
@[simp] theorem chord_zero (p h : E) : chord p h 0 = (p,p) := by simp [chord]

omit [CompleteSpace E] in
theorem chord_derivative (p h : E) (t : ℝ) : HasDerivAt (chord p h) (-h,h) t :=
  (ray_hasDerivAt p (-h) t).prodMk (ray_hasDerivAt p h t)

omit [CompleteSpace E] in
theorem chord_smooth (p h : E) (n : ℕ∞ω) : ContDiff ℝ n (chord p h) := by
  unfold chord ray
  fun_prop

theorem chord_center_bound (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F)
    (c : ChartAt F p) (h : E) :
    (fun t ↦ c.pool (1/2) (chord p h t) - p) =O[𝓝 0] fun t : ℝ ↦ t^2 := by
  have hs := c.pool_smooth (by decide) (rF p hp).1 (rF p hp).2 (1/2)
  have hS : ContDiffAt ℝ 2 (fun t ↦ c.pool (1/2) (chord p h t)) 0 :=
    (chord_zero p h ▸ hs).comp 0 (chord_smooth p h 2).contDiffAt
  have hd := (c.eventually_pool_derivative (by decide) ho hp rF (1/2)).self_of_nhds
  have he := hd.comp_hasDerivAt_of_eq 0 (chord_derivative p h 0) (chord_zero _ _).symm
  have hh : HasDerivAt (fun t ↦ c.pool (1/2) (chord p h t)) 0 0 := by
    have z : blendJac (1/2) (jac F p) (jac F p) (-h,h) = 0 := by
      simp [blendJac]
      module
    simpa only [Function.comp_def, ChartAt.pool_base, ContinuousLinearMap.comp_apply, z, map_zero] using he
  simpa only [chord_zero, ChartAt.pool_base] using second_bigO hS hh

end CentroidRigidity
