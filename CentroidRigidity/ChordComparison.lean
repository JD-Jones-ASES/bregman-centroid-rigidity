module

public import CentroidRigidity.Transition
public import CentroidRigidity.ChordAlgebra

/-! # Vanishing cubic obstruction from the actual balanced means -/

@[expose] public section
noncomputable section
open Filter Set Asymptotics
open scoped Topology ContDiff
namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω : Set E} {F G : E → E} {p : E}

theorem RegularOn.lower {n m : ℕ∞ω} (H : RegularOn n Ω F) (hm : m ≤ n) : RegularOn m Ω F :=
  fun x hx ↦ ⟨(H x hx).1.of_le hm, (H x hx).2⟩

theorem logJac_diff (hF : ContDiffAt ℝ 3 F p) (hi : (jac F p).IsInvertible) (h : E) :
    DifferentiableAt ℝ (fun x ↦ logJac F x h) p := by
  have ha : ContDiffAt ℝ 2 (jac F) p := hF.fderiv_right (by decide)
  have hb := (((hi.contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)).differentiableAt
    (by decide)).comp p (ha.differentiableAt (by decide)))
  exact hb.mul (((ha.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).clm_apply (differentiableAt_const h))

theorem normalize_endpoint {A B U V X Y : Endo E} (ha : A.IsInvertible) (hv : V.IsInvertible)
    (eqn : U.inverse * X + V.inverse * Y = 0) :
    ((B.inverse * V) * (U.inverse * A)) * (A.inverse * X) + B.inverse * Y = 0 := by
  have hx : A * (A.inverse * X) = X := by rw [← mul_assoc,mul_inv ha,one_mul]
  have hy : V * (V.inverse * Y) = Y := by rw [← mul_assoc,mul_inv hv,one_mul]
  have e := congrArg (fun t : Endo E ↦ (B.inverse * V) * t) eqn
  simpa only [mul_add, mul_assoc, mul_zero, hx, hy] using
    (show (B.inverse * V) * (U.inverse * A * (A.inverse * X)) + B.inverse * Y = 0 by
      simpa only [mul_add,mul_assoc,mul_zero,hx,hy] using e)

def onRay (F : E → E) (p h : E) (t : ℝ) := normalJac F p (ray p h t)

theorem ray_neg_dir (p h : E) (t : ℝ) : ray p (-h) t = ray p h (-t) := by simp [ray]

theorem chord_reflection (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F)
    (rG : RegularOn 2 Ω G) (bal : LocalBalance Ω (1/2) F G) (c : ChartAt F p) (d : ChartAt G p)
    (h : E) : ∀ᶠ t in 𝓝 (0:ℝ),
      d.pool (1/2) (chord p h t) = reflect p (c.pool (1/2) (chord p h t)) := by
  have ht : Tendsto (chord p h) (𝓝 0) (𝓝 (p,p)) := by
    simpa using (chord_derivative p h 0).continuousAt.tendsto
  have e := balance_pool hp bal c d (rF p hp).1.continuousAt (rG p hp).1.continuousAt
  filter_upwards [ht.eventually e] with t he
  have hm : mix (1/2) (chord p h t).1 (chord p h t).2 = p := by
    unfold chord ray mix
    simp only [smul_neg]
    module
  rw [hm] at he
  unfold reflect
  rw [← add_sub_assoc, ← two_smul ℝ p, ← he]
  abel

theorem normalized_chord (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F)
    (rG : RegularOn 2 Ω G) (bal : LocalBalance Ω (1/2) F G)
    (c : ChartAt F p) (d : ChartAt G p) (h : E) :
    ∀ᶠ t in 𝓝 (0:ℝ),
      transition F G p (c.pool (1/2) (chord p h t)) * (onRay F p h t - onRay F p h (-t)) +
        (onRay G p h t - onRay G p h (-t)) = 0 := by
  have ht : Tendsto (chord p h) (𝓝 0) (𝓝 (p,p)) := by
    simpa using (chord_derivative p h 0).continuousAt.tendsto
  have hv := (d.pool_tendsto (1/2) (rG p hp).1.continuousAt).comp ht
  have he := endpoint_equation (by decide) ho hp rF rG bal (by norm_num) (by norm_num) c d
  filter_upwards [ht.eventually he, hv (ho.mem_nhds hp), chord_reflection ho hp rF rG bal c d h]
    with t eqn hmem ref
  have hnorm := normalize_endpoint (B := jac G p) (rF p hp).2 (rG _ hmem).2 eqn
  simp only [transition, ← ref, normalJac, invNormal, onRay, ← mul_sub]
  simpa only [Function.comp_def, jac, chord, Prod.fst, Prod.snd, ray_neg_dir] using hnorm

theorem odd_chord_small (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F)
    (rG : RegularOn 2 Ω G) (bal : LocalBalance Ω (1/2) F G) (h : E) :
    (fun t : ℝ ↦ (onRay F p h t + onRay G p h t) -
      (onRay F p h (-t) + onRay G p h (-t))) =o[𝓝 0] fun t : ℝ ↦ t^3 := by
  obtain ⟨c⟩ := exists_chartAt (by decide : (1:ℕ∞ω) ≤ 2) (rF p hp).1 (rF p hp).2
  obtain ⟨d⟩ := exists_chartAt (by decide : (1:ℕ∞ω) ≤ 2) (rG p hp).1 (rG p hp).2
  let u := fun t ↦ c.pool (1/2) (chord p h t)
  have ht : Tendsto (chord p h) (𝓝 0) (𝓝 (p,p)) := by
    simpa using (chord_derivative p h 0).continuousAt.tendsto
  have hu : Tendsto u (𝓝 0) (𝓝 p) := (c.pool_tendsto _ (rF p hp).1.continuousAt).comp ht
  have h0 := transition_stationary ho hp rF rG
    (opposite_logJac ho hp rF rG bal (by norm_num) (by norm_num))
  have h1 : (fun x ↦ transition F G p x - 1) =o[𝓝 p] fun x ↦ x - p := by
    simpa only [ContinuousLinearMap.zero_apply,sub_zero,transition_base (rF p hp).2 (rG p hp).2]
      using (hasFDerivAt_iff_isLittleO.mp h0)
  have h2 := (h1.comp_tendsto hu).trans_isBigO (chord_center_bound ho hp rF c h)
  have dU : HasDerivAt (onRay F p h) (logJac F p h) 0 := normal_curve (rF p hp).1 h
  have dm := dU.scomp_of_eq 0 (hasDerivAt_id (0:ℝ)).neg (by simp)
  have h3 := (dU.sub dm).isBigO_sub
  have h3' : (fun t : ℝ ↦ onRay F p h t - onRay F p h (-t)) =O[𝓝 0] fun t : ℝ ↦ t := by
    simpa [Function.comp_def, Pi.sub_def] using h3
  apply (h2.mul_isBigO h3').neg_left.congr'
  · filter_upwards [normalized_chord ho hp rF rG bal c d h] with t he
    dsimp [u]
    rw [sub_mul,one_mul,neg_sub]
    rw [← sub_add_sub_comm]
    abel_nf at he ⊢
    linear_combination (norm := abel) -he
  · exact Filter.Eventually.of_forall fun t ↦ (pow_succ t 2).symm

theorem onRay_ode (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F) (h : E) :
    ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt (onRay F p h) (onRay F p h t * logJac F (ray p h t) h) t := by
  have ht : Tendsto (ray p h) (𝓝 0) (𝓝 p) := by simpa using (ray_hasDerivAt p h 0).continuousAt.tendsto
  filter_upwards [ht (ho.mem_nhds hp)] with t hx
  have hd := (jac_diff (rF _ hx).1).hasFDerivAt.comp_hasDerivAt t (ray_hasDerivAt p h t)
  change HasDerivAt (fun s ↦ (jac F p).inverse * jac F (ray p h s)) _ _
  simpa only [onRay,normalJac,Function.comp_def,mul_assoc,jac_mul_logJac (rF _ hx).2]
    using hd.const_mul (jac F p).inverse

/-- Intrinsic ordered equation at the base point for the variation of a logarithmic Jacobian. -/
theorem cubic_obstruction (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F)
    (rG : RegularOn 3 Ω G) (bal : LocalBalance Ω (1/2) F G) (h : E) :
    let K := logJac F p h
    let D := fderiv ℝ (fun x ↦ logJac F x h) p h
    2 * (K * D) + D * K = 0 := by
  have f2 := rF.lower (by decide : (2:ℕ∞ω) ≤ 3)
  have g2 := rG.lower (by decide : (2:ℕ∞ω) ≤ 3)
  have ht : Tendsto (ray p h) (𝓝 0) (𝓝 p) := by simpa using (ray_hasDerivAt p h 0).continuousAt.tendsto
  have hG : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt (onRay G p h)
      (-(onRay G p h t * logJac F (ray p h t) h)) t := by
    filter_upwards [onRay_ode ho hp g2 h, ht (ho.mem_nhds hp)] with t hg hx
    have e := opposite_logJac ho hx f2 g2 bal (by norm_num) (by norm_num) h
    simpa only [eq_neg_of_add_eq_zero_right e,mul_neg] using hg
  have hd := (logJac_diff (rF p hp).1 (rF p hp).2 h).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (ray_hasDerivAt p h 0) (ray_zero _ _).symm
  simpa only [ray_zero,Function.comp_def] using ordered_chord_identity (onRay_ode ho hp f2 h) hG
    (by simp [onRay, normal_base (rF p hp).2]) (by simp [onRay, normal_base (rG p hp).2])
    hd (odd_chord_small ho hp f2 g2 bal h)

end CentroidRigidity
