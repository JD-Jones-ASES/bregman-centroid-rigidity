module

public import CentroidRigidity.ChordComparison
public import CentroidRigidity.Metric

/-! # Constancy along lines without a spectral assumption -/

@[expose] public section
noncomputable section
open Filter Set
open scoped Topology InnerProductSpace ContDiff
namespace CentroidRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H} {F G : H → H} {p : H}

def logDeriv (F : H → H) (p a h : H) : Endo H := fderiv ℝ (fun x ↦ logJac F x h) p a

theorem log_curve (rF : RegularOn 3 Ω F) {t : ℝ} (p a h : H) (hp : ray p a t ∈ Ω) :
    HasDerivAt (fun s ↦ logJac F (ray p a s) h) (logDeriv F (ray p a t) a h) t :=
  (logJac_diff (rF _ hp).1 (rF _ hp).2 h).hasFDerivAt.comp_hasDerivAt t (ray_hasDerivAt p a t)

theorem logDeriv_sym (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F)
    (pos : PositiveJacobian Ω F) (h : H) : SymFor (jac F p) (logDeriv F p h h) := by
  let J := fun t ↦ jac F (ray p h t)
  let C := fun t ↦ logJac F (ray p h t) h
  let A := jac F p
  let K := logJac F p h
  let D := logDeriv F p h h
  have f2 := rF.lower (by decide : (2:ℕ∞ω) ≤ 3)
  have hJ : HasDerivAt J (A*K) 0 := by
    rw [show A*K = fderiv ℝ (jac F) p h from jac_mul_logJac (rF p hp).2 h]
    exact (jac_diff (f2 p hp).1).hasFDerivAt.comp_hasDerivAt_of_eq 0
      (ray_hasDerivAt p h 0) (ray_zero _ _).symm
  have hC : HasDerivAt C D 0 := by
    simpa only [ray_zero] using log_curve rF (t := 0) p h h (by simpa)
  have hJ0 : J 0 = A := by simp [J,A]
  have hC0 : C 0 = K := by simp [C,K]
  have sym : SymFor A K := logJac_sym ho hp f2 pos h
  have ht : Tendsto (ray p h) (𝓝 0) (𝓝 p) := by simpa using (ray_hasDerivAt p h 0).continuousAt.tendsto
  intro u v
  have e : (fun t ↦ ⟪(J t * C t) u,v⟫_ℝ) =ᶠ[𝓝 (0:ℝ)] fun t ↦ ⟪J t u,C t v⟫_ℝ := by
    filter_upwards [ht (ho.mem_nhds hp)] with t hx
    exact logJac_sym ho hx f2 pos h u v
  have l := ((hJ.mul hC).clm_apply (hasDerivAt_const 0 u)).inner ℝ (hasDerivAt_const 0 v)
  have r := (hJ.clm_apply (hasDerivAt_const 0 u)).inner ℝ (hC.clm_apply (hasDerivAt_const 0 v))
  have eqn := l.unique (r.congr_of_eventuallyEq e)
  simp only [hJ0,hC0,mul_apply_eq_comp,add_apply,Pi.mul_apply,map_zero,add_zero,zero_add,
    inner_zero_right,inner_add_left] at eqn
  have hcancel := sym (K u) v
  change ⟪A (D u),v⟫_ℝ = ⟪A u,D v⟫_ℝ
  linarith

theorem logJac_annihilates (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F)
    (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F) (bal : LocalBalance Ω (1/2) F G)
    (h : H) :
    logJac F p h * logDeriv F p h h = 0 ∧ logDeriv F p h h * logJac F p h = 0 :=
  annihilating_products (pos p hp).2
    (logJac_sym ho hp (rF.lower (by decide)) pos h) (logDeriv_sym ho hp rF pos h)
    (cubic_obstruction ho hp rF rG bal h)

/-- The logarithmic Jacobian in a direction has zero derivative in that direction.
The kernel argument is valid in a real Hilbert space of arbitrary dimension. -/
theorem directional_stationarity (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 3 Ω F)
    (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F) (bal : LocalBalance Ω (1/2) F G)
    (h : H) : logDeriv F p h h = 0 := by
  let C := fun t ↦ logJac F (ray p h t) h
  let A := fun t ↦ jac F (ray p h t)
  have ht : Tendsto (ray p h) (𝓝 0) (𝓝 p) := by simpa using (ray_hasDerivAt p h 0).continuousAt.tendsto
  have hx : ∀ᶠ t in 𝓝 (0:ℝ), ray p h t ∈ Ω := ht (ho.mem_nhds hp)
  have he : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt (fun s ↦ C s*C s) 0 t := by
    filter_upwards [hx] with t hmem
    have d := log_curve rF p h h hmem
    obtain ⟨h1,h2⟩ := logJac_annihilates ho hmem rF rG pos bal h
    simpa only [C,Pi.mul_def,h1,h2,add_zero] using d.mul d
  have hsq := local_const_of_derivative_zero he
  apply stationary_from_square (A := A) (C := C) _ _ _ _ hsq
  · filter_upwards [hx] with t hmem
    exact ⟨logJac_sym ho hmem (rF.lower (by decide)) pos h,(pos _ hmem).2⟩
  · simpa [C] using log_curve rF (t := 0) p h h (by simpa)
  · simpa [A] using logDeriv_sym ho hp rF pos h
  · simpa [C] using (logJac_annihilates ho hp rF rG pos bal h).1

end CentroidRigidity
