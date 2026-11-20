module

public import CentroidRigidity.Diagonal
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Rigidity under an unequal input weight -/

@[expose] public section
noncomputable section

open Filter Set ContinuousLinearMap
open scoped Topology ContDiff InnerProductSpace
namespace CentroidRigidity

section Products
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The coefficient of a product of two functions vanishing to first order
can be read from their difference quotients, without second derivatives. -/
theorem zero_product_coefficient {P Q X Y : ℝ → R} {p q x y : R}
    (hP : HasDerivAt P p 0) (hQ : HasDerivAt Q q 0)
    (hX : HasDerivAt X x 0) (hY : HasDerivAt Y y 0)
    (p0 : P 0 = 0) (q0 : Q 0 = 0) (x0 : X 0 = 0) (y0 : Y 0 = 0)
    (he : ∀ᶠ t in 𝓝 (0:ℝ), P t * X t + Q t * Y t = 0) : p*x + q*y = 0 := by
  have slope0 {f : ℝ → R} {a : R} (hd : HasDerivAt f a 0) (hf : f 0 = 0) :
      Tendsto (fun t : ℝ ↦ t⁻¹ • f t) (𝓝[≠] 0) (𝓝 a) := by
    simpa only [zero_add, hf, sub_zero] using hd.tendsto_slope_zero
  have ht := ((slope0 hP p0).mul (slope0 hX x0)).add ((slope0 hQ q0).mul (slope0 hY y0))
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_add, ht, smul_zero]

end Products

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω : Set E} {F G : E → E} {p : E} {w : ℝ}

/-- With no metric assumption, the square of every logarithmic Jacobian
derivative must vanish. Nonlinear shear solutions attain this obstruction. -/
theorem square_zero_of_unequal (ho : IsOpen Ω) (hp : p ∈ Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (bal : LocalBalance Ω w F G)
    (hw : 0 < w) (hw' : w < 1) (hne : w ≠ 1/2) (h : E) :
    logJac F p h * logJac F p h = 0 := by
  obtain ⟨c⟩ := exists_chartAt (by decide : (1 : ℕ∞ω) ≤ 2) (rF p hp).1 (rF p hp).2
  obtain ⟨d⟩ := exists_chartAt (by decide : (1 : ℕ∞ω) ≤ 2) (rG p hp).1 (rG p hp).2
  have he := endpoint_line ho hp rF rG bal hw hw' c d h
  have he' := endpoint_line ho hp rF rG bal.swap (by linarith) (by linarith) c d h
  have hd (H : E → E) (rH : RegularOn 2 Ω H) (e : ChartAt H p) :=
    (centerInv_derivative ho hp rH e w h).sub (centerInv_derivative ho hp rH e (1-w) h)
  have hs := zero_product_coefficient (hd F rF c) (hd G rG d)
    (jacDelta_derivative (rF p hp).1 h) (jacDelta_derivative (rG p hp).1 h)
    (by simp) (by simp) (by simp) (by simp) (by
      filter_upwards [he, he'] with t ht ht'
      simp only [Pi.sub_apply, sub_mul, sub_add_sub_comm, ht, ht', sub_self])
  have scaled (H : E → E) :
      ((-w) • (logJac H p h * (jac H p).inverse) -
        (-(1-w)) • (logJac H p h * (jac H p).inverse)) * fderiv ℝ (jac H) p h =
      (1-2*w) • (logJac H p h * logJac H p h) := by
    rw [← sub_smul, smul_mul_assoc, mul_assoc]
    have e : -w - -(1-w) = 1-2*w := by ring
    rw [e]
    rfl
  rw [scaled, scaled] at hs
  have hopp := opposite_logJac ho hp rF rG bal hw hw' h
  have hg : logJac G p h = -logJac F p h := eq_neg_of_add_eq_zero_right hopp
  rw [hg, neg_mul_neg, ← add_smul] at hs
  exact (smul_eq_zero.mp hs).resolve_left (by intro e; apply hne; linarith)

omit [CompleteSpace E] in
theorem affine_of_jac_deriv_zero (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (hz : ∀ p ∈ Ω, ∀ h, fderiv ℝ (jac F) p h = 0) :
    AffineOn Ω F := by
  obtain ⟨L,hL⟩ := ho.exists_is_const_of_fderiv_eq_zero hc
    (fun p hp ↦ (jac_diff (rF p hp).1).differentiableWithinAt)
    (fun p hp ↦ ContinuousLinearMap.ext (hz p hp))
  obtain ⟨b,hb⟩ := ho.exists_eq_add_of_fderiv_eq hc
    (fun p hp ↦ ((rF p hp).1.differentiableAt (by decide)).differentiableWithinAt)
    L.differentiable.differentiableOn (fun p hp ↦ by simpa using hL p hp)
  exact ⟨L,b,hb⟩

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {S : Set H} {A B : H → H} {p : H}

omit [CompleteSpace H] in
/-- Symmetry of a Jacobian is inherited by its directional derivatives. -/
theorem jac_deriv_symmetric (ho : IsOpen S) (hp : p ∈ S) (rA : RegularOn 2 S A)
    (hA : PositiveJacobian S A) (h u v : H) :
    ⟪fderiv ℝ (jac A) p h u, v⟫_ℝ = ⟪u, fderiv ℝ (jac A) p h v⟫_ℝ := by
  have hd := (jac_diff (rA p hp).1).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (ray_hasDerivAt p h 0) (ray_zero p h).symm
  have hu := hd.clm_apply (hasDerivAt_const 0 u)
  have hv := hd.clm_apply (hasDerivAt_const 0 v)
  have e : (fun t ↦ ⟪jac A (ray p h t) u, v⟫_ℝ) =ᶠ[𝓝 (0:ℝ)]
      fun t ↦ ⟪u, jac A (ray p h t) v⟫_ℝ := by
    have ht : Tendsto (ray p h) (𝓝 0) (𝓝 p) := by simpa using (ray_hasDerivAt p h 0).continuousAt.tendsto
    filter_upwards [ht (ho.mem_nhds hp)] with t ht
    exact (hA _ ht).1 u v
  simpa using (hu.inner ℝ (hasDerivAt_const 0 v)).unique
    (((hasDerivAt_const 0 u).inner ℝ hv).congr_of_eventuallyEq e)

omit [CompleteSpace H] in
/-- A positive-definite Jacobian makes a square-zero logarithmic derivative vanish. -/
theorem logJac_zero_of_square (ho : IsOpen S) (hp : p ∈ S) (rA : RegularOn 2 S A)
    (hA : PositiveJacobian S A) (h : H) (hs : logJac A p h * logJac A p h = 0) :
    logJac A p h = 0 := by
  let K := logJac A p h
  have hK (x : H) : jac A p (K x) = fderiv ℝ (jac A) p h x :=
    congrArg (fun L : Endo H ↦ L x) (jac_mul_logJac (rA p hp).2 h)
  have h0 (x : H) : K (K x) = 0 := congrArg (fun L : Endo H ↦ L x) hs
  ext x
  change K x = 0
  by_contra hx
  have positive := (hA p hp).2 (K x) hx
  have eq : ⟪jac A p (K x), K x⟫_ℝ = 0 := by
    rw [hK, jac_deriv_symmetric ho hp rA hA, ← hK, h0]
    simp
  linarith

/-- A single unequal input weight forces both generators to be affine on a
connected open domain in a real Hilbert space. Only the first Jacobian
needs to be symmetric positive definite. -/
theorem unequal_weight_rigidity (ho : IsOpen S) (hc : IsPreconnected S)
    (rA : RegularOn 2 S A) (rB : RegularOn 2 S B) (hA : PositiveJacobian S A)
    (hw : 0 < w) (hw' : w < 1) (hne : w ≠ 1/2) (bal : LocalBalance S w A B) :
    AffineOn S A ∧ AffineOn S B := by
  have H0 (p : H) (hp : p ∈ S) (h : H) : logJac A p h = 0 :=
    logJac_zero_of_square ho hp rA hA h (square_zero_of_unequal ho hp rA rB bal hw hw' hne h)
  constructor
  · exact affine_of_jac_deriv_zero ho hc rA fun p hp h ↦ by
      rw [← jac_mul_logJac (rA p hp).2 h, H0 p hp h, mul_zero]
  · exact affine_of_jac_deriv_zero ho hc rB fun p hp h ↦ by
      have he := opposite_logJac ho hp rA rB bal hw hw' h
      rw [H0 p hp h, zero_add] at he
      rw [← jac_mul_logJac (rB p hp).2 h, he, mul_zero]

end Hilbert
end CentroidRigidity
