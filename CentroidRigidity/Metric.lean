module

public import CentroidRigidity.Transition

/-! # Self-adjoint operators for the variable Hessian metric -/

@[expose] public section
noncomputable section
open Filter Set
open scoped Topology InnerProductSpace ContDiff
namespace CentroidRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def SymFor (A T : Endo H) : Prop := ∀ u v, ⟪A (T u),v⟫_ℝ = ⟪A u,T v⟫_ℝ
def StrictPos (A : Endo H) : Prop := ∀ u ≠ 0, 0 < ⟪A u,u⟫_ℝ

theorem zero_of_square_apply {A T : Endo H} (pos : StrictPos A) (sym : SymFor A T)
    (v : H) (hz : T (T v) = 0) : T v = 0 := by
  by_contra hn
  have hp := pos _ hn
  have he := sym v (T v)
  rw [hz, inner_zero_right] at he
  linarith

/-- Transposing the ordered identity separates its two products. -/
theorem annihilating_products {A C D : Endo H} (hp : StrictPos A)
    (hc : SymFor A C) (hd : SymFor A D) (he : 2*(C*D) + D*C = 0) :
    C*D = 0 ∧ D*C = 0 := by
  unfold SymFor at hc hd
  have rev : 2*(D*C) + C*D = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    let y := (2*(D*C) + C*D) x
    change y = 0
    by_contra hy
    have hypos := hp y hy
    have e := congrArg (fun L : Endo H ↦ ⟪A x,L y⟫_ℝ) he
    have eq0 : ⟪A y,y⟫_ℝ = 0 := by
      change ⟪A ((2*(D*C) + C*D) x),y⟫_ℝ = 0
      simpa only [two_mul, add_apply, mul_apply_eq_comp, map_add, inner_add_left,
        inner_add_right, hd, hc, ContinuousLinearMap.zero_apply, inner_zero_right] using e
    linarith
  have he' : (2:ℝ) • (C*D) + D*C = 0 := by simpa [two_smul,two_mul] using he
  have rev' : (2:ℝ) • (D*C) + C*D = 0 := by simpa [two_smul,two_mul] using rev
  have hz : (3:ℝ) • (C*D) = 0 := by
    calc
      _ = (2:ℝ) • ((2:ℝ) • (C*D) + D*C) - ((2:ℝ) • (D*C) + C*D) := by module
      _ = 0 := by rw [he',rev']; simp
  have hz' := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  exact ⟨hz',by simpa [hz'] using he⟩

variable {Ω : Set H} {F : H → H} {p : H}

theorem logJac_sym (ho : IsOpen Ω) (hp : p ∈ Ω) (rF : RegularOn 2 Ω F)
    (pos : PositiveJacobian Ω F) (h : H) : SymFor (jac F p) (logJac F p h) := by
  have he (x : H) : jac F p (logJac F p h x) = fderiv ℝ (jac F) p h x :=
    congrArg (fun L : Endo H ↦ L x) (jac_mul_logJac (rF p hp).2 h)
  intro u v
  rw [he, jac_deriv_symmetric ho hp rF pos, ← he, (pos p hp).1]

theorem local_const_of_derivative_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V} (hd : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f 0 t) :
    ∀ᶠ t in 𝓝 (0:ℝ), f t = f 0 := by
  obtain ⟨r,hr,h⟩ := Metric.eventually_nhds_iff_ball.mp hd
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with t ht
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℝ) r).isPreconnected
    (fun s hs ↦ (h s hs).differentiableAt.differentiableWithinAt) (fun s hs ↦ (h s hs).deriv)
    ht (Metric.mem_ball_self hr)

/-- If the square is locally constant, its kernel is locally constant.
A derivative taking values in that kernel and self-adjoint at the base
point must vanish. No finite-dimensional spectral theorem is needed. -/
theorem stationary_from_square {A C : ℝ → Endo H} {D : Endo H}
    (hsym : ∀ᶠ t in 𝓝 (0:ℝ), SymFor (A t) (C t) ∧ StrictPos (A t))
    (hD : HasDerivAt C D 0) (hd : SymFor (A 0) D) (hc : C 0 * D = 0)
    (hsq : ∀ᶠ t in 𝓝 (0:ℝ), C t * C t = C 0 * C 0) : D = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  let b := D x
  have hz : C 0 b = 0 := congrArg (fun L : Endo H ↦ L x) hc
  have e : (fun t ↦ C t b) =ᶠ[𝓝 (0:ℝ)] fun _ ↦ 0 := by
    filter_upwards [hsym,hsq] with t ht he
    apply zero_of_square_apply ht.2 ht.1 b
    have hv := congrArg (fun L : Endo H ↦ L b) he
    simpa only [mul_apply_eq_comp, hz, map_zero] using hv
  have der := hD.clm_apply (hasDerivAt_const 0 b)
  have hdb : D b = 0 := by
    simpa using der.unique ((hasDerivAt_const 0 (0:H)).congr_of_eventuallyEq e)
  exact zero_of_square_apply hsym.self_of_nhds.2 hd x hdb

end CentroidRigidity
