module

public import CentroidRigidity.Families
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Losses with affine gradients -/

@[expose] public section
noncomputable section
open Set Filter
open scoped InnerProductSpace Topology
namespace CentroidRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H} {F G : H → H} {φ ψ : H → ℝ}

theorem affine_jacobian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {f : E → E} {L : E →L[ℝ] E} {b x : E} (ho : IsOpen S) (hx : x ∈ S)
    (hf : ∀ y ∈ S, f y = L y + b) : jac f x = L := by
  have he : f =ᶠ[𝓝 x] (fun y ↦ L y + b) := by
    filter_upwards [ho.mem_nhds hx] with y hy using hf y hy
  exact ((L.hasFDerivAt.add_const b).congr_of_eventuallyEq he).fderiv

theorem quadratic_of_affine_gradient (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (hn : Ω.Nonempty) (grad : ∀ x ∈ Ω, HasGradientAt φ (F x) x)
    (pos : PositiveJacobian Ω F) (aff : AffineOn Ω F) : QuadraticLossOn Ω φ F := by
  obtain ⟨L,b,hL⟩ := aff
  obtain ⟨p,hp⟩ := hn
  have hpos := pos p hp
  change (∀ a b, ⟪jac F p a,b⟫_ℝ = ⟪a,jac F p b⟫_ℝ) ∧ _ at hpos
  have hj := affine_jacobian ho hp hL
  change (∀ a b, ⟪jac F p a,b⟫_ℝ = ⟪a,jac F p b⟫_ℝ) ∧
    (∀ a ≠ 0, 0 < ⟪jac F p a,a⟫_ℝ) at hpos
  rw [hj] at hpos
  refine ⟨L,hpos.1,hpos.2,?_⟩
  intro z hz x hx
  let Q (y : H) := φ x + ⟪F x,y-x⟫_ℝ + (1/2:ℝ) * ⟪L (y-x),y-x⟫_ℝ
  have hQ (y : H) (hy : y ∈ Ω) : HasGradientAt Q (F y) y := by
    have hsub := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
    have ha := (hasFDerivAt_const (F x) y).inner ℝ hsub
    have hb := ((L.hasFDerivAt.comp y hsub).inner ℝ hsub).const_mul (1/2:ℝ)
    have h := (ha.const_add (φ x)).add hb
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert h using 1
    · rfl
    apply ContinuousLinearMap.ext
    intro u
    change ⟪F y,u⟫_ℝ = (⟪F x,u⟫_ℝ + ⟪(0:H),y-x⟫_ℝ) +
      (1/2:ℝ) * (⟪L (y-x),u⟫_ℝ + ⟪L u,y-x⟫_ℝ)
    have es : ⟪L u,y-x⟫_ℝ = ⟪L (y-x),u⟫_ℝ := by
      rw [hpos.1 u, real_inner_comm u (L (y-x))]
    rw [es,hL y hy,hL x hx,map_sub]
    simp [inner_sub_left,inner_add_left]
    ring
  have eqn := ho.eqOn_of_fderiv_eq hc
    (fun y hy ↦ (grad y hy).hasFDerivAt.differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hQ y hy).hasFDerivAt.differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (grad y hy).hasFDerivAt.fderiv.trans (hQ y hy).hasFDerivAt.fderiv.symm)
    hx (show φ x = Q x by simp [Q])
  have h := eqn hz
  change φ z = φ x + _ + _ at h
  unfold divergence
  linarith

/-- Triple balance of two Bregman centroids characterizes a positive quadratic
divergence for each loss, with independently chosen quadratic forms. -/
theorem ternary_quadratic_losses (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hn : Ω.Nonempty)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G)
    (pF : PositiveJacobian Ω F) (pG : PositiveJacobian Ω G)
    (hφ : ∀ x ∈ Ω, HasGradientAt φ (F x) x) (hψ : ∀ x ∈ Ω, HasGradientAt ψ (G x) x)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G) :
    QuadraticLossOn Ω φ F ∧ QuadraticLossOn Ω ψ G := by
  obtain ⟨hF,hG⟩ := ternary_rigidity ho hc rF rG pF bal
  exact ⟨quadratic_of_affine_gradient ho hc hn hφ pF hF,
    quadratic_of_affine_gradient ho hc hn hψ pG hG⟩

end CentroidRigidity
