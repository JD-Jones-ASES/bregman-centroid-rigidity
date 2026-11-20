module

public import CentroidRigidity.Classification
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Values of the two pooled predictions in the common basis -/

@[expose] public section
noncomputable section
namespace CentroidRigidity

theorem pairPool_unique {l a b u : ℝ} (hu : sExp l u = (sExp l a + sExp l b)/2) :
    u = pairPool l a b := by
  by_cases hl : l = 0
  · simpa [pairPool,sExp,hl] using hu
  · simp [pairPool,sExp,hl] at hu ⊢
    field_simp [hl] at hu
    have eqn : Real.exp (l*u) = (Real.exp (l*a) + Real.exp (l*b))/2 := by linarith
    have h := congrArg Real.log eqn
    rw [Real.log_exp] at h
    apply (eq_div_iff hl).mpr
    linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H] {Ω : Set H} {F G : H → H} {p : H}

theorem fixed_basis_predictions (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F)
    (bal : LocalBalance Ω (1/2) F G) :
    ∃ (B : Module.Basis (Fin (Module.finrank ℝ H)) ℝ H) (l : Fin (Module.finrank ℝ H) → ℝ),
    ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ u ∈ Ω, ∀ v ∈ Ω,
    F u = mix (1/2) (F x) (F y) → G v = mix (1/2) (G x) (G y) →
    ∀ i, B.repr (u-p) i = pairPool (l i) (B.repr (x-p) i) (B.repr (y-p) i) ∧
         B.repr (v-p) i = pairPool (-l i) (B.repr (x-p) i) (B.repr (y-p) i) := by
  obtain ⟨B,l,hF,hG⟩ := (equal_weight_classification ho hc hp rF rG pos).mp bal
  exact ⟨B,l,fun x hx y hy u hu v hv eF eG i ↦
    ⟨pairPool_unique (centroid_coordinate B l hF (rF p hp).2 hx hy hu eF i),
     pairPool_unique (centroid_coordinate B (fun j ↦ -l j) hG (rG p hp).2 hx hy hv eG i)⟩⟩

end CentroidRigidity
