module

public import CentroidRigidity.Charts
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.NoncommRing

/-! # Differential identities for invertible Jacobians -/

@[expose] public section
noncomputable section

open Filter Set
open scoped Topology ContDiff
namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem inv_mul {a : Endo E} (h : a.IsInvertible) : a.inverse * a = 1 := by
  obtain ⟨L,rfl⟩ := h
  ext x
  simp [ContinuousLinearMap.mul_apply]

theorem mul_inv {a : Endo E} (h : a.IsInvertible) : a * a.inverse = 1 := by
  obtain ⟨L,rfl⟩ := h
  ext x
  simp [ContinuousLinearMap.mul_apply]

theorem inv_apply_apply {a : Endo E} (ha : a.IsInvertible) (x : E) :
    a.inverse (a x) = x := congrArg (fun t : Endo E ↦ t x) (inv_mul ha)

theorem apply_inv_apply {a : Endo E} (ha : a.IsInvertible) (x : E) :
    a (a.inverse x) = x := congrArg (fun t : Endo E ↦ t x) (mul_inv ha)

/-- Differentiate the inverse along a curve by differentiating its product with the curve. -/
theorem inverse_curve {A : ℝ → Endo E} {a : Endo E} {t : ℝ}
    (hd : HasDerivAt A a t) (hi : ∀ᶠ s in 𝓝 t, (A s).IsInvertible) :
    HasDerivAt (fun s ↦ (A s).inverse) (-((A t).inverse * a * (A t).inverse)) t := by
  let D := deriv (fun s ↦ (A s).inverse) t
  have ht := hi.self_of_nhds
  have hD : HasDerivAt (fun s ↦ (A s).inverse) D t :=
    (((ht.contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)).differentiableAt (by decide)).comp t
      hd.differentiableAt).hasDerivAt
  have hconst : HasDerivAt (fun s ↦ (A s).inverse * A s) 0 t :=
    (hasDerivAt_const t (1 : Endo E)).congr_of_eventuallyEq (hi.mono fun _ hs ↦ inv_mul hs)
  have h := (hD.mul hd).unique hconst
  have hh := congrArg (fun z : Endo E ↦ z * (A t).inverse) h
  simp only [add_mul, mul_assoc, mul_inv ht, mul_one, zero_mul] at hh
  convert hD using 1
  rw [mul_assoc]
  exact (eq_neg_of_add_eq_zero_left hh).symm

/-- The normalized derivative of a Jacobian in direction `h`. -/
def logJac (F : E → E) (p h : E) : Endo E :=
  (jac F p).inverse * fderiv ℝ (jac F) p h

theorem jac_mul_logJac {F : E → E} {p : E} (hi : (jac F p).IsInvertible) (h : E) :
    jac F p * logJac F p h = fderiv ℝ (jac F) p h := by
  simp only [logJac, ← mul_assoc, mul_inv hi, one_mul]

end CentroidRigidity
