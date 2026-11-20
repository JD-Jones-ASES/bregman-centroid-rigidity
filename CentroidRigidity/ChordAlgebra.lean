module

public import CentroidRigidity.Peano

/-! # The ordered cubic coefficient of a symmetric chord -/

@[expose] public section
noncomputable section
open Filter Set Asymptotics
open scoped Topology ContDiff
namespace CentroidRigidity

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

theorem monomial_bound (n : ℕ) (a : R) :
    (fun t : ℝ ↦ t^n • a) =O[𝓝 0] fun t : ℝ ↦ t^n := by
  refine isBigO_iff.mpr ⟨‖a‖, Filter.Eventually.of_forall fun t ↦ ?_⟩
  rw [norm_smul, mul_comm]

/-- Multiply a second-order jet with zero constant term by a first-order jet.
The order of the factors is essential. -/
theorem ordered_product_jet {D C : ℝ → R} {a b c e : R}
    (hd : (fun t : ℝ ↦ D t - (t • a + t^2 • b)) =o[𝓝 0] fun t : ℝ ↦ t^2)
    (hc : HasDerivAt C e 0) (hc0 : C 0 = c) :
    (fun t : ℝ ↦ D t * C t - (t • (a*c) + t^2 • (b*c+a*e))) =o[𝓝 0] fun t : ℝ ↦ t^2 := by
  have h1 := hd.mul_isBigO (hc.continuousAt.tendsto.isBigO_one ℝ)
  have h2 := (monomial_bound 1 a).mul_isLittleO hc.isLittleO
  have h3 := (monomial_bound 2 b).mul_isLittleO
    ((isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hc.continuousAt.tendsto))
  simp only [mul_one, pow_one, sub_zero, hc0] at h1 h2 h3
  have h2' := h2.congr_right (fun t ↦ (pow_two t).symm)
  apply ((h1.add h2').add h3).congr_left
  intro t
  simp only [sub_mul, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
  rw [← pow_two]
  abel

theorem cubic_primitive {f g : ℝ → R} {a b : R}
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (g t) t)
    (he : (fun t : ℝ ↦ g t - (t • a + t^2 • b)) =o[𝓝 0] fun t : ℝ ↦ t^2) :
    (fun t : ℝ ↦ f t - (f 0 + (t^2/2) • a + (t^3/3) • b)) =o[𝓝 0] fun t : ℝ ↦ t^3 := by
  let P := fun t : ℝ ↦ f 0 + (t^2/2) • a + (t^3/3) • b
  have hP (t : ℝ) : HasDerivAt P (t • a + t^2 • b) t := by
    have h2 : HasDerivAt (fun s : ℝ ↦ s^2/2) t t := by
      convert ((hasDerivAt_pow 2 t).div_const 2) using 1
      ring
    have h3 : HasDerivAt (fun s : ℝ ↦ s^3/3) (t^2) t := by
      convert ((hasDerivAt_pow 3 t).div_const 3) using 1
      ring
    simpa [P, Pi.add_def] using ((hasDerivAt_const t (f 0)).add (h2.smul_const a)).add (h3.smul_const b)
  have hr := integrate_remainder (f := fun t ↦ f t - P t) (n := 2)
    (hd.mono fun t ht ↦ ht.sub (hP t)) he
  simpa [P] using hr

/-- The symmetric chord coefficient for the two normalized Jacobian ODEs. -/
theorem ordered_chord_identity {U V C : ℝ → R} {e : R}
    (hu : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt U (U t * C t) t)
    (hv : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt V (-(V t * C t)) t)
    (hU : U 0 = 1) (hV : V 0 = 1) (hc : HasDerivAt C e 0)
    (odd : (fun t : ℝ ↦ (U t + V t) - (U (-t) + V (-t))) =o[𝓝 0] fun t : ℝ ↦ t^3) :
    2 * (C 0 * e) + e * C 0 = 0 := by
  let c := C 0
  have du : HasDerivAt U c 0 := by simpa [c,hU] using hu.self_of_nhds
  have dv : HasDerivAt V (-c) 0 := by simpa [c,hV] using hv.self_of_nhds
  have hD : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt (fun s ↦ U s - V s) ((U t + V t)*C t) t := by
    filter_upwards [hu,hv] with t ht ht'
    simpa only [Pi.sub_def,add_mul,sub_neg_eq_add] using ht.sub ht'
  have hDD := (du.add dv).mul hc
  have hDD' : HasDerivAt (fun s ↦ (U s + V s) * C s) ((2:ℝ) • e) 0 := by
    simpa [hU,hV,add_mul,two_smul, Pi.add_def,Pi.mul_def] using hDD
  have hD2 := second_peano hD hDD'
  have hD2' : (fun t : ℝ ↦ (U t - V t) - (t • (c+c) + t^2 • e)) =o[𝓝 0] fun t : ℝ ↦ t^2 := by
    apply hD2.congr_left
    intro t
    simp only [hU,hV,sub_self,zero_add,add_mul,one_mul,c,smul_smul]
    module
  have hS : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt (fun s ↦ U s + V s) ((U t - V t)*C t) t := by
    filter_upwards [hu,hv] with t ht ht'
    simpa only [Pi.add_def, sub_mul, ← sub_eq_add_neg] using ht.add ht'
  let b := e*c + (c+c)*e
  have h := cubic_primitive hS (ordered_product_jet hD2' hc rfl)
  have hneg := h.comp_tendsto (show Tendsto (fun t : ℝ ↦ -t) (𝓝 0) (𝓝 0) by
    simpa using continuous_neg.tendsto (0:ℝ))
  simp only [Function.comp_def, Even.neg_pow (by decide : Even 2),
    Odd.neg_pow (by decide : Odd 3), isLittleO_neg_right] at hneg
  have zero : (2/3:ℝ) • b = 0 := by
    apply coefficient_zero (n := 3)
    apply (odd.sub (h.sub hneg)).congr_left
    intro t
    dsimp [b,c]
    module
  have hb : b = 0 := (smul_eq_zero.mp zero).resolve_left (by norm_num)
  simpa [b, c, two_mul, add_mul, add_comm, add_left_comm, add_assoc] using hb

end CentroidRigidity
