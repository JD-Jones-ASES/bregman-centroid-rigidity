module

public import CentroidRigidity.Diagonal
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Local Taylor estimates for symmetric chords

All estimates are at zero along a real line. Integrating a Peano remainder
uses the mean value inequality on a small ball. This saves one derivative
in the equal-weight theorem.
-/

@[expose] public section
noncomputable section
open Filter Set Asymptotics
open scoped Topology ContDiff
namespace CentroidRigidity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem integrate_remainder {f g : ℝ → V} {n : ℕ}
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (g t) t)
    (hg : g =o[𝓝 0] (fun t : ℝ ↦ t^n)) :
    (fun t ↦ f t - f 0) =o[𝓝 0] (fun t : ℝ ↦ t^(n+1)) := by
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff_ball.mp hd
  let S := Metric.ball (0:ℝ) r
  have hn : S ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds _ hr
  have h := (convex_ball (0:ℝ) r).isLittleO_pow_succ_real (n := n) (Metric.mem_ball_self hr)
    (fun t ht ↦ (hs t ht).hasDerivWithinAt)
    (by simpa using hg.mono (nhdsWithin_le_nhds : 𝓝[Metric.ball (0:ℝ) r] 0 ≤ 𝓝 0))
  simpa [S, nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds (0:ℝ) hr)] using h

theorem second_peano {f g : ℝ → V} {a : V}
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (g t) t) (hg : HasDerivAt g a 0) :
    (fun t ↦ f t - (f 0 + t • g 0 + (t^2 / 2) • a)) =o[𝓝 0] fun t : ℝ ↦ t^2 := by
  let P := fun t : ℝ ↦ f 0 + t • g 0 + (t^2/2) • a
  have hP (t : ℝ) : HasDerivAt P (g 0 + t • a) t := by
    have h2 : HasDerivAt (fun s : ℝ ↦ s^2/2) t t := by
      convert ((hasDerivAt_pow 2 t).div_const 2) using 1 <;> ring
    have h1 : HasDerivAt (fun s : ℝ ↦ f 0 + s • g 0) (g 0) t := by
      simpa only [zero_add, one_smul, Pi.add_def, id_eq] using
        (hasDerivAt_const t (f 0)).add ((hasDerivAt_id t).smul_const (g 0))
    exact h1.add (h2.smul_const a)
  have he := integrate_remainder (f := fun t ↦ f t - P t)
    (g := fun t ↦ g t - (g 0 + t • a)) (n := 1)
    (hd.mono fun t ht ↦ ht.sub (hP t)) (by
      simpa only [sub_zero, pow_one, ← sub_sub] using hg.isLittleO)
  simpa [P] using he

theorem second_bigO {f : ℝ → V} (hf : ContDiffAt ℝ 2 f 0) (hd : HasDerivAt f 0 0) :
    (fun t ↦ f t - f 0) =O[𝓝 0] fun t : ℝ ↦ t^2 := by
  have hder : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (deriv f t) t :=
    (hf.eventually (by decide)).mono fun _ ht ↦ (ht.differentiableAt (by decide)).hasDerivAt
  have hg := ((hf.derivWithin (m := 1) (by decide)).differentiableAt (by decide)).hasDerivAt
  have he := (second_peano hder hg).isBigO
  rw [hd.deriv] at he
  have bound (a : V) : (fun t : ℝ ↦ (t^2/2) • a) =O[𝓝 0] fun t : ℝ ↦ t^2 := by
    refine isBigO_iff.mpr ⟨‖a‖, Filter.Eventually.of_forall fun t ↦ ?_⟩
    simp only [norm_smul, norm_div, Real.norm_ofNat]
    nlinarith [norm_nonneg (t^2), norm_nonneg a, mul_nonneg (norm_nonneg (t^2)) (norm_nonneg a)]
  apply (he.add (bound (deriv (deriv f) 0))).congr_left
  intro t
  simp only [smul_zero, add_zero]
  abel

theorem coefficient_zero {n : ℕ} {a : V}
    (h : (fun t : ℝ ↦ t^n • a) =o[𝓝 0] fun t : ℝ ↦ t^n) : a = 0 := by
  by_contra ha
  have hp : 0 < ‖a‖/2 := by positivity
  have small := (isLittleO_iff.mp h hp).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  obtain ⟨t, ht, hn⟩ := (small.and (eventually_mem_nhdsWithin (s := {0}ᶜ) (a := (0:ℝ)))).exists
  have ht' : 0 < ‖t^n‖ := norm_pos_iff.mpr (pow_ne_zero n hn)
  rw [norm_smul] at ht
  nlinarith [mul_pos ht' (norm_pos_iff.mpr ha)]

end CentroidRigidity
