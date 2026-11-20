module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! # Complementary centroid rules

The two generator equations specify the actual nearby centroids. The
arithmetic, exponential and loss formulas use the same input coordinates.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped BigOperators Topology InnerProductSpace ContDiff
namespace CentroidRigidity

section Pooling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weighted arithmetic interpolation, with weight `w` on the second argument. -/
def mix (w : ℝ) (x y : E) : E := (1 - w) • x + w • y

/-- A generator with the indicated smoothness and invertible derivative at each domain point. -/
def RegularOn (n : ℕ∞ω) (Ω : Set E) (F : E → E) : Prop :=
  ∀ p ∈ Ω, ContDiffAt ℝ n F p ∧ (fderiv ℝ F p).IsInvertible

/-- The two locally defined pooling rules average to the arithmetic rule.
The four points are the inputs and their respective centroids. -/
def LocalBalance (Ω : Set E) (w : ℝ) (F G : E → E) : Prop :=
  ∀ p ∈ Ω, ∃ U ∈ 𝓝 p, ∀ x ∈ U, ∀ y ∈ U, ∀ u ∈ U, ∀ v ∈ U,
    F u = mix w (F x) (F y) → G v = mix w (G x) (G y) →
    u + v = (2 : ℝ) • mix w x y

/-- The restriction of a continuous affine map. -/
def AffineOn (Ω : Set E) (F : E → E) : Prop :=
  ∃ (L : E →L[ℝ] E) (b : E), ∀ x ∈ Ω, F x = L x + b

/-- Positive definiteness and symmetry of the Jacobian of the first generator. -/
def PositiveJacobian {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω : Set H) (F : H → H) : Prop :=
  ∀ p ∈ Ω, (∀ a b, ⟪fderiv ℝ F p a, b⟫_ℝ = ⟪a, fderiv ℝ F p b⟫_ℝ) ∧
    ∀ a ≠ 0, 0 < ⟪fderiv ℝ F p a, a⟫_ℝ

variable {ι : Type*} [Fintype ι]

/-- Balance of two generator centroids of an actual finite family of inputs. -/
def FamilyBalance (Ω : Set E) (w : ι → ℝ) (F G : E → E) : Prop :=
  ∀ p ∈ Ω, ∃ U ∈ 𝓝 p, ∀ x : ι → E, (∀ i, x i ∈ U) →
    ∀ u ∈ U, ∀ v ∈ U,
    F u = ∑ i, w i • F (x i) → G v = ∑ i, w i • G (x i) →
    u + v = (2 : ℝ) • ∑ i, w i • x i

end Pooling

section Coordinates

/-- The exponential generator with value zero and derivative one at the origin.
The parameter zero gives the arithmetic generator. -/
def sExp (l t : ℝ) : ℝ := if l = 0 then t else (Real.exp (l*t) - 1) / l

variable {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]

/-- Apply a normalized scalar generator on each axis of a single basis. -/
def axisMap (B : Module.Basis ι ℝ H) (l : ι → ℝ) (z : H) : H :=
  ∑ i, sExp (l i) (B.repr z i) • B i

/-- The generator itself in common input coordinates, with its output affine freedom fixed at p. -/
def RepresentsOn (Ω : Set H) (F : H → H) (p : H) (B : Module.Basis ι ℝ H) (l : ι → ℝ) : Prop :=
  ∀ x ∈ Ω, F x = F p + fderiv ℝ F p (axisMap B l (x-p))

end Coordinates

/-- The arithmetic or log-mean-exp prediction of two scalar inputs. -/
def pairPool (l a b : ℝ) :=
  if l = 0 then (a+b)/2 else Real.log ((Real.exp (l*a)+Real.exp (l*b))/2)/l

/-- Logarithm of the arithmetic mean of three exponentials. -/
def logMeanThree (a b c : ℝ) := Real.log ((Real.exp a + Real.exp b + Real.exp c)/3)

/-- The scalar three-input quasi-arithmetic pool with signed parameter. -/
def triplePool (l a b c : ℝ) := if l = 0 then (a+b+c)/3 else logMeanThree (l*a) (l*b) (l*c)/l

section Losses

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The divergence has the candidate prediction in its first argument. -/
def divergence (φ : H → ℝ) (F : H → H) (z x : H) : ℝ :=
  φ z - φ x - ⟪F x,z-x⟫_ℝ

/-- A single fixed positive quadratic form represents the entire divergence. -/
def QuadraticLossOn (Ω : Set H) (φ : H → ℝ) (F : H → H) : Prop :=
  ∃ L : H →L[ℝ] H, (∀ a b, ⟪L a,b⟫_ℝ = ⟪a,L b⟫_ℝ) ∧
    (∀ a ≠ 0, 0 < ⟪L a,a⟫_ℝ) ∧ ∀ z ∈ Ω, ∀ x ∈ Ω,
      divergence φ F z x = (1/2:ℝ) * ⟪L (z-x),z-x⟫_ℝ

end Losses

/-- Okamura’s shear generator for a scalar function. -/
def shear (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1,x.2 + f x.1)


universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H} {F G : H → H} {p : H}

/-- One unequal input weight forces both generators to be affine in every real Hilbert space. -/
theorem complementary_unequal_weight {w : ℝ} (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (hw : 0 < w) (hw' : w < 1) (hne : w ≠ 1/2) (bal : LocalBalance Ω w F G) :
    AffineOn Ω F ∧ AffineOn Ω G := by
  sorry

/-- A family of three equally weighted predictions alone forces affine generators. -/
theorem three_input_centroids (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G) :
    AffineOn Ω F ∧ AffineOn Ω G := by
  sorry

/-- For every fixed list of at least three positive weights, family balance is equivalent to affine generators. -/
theorem weighted_family_centroids {n : ℕ} (hn : 3 ≤ n) (w : Fin n → ℝ)
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F) :
    FamilyBalance Ω w F G ↔ AffineOn Ω F ∧ AffineOn Ω G := by
  sorry

/-- Triple balance determines each output for all finite weighted prediction families. -/
theorem arithmetic_predictions_of_triples (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∑ i, w i = 1) (x : Fin n → H) (hx : ∀ i, x i ∈ Ω)
    {u v : H} (hu : u ∈ Ω) (hv : v ∈ Ω)
    (eF : F u = ∑ i, w i • F (x i)) (eG : G v = ∑ i, w i • G (x i)) :
    u = ∑ i, w i • x i ∧ v = ∑ i, w i • x i := by
  sorry

/-- The logarithmic Jacobian is constant across the domain and its directional operators commute. -/
theorem half_weight_operator (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F)
    (bal : LocalBalance Ω (1/2) F G) :
    let K := fun (x h v : H) ↦ (fderiv ℝ F x).inverse (fderiv ℝ (fderiv ℝ F) x h v)
    (∀ x ∈ Ω, ∀ y ∈ Ω, ∀ h v, K x h v = K y h v) ∧
    (∀ x ∈ Ω, ∀ a b v, K x a (K x b v) = K x b (K x a v)) := by
  sorry

/-- In finite dimension the two generators have one fixed basis on the whole domain. -/
theorem binary_generator_classification [FiniteDimensional ℝ H] (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F) :
    LocalBalance Ω (1/2) F G ↔
    ∃ (B : Module.Basis (Fin (Module.finrank ℝ H)) ℝ H) (l : Fin (Module.finrank ℝ H) → ℝ),
      RepresentsOn Ω F p B l ∧ RepresentsOn Ω G p B (fun i ↦ -l i) := by
  sorry

/-- The actual binary predictions are opposite log-mean-exp rules on the common axes. -/
theorem binary_prediction_formulas [FiniteDimensional ℝ H] (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F)
    (bal : LocalBalance Ω (1/2) F G) :
    ∃ (B : Module.Basis (Fin (Module.finrank ℝ H)) ℝ H) (l : Fin (Module.finrank ℝ H) → ℝ),
    ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ u ∈ Ω, ∀ v ∈ Ω,
    F u = mix (1/2) (F x) (F y) → G v = mix (1/2) (G x) (G y) →
    ∀ i, B.repr (u-p) i = pairPool (l i) (B.repr (x-p) i) (B.repr (y-p) i) ∧
         B.repr (v-p) i = pairPool (-l i) (B.repr (x-p) i) (B.repr (y-p) i) := by
  sorry

/-- Each Bregman divergence is a squared distance in its own fixed positive quadratic form. -/
theorem bregman_losses_of_triple_balance {φ ψ : H → ℝ} (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hn : Ω.Nonempty)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G)
    (pF : PositiveJacobian Ω F) (pG : PositiveJacobian Ω G)
    (hφ : ∀ x ∈ Ω, HasGradientAt φ (F x) x) (hψ : ∀ x ∈ Ω, HasGradientAt ψ (G x) x)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G) :
    QuadraticLossOn Ω φ F ∧ QuadraticLossOn Ω ψ G := by
  sorry

/-- The generator equations have actual nearby solutions in every prescribed neighborhood. -/
theorem local_centroid_existence {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ω : Set E} {F G : E → E} {p : E} (hp : p ∈ Ω) (rF : RegularOn 1 Ω F) (rG : RegularOn 1 Ω G)
    (w : ℝ) {U : Set E} (hU : U ∈ 𝓝 p) :
    ∀ᶠ q : E × E in 𝓝 (p,p), ∃ u ∈ U, ∃ v ∈ U,
      F u = mix w (F q.1) (F q.2) ∧ G v = mix w (G q.1) (G q.2) := by
  sorry

/-- A nonzero scalar exponential axis balances a triple precisely when one input is its mean. -/
theorem individual_triples (l a b c : ℝ) :
    (triplePool l a b c + triplePool (-l) a b c)/2 = (a+b+c)/3 ↔
    l=0 ∨ a=(a+b+c)/3 ∨ b=(a+b+c)/3 ∨ c=(a+b+c)/3 := by
  sorry

/-- The displayed three-input formula solves the scalar generator equation. -/
theorem exponential_triple_generator_equation (l a b c : ℝ) :
    sExp l (triplePool l a b c) = (sExp l a + sExp l b + sExp l c)/3 := by
  sorry

/-- Opposite exponential gradients balance every equally weighted pair. -/
theorem exponential_binary_balance :
    LocalBalance (Set.univ : Set ℝ) (1/2) Real.exp (fun x ↦ -Real.exp (-x)) := by
  sorry

/-- There are two distinct nonarithmetic outputs for a concrete pair of inputs. -/
theorem nonlinear_binary_centroids : ∃ x y u v : ℝ,
    Real.exp u = mix (1/2) (Real.exp x) (Real.exp y) ∧
    -Real.exp (-v) = mix (1/2) (-Real.exp (-x)) (-Real.exp (-y)) ∧
    u+v=x+y ∧ u ≠ (x+y)/2 ∧ v ≠ (x+y)/2 := by
  sorry

/-- Okamura’s vector shears balance at every weight and arity. -/
theorem complementary_vector_shears {ι : Type v} [Fintype ι] (f : ℝ → ℝ) (w : ι → ℝ) :
    FamilyBalance (Set.univ : Set (ℝ × ℝ)) w (shear f) (shear (fun s ↦ -f s)) := by
  sorry

end CentroidRigidity
