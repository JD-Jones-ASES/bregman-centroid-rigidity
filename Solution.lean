module

public import CentroidRigidity

/-! # Proofs of the complementary centroid theorems -/

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology InnerProductSpace ContDiff
namespace CentroidRigidity

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H} {F G : H → H} {p : H}

/-- One unequal input weight forces both generators to be affine in every real Hilbert space. -/
theorem complementary_unequal_weight {w : ℝ} (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (hw : 0 < w) (hw' : w < 1) (hne : w ≠ 1/2) (bal : LocalBalance Ω w F G) :
    AffineOn Ω F ∧ AffineOn Ω G := by
  exact unequal_weight_rigidity ho hc rF rG hF hw hw' hne bal

/-- A family of three equally weighted predictions alone forces affine generators. -/
theorem three_input_centroids (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G) :
    AffineOn Ω F ∧ AffineOn Ω G := by
  exact ternary_rigidity ho hc rF rG hF bal

/-- For every fixed list of at least three positive weights, family balance is equivalent to affine generators. -/
theorem weighted_family_centroids {n : ℕ} (hn : 3 ≤ n) (w : Fin n → ℝ)
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F) :
    FamilyBalance Ω w F G ↔ AffineOn Ω F ∧ AffineOn Ω G := by
  exact ⟨family_rigidity hn w hw hpos ho hc rF rG hF,
    fun ⟨aF,aG⟩ ↦ all_weights_of_affine ho rF rG aF aG w hw⟩

/-- Triple balance determines each output for all finite weighted prediction families. -/
theorem arithmetic_predictions_of_triples (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (hF : PositiveJacobian Ω F)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G)
    {n : ℕ} (w : Fin n → ℝ) (hw : ∑ i, w i = 1) (x : Fin n → H) (hx : ∀ i, x i ∈ Ω)
    {u v : H} (hu : u ∈ Ω) (hv : v ∈ Ω)
    (eF : F u = ∑ i, w i • F (x i)) (eG : G v = ∑ i, w i • G (x i)) :
    u = ∑ i, w i • x i ∧ v = ∑ i, w i • x i := by
  obtain ⟨aF,aG⟩ := ternary_rigidity ho hc rF rG hF bal
  exact ⟨affine_weighted_prediction hw ho rF aF x hx hu eF,
    affine_weighted_prediction hw ho rG aG x hx hv eG⟩

/-- The logarithmic Jacobian is constant across the domain and its directional operators commute. -/
theorem half_weight_operator (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F)
    (bal : LocalBalance Ω (1/2) F G) :
    let K := fun (x h v : H) ↦ (fderiv ℝ F x).inverse (fderiv ℝ (fderiv ℝ F) x h v)
    (∀ x ∈ Ω, ∀ y ∈ Ω, ∀ h v, K x h v = K y h v) ∧
    (∀ x ∈ Ω, ∀ a b v, K x a (K x b v) = K x b (K x a v)) := by
  exact ⟨fun x hx y hy h v ↦ congrArg (fun T : Endo H ↦ T v)
    (constant_logJac ho hc rF rG pos bal hx hy h),
    fun x hx a b v ↦ congrArg (fun T : Endo H ↦ T v)
      (mixed_commute ho hx rF rG bal (by norm_num) (by norm_num) a b).1.eq⟩

/-- In finite dimension the two generators have one fixed basis on the whole domain. -/
theorem binary_generator_classification [FiniteDimensional ℝ H] (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F) :
    LocalBalance Ω (1/2) F G ↔
    ∃ (B : Module.Basis (Fin (Module.finrank ℝ H)) ℝ H) (l : Fin (Module.finrank ℝ H) → ℝ),
      RepresentsOn Ω F p B l ∧ RepresentsOn Ω G p B (fun i ↦ -l i) := by
  exact equal_weight_classification ho hc hp rF rG pos

/-- The actual binary predictions are opposite log-mean-exp rules on the common axes. -/
theorem binary_prediction_formulas [FiniteDimensional ℝ H] (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F)
    (bal : LocalBalance Ω (1/2) F G) :
    ∃ (B : Module.Basis (Fin (Module.finrank ℝ H)) ℝ H) (l : Fin (Module.finrank ℝ H) → ℝ),
    ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ u ∈ Ω, ∀ v ∈ Ω,
    F u = mix (1/2) (F x) (F y) → G v = mix (1/2) (G x) (G y) →
    ∀ i, B.repr (u-p) i = pairPool (l i) (B.repr (x-p) i) (B.repr (y-p) i) ∧
         B.repr (v-p) i = pairPool (-l i) (B.repr (x-p) i) (B.repr (y-p) i) := by
  exact fixed_basis_predictions ho hc hp rF rG pos bal

/-- Each Bregman divergence is a squared distance in its own fixed positive quadratic form. -/
theorem bregman_losses_of_triple_balance {φ ψ : H → ℝ} (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hn : Ω.Nonempty)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G)
    (pF : PositiveJacobian Ω F) (pG : PositiveJacobian Ω G)
    (hφ : ∀ x ∈ Ω, HasGradientAt φ (F x) x) (hψ : ∀ x ∈ Ω, HasGradientAt ψ (G x) x)
    (bal : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G) :
    QuadraticLossOn Ω φ F ∧ QuadraticLossOn Ω ψ G := by
  exact ternary_quadratic_losses ho hc hn rF rG pF pG hφ hψ bal

/-- The generator equations have actual nearby solutions in every prescribed neighborhood. -/
theorem local_centroid_existence {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ω : Set E} {F G : E → E} {p : E} (hp : p ∈ Ω) (rF : RegularOn 1 Ω F) (rG : RegularOn 1 Ω G)
    (w : ℝ) {U : Set E} (hU : U ∈ 𝓝 p) :
    ∀ᶠ q : E × E in 𝓝 (p,p), ∃ u ∈ U, ∃ v ∈ U,
      F u = mix w (F q.1) (F q.2) ∧ G v = mix w (G q.1) (G q.2) := by
  exact local_pools_exist hp rF rG w hU

/-- A nonzero scalar exponential axis balances a triple precisely when one input is its mean. -/
theorem individual_triples (l a b c : ℝ) :
    (triplePool l a b c + triplePool (-l) a b c)/2 = (a+b+c)/3 ↔
    l=0 ∨ a=(a+b+c)/3 ∨ b=(a+b+c)/3 ∨ c=(a+b+c)/3 := by
  exact triple_balance_criterion l a b c

/-- The displayed three-input formula solves the scalar generator equation. -/
theorem exponential_triple_generator_equation (l a b c : ℝ) :
    sExp l (triplePool l a b c) = (sExp l a + sExp l b + sExp l c)/3 := by
  exact triplePool_equation l a b c

/-- Opposite exponential gradients balance every equally weighted pair. -/
theorem exponential_binary_balance :
    LocalBalance (Set.univ : Set ℝ) (1/2) Real.exp (fun x ↦ -Real.exp (-x)) := by
  exact exponential_pair_balances

/-- There are two distinct nonarithmetic outputs for a concrete pair of inputs. -/
theorem nonlinear_binary_centroids : ∃ x y u v : ℝ,
    Real.exp u = mix (1/2) (Real.exp x) (Real.exp y) ∧
    -Real.exp (-v) = mix (1/2) (-Real.exp (-x)) (-Real.exp (-y)) ∧
    u+v=x+y ∧ u ≠ (x+y)/2 ∧ v ≠ (x+y)/2 := by
  exact nonlinear_pair_witness

/-- Okamura’s vector shears balance at every weight and arity. -/
theorem complementary_vector_shears {ι : Type v} [Fintype ι] (f : ℝ → ℝ) (w : ι → ℝ) :
    FamilyBalance (Set.univ : Set (ℝ × ℝ)) w (shear f) (shear (fun s ↦ -f s)) := by
  exact shear_family_balance f w

end CentroidRigidity
