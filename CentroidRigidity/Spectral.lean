module

public import CentroidRigidity.FlatField
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-! # Common axes of the two generators -/

@[expose] public section
noncomputable section
open Set
open scoped InnerProductSpace BigOperators
namespace CentroidRigidity

theorem basis_of_joint_eigenvectors {M ι : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (g : InnerProductSpace.Core ℝ M) (T : ι → M →ₗ[ℝ] M)
    (hs : ∀ i x y, g.inner (T i x) y = g.inner x (T i y))
    (hc : ∀ i j, Commute (T i) (T j)) :
    ∃ B : Module.Basis (Fin (Module.finrank ℝ M)) ℝ M,
      ∀ j, ∃ χ : ι → ℝ, ∀ i, T i (B j) = χ i • B j := by
  classical
  letI : NormedAddCommGroup M := g.toNormedAddCommGroup
  letI : InnerProductSpace ℝ M := InnerProductSpace.ofCore g.toCore
  have hsym (i : ι) : (T i).IsSymmetric := hs i
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym (fun i j _ ↦ hc i j)
  let S : Set M := {x | ∃ χ : ι → ℝ, ∀ i, T i x = χ i • x}
  have hspan : Submodule.span ℝ S = ⊤ := by
    apply top_unique
    rw [← htop]
    refine iSup_le fun χ x hx ↦ Submodule.subset_span ⟨χ, fun i ↦ ?_⟩
    exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx i)
  obtain ⟨s, hsS, hsp, hli⟩ := exists_linearIndependent ℝ S
  let B := Module.Basis.mk hli (by rw [Subtype.range_coe_subtype, Set.setOf_mem_eq,hsp,hspan])
  haveI : Finite s := Module.Finite.finite_basis B
  letI := Fintype.ofFinite s
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
  refine ⟨B.reindex e,fun j ↦ ?_⟩
  rw [B.reindex_apply]
  simpa only [B, Module.Basis.mk_apply,S,Set.mem_setOf_eq] using hsS (e.symm j).property

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Ω : Set H} {F G : H → H} {p : H}

@[reducible] def jacMetric (pos : PositiveJacobian Ω F) (hp : p ∈ Ω) : InnerProductSpace.Core ℝ H where
  inner u v := ⟪jac F p u,v⟫_ℝ
  conj_inner_symm u v := by
    change ⟪jac F p v,u⟫_ℝ = ⟪jac F p u,v⟫_ℝ
    rw [real_inner_comm,← (pos p hp).1 u v]
  re_inner_nonneg u := by
    by_cases hu : u = 0
    · simp [hu]
    · exact (pos p hp).2 u hu |>.le
  add_left u v z := by simp [inner_add_left]
  smul_left u v r := by simp [real_inner_smul_left]
  definite u hu := by
    by_contra h
    exact ((pos p hp).2 u h).ne' hu

variable [CompleteSpace H] [FiniteDimensional ℝ H]

theorem common_axes (ho : IsOpen Ω) (hc : IsPreconnected Ω) (hp : p ∈ Ω)
    (rF : RegularOn 3 Ω F) (rG : RegularOn 3 Ω G) (pos : PositiveJacobian Ω F)
    (bal : LocalBalance Ω (1/2) F G) :
    ∃ (B : Module.Basis (Fin (Module.finrank ℝ H)) ℝ H) (l : Fin (Module.finrank ℝ H) → ℝ),
    ∀ x ∈ Ω, ∀ h i, logJac F x h (B i) = (l i * B.repr h i) • B i := by
  classical
  let T (a : H) := (logJac F p a).toLinearMap
  have hcom (a b : H) : Commute (T a) (T b) := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun z : Endo H ↦ z x)
      (mixed_commute ho hp rF rG bal (by norm_num) (by norm_num) a b).1.eq
  obtain ⟨B, hB⟩ := basis_of_joint_eigenvectors (jacMetric pos hp) T
    (fun i ↦ logJac_sym ho hp (rF.lower (by decide)) pos i) hcom
  choose χ hχ using hB
  have heig (i) (a : H) : logJac F p a (B i) = χ i a • B i := hχ i a
  have hcross (i j) (hne : i ≠ j) : logJac F p (B i) (B j) = 0 := by
    have he := logJac_comm_arguments ((rF.lower (by decide) p hp).1) (B i) (B j)
    rw [heig,heig] at he
    have e := congrArg (fun x : H ↦ B.repr x j) he
    have hz : χ j (B i) = 0 := by simpa [B.repr_self_apply,hne] using e
    rw [heig,hz,zero_smul]
  refine ⟨B, fun i ↦ χ i (B i), fun x hx h i ↦ ?_⟩
  rw [constant_logJac ho hc rF rG pos bal hx hp,
    logJac_comm_arguments ((rF.lower (by decide) p hp).1) h (B i)]
  calc
    _ = logJac F p (B i) (∑ j, B.repr h j • B j) := by rw [B.sum_repr h]
    _ = ∑ j, B.repr h j • logJac F p (B i) (B j) := by rw [map_sum]; simp only [map_smul]
    _ = B.repr h i • logJac F p (B i) (B i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hcross i j hji.symm,smul_zero]
      · simp
    _ = _ := by rw [heig,smul_smul,mul_comm]

end CentroidRigidity
