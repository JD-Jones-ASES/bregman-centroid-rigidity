module

public import CentroidRigidity.Unequal

/-! # Weighted prediction families and repeated inputs -/

@[expose] public section
noncomputable section

open Filter Set
open scoped Topology BigOperators
namespace CentroidRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem sum_repeated [DecidableEq ι] (w : ι → ℝ) (hw : ∑ i, w i = 1)
    (k : ι) (x y : E) : (∑ i, w i • (if i = k then y else x)) = mix (w k) x y := by
  calc
    _ = ∑ i, (w i • x + if i = k then w i • (y-x) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases e : i = k <;> simp [e, smul_sub]
    _ = mix (w k) x y := by
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, hw]
      simp [mix, sub_smul, smul_sub]
      abel

theorem FamilyBalance.repeated {Ω : Set E} {F G : E → E} {w : ι → ℝ}
    (h : FamilyBalance Ω w F G) (hw : ∑ i, w i = 1) (k : ι) : LocalBalance Ω (w k) F G := by
  classical
  intro p hp
  obtain ⟨U, hU, h⟩ := h p hp
  refine ⟨U, hU, ?_⟩
  intro x hx y hy u hu v hv hF hG
  let z (i : ι) := if i = k then y else x
  have hz (i : ι) : z i ∈ U := by by_cases e : i = k <;> simp [z, e, hx, hy]
  have hzF (H : E → E) : (∑ i, w i • H (z i)) = mix (w k) (H x) (H y) := by
    simpa only [z, apply_ite H] using sum_repeated w hw k (H x) (H y)
  simpa only [z, sum_repeated w hw] using h z hz u hu v hv (hF.trans (hzF F).symm)
    (hG.trans (hzF G).symm)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Set H} {F G : H → H}

/-- Three equal input weights by themselves force both generators to be affine. -/
theorem ternary_rigidity (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (pos : PositiveJacobian Ω F)
    (h : FamilyBalance Ω (fun _ : Fin 3 ↦ (1/3:ℝ)) F G) : AffineOn Ω F ∧ AffineOn Ω G := by
  have hw : (∑ _i : Fin 3, (1/3:ℝ)) = 1 := by norm_num
  exact unequal_weight_rigidity ho hc rF rG pos (by norm_num) (by norm_num) (by norm_num)
    (h.repeated hw 0)

/-- Every fixed list of at least three positive weights has an unequal binary reduction. -/
theorem family_rigidity {n : ℕ} (hn : 3 ≤ n) (w : Fin n → ℝ)
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (rF : RegularOn 2 Ω F) (rG : RegularOn 2 Ω G) (pos : PositiveJacobian Ω F)
    (h : FamilyBalance Ω w F G) : AffineOn Ω F ∧ AffineOn Ω G := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 1/2 := by
    by_contra! eq
    simp [eq] at hw
    have : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨j,hj⟩ : ∃ j : Fin n, j ≠ k := by
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    by_cases ha : a = k
    · exact ⟨b, ha ▸ (by decide : (1:ℕ) ≠ 0) ∘ congrArg Fin.val⟩
    · exact ⟨a,ha⟩
  have hj' : j ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
  have ht : 0 < ∑ i ∈ Finset.univ.erase k, w i :=
    Finset.sum_pos' (fun i _ ↦ (hpos i).le) ⟨j, hj', hpos j⟩
  have hs := Finset.sum_erase_add _ w (Finset.mem_univ k)
  exact unequal_weight_rigidity ho hc rF rG pos (hpos k) (by linarith) hk (h.repeated hw k)

end CentroidRigidity
