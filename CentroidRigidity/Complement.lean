module

public import CentroidRigidity.Operator
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The converse and actual complementary centroids -/

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace CentroidRigidity

theorem complementary_scalars {l a b u v : ℝ}
    (hu : sExp l u = (sExp l a + sExp l b)/2)
    (hv : sExp (-l) v = (sExp (-l) a + sExp (-l) b)/2) : u + v = a + b := by
  by_cases hl : l = 0
  · subst l
    simp [sExp] at hu hv
    linarith
  · simp only [sExp,if_neg hl,if_neg (neg_ne_zero.mpr hl)] at hu hv
    field_simp [hl] at hu hv
    have eu : 2 * Real.exp (l*u) = Real.exp (l*a) + Real.exp (l*b) := by linarith [hu]
    have ev : 2 * Real.exp (-l*v) = Real.exp (-l*a) + Real.exp (-l*b) := by simp only [neg_mul]; linarith [hv]
    have factor (s t : ℝ) :
        Real.exp (l*(s+t)) * Real.exp (-l*s) = Real.exp (l*t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have euv : Real.exp (l*u) = Real.exp (l*(a+b)) * Real.exp (-l*v) := by
      have ha := factor a b
      have hb := factor b a
      rw [add_comm b a] at hb
      nlinarith only [eu,ev,ha,hb,congrArg (fun z : ℝ ↦ Real.exp (l*(a+b))*z) ev]
    rw [← Real.exp_add,Real.exp_injective.eq_iff] at euv
    apply (mul_left_cancel₀ hl)
    linarith [euv]

variable {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]
variable {Ω : Set H} {F G : H → H} {p : H}

theorem coord_axisMap (B : Module.Basis ι ℝ H) (l : ι → ℝ) (z : H) (i : ι) :
    B.repr (axisMap B l z) i = sExp (l i) (B.repr z i) := by
  classical
  change (B.coord i) (axisMap B l z) = _
  simp [axisMap, Module.Basis.coord_apply,Finsupp.single_apply, mul_ite]

variable [CompleteSpace H]

theorem centroid_coordinate (B : Module.Basis ι ℝ H) (l : ι → ℝ)
    (hf : RepresentsOn Ω F p B l) (hp : (jac F p).IsInvertible)
    {x y u : H} (hx : x ∈ Ω) (hy : y ∈ Ω) (hu : u ∈ Ω)
    (he : F u = mix (1/2) (F x) (F y)) (i : ι) :
    sExp (l i) (B.repr (u-p) i) = (sExp (l i) (B.repr (x-p) i) +
      sExp (l i) (B.repr (y-p) i))/2 := by
  rw [hf u hu,hf x hx,hf y hy] at he
  have hJ : jac F p (axisMap B l (u-p)) =
      jac F p ((1/2:ℝ) • axisMap B l (x-p) + (1/2:ℝ) • axisMap B l (y-p)) := by
    rw [map_add,map_smul,map_smul]
    change F p + jac F p _ = mix _ (F p + jac F p _) (F p + jac F p _) at he
    apply add_left_cancel (a := F p)
    rw [he]
    unfold mix
    module
  have eqn := congrArg (fun v : H ↦ (jac F p).inverse v) hJ
  simp only [inv_apply_apply hp] at eqn
  have hcoord := congrArg (fun v : H ↦ (B.coord i) v) eqn
  simpa [Module.Basis.coord_apply,coord_axisMap, smul_eq_mul,add_div,div_eq_mul_inv,mul_comm,mul_add]
    using hcoord

/-- The common-basis representation gives local balance of every pair
of actual centroids, including mixed coordinates and zero exponential parameters. -/
theorem balance_of_representation (ho : IsOpen Ω) (B : Module.Basis ι ℝ H) (l : ι → ℝ)
    (hF : RepresentsOn Ω F p B l) (hG : RepresentsOn Ω G p B (fun i ↦ -l i))
    (hiF : (jac F p).IsInvertible) (hiG : (jac G p).IsInvertible) :
    LocalBalance Ω (1/2) F G := by
  intro q hq
  refine ⟨Ω,ho.mem_nhds hq,?_⟩
  intro x hx y hy u hu v hv eF eG
  have eqn (i : ι) := complementary_scalars (centroid_coordinate B l hF hiF hx hy hu eF i)
    (centroid_coordinate B (fun i ↦ -l i) hG hiG hx hy hv eG i)
  have h : u+v=x+y := by
    apply B.repr.injective
    ext i
    have e := eqn i
    simp only [map_sub, map_add, Finsupp.sub_apply,Finsupp.add_apply] at e ⊢
    linarith
  rw [h]
  unfold mix
  module

end CentroidRigidity
