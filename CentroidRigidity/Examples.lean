module

public import CentroidRigidity.Complement
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Nonlinear binary witnesses and an exact test for triples -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace CentroidRigidity

theorem triplePool_equation (l a b c : ℝ) :
    sExp l (triplePool l a b c) = (sExp l a + sExp l b + sExp l c)/3 := by
  by_cases hl : l = 0
  · simp [sExp,triplePool,hl]
  · simp [triplePool,sExp,hl,logMeanThree, mul_div_cancel₀, Real.exp_log (by positivity :
        0 < (Real.exp (l*a) + Real.exp (l*b) + Real.exp (l*c))/3)]
    field_simp
    ring

theorem logMeanThree_shift (a b c t : ℝ) :
    logMeanThree (a+t) (b+t) (c+t) = logMeanThree a b c + t := by
  unfold logMeanThree
  simp only [Real.exp_add]
  rw [show (Real.exp a * Real.exp t + Real.exp b * Real.exp t + Real.exp c * Real.exp t)/3 =
    ((Real.exp a + Real.exp b + Real.exp c)/3) * Real.exp t by ring]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_exp]

theorem centered_exponential_triples {a b c : ℝ} (hc : a+b+c=0) :
    logMeanThree a b c = logMeanThree (-a) (-b) (-c) ↔ a=0 ∨ b=0 ∨ c=0 := by
  have ha : Real.exp (-a) = Real.exp b * Real.exp c := by
    rw [← Real.exp_add]; congr 1; linarith
  have hb : Real.exp (-b) = Real.exp a * Real.exp c := by
    rw [← Real.exp_add]; congr 1; linarith
  have hec : Real.exp (-c) = Real.exp a * Real.exp b := by
    rw [← Real.exp_add]; congr 1; linarith
  have hprod : Real.exp a * Real.exp b * Real.exp c = 1 := by
    rw [← Real.exp_add,← Real.exp_add,hc,Real.exp_zero]
  have hfac : (Real.exp a + Real.exp b + Real.exp c) -
      (Real.exp (-a)+Real.exp (-b)+Real.exp (-c)) =
      (Real.exp a-1)*(Real.exp b-1)*(Real.exp c-1) := by
    rw [ha,hb,hec]
    nlinarith only [hprod]
  have hoff : logMeanThree a b c = logMeanThree (-a) (-b) (-c) ↔
      (Real.exp a + Real.exp b + Real.exp c) - (Real.exp (-a)+Real.exp (-b)+Real.exp (-c)) = 0 := by
    unfold logMeanThree
    constructor
    · intro h
      have ee := Real.log_injOn_pos (x₁ := (Real.exp a + Real.exp b + Real.exp c)/3)
        (x₂ := (Real.exp (-a) + Real.exp (-b) + Real.exp (-c))/3)
        (by change 0 < _; positivity) (by change 0 < _; positivity) h
      linarith
    · intro h
      congr 1
      linarith
  rw [hoff,hfac]
  simp [mul_eq_zero,sub_eq_zero,or_assoc]

/-- On a nonlinear axis the three inputs must form an arithmetic progression,
up to reordering. The parameter zero works for every triple. -/
theorem triple_balance_criterion (l a b c : ℝ) :
    (triplePool l a b c + triplePool (-l) a b c)/2 = (a+b+c)/3 ↔
    l=0 ∨ a=(a+b+c)/3 ∨ b=(a+b+c)/3 ∨ c=(a+b+c)/3 := by
  by_cases hl : l = 0
  · simp [hl,triplePool]
  · let m := (a+b+c)/3
    let A := l*(a-m)
    let B := l*(b-m)
    let C := l*(c-m)
    have hzero : A+B+C=0 := by dsimp [A,B,C,m]; ring
    have hp : logMeanThree (l*a) (l*b) (l*c) = logMeanThree A B C + l*m := by
      convert logMeanThree_shift A B C (l*m) using 2 <;> dsimp [A,B,C] <;> ring
    have hn : logMeanThree (-l*a) (-l*b) (-l*c) = logMeanThree (-A) (-B) (-C) + (-l*m) := by
      convert logMeanThree_shift (-A) (-B) (-C) (-l*m) using 2 <;> dsimp [A,B,C] <;> ring
    change _ ↔ l=0 ∨ a=m ∨ b=m ∨ c=m
    rw [show (a+b+c)/3 = m from rfl]
    simp only [triplePool,if_neg hl,if_neg (neg_ne_zero.mpr hl),hp,hn,hl,ite_false,false_or]
    have eqn : ((logMeanThree A B C + l*m)/l + (logMeanThree (-A) (-B) (-C) + -l*m)/(-l))/2 = m
        ↔ logMeanThree A B C = logMeanThree (-A) (-B) (-C) := by
      constructor <;> intro h <;> field_simp [hl] at h ⊢ <;> linarith
    rw [eqn,centered_exponential_triples hzero]
    simp [A,B,C,hl,sub_eq_zero]

/-- The positive-gradient pair from the potentials exp(x) and exp(-x)
balances at half weights. -/
theorem exponential_pair_balances :
    LocalBalance (Set.univ : Set ℝ) (1/2) Real.exp (fun x ↦ -Real.exp (-x)) := by
  intro p _
  refine ⟨Set.univ,Filter.univ_mem,?_⟩
  intro x _ y _ u _ v _ hF hG
  have hu : sExp 1 u = (sExp 1 x + sExp 1 y)/2 := by
    simp [mix,smul_eq_mul] at hF
    simp [sExp]; linarith
  have hv : sExp (-(1:ℝ)) v = (sExp (-(1:ℝ)) x + sExp (-(1:ℝ)) y)/2 := by
    simp [mix,smul_eq_mul] at hG
    simp [sExp]; linarith
  have h := complementary_scalars hu hv
  simp [mix,smul_eq_mul]
  linarith

/-- A pair for which the two actual complementary centroids are both nonlinear. -/
theorem nonlinear_pair_witness : ∃ x y u v : ℝ,
    Real.exp u = mix (1/2) (Real.exp x) (Real.exp y) ∧
    -Real.exp (-v) = mix (1/2) (-Real.exp (-x)) (-Real.exp (-y)) ∧
    u+v=x+y ∧ u ≠ (x+y)/2 ∧ v ≠ (x+y)/2 := by
  refine ⟨-Real.log 2,Real.log 2,Real.log (5/4),-Real.log (5/4),?_⟩
  have h : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  norm_num [mix,smul_eq_mul,Real.exp_neg,Real.exp_log,show (0:ℝ) < 5/4 by norm_num,
    show (0:ℝ) < 2 by norm_num] <;> constructor <;> linarith

end CentroidRigidity
