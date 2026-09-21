import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace GD.N0049.N0306

theorem d008252
    {ι : Type*} [Fintype ι]
    (a r : ι → ℝ) (w : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : ∀ i, 0 < r i)
    (hw : 0 ≤ w) (hcap : ∀ i, w ≤ a i * r i) :
    w ^ 2 * (∑ i, (r i ^ 2)⁻¹) ≤ ∑ i, a i ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hs : w ^ 2 ≤ (a i * r i) ^ 2 :=
    (sq_le_sq₀ hw (mul_nonneg (ha i) (hr i).le)).mpr (hcap i)
  have hpos : 0 < r i ^ 2 := sq_pos_of_pos (hr i)
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ hpos).mpr
  simpa only [mul_pow] using hs

theorem d008253
    {ι : Type*} [Fintype ι]
    (a r : ι → ℝ) (w : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : ∀ i, 0 < r i)
    (hw : 0 ≤ w) (hcap : ∀ i, w ≤ a i * r i) :
    w * Real.sqrt (∑ i, (r i ^ 2)⁻¹) ≤ Real.sqrt (∑ i, a i ^ 2) := by
  have hsum : 0 ≤ ∑ i, (r i ^ 2)⁻¹ :=
    Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (sq_nonneg _))
  have henergy := _root_.GD.N0049.N0306.d008252 a r w ha hr hw hcap
  have hright : 0 ≤ ∑ i, a i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply (sq_le_sq₀ (mul_nonneg hw (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)).mp
  simpa only [mul_pow, Real.sq_sqrt hsum, Real.sq_sqrt hright] using henergy

theorem d008254
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (∀ i, 0 < (a i)⁻¹) ∧
    (∀ i, (1 : ℝ) = a i * (a i)⁻¹) ∧
    Real.sqrt (∑ i, (((a i)⁻¹) ^ 2)⁻¹) = Real.sqrt (∑ i, a i ^ 2) := by
  refine ⟨fun i => inv_pos.mpr (ha i), fun i => ?_, ?_⟩
  · exact (mul_inv_cancel₀ (ha i).ne').symm
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp

theorem d008255
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (C : ℝ) :
    (∀ (r : ι → ℝ) (w : ℝ), (∀ i, 0 < r i) → 0 ≤ w →
      (∀ i, w ≤ a i * r i) →
      w * Real.sqrt (∑ i, (r i ^ 2)⁻¹) ≤ C) ↔
    Real.sqrt (∑ i, a i ^ 2) ≤ C := by
  constructor
  · intro h
    obtain ⟨hr, heq, hsum⟩ := _root_.GD.N0049.N0306.d008254 a ha
    have hh := h (fun i => (a i)⁻¹) 1 hr (by norm_num) (fun i => (heq i).le)
    simpa only [one_mul, hsum] using hh
  · intro h r w hr hw hcap
    exact (_root_.GD.N0049.N0306.d008253 a r w (fun i => (ha i).le) hr hw hcap).trans h

end GD.N0049.N0306

#print axioms _root_.GD.N0049.N0306.d008252
#print axioms _root_.GD.N0049.N0306.d008253
#print axioms _root_.GD.N0049.N0306.d008254
#print axioms _root_.GD.N0049.N0306.d008255
