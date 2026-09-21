import GD.Module0375
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic


























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

open MeasureTheory Set

namespace GD.N0106.N0428.N0765.N1628
open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1618
noncomputable section


def d005801 (Qv τ : ℝ) : ℝ := τ ^ ((11 : ℝ) / 2 - 1) * Real.exp (-(Qv / 2 * τ))


def d005802 (S₁ S₂ a b μ τ₁ τ₂ : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1628.d005801 (_root_.GD.N0106.N0428.N0765.N1618.d005722 S₁ a μ) τ₁ * _root_.GD.N0106.N0428.N0765.N1628.d005801 (_root_.GD.N0106.N0428.N0765.N1618.d005722 S₂ b μ) τ₂


def d005803 : ℝ := (2 ^ ((11 : ℝ) / 2) * Real.Gamma ((11 : ℝ) / 2)) ^ 2



def d005804 (S₁ S₂ a b : ℝ) : ℝ :=
  (∫ μ, ∫ τ₁ in Ioi (0 : ℝ), ∫ τ₂ in Ioi (0 : ℝ), μ * _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b μ τ₁ τ₂) /
    ∫ μ, ∫ τ₁ in Ioi (0 : ℝ), ∫ τ₂ in Ioi (0 : ℝ), _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b μ τ₁ τ₂

theorem d005805 {Qv : ℝ} (hQ : 0 < Qv) :
    ∫ τ in Ioi (0 : ℝ), _root_.GD.N0106.N0428.N0765.N1628.d005801 Qv τ
      = (2 ^ ((11 : ℝ) / 2) * Real.Gamma ((11 : ℝ) / 2)) * Qv ^ (-((11 : ℝ) / 2)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1628.d005801
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 11 / 2)
    (by positivity : 0 < Qv / 2)]
  rw [one_div, inv_div, Real.div_rpow (by norm_num) hQ.le, Real.rpow_neg hQ.le]
  ring

theorem d005806 : 0 < _root_.GD.N0106.N0428.N0765.N1628.d005803 := by
  unfold _root_.GD.N0106.N0428.N0765.N1628.d005803
  have h1 : 0 < (2 : ℝ) ^ ((11 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : 0 < Real.Gamma ((11 : ℝ) / 2) := Real.Gamma_pos_of_pos (by norm_num)
  positivity



theorem d005807 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b μ : ℝ) :
    ∫ τ₁ in Ioi (0 : ℝ), ∫ τ₂ in Ioi (0 : ℝ), _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b μ τ₁ τ₂
      = _root_.GD.N0106.N0428.N0765.N1628.d005803 * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b μ := by
  unfold _root_.GD.N0106.N0428.N0765.N1628.d005802
  simp_rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_mul_const, _root_.GD.N0106.N0428.N0765.N1628.d005805 (_root_.GD.N0106.N0428.N0765.N1618.d005725 hS₁ a μ),
    _root_.GD.N0106.N0428.N0765.N1628.d005805 (_root_.GD.N0106.N0428.N0765.N1618.d005725 hS₂ b μ)]
  unfold _root_.GD.N0106.N0428.N0765.N1628.d005803 _root_.GD.N0106.N0428.N0765.N1618.d005723
  ring

theorem d005808 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (a b : ℝ) : _root_.GD.N0106.N0428.N0765.N1628.d005804 S₁ S₂ a b = _root_.GD.N0106.N0428.N0765.N1618.d005724 S₁ S₂ a b := by
  unfold _root_.GD.N0106.N0428.N0765.N1628.d005804 _root_.GD.N0106.N0428.N0765.N1618.d005724
  have hnum : ∀ μ : ℝ,
      (∫ τ₁ in Ioi (0 : ℝ), ∫ τ₂ in Ioi (0 : ℝ), μ * _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b μ τ₁ τ₂)
        = _root_.GD.N0106.N0428.N0765.N1628.d005803 * (μ * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b μ) := by
    intro μ
    simp_rw [MeasureTheory.integral_const_mul]
    rw [_root_.GD.N0106.N0428.N0765.N1628.d005807 hS₁ hS₂ a b μ]
    ring
  have hden : ∀ μ : ℝ,
      (∫ τ₁ in Ioi (0 : ℝ), ∫ τ₂ in Ioi (0 : ℝ), _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b μ τ₁ τ₂)
        = _root_.GD.N0106.N0428.N0765.N1628.d005803 * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b μ :=
    _root_.GD.N0106.N0428.N0765.N1628.d005807 hS₁ hS₂ a b
  simp_rw [hnum, hden]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    mul_div_mul_left _ _ _root_.GD.N0106.N0428.N0765.N1628.d005806.ne']



theorem d005809 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1628.d005804 S₁ S₂ a b = _root_.GD.N0106.N0428.N0765.N1534.d005300 a (b - a) S₁ S₂ := by
  rw [_root_.GD.N0106.N0428.N0765.N1628.d005808 hS₁ hS₂ a b]
  exact _root_.GD.N0106.N0428.N0765.N1618.d005769 hS₁ hS₂ a b

end
end GD.N0106.N0428.N0765.N1628

#print axioms _root_.GD.N0106.N0428.N0765.N1628.d005805
#print axioms _root_.GD.N0106.N0428.N0765.N1628.d005806
#print axioms _root_.GD.N0106.N0428.N0765.N1628.d005807
#print axioms _root_.GD.N0106.N0428.N0765.N1628.d005808
#print axioms _root_.GD.N0106.N0428.N0765.N1628.d005809
