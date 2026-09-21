import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0208
namespace N0456

noncomputable section

def d007928 (v w : ℝ) : ℝ :=
  Real.exp ((w - v) / 2) /
    (4 * Real.pi * Real.cosh ((v + w) / 2) * Real.cosh ((v - w) / 2))

def d007929 (v w : ℝ) : ℝ := 1 / (4 * Real.pi * Real.cosh ((v + w) / 2))

theorem d007930 (v w : ℝ) : 0 ≤ _root_.GD.N0208.N0456.d007928 v w := by
  unfold _root_.GD.N0208.N0456.d007928
  exact (div_pos (Real.exp_pos _) (by positivity)).le

theorem d007931 (v w : ℝ) :
    (_root_.GD.N0208.N0456.d007928 v w + _root_.GD.N0208.N0456.d007928 w v) / 2 = _root_.GD.N0208.N0456.d007929 v w := by
  have he : Real.exp ((w - v) / 2) + Real.exp ((v - w) / 2) =
      2 * Real.cosh ((v - w) / 2) := by
    rw [Real.cosh_eq, show -((v - w) / 2) = (w - v) / 2 by ring]
    ring
  unfold _root_.GD.N0208.N0456.d007928 _root_.GD.N0208.N0456.d007929
  rw [show (w + v) / 2 = (v + w) / 2 by ring,
    show (w - v) / 2 = -((v - w) / 2) by ring, Real.cosh_neg]
  rw [← show (w - v) / 2 = -((v - w) / 2) by ring]
  have hc := (Real.cosh_pos ((v - w) / 2)).ne'
  have hm := (Real.cosh_pos ((v + w) / 2)).ne'
  field_simp
  nlinarith

theorem d007932 (v w : ℝ) :
    _root_.GD.N0208.N0456.d007929 v (-w) = 1 / (4 * Real.pi * Real.cosh ((v - w) / 2)) := by
  simp only [_root_.GD.N0208.N0456.d007929, sub_eq_add_neg]

theorem d007933 (v w : ℝ) :
    _root_.GD.N0208.N0456.d007929 v w ≤ Real.exp (-|v + w| / 2) / (2 * Real.pi) := by
  have hcosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      linarith [Real.exp_pos (-x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [Real.exp_pos x]
  have he := hcosh ((v + w) / 2)
  have hab : |(v + w) / 2| = |v + w| / 2 := by rw [abs_div]; norm_num
  rw [hab] at he
  have hexp : Real.exp (-|v + w| / 2) * Real.exp (|v + w| / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  unfold _root_.GD.N0208.N0456.d007929
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * Real.pi * Real.cosh ((v+w)/2))
    (by positivity : 0 < 2 * Real.pi)).mpr
  have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos (-|v+w|/2)).le
  rw [hexp] at hmul
  nlinarith [Real.pi_pos]

theorem d007934 (v a : ℝ) :
    (∫ s : ℝ in Ioi 0, Real.exp (-Real.cosh (v - a / 2) * s)) =
      1 / Real.cosh (v - a / 2) := by
  simpa using integral_exp_mul_Ioi (neg_neg_of_pos (Real.cosh_pos (v - a / 2))) 0

theorem d007935 :
    (∫ a : ℝ, a ^ 2 * Real.exp (-|a| / 2)) = 32 := by
  have heq : (fun a : ℝ ↦ a ^ 2 * Real.exp (-|a| / 2)) =
      (fun a : ℝ ↦ |a| ^ 2 * Real.exp (-|a| / 2)) := by
    funext a
    rw [sq_abs]
  rw [heq]
  change (∫ a : ℝ, (fun b : ℝ ↦ b ^ 2 * Real.exp (-b / 2)) |a|) = 32
  rw [integral_comp_abs (f := fun b : ℝ ↦ b ^ 2 * Real.exp (-b / 2))]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  norm_num [Real.rpow_natCast, show (fun t : ℝ ↦ t ^ 2 * Real.exp (-(1 / 2 * t))) =
      (fun t : ℝ ↦ t ^ 2 * Real.exp (-t / 2)) by funext t; congr 2; ring] at h
  linarith

theorem d007936 :
    (∫⁻ a : ℝ, ENNReal.ofReal (a ^ 2 * Real.exp (-|a| / 2))) = 32 := by
  have hi : Integrable (fun a : ℝ ↦ a ^ 2 * Real.exp (-|a| / 2)) :=
    by
      by_contra hn
      have hz := integral_undef hn
      rw [_root_.GD.N0208.N0456.d007935] at hz
      norm_num at hz
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (by intro a; positivity)),
    _root_.GD.N0208.N0456.d007935]
  norm_num

end
end N0456
end GD.N0208

#print axioms _root_.GD.N0208.N0456.d007931
#print axioms _root_.GD.N0208.N0456.d007932
#print axioms _root_.GD.N0208.N0456.d007933
#print axioms _root_.GD.N0208.N0456.d007934
#print axioms _root_.GD.N0208.N0456.d007935
#print axioms _root_.GD.N0208.N0456.d007936
