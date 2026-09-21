import GD.Module0371
import GD.Module1292











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1561
noncomputable section

open MeasureTheory _root_.GD.N0106.N0428.N0765.N1616
open scoped FourierTransform

theorem d021034 {eta u v w d h : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h) (offset : ℝ) :
    |h * (∑' n : ℤ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (offset + h*n)) -
        ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c| ≤
      (2 * (Real.cos d) ^ (-21 / 2 : ℝ) / (Real.exp (2 * Real.pi * d / h) - 1)) *
        ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  have hline := _root_.GD.N0106.N0428.N0765.N1558.d021015 heta hu hv hw hd.le hdpi
    (t := 0) (by simpa only [abs_zero] using hd.le)
  have heq : (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w
      ((c : ℂ) + (0 : ℂ) * Complex.I)) =
      (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c : ℂ)) := by
    funext c
    simpa only [zero_mul, add_zero] using _root_.GD.N0106.N0428.N0765.N1563.d020991 heta hu hv hw c
  simp only [Complex.ofReal_zero] at hline
  rw [heq] at hline
  have hc : Continuous (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w) := by
    have hre : (Complex.re ∘ (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c : ℂ))) =
        _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w := by
      funext c
      simp only [Function.comp_apply, Complex.ofReal_re]
    have hcont := Complex.continuous_re.comp hline
    rw [hre] at hcont
    exact hcont
  have hnn (c : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
    have hq := _root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c
    unfold _root_.GD.N0106.N0428.N0765.N1616.d020957
    positivity
  have hl : ∀ c : ℝ, c ≤ 0 → |_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c| ≤
      ((2 : ℝ)^10 * v^(-21/2 : ℝ)) * Real.exp ((11/2 : ℝ)*c) := by
    intro c hcle
    simpa only [abs_of_nonneg (hnn c),
      show (11/2 : ℝ)*c = 11*c/2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1564.d021003 heta hu hv hw hcle
  have hr : ∀ c : ℝ, 0 ≤ c → |_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c| ≤
      ((2 : ℝ)^10 * (eta*w)^(-21/2 : ℝ)) * Real.exp (-(11/2 : ℝ)*c) := by
    intro c hcle
    simpa only [abs_of_nonneg (hnn c),
      show -(11/2 : ℝ)*c = -11*c/2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1564.d021005 heta hu hv hw hcle
  have hF : ∀ xi : ℝ, ‖𝓕 (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c : ℂ)) xi‖ ≤
      ((Real.cos d)^(-21/2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c) *
        Real.exp (-(2*Real.pi*d)*|xi|) := by
    intro xi
    calc
      _ ≤ Real.exp (-2*Real.pi*d*|xi|) * (Real.cos d)^(-21/2 : ℝ) *
          ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c :=
        _root_.GD.N0106.N0428.N0765.N1559.d021032 heta hu hv hw hd.le hdpi xi
      _ = _ := by
        rw [show -(2*Real.pi*d)*|xi| = -2*Real.pi*d*|xi| by ring]
        ring
  have he := _root_.GD.N0106.N0428.N0765.N1613.d005636 hc
    (by norm_num : 0 < (11/2 : ℝ)) (by norm_num : 0 < (11/2 : ℝ))
    (by positivity : 0 < 2*Real.pi*d) hh hl hr hF offset
  calc
    _ ≤ 2 * ((Real.cos d)^(-21/2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c) /
        (Real.exp ((2*Real.pi*d)/h)-1) := he
    _ = _ := by ring

theorem d021035 {eta u v w d h : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h) (offset : ℝ) :
    |h * (∑' n : ℤ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (offset + h*n)) -
        ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c| ≤
      (2 * (Real.cos d) ^ (-21 / 2 : ℝ) / (Real.exp (2 * Real.pi * d / h) - 1)) *
        ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  have hline := _root_.GD.N0106.N0428.N0765.N1558.d021016 heta hu hv hw hd.le hdpi
    (t := 0) (by simpa only [abs_zero] using hd.le)
  have heq : (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w
      ((c : ℂ) + (0 : ℂ) * Complex.I)) =
      (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c : ℂ)) := by
    funext c
    simpa only [zero_mul, add_zero] using _root_.GD.N0106.N0428.N0765.N1563.d020992 heta hu hv hw c
  simp only [Complex.ofReal_zero] at hline
  rw [heq] at hline
  have hc : Continuous (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w) := by
    have hre : (Complex.re ∘ (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c : ℂ))) =
        _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w := by
      funext c
      simp only [Function.comp_apply, Complex.ofReal_re]
    have hcont := Complex.continuous_re.comp hline
    rw [hre] at hcont
    exact hcont
  have hnn (c : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
    have hq := _root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c
    unfold _root_.GD.N0106.N0428.N0765.N1616.d020958
    positivity
  have hl : ∀ c : ℝ, c ≤ 0 → |_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c| ≤
      ((2 : ℝ)^9 * v^(-21/2 : ℝ)) * Real.exp ((13/2 : ℝ)*c) := by
    intro c hcle
    simpa only [abs_of_nonneg (hnn c),
      show (13/2 : ℝ)*c = 13*c/2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1564.d021004 heta hu hv hw hcle
  have hr : ∀ c : ℝ, 0 ≤ c → |_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c| ≤
      ((2 : ℝ)^9 * (eta*w)^(-21/2 : ℝ)) * Real.exp (-(11/2 : ℝ)*c) := by
    intro c hcle
    simpa only [abs_of_nonneg (hnn c),
      show -(11/2 : ℝ)*c = -11*c/2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1564.d021006 heta hu hv hw hcle
  have hF : ∀ xi : ℝ, ‖𝓕 (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c : ℂ)) xi‖ ≤
      ((Real.cos d)^(-21/2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c) *
        Real.exp (-(2*Real.pi*d)*|xi|) := by
    intro xi
    calc
      _ ≤ Real.exp (-2*Real.pi*d*|xi|) * (Real.cos d)^(-21/2 : ℝ) *
          ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c :=
        _root_.GD.N0106.N0428.N0765.N1559.d021033 heta hu hv hw hd.le hdpi xi
      _ = _ := by
        rw [show -(2*Real.pi*d)*|xi| = -2*Real.pi*d*|xi| by ring]
        ring
  have he := _root_.GD.N0106.N0428.N0765.N1613.d005636 hc
    (by norm_num : 0 < (13/2 : ℝ)) (by norm_num : 0 < (11/2 : ℝ))
    (by positivity : 0 < 2*Real.pi*d) hh hl hr hF offset
  calc
    _ ≤ 2 * ((Real.cos d)^(-21/2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c) /
        (Real.exp ((2*Real.pi*d)/h)-1) := he
    _ = _ := by ring

end
end GD.N0106.N0428.N0765.N1561

#print axioms _root_.GD.N0106.N0428.N0765.N1561.d021034
#print axioms _root_.GD.N0106.N0428.N0765.N1561.d021035
