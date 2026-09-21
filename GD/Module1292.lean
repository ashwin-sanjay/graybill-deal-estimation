import GD.Module0364
import GD.Module1291










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1559
noncomputable section

open MeasureTheory _root_.GD.N0106.N0428.N0765.N1616 _root_.GD.N0106.N0428.N0765.N1550
open scoped FourierTransform

theorem d021031 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (a : ℝ) (n : ℕ)
    {z : ℂ} (hz : |z.im| ≤ d) :
    DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1563.d020973 a n eta u v w) z := by
  have hQ : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w) z :=
    _root_.GD.N0106.N0428.N0765.N1563.d020988 eta u v w z
  have hp := hQ.cpow_const (c := ((-21 / 2 : ℝ) : ℂ))
    (_root_.GD.N0106.N0428.N0765.N1563.d020987 heta hu hv hw hd0 hd hz)
  have hn : DifferentiableAt ℂ (fun z : ℂ =>
      Complex.exp ((a : ℂ) * z) * (1 + Complex.exp z) ^ n) z := by
    fun_prop
  exact hn.mul hp

theorem d021032 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (xi : ℝ) :
    ‖𝓕 (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c : ℂ)) xi‖ ≤
      Real.exp (-2 * Real.pi * d * |xi|) * (Real.cos d) ^ (-21 / 2 : ℝ) *
        ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  have hhol : ∀ z : ℂ, |z.im| ≤ d →
      DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w) z := by
    intro z hz
    exact _root_.GD.N0106.N0428.N0765.N1559.d021031 heta hu hv hw hd0 hd (11 / 2) 10 hz
  have h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w) 0) := by
    change Integrable (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w
      ((c : ℂ) + (0 : ℂ) * Complex.I))
    exact _root_.GD.N0106.N0428.N0765.N1558.d021021 heta hu hv hw hd0 hd
        (t := 0) (by simpa only [abs_zero] using hd0)
  have hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w) (-d)) := by
    change Integrable (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w
      ((c : ℂ) + ((-d : ℝ) : ℂ) * Complex.I))
    exact _root_.GD.N0106.N0428.N0765.N1558.d021021 heta hu hv hw hd0 hd
        (t := -d) (by simpa only [abs_neg, abs_of_nonneg hd0] using (le_refl d))
  have hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w) d) := by
    change Integrable (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w
      ((c : ℂ) + (d : ℂ) * Complex.I))
    exact _root_.GD.N0106.N0428.N0765.N1558.d021021 heta hu hv hw hd0 hd
        (t := d) (by simpa only [abs_of_nonneg hd0] using (le_refl d))
  have hleft : ∀ z : ℂ, |z.im| ≤ d → z.re ≤ 0 →
      ‖_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w z‖ ≤
        ((Real.cos d) ^ (-21 / 2 : ℝ) * ((2 : ℝ) ^ 10 * v ^ (-21 / 2 : ℝ))) *
          Real.exp ((11 / 2 : ℝ) * z.re) := by
    intro z hz hc
    simpa only [mul_assoc, show (11 / 2 : ℝ) * z.re = 11 * z.re / 2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1558.d021027 heta hu hv hw hd0 hd hz hc
  have hright : ∀ z : ℂ, |z.im| ≤ d → 0 ≤ z.re →
      ‖_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w z‖ ≤
        ((Real.cos d) ^ (-21 / 2 : ℝ) *
          ((2 : ℝ) ^ 10 * (eta * w) ^ (-21 / 2 : ℝ))) *
            Real.exp (-(11 / 2 : ℝ) * z.re) := by
    intro z hz hc
    simpa only [mul_assoc, show -(11 / 2 : ℝ) * z.re = -11 * z.re / 2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1558.d021029 heta hu hv hw hd0 hd hz hc
  have hfourier := _root_.GD.N0106.N0428.N0765.N1550.d005490 hd0 hhol h0 hminus hplus
    (by norm_num : 0 < (11 / 2 : ℝ)) (by norm_num : 0 < (11 / 2 : ℝ))
    hleft hright xi
  have hreal : (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c : ℂ)) =
      _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w) 0 := by
    funext c
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005478] using
      (_root_.GD.N0106.N0428.N0765.N1563.d020991 heta hu hv hw c).symm
  have hheight : |(if 0 ≤ xi then -d else d)| ≤ d := by
    split_ifs <;> simpa only [abs_neg, abs_of_nonneg hd0] using (le_refl d)
  have hboundary := _root_.GD.N0106.N0428.N0765.N1558.d021023
    heta hu hv hw hd0 hd hheight
  rw [hreal]
  calc
    _ ≤ Real.exp (-2 * Real.pi * d * |xi|) *
        ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w)
          (if 0 ≤ xi then -d else d) x‖ := hfourier
    _ ≤ Real.exp (-2 * Real.pi * d * |xi|) *
        ((Real.cos d) ^ (-21 / 2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005473] using hboundary
    _ = _ := by ring

theorem d021033 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (xi : ℝ) :
    ‖𝓕 (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c : ℂ)) xi‖ ≤
      Real.exp (-2 * Real.pi * d * |xi|) * (Real.cos d) ^ (-21 / 2 : ℝ) *
        ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  have hhol : ∀ z : ℂ, |z.im| ≤ d →
      DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w) z := by
    intro z hz
    exact _root_.GD.N0106.N0428.N0765.N1559.d021031 heta hu hv hw hd0 hd (13 / 2) 9 hz
  have h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w) 0) := by
    change Integrable (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w
      ((c : ℂ) + (0 : ℂ) * Complex.I))
    exact _root_.GD.N0106.N0428.N0765.N1558.d021022 heta hu hv hw hd0 hd
        (t := 0) (by simpa only [abs_zero] using hd0)
  have hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w) (-d)) := by
    change Integrable (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w
      ((c : ℂ) + ((-d : ℝ) : ℂ) * Complex.I))
    exact _root_.GD.N0106.N0428.N0765.N1558.d021022 heta hu hv hw hd0 hd
        (t := -d) (by simpa only [abs_neg, abs_of_nonneg hd0] using (le_refl d))
  have hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w) d) := by
    change Integrable (fun c : ℝ => _root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w
      ((c : ℂ) + (d : ℂ) * Complex.I))
    exact _root_.GD.N0106.N0428.N0765.N1558.d021022 heta hu hv hw hd0 hd
        (t := d) (by simpa only [abs_of_nonneg hd0] using (le_refl d))
  have hleft : ∀ z : ℂ, |z.im| ≤ d → z.re ≤ 0 →
      ‖_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w z‖ ≤
        ((Real.cos d) ^ (-21 / 2 : ℝ) * ((2 : ℝ) ^ 9 * v ^ (-21 / 2 : ℝ))) *
          Real.exp ((13 / 2 : ℝ) * z.re) := by
    intro z hz hc
    simpa only [mul_assoc, show (13 / 2 : ℝ) * z.re = 13 * z.re / 2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1558.d021028 heta hu hv hw hd0 hd hz hc
  have hright : ∀ z : ℂ, |z.im| ≤ d → 0 ≤ z.re →
      ‖_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w z‖ ≤
        ((Real.cos d) ^ (-21 / 2 : ℝ) *
          ((2 : ℝ) ^ 9 * (eta * w) ^ (-21 / 2 : ℝ))) *
            Real.exp (-(11 / 2 : ℝ) * z.re) := by
    intro z hz hc
    simpa only [mul_assoc, show -(11 / 2 : ℝ) * z.re = -11 * z.re / 2 by ring] using
      _root_.GD.N0106.N0428.N0765.N1558.d021030 heta hu hv hw hd0 hd hz hc
  have hfourier := _root_.GD.N0106.N0428.N0765.N1550.d005490 hd0 hhol h0 hminus hplus
    (by norm_num : 0 < (13 / 2 : ℝ)) (by norm_num : 0 < (11 / 2 : ℝ))
    hleft hright xi
  have hreal : (fun c : ℝ => (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c : ℂ)) =
      _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w) 0 := by
    funext c
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005478] using
      (_root_.GD.N0106.N0428.N0765.N1563.d020992 heta hu hv hw c).symm
  have hheight : |(if 0 ≤ xi then -d else d)| ≤ d := by
    split_ifs <;> simpa only [abs_neg, abs_of_nonneg hd0] using (le_refl d)
  have hboundary := _root_.GD.N0106.N0428.N0765.N1558.d021024
    heta hu hv hw hd0 hd hheight
  rw [hreal]
  calc
    _ ≤ Real.exp (-2 * Real.pi * d * |xi|) *
        ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w)
          (if 0 ≤ xi then -d else d) x‖ := hfourier
    _ ≤ Real.exp (-2 * Real.pi * d * |xi|) *
        ((Real.cos d) ^ (-21 / 2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005473] using hboundary
    _ = _ := by ring

end
end GD.N0106.N0428.N0765.N1559

#print axioms _root_.GD.N0106.N0428.N0765.N1559.d021031
#print axioms _root_.GD.N0106.N0428.N0765.N1559.d021032
#print axioms _root_.GD.N0106.N0428.N0765.N1559.d021033
