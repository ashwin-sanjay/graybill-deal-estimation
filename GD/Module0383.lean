import GD.Module0382
import GD.Module0381












set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped FourierTransform Topology BigOperators

namespace GD.N0106.N0428.N0765.N1653
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1652



theorem d005827 {f : ℝ × ℝ → ℝ} {h d0 d1 Ma Mb Mab : ℝ}
    (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (hrows : ∀ a : ℝ, _root_.GD.N0106.N0428.N0765.N1652.d005813
      (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1652.d005822 (fun p : ℝ × ℝ => (f p : ℂ)) h (a, b)))
    (hcolumns : ∀ n : ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005813
      (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (fun p : ℝ × ℝ => (f p : ℂ)) h) n))
    (x y : ℝ)
    (hsamples : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005822 (fun q : ℝ × ℝ => (f q : ℂ)) h (x / h + p.1, y / h + p.2)))
    (hcross : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (fun q : ℝ × ℝ => (f q : ℂ)) h) p.2 (x / h + p.1)))
    (hcoeff : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1652.d005822 (fun q : ℝ × ℝ => (f q : ℂ)) h) p.1 p.2))
    (haxisA : ∀ m : ℤ, m ≠ 0 →
      ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (fun p : ℝ × ℝ => (f p : ℂ)) (m / h) 0‖ ≤
        Ma * Real.exp (-(2 * Real.pi * d0 / h) * |(m : ℝ)|))
    (haxisB : ∀ n : ℤ, n ≠ 0 →
      ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (fun p : ℝ × ℝ => (f p : ℂ)) 0 (n / h)‖ ≤
        Mb * Real.exp (-(2 * Real.pi * d0 / h) * |(n : ℝ)|))
    (hmixed : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
      ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (fun p : ℝ × ℝ => (f p : ℂ)) (m / h) (n / h)‖ ≤
        Mab * Real.exp (-(2 * Real.pi * d1 / h) * |(m : ℝ)|) *
          Real.exp (-(2 * Real.pi * d1 / h) * |(n : ℝ)|)) :
    |(∫ a : ℝ, ∫ b : ℝ, f (a, b)) -
        h ^ 2 * (∑' p : ℤ × ℤ, f (x + h * p.1, y + h * p.2))| ≤
      (2 * Ma + 2 * Mb) / (Real.exp (2 * Real.pi * d0 / h) - 1) +
        4 * Mab / (Real.exp (2 * Real.pi * d1 / h) - 1) ^ 2 := by
  let fc : ℝ × ℝ → ℂ := fun p => (f p : ℂ)
  let c (m n : ℤ) : ℂ := _root_.GD.N0106.N0428.N0765.N1652.d005817 fc (m / h) (n / h)
  let phaseA (m : ℤ) : ℂ := fourier m ((x / h : ℝ) : UnitAddCircle)
  let phaseB (n : ℤ) : ℂ := fourier n ((y / h : ℝ) : UnitAddCircle)
  have hphaseA (m : ℤ) : ‖phaseA m‖ = 1 := Circle.norm_coe _
  have hphaseB (n : ℤ) : ‖phaseB n‖ = 1 := Circle.norm_coe _
  have hphaseA0 : phaseA 0 = 1 := fourier_zero
  have hphaseB0 : phaseB 0 = 1 := fourier_zero
  have hc : Summable (fun p : ℤ × ℤ => c p.1 p.2) := by
    have hs := Summable.const_smul (h ^ 2) hcoeff
    change Summable (fun p : ℤ × ℤ => h ^ 2 • _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1652.d005822 fc h) p.1 p.2) at hs
    simpa only [c, _root_.GD.N0106.N0428.N0765.N1652.d005825 fc hh] using hs
  have hzero : c 0 0 = (((∫ a : ℝ, ∫ b : ℝ, f (a, b)) : ℝ) : ℂ) := by
    simp only [c, Int.cast_zero, zero_div, _root_.GD.N0106.N0428.N0765.N1652.d005818, fc, integral_complex_ofReal]
  have hp := _root_.GD.N0106.N0428.N0765.N1652.d005826 hh hrows hcolumns x y hsamples hcross hcoeff
  have hcoerce : ((h ^ 2 * (∑' p : ℤ × ℤ,
      f (x + h * p.1, y + h * p.2)) : ℝ) : ℂ) =
      h ^ 2 • (∑' p : ℤ × ℤ, fc (x + h * p.1, y + h * p.2)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_tsum, Complex.real_smul]
  have hrep : ((h ^ 2 * (∑' p : ℤ × ℤ,
      f (x + h * p.1, y + h * p.2)) : ℝ) : ℂ) =
      ∑' p : ℤ × ℤ, c p.1 p.2 * phaseA p.1 * phaseB p.2 :=
    hcoerce.trans hp
  have hk0 : 0 < 2 * Real.pi * d0 / h := by positivity
  have hk1 : 0 < 2 * Real.pi * d1 / h := by positivity
  apply _root_.GD.N0106.N0428.N0765.N1646.d005812 hk0 hk1
    hphaseA hphaseB hphaseA0 hphaseB0 hc hzero hrep
  · intro m hm
    simpa only [c, Int.cast_zero, zero_div] using haxisA m hm
  · intro n hn
    simpa only [c, Int.cast_zero, zero_div] using haxisB n hn
  · exact hmixed

end
end GD.N0106.N0428.N0765.N1653

#print axioms _root_.GD.N0106.N0428.N0765.N1653.d005827
