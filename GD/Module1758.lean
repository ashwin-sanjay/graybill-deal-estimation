import GD.Module1755
import GD.Module1756
import GD.Module1757





















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace GD.N0106.N0428.N0765.N1682
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1683 _root_.GD.N0106.N0428.N0765.N1684
open _root_.GD.N0106.N0428.N0765.N1686

theorem d029129 : Integrable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1686.d029103 (x : ℂ)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1686.d029122] using
    (_root_.GD.N0106.N0428.N0765.N1684.d029081.ofReal : Integrable (fun x : ℝ => (_root_.GD.N0106.N0428.N0765.N1683.d029050 x : ℂ)))

theorem d029130 :
    Integrable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) + Complex.I)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1686.d029123] using _root_.GD.N0106.N0428.N0765.N1684.d029082

theorem d029131 :
    Integrable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) - Complex.I)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1686.d029124] using _root_.GD.N0106.N0428.N0765.N1684.d029083

theorem d029132 :
    Summable (fun k : ℤ => _root_.GD.N0106.N0428.N0765.N1686.d029103 ((1 + 16 * (k : ℝ) : ℝ) : ℂ)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1686.d029122] using
    (Complex.summable_ofReal.mpr _root_.GD.N0106.N0428.N0765.N1684.d029088)

theorem d029133 :
    Summable (fun k : ℤ => ‖_root_.GD.N0106.N0428.N0765.N1686.d029103 ((1 + 16 * (k : ℝ) : ℝ) : ℂ)‖) := by
  apply _root_.GD.N0106.N0428.N0765.N1684.d029088.congr
  intro k
  simp only [_root_.GD.N0106.N0428.N0765.N1686.d029122, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (_root_.GD.N0106.N0428.N0765.N1683.d029057 _)]




theorem d029134 :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ x y : ℝ, R ≤ |x| → |y| ≤ 1 →
        ‖_root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ε := by
  intro ε hε
  refine ⟨_root_.GD.N0106.N0428.N0765.N1685.d029097 ε,
    _root_.GD.N0106.N0428.N0765.N1685.d029098 ε, ?_⟩
  intro x y hx hy
  have hxone : 1 ≤ |x| := (le_max_left _ _).trans hx
  have hxne : x ≠ 0 := by
    intro h
    norm_num [h] at hxone
  have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re ≠ 0 := by simpa using hxne
  rw [_root_.GD.N0106.N0428.N0765.N1686.d029103, if_neg (_root_.GD.N0106.N0428.N0765.N1686.d029107 hre)]
  exact _root_.GD.N0106.N0428.N0765.N1685.d029099 hε hx hy

theorem d029135 :
    ((∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) - Complex.I)‖) +
        (∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1686.d029103 ((x : ℂ) + Complex.I)‖)) /
        (Real.exp (2 * Real.pi / 16) - 1) <
      ‖(∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1686.d029103 (x : ℂ)) -
        (16 : ℂ) * (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1686.d029103 ((1 + 16 * (k : ℝ) : ℝ) : ℂ))‖ := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1686.d029124, _root_.GD.N0106.N0428.N0765.N1686.d029123, _root_.GD.N0106.N0428.N0765.N1686.d029122, _root_.GD.N0106.N0428.N0765.N1683.d029056]
    using _root_.GD.N0106.N0428.N0765.N1684.d029093



theorem d029136 :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f {z : ℂ | |z.im| < 1} ∧
      (∀ r : ℝ, r < 1 → ContinuousOn f {z : ℂ | |z.im| ≤ r}) ∧
      (∀ x : ℝ, Tendsto (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I))
        (𝓝[Ioo (-1 : ℝ) 1] (1 : ℝ)) (𝓝 (f ((x : ℂ) + Complex.I)))) ∧
      (∀ x : ℝ, Tendsto (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I))
        (𝓝[Ioo (-1 : ℝ) 1] (-1 : ℝ)) (𝓝 (f ((x : ℂ) - Complex.I)))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        ∀ x y : ℝ, R ≤ |x| → |y| ≤ 1 →
          ‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ε) ∧
      Integrable (fun x : ℝ => f (x : ℂ)) ∧
      Integrable (fun x : ℝ => f ((x : ℂ) - Complex.I)) ∧
      Integrable (fun x : ℝ => f ((x : ℂ) + Complex.I)) ∧
      Summable (fun k : ℤ => f ((1 + 16 * (k : ℝ) : ℝ) : ℂ)) ∧
      Summable (fun k : ℤ => ‖f ((1 + 16 * (k : ℝ) : ℝ) : ℂ)‖) ∧
      ((∫ x : ℝ, ‖f ((x : ℂ) - Complex.I)‖) +
          (∫ x : ℝ, ‖f ((x : ℂ) + Complex.I)‖)) /
          (Real.exp (2 * Real.pi / 16) - 1) <
        ‖(∫ x : ℝ, f (x : ℂ)) -
          (16 : ℂ) * (∑' k : ℤ, f ((1 + 16 * (k : ℝ) : ℝ) : ℂ))‖ := by
  exact ⟨_root_.GD.N0106.N0428.N0765.N1686.d029103, _root_.GD.N0106.N0428.N0765.N1686.d029125, _root_.GD.N0106.N0428.N0765.N1686.d029126,
    _root_.GD.N0106.N0428.N0765.N1686.d029127, _root_.GD.N0106.N0428.N0765.N1686.d029128,
    _root_.GD.N0106.N0428.N0765.N1682.d029134, _root_.GD.N0106.N0428.N0765.N1682.d029129,
    _root_.GD.N0106.N0428.N0765.N1682.d029131, _root_.GD.N0106.N0428.N0765.N1682.d029130, _root_.GD.N0106.N0428.N0765.N1682.d029132,
    _root_.GD.N0106.N0428.N0765.N1682.d029133, _root_.GD.N0106.N0428.N0765.N1682.d029135⟩

end
end GD.N0106.N0428.N0765.N1682

#print axioms _root_.GD.N0106.N0428.N0765.N1682.d029129
#print axioms _root_.GD.N0106.N0428.N0765.N1682.d029132
#print axioms _root_.GD.N0106.N0428.N0765.N1682.d029133
#print axioms _root_.GD.N0106.N0428.N0765.N1682.d029134
#print axioms _root_.GD.N0106.N0428.N0765.N1682.d029135
#print axioms _root_.GD.N0106.N0428.N0765.N1682.d029136
