import GD.Module1713
import GD.Module1874
import GD.Module1371

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal BigOperators

namespace GD.N0224.N0532
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1497
open _root_.GD.N0076.N0310.N0759
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0213.N0486
open _root_.GD.N0101.N0411
open _root_.GD.N0224.N0534

theorem d030672
    (d : _root_.GD.N0232.N0719.N0859.d010811 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) → ℝ)
    (hd : Measurable d)
    (c : ℝ≥0∞)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) θ d ≤
      c * _root_.GD.N0232.N0719.N0859.d010840 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) θ
        (_root_.GD.N0232.N0719.N0900.d009111 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2))) : 1 ≤ c := by
  by_contra hc
  have hc1 : c < 1 := lt_of_not_ge hc
  have hct : c ≠ ⊤ := ne_top_of_lt hc1
  have hq : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hq1 : c.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal hct ENNReal.one_ne_top).mpr hc1
  apply _root_.GD.N0101.N0378.d030662
    (d ∘ _root_.GD.N0232.N0720.N1467.d012541 2 2) (hd.comp (_root_.GD.N0232.N0720.N1497.d012554 2 2)) hq hq1
  intro θ
  rw [_root_.GD.N0076.N0310.N0759.d014243, ENNReal.ofReal_mul hq, ENNReal.ofReal_toReal hct,
    _root_.GD.N0076.N0313.d030567]
  have hb := _root_.GD.N0076.N0310.N0759.d014247 2 2 (by decide) (by decide) θ
  rw [_root_.GD.N0232.N0720.N1080.d014199
    2 2 (by decide) (by decide) θ] at hb
  change _root_.GD.N0232.N0719.N0859.d010840 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) (_root_.GD.N0076.N0310.N0759.d014240 θ) d ≤
    c * _root_.GD.N0232.N0720.N1080.d014182 2 2 θ
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by decide) (by decide))
  rw [← hb]
  exact hcap (_root_.GD.N0076.N0310.N0759.d014240 θ)

theorem d030673
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin 2 → ℝ) → Fin 2 → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (c : ℝ≥0∞)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      c * _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes)) : 1 ≤ c := by
  by_cases hlarge : 3 ≤ sizes 0 ∨ 3 ≤ sizes 1
  · exact _root_.GD.N0224.N0534.d028678 sizes (by decide) hn
      (_root_.GD.N0213.N0486.d028584 sizes hn hlarge) w hw hunit c hcap
  · have hsizes : sizes = _root_.GD.N0232.N0720.N1467.d012537 2 2 := by
      funext i
      have h0 := hn 0
      have h1 := hn 1
      fin_cases i
      · change sizes 0 = 2
        omega
      · change sizes 1 = 2
        omega
    subst sizes
    exact _root_.GD.N0224.N0532.d030672 _
      (_root_.GD.N0072.d023295 _ w hw) c hcap

theorem d030674
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i) (c : ℝ≥0∞) :
    (∃ w : (Fin 2 → ℝ) → Fin 2 → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        c * _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes)) ↔ 1 ≤ c := by
  constructor
  · rintro ⟨w, hw, hu, hc⟩
    exact _root_.GD.N0224.N0532.d030673 sizes hn w hw hu c hc
  · intro hc
    refine ⟨_root_.GD.N0021.d023313, _root_.GD.N0021.d023314, _root_.GD.N0101.N0411.d028560 (by decide), ?_⟩
    intro θ
    rw [← _root_.GD.N0021.d023315]
    simpa only [one_mul] using mul_le_mul_left hc
      (_root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes))

end
end GD.N0224.N0532

#print axioms _root_.GD.N0224.N0532.d030672
#print axioms _root_.GD.N0224.N0532.d030673
#print axioms _root_.GD.N0224.N0532.d030674
