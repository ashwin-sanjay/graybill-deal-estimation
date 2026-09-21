import GD.Module1213
import GD.Module1278
import GD.Module0983

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0024.N0263

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1226
open _root_.GD.N0230.N0611

theorem d020636 : _root_.GD.N0232.N0720.N1256.d015549 2 2 = ⊤ :=
  _root_.GD.N0232.N0720.N1223.d019625
    _root_.GD.N0232.N0720.N1225.d020635

theorem d020637
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0720.N1256.d015548 2 2 d = ⊤ := by
  apply top_unique
  rw [← _root_.GD.N0024.N0263.d020636]
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 2 2) hd

theorem d020638 (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) (hd : Measurable d) :
    ¬ (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 2 θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 2 2 θ)) := by
  intro hbound
  obtain ⟨g, hg, hb, hcap⟩ :=
    _root_.GD.N0232.N0720.N1223.d019624 C hC d hd hbound
  exact _root_.GD.N0232.N0720.N1225.d020635 g hg hb C hcap

theorem d020639 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    min (_root_.GD.N0232.N0720.N1080.d014197 2 2 θ (_root_.GD.N0232.N0720.N1080.d014175 2 2))
      (_root_.GD.N0232.N0720.N1256.d015549 2 2 * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 2 2 θ)) =
      _root_.GD.N0232.N0720.N1080.d014197 2 2 θ (_root_.GD.N0232.N0720.N1080.d014175 2 2) := by
  rw [_root_.GD.N0024.N0263.d020636, ENNReal.top_mul
    (ne_of_gt (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1257.d015510 2 2 (by omega) θ)))]
  exact min_eq_left le_top

theorem d020640 : _root_.GD.N0232.N0720.N1226.d015578 2 2 :=
  _root_.GD.N0232.N0720.N1226.d015586
    2 2 (by omega) (by omega) _root_.GD.N0024.N0263.d020636

theorem d020641 :
    ∃ d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ, Measurable d ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 2 θ d ≤
        min (_root_.GD.N0232.N0720.N1080.d014197 2 2 θ (_root_.GD.N0232.N0720.N1080.d014175 2 2))
          (_root_.GD.N0232.N0720.N1256.d015549 2 2 * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 2 2 θ)) := by
  obtain ⟨d, hd, _⟩ := _root_.GD.N0024.N0263.d020640
  refine ⟨d, hd.1, fun θ => ?_⟩
  rw [_root_.GD.N0024.N0263.d020639]
  exact (hd.2.1 θ).le

theorem d020642 :
    _root_.GD.N0232.N0720.N1256.d015549 2 2 = ⊤ ∧
    _root_.GD.N0232.N0720.N1226.d015578 2 2 ∧
    ∃ d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ, Measurable d ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 2 θ d ≤
        min (_root_.GD.N0232.N0720.N1080.d014197 2 2 θ (_root_.GD.N0232.N0720.N1080.d014175 2 2))
          (_root_.GD.N0232.N0720.N1256.d015549 2 2 * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 2 2 θ)) :=
  ⟨_root_.GD.N0024.N0263.d020636, _root_.GD.N0024.N0263.d020640, _root_.GD.N0024.N0263.d020641⟩

end
end GD.N0024.N0263

#print axioms _root_.GD.N0024.N0263.d020636
#print axioms _root_.GD.N0024.N0263.d020637
#print axioms _root_.GD.N0024.N0263.d020638
#print axioms _root_.GD.N0024.N0263.d020639
#print axioms _root_.GD.N0024.N0263.d020640
#print axioms _root_.GD.N0024.N0263.d020641
#print axioms _root_.GD.N0024.N0263.d020642
