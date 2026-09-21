import GD.Module1439
import GD.Module1513

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0024.N0279

open MeasureTheory Set
open scoped ENNReal
open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1396
open _root_.GD.N0107
open _root_.GD.N0024.N0275 _root_.GD.N0024.N0278

noncomputable section

theorem d023580 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 6 6 θ (_root_.GD.N0232.N0720.N1080.d014175 6 6) =
      ENNReal.ofReal (_root_.GD.N0024.N0275.d022893 θ *
        (_root_.GD.N0024.N0277.d007879 (_root_.GD.N0024.N0275.d022892 θ) + _root_.GD.N0024.N0278.d023550 (_root_.GD.N0024.N0275.d022892 θ).val)) := by
  rw [_root_.GD.N0232.N0720.N1080.d014199 6 6 (by norm_num) (by norm_num),
    _root_.GD.N0232.N0720.N1287.d019529 6 6 (by norm_num) (by norm_num)]
  have horacle := _root_.GD.N0232.N0720.N1396.d014795 6 6 (by norm_num) (by norm_num) θ
  unfold _root_.GD.N0232.N0720.N1396.d014778 at horacle
  rw [horacle]
  congr 1
  unfold _root_.GD.N0024.N0275.d022893 _root_.GD.N0024.N0275.d022892 _root_.GD.N0024.N0277.d007879 _root_.GD.N0024.N0278.d023550 _root_.GD.N0232.N0720.N1424.d014839
  ring

theorem d023581 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 6 6 θ (_root_.GD.N0232.N0720.N1080.d014175 6 6) =
      ENNReal.ofReal (_root_.GD.N0024.N0278.d023552 (_root_.GD.N0024.N0275.d022892 θ).val) := by
  have hS := _root_.GD.N0024.N0275.d022894 θ
  have ht := _root_.GD.N0024.N0277.d007880 (_root_.GD.N0024.N0275.d022892 θ)
  unfold _root_.GD.N0232.N0720.N1256.d015547
  rw [_root_.GD.N0024.N0279.d023580, _root_.GD.N0024.N0275.d022895,
    ← ENNReal.ofReal_div_of_pos (mul_pos hS ht)]
  congr 1
  change _root_.GD.N0024.N0275.d022893 θ *
      (_root_.GD.N0024.N0277.d007879 (_root_.GD.N0024.N0275.d022892 θ) + _root_.GD.N0024.N0278.d023550 (_root_.GD.N0024.N0275.d022892 θ).val) /
        (_root_.GD.N0024.N0275.d022893 θ * _root_.GD.N0024.N0277.d007879 (_root_.GD.N0024.N0275.d022892 θ)) =
      1 + _root_.GD.N0024.N0278.d023550 (_root_.GD.N0024.N0275.d022892 θ).val / _root_.GD.N0024.N0277.d007879 (_root_.GD.N0024.N0275.d022892 θ)
  field_simp [hS.ne', ht.ne']

theorem d023582 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 6 6 θ (_root_.GD.N0232.N0720.N1080.d014175 6 6) ≤ ENNReal.ofReal (289 / 3) := by
  rw [_root_.GD.N0024.N0279.d023581]
  exact ENNReal.ofReal_le_ofReal
    (_root_.GD.N0024.N0278.d023579 (_root_.GD.N0024.N0275.d022892 θ).val
      (_root_.GD.N0024.N0275.d022892 θ).property.1 (_root_.GD.N0024.N0275.d022892 θ).property.2)

theorem d023583 :
    _root_.GD.N0232.N0720.N1256.d015548 6 6 (_root_.GD.N0232.N0720.N1080.d014175 6 6) ≤ ENNReal.ofReal (289 / 3) := by
  apply iSup_le
  exact _root_.GD.N0024.N0279.d023582

theorem d023584 :
    _root_.GD.N0232.N0720.N1256.d015549 6 6 ≤ ENNReal.ofReal (289 / 3) := by
  have hd : _root_.GD.N0232.N0720.N1080.d014175 6 6 ∈ _root_.GD.N0232.N0720.N1256.d015545 6 6 :=
    _root_.GD.N0117.d014146 6 6
  have hmin := _root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0720.N1256.d015547 6 6) hd
  exact hmin.trans _root_.GD.N0024.N0279.d023583

theorem d023585 : _root_.GD.N0232.N0720.N1256.d015549 6 6 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top _root_.GD.N0024.N0279.d023584

theorem d023586
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 6 6 θ (_root_.GD.N0232.N0720.N1425.d014719 6 6 g) ≤
      _root_.GD.N0232.N0720.N1080.d014197 6 6 θ (_root_.GD.N0232.N0720.N1080.d014175 6 6)) :
    ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0232.N0720.N1441.d013678 6 6) g t ≤
      _root_.GD.N0024.N0278.d023551 t.val := by
  intro t
  have h := hcap (_root_.GD.N0024.N0275.d022898 t)
  rw [_root_.GD.N0024.N0275.d022896 g hg hb, _root_.GD.N0024.N0279.d023580, _root_.GD.N0024.N0275.d022899] at h
  have hS := _root_.GD.N0024.N0275.d022894 (_root_.GD.N0024.N0275.d022898 t)
  have ht := _root_.GD.N0024.N0277.d007880 t
  have hright : 0 ≤ _root_.GD.N0024.N0275.d022893 (_root_.GD.N0024.N0275.d022898 t) *
      (_root_.GD.N0024.N0277.d007879 t + _root_.GD.N0024.N0278.d023550 t.val) :=
    mul_nonneg hS.le (add_nonneg ht.le (_root_.GD.N0024.N0278.d023554 t.val))
  have hreal := (ENNReal.ofReal_le_ofReal_iff hright).mp h
  have hcancel := le_of_mul_le_mul_left hreal hS
  have hloss : _root_.GD.N0024.N0277.d007881 (_root_.GD.N0232.N0720.N1441.d013678 6 6 t) g t.val ≤ _root_.GD.N0024.N0278.d023550 t.val := by
    linarith
  change _root_.GD.N0024.N0277.d007881 (_root_.GD.N0232.N0720.N1441.d013678 6 6 t) g t.val /
      _root_.GD.N0024.N0277.d007879 t ≤ _root_.GD.N0024.N0278.d023550 t.val / _root_.GD.N0024.N0277.d007879 t
  exact div_le_div_of_nonneg_right hloss ht.le

theorem d023587
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 6 6 θ (_root_.GD.N0232.N0720.N1425.d014719 6 6 g) ≤
      _root_.GD.N0232.N0720.N1080.d014182 6 6 θ (_root_.GD.N0232.N0720.N1080.d014180 6 6 (by norm_num) (by norm_num))) :
    ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0232.N0720.N1441.d013678 6 6) g t ≤
      _root_.GD.N0024.N0278.d023551 t.val := by
  apply _root_.GD.N0024.N0279.d023586 g hg hb
  intro θ
  rw [_root_.GD.N0232.N0720.N1080.d014199 6 6 (by norm_num) (by norm_num)]
  exact hcap θ

#print axioms _root_.GD.N0024.N0279.d023580
#print axioms _root_.GD.N0024.N0279.d023581
#print axioms _root_.GD.N0024.N0279.d023582
#print axioms _root_.GD.N0024.N0279.d023583
#print axioms _root_.GD.N0024.N0279.d023584
#print axioms _root_.GD.N0024.N0279.d023585
#print axioms _root_.GD.N0024.N0279.d023586
#print axioms _root_.GD.N0024.N0279.d023587

end
end GD.N0024.N0279
