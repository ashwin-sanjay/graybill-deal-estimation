import GD.Module1897
import GD.Module0622
import GD.Module1172
import GD.Module0932















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0200
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1089
open _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0149.N0432


def d030833 (omega : _root_.GD.N0232.N0720.N1080.d014170 3 3) : ℝ :=
  _root_.GD.N0232.N0720.N1437.d003016 (fun r _ => _root_.GD.N0232.N0720.N1089.d003092 r)
    (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
    (_root_.GD.N0107.d009085 omega.1 / 3) (_root_.GD.N0107.d009085 omega.2 / 3)


theorem d030834 (a b : ℝ) (hab : a + b ≠ 0) :
    _root_.GD.N0232.N0720.N1089.d003092 (b / (a + b)) = b ^ 2 / (a ^ 2 + b ^ 2) := by
  have hs : a ^ 2 + b ^ 2 ≠ 0 := by
    have hpos : 0 < (a + b) ^ 2 := sq_pos_of_ne_zero hab
    have hpos' : 0 < a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    exact hpos'.ne'
  have hc : 1 - b / (a + b) = a / (a + b) := by
    field_simp [hab] <;> ring
  unfold _root_.GD.N0232.N0720.N1089.d003092
  apply (div_eq_div_iff (_root_.GD.N0232.N0720.N1089.d003095 (b / (a + b))).ne' hs).2
  rw [hc]
  field_simp [hab] <;> ring


theorem d030835 (x y a b : ℝ) (hab : a + b ≠ 0) :
    _root_.GD.N0232.N0720.N1437.d002998 (fun r _ => _root_.GD.N0232.N0720.N1089.d003092 r) x y (a / 3) (b / 3) =
      (b ^ 2 * x + a ^ 2 * y) / (a ^ 2 + b ^ 2) := by
  have hscaled : a / 3 + b / 3 ≠ 0 := by
    intro hzero
    apply hab
    linarith
  have hf : _root_.GD.N0232.N0720.N1437.d002996 (a / 3) (b / 3) =
      b / (a + b) := by
    unfold _root_.GD.N0232.N0720.N1437.d002996
    field_simp [hab, hscaled] <;> ring
  have hs : a ^ 2 + b ^ 2 ≠ 0 := by
    have hpos : 0 < (a + b) ^ 2 := sq_pos_of_ne_zero hab
    have hpos' : 0 < a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    exact hpos'.ne'
  simp only [_root_.GD.N0232.N0720.N1437.d002998, hf]
  rw [_root_.GD.N0200.d030834 a b hab]
  field_simp [hs] <;> ring


theorem d030836 (omega : _root_.GD.N0232.N0720.N1080.d014170 3 3) :
    _root_.GD.N0200.d030833 omega =
      if _root_.GD.N0107.d009085 omega.1 = 0 ∧ _root_.GD.N0107.d009085 omega.2 = 0
      then (_root_.GD.N0107.d009084 omega.1 + _root_.GD.N0107.d009084 omega.2) / 2
      else
        ((_root_.GD.N0107.d009085 omega.2) ^ 2 * _root_.GD.N0107.d009084 omega.1 +
          (_root_.GD.N0107.d009085 omega.1) ^ 2 * _root_.GD.N0107.d009084 omega.2) /
          ((_root_.GD.N0107.d009085 omega.1) ^ 2 +
            (_root_.GD.N0107.d009085 omega.2) ^ 2) := by
  classical
  have hx : 0 ≤ _root_.GD.N0107.d009085 omega.1 := by
    unfold _root_.GD.N0107.d009085 _root_.GD.N0126.d006422
    positivity
  have hy : 0 ≤ _root_.GD.N0107.d009085 omega.2 := by
    unfold _root_.GD.N0107.d009085 _root_.GD.N0126.d006422
    positivity
  by_cases hzero : _root_.GD.N0107.d009085 omega.1 = 0 ∧
      _root_.GD.N0107.d009085 omega.2 = 0
  · simp [_root_.GD.N0200.d030833, _root_.GD.N0232.N0720.N1437.d003016,
      _root_.GD.N0232.N0720.N1437.d003012, _root_.GD.N0232.N0720.N1437.d003014, hzero.1, hzero.2]
  · have hsum : _root_.GD.N0107.d009085 omega.1 +
        _root_.GD.N0107.d009085 omega.2 ≠ 0 := by
      intro heq
      exact hzero ⟨by linarith, by linarith⟩
    have hstratum : _root_.GD.N0232.N0720.N1437.d003012 (_root_.GD.N0107.d009085 omega.1 / 3)
        (_root_.GD.N0107.d009085 omega.2 / 3) := by
      unfold _root_.GD.N0232.N0720.N1437.d003012
      intro heq
      apply hsum
      linarith
    rw [if_neg hzero, _root_.GD.N0200.d030833,
      _root_.GD.N0232.N0720.N1437.d003018 _ _ _ _ _ hstratum]
    exact _root_.GD.N0200.d030835 _ _ _ _ hsum


theorem d030837
    (omega : _root_.GD.N0232.N0720.N1080.d014170 3 3)
    (h : _root_.GD.N0232.N0720.N1437.d003012 (_root_.GD.N0107.d009085 omega.1 / 3)
      (_root_.GD.N0107.d009085 omega.2 / 3)) :
    _root_.GD.N0200.d030833 omega = _root_.GD.N0149.N0432.d030808 omega := by
  rw [_root_.GD.N0200.d030833,
    _root_.GD.N0232.N0720.N1437.d003018 _ _ _ _ _ h]
  rfl


theorem d030838 : Measurable _root_.GD.N0200.d030833 := by
  classical
  have hv : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 3 3 =>
      _root_.GD.N0107.d009085 omega.1 / 3 + _root_.GD.N0107.d009085 omega.2 / 3) := by
    fun_prop
  have hs : MeasurableSet {omega : _root_.GD.N0232.N0720.N1080.d014170 3 3 |
      _root_.GD.N0232.N0720.N1437.d003012 (_root_.GD.N0107.d009085 omega.1 / 3)
        (_root_.GD.N0107.d009085 omega.2 / 3)} :=
    (hv (measurableSet_singleton (0 : ℝ))).compl
  unfold _root_.GD.N0200.d030833 _root_.GD.N0232.N0720.N1437.d003016
  apply Measurable.ite hs
  · change Measurable _root_.GD.N0149.N0432.d030808
    exact _root_.GD.N0149.N0432.d030809.1
  · unfold _root_.GD.N0232.N0720.N1437.d003014
    fun_prop


theorem d030839 :
    _root_.GD.N0200.d030833 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 3 3] _root_.GD.N0149.N0432.d030808 := by
  have hpos := _root_.GD.N0119.d009075
    3 3 (by norm_num) (by norm_num) (e := 1 / 2) (by norm_num) (by norm_num)
  have href : _root_.GD.N0232.N0720.N1080.d014172 3 3 = _root_.GD.N0137.d008914 3 3 := by
    rw [_root_.GD.N0232.N0720.N1449.d018839]
    rfl
  rw [href]
  filter_upwards [hpos] with omega homega
  apply _root_.GD.N0200.d030837
  have hx : 0 < _root_.GD.N0107.d009085 omega.1 := homega.1
  have hy : 0 < _root_.GD.N0107.d009085 omega.2 := homega.2
  change _root_.GD.N0107.d009085 omega.1 / 3 + _root_.GD.N0107.d009085 omega.2 / 3 ≠ 0
  linarith


theorem d030840 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0200.d030833 =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 3 3 theta] _root_.GD.N0149.N0432.d030808 :=
  (_root_.GD.N0232.N0720.N1080.d014173 3 3 theta).ae_le _root_.GD.N0200.d030839


theorem d030841 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 3 3 theta _root_.GD.N0200.d030833 =
      _root_.GD.N0232.N0720.N1080.d014197 3 3 theta _root_.GD.N0149.N0432.d030808 :=
  _root_.GD.N0232.N0720.N1159.d014662 3 3 theta (_root_.GD.N0200.d030840 theta)


theorem d030842 :
    _root_.GD.N0200.d030833 ∈ _root_.GD.N0232.N0720.N1256.d015551 3 3 := by
  refine ⟨_root_.GD.N0200.d030838, ?_⟩
  intro theta
  rw [_root_.GD.N0200.d030841]
  exact _root_.GD.N0149.N0432.d030809.2 theta


theorem d030843 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 theta _root_.GD.N0200.d030833 =
      _root_.GD.N0232.N0720.N1256.d015547 3 3 theta _root_.GD.N0149.N0432.d030808 := by
  unfold _root_.GD.N0232.N0720.N1256.d015547
  rw [_root_.GD.N0200.d030841]

end
end GD.N0200

#print axioms _root_.GD.N0200.d030834
#print axioms _root_.GD.N0200.d030835
#print axioms _root_.GD.N0200.d030836
#print axioms _root_.GD.N0200.d030837
#print axioms _root_.GD.N0200.d030838
#print axioms _root_.GD.N0200.d030839
#print axioms _root_.GD.N0200.d030840
#print axioms _root_.GD.N0200.d030841
#print axioms _root_.GD.N0200.d030842
#print axioms _root_.GD.N0200.d030843
