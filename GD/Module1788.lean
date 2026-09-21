import GD.Module1787
import GD.Module1299











set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set Finset

namespace GD.N0106.N0428.N0765.N1515
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1627
  _root_.GD.N0106.N0428.N0765.N1585 _root_.GD.N0106.N0428.N0765.N1512 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1550

def d029729 (eta : ℝ) : ℝ := (1 + eta) / 11

def d029730 (location eta : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta / _root_.GD.N0106.N0428.N0765.N1515.d029729 eta


def d029731 (x : ℝ) : ℝ := (_root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ)).re

def d029732 (eta : ℝ) (q : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1521.d020868 q * _root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)

def d029733 (eta : ℝ) (z w : ℂ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z * _root_.GD.N0106.N0428.N0765.N1585.d005529 5 5 w *
    ((_root_.GD.N0106.N0428.N0765.N1585.d005540 eta w - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)) ^ 2 -
      (_root_.GD.N0106.N0428.N0765.N1512.d029181 eta z w - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)) ^ 2)

def d029734 (eta α β : ℝ) (q : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1515.d029733 eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)

def d029735 (eta α β : ℝ) : ℝ :=
  (((Real.cos (β / 2))⁻¹ + _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 +
    (_root_.GD.N0106.N0428.N0765.N1512.d029183 α β + _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2)

def d029736 (eta α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1515.d029735 eta α β *
    (Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * Real.cos (β / 2) ^ (-(10 : ℝ)))

def d029737 (α β : ℝ) : ℝ :=
  (((Real.cos (β / 2))⁻¹ + 1) ^ 2 + (_root_.GD.N0106.N0428.N0765.N1512.d029183 α β + 1) ^ 2) *
    (Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * Real.cos (β / 2) ^ (-(10 : ℝ)))

def d029738 (eta h d0 d1 : ℝ) : ℝ :=
  (2 * _root_.GD.N0106.N0428.N0765.N1515.d029736 eta d0 0 + 2 * _root_.GD.N0106.N0428.N0765.N1515.d029736 eta 0 d0) /
    (Real.exp (2 * Real.pi * d0 / h) - 1) +
    4 * _root_.GD.N0106.N0428.N0765.N1515.d029736 eta d1 d1 / (Real.exp (2 * Real.pi * d1 / h) - 1) ^ 2

def d029739 (eta hA hB a₀ b₀ : ℝ) (p : ℤ × ℤ) : ℝ :=
  (hA * hB) * _root_.GD.N0106.N0428.N0765.N1515.d029732 eta
    (a₀ + (p.1 : ℝ) * hA, b₀ + (p.2 : ℝ) * hB)


def d029740 (hA hB a₀ b₀ : ℝ) (NA NB : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1518.d029721 hA a₀ NA *
      (_root_.GD.N0106.N0428.N0765.N1518.d029720 hB b₀ NB +
        _root_.GD.N0106.N0428.N0765.N1518.d029722 hB b₀ NB) +
    _root_.GD.N0106.N0428.N0765.N1518.d029719 hA a₀ NA *
      _root_.GD.N0106.N0428.N0765.N1518.d029722 hB b₀ NB

theorem d029741 {eta : ℝ} (heta : 0 < eta) : 0 < _root_.GD.N0106.N0428.N0765.N1515.d029729 eta := by
  unfold _root_.GD.N0106.N0428.N0765.N1515.d029729
  positivity

theorem d029742 (eta : ℝ) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029220 eta q = _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029732 eta q := rfl

theorem d029743 (eta : ℝ) (z w : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029218 eta z w = (_root_.GD.N0106.N0428.N0765.N1515.d029729 eta : ℂ) * _root_.GD.N0106.N0428.N0765.N1515.d029733 eta z w := rfl

theorem d029744 (eta α β : ℝ) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β q = (_root_.GD.N0106.N0428.N0765.N1515.d029729 eta : ℂ) * _root_.GD.N0106.N0428.N0765.N1515.d029734 eta α β q := rfl

theorem d029745 (eta α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β = _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029736 eta α β := by
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029223 _root_.GD.N0106.N0428.N0765.N1516.d029221 _root_.GD.N0106.N0428.N0765.N1515.d029729 _root_.GD.N0106.N0428.N0765.N1515.d029736 _root_.GD.N0106.N0428.N0765.N1515.d029735
  ring

theorem d029746 (eta hA hB a₀ b₀ : ℝ) (p : ℤ × ℤ) :
    _root_.GD.N0106.N0428.N0765.N1518.d029723 eta hA hB a₀ b₀ p =
      _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029739 eta hA hB a₀ b₀ p := by
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029723 _root_.GD.N0106.N0428.N0765.N1515.d029739
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029742]
  ring

theorem d029747 (eta hA hB a₀ b₀ : ℝ) (NA NB : ℕ) :
    _root_.GD.N0106.N0428.N0765.N1518.d029724 eta hA hB a₀ b₀ NA NB =
      _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029740 hA hB a₀ b₀ NA NB := rfl

theorem d029748 (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta = _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029730 location eta := by
  unfold _root_.GD.N0106.N0428.N0765.N1515.d029730
  field_simp [(_root_.GD.N0106.N0428.N0765.N1515.d029741 heta).ne']

theorem d029749 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029220 eta q / _root_.GD.N0106.N0428.N0765.N1515.d029729 eta = _root_.GD.N0106.N0428.N0765.N1515.d029732 eta q := by
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029742]
  field_simp [(_root_.GD.N0106.N0428.N0765.N1515.d029741 heta).ne']

theorem d029750 {eta : ℝ} (heta : 0 < eta) (α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β / _root_.GD.N0106.N0428.N0765.N1515.d029729 eta = _root_.GD.N0106.N0428.N0765.N1515.d029736 eta α β := by
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029745]
  field_simp [(_root_.GD.N0106.N0428.N0765.N1515.d029741 heta).ne']

theorem d029751 {eta : ℝ} (heta : 0 < eta)
    (hA hB a₀ b₀ : ℝ) (NA NB : ℕ) :
    _root_.GD.N0106.N0428.N0765.N1518.d029724 eta hA hB a₀ b₀ NA NB / _root_.GD.N0106.N0428.N0765.N1515.d029729 eta =
      _root_.GD.N0106.N0428.N0765.N1515.d029740 hA hB a₀ b₀ NA NB := by
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029747]
  field_simp [(_root_.GD.N0106.N0428.N0765.N1515.d029741 heta).ne']

theorem d029752 {eta : ℝ} (heta : 0 < eta) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1515.d029732 eta) := _root_.GD.N0106.N0428.N0765.N1521.d020876 eta heta


theorem d029753 (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (∫ q, _root_.GD.N0106.N0428.N0765.N1515.d029732 eta q) = _root_.GD.N0106.N0428.N0765.N1515.d029730 location eta := by
  have h := _root_.GD.N0106.N0428.N0765.N1516.d029239 location heta
  simp only [_root_.GD.N0106.N0428.N0765.N1515.d029742, integral_const_mul] at h
  unfold _root_.GD.N0106.N0428.N0765.N1515.d029730
  exact (eq_div_iff (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta).ne').2 (by simpa only [mul_comm] using h)

theorem d029754 (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1515.d029730 location eta = 11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta / (1 + eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1515.d029730 _root_.GD.N0106.N0428.N0765.N1515.d029729
  field_simp [show (1 + eta : ℝ) ≠ 0 by positivity]
  <;> ring


theorem d029755 (location x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1515.d029731 x = 11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp x) / (1 + Real.exp x) := by
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029731, _root_.GD.N0106.N0428.N0765.N1535.d021163 location x, Complex.ofReal_re]

theorem d029756 (location x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1515.d029730 location (Real.exp x) = _root_.GD.N0106.N0428.N0765.N1515.d029731 x := by
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029754 location (Real.exp_pos x), _root_.GD.N0106.N0428.N0765.N1515.d029755 location x]

theorem d029757 (x : ℝ) :
    (∫ q, _root_.GD.N0106.N0428.N0765.N1515.d029732 (Real.exp x) q) = _root_.GD.N0106.N0428.N0765.N1515.d029731 x := by
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029753 0 (Real.exp_pos x), _root_.GD.N0106.N0428.N0765.N1515.d029756]

theorem d029758 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1515.d029733 eta (q.1 : ℂ) (q.2 : ℂ) = (_root_.GD.N0106.N0428.N0765.N1515.d029732 eta q : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029733, _root_.GD.N0106.N0428.N0765.N1512.d029185 heta, _root_.GD.N0106.N0428.N0765.N1516.d029236,
    ← _root_.GD.N0106.N0428.N0765.N1680.d021562 heta q, _root_.GD.N0106.N0428.N0765.N1585.d005530, _root_.GD.N0106.N0428.N0765.N1585.d005530]
  unfold _root_.GD.N0106.N0428.N0765.N1515.d029732 _root_.GD.N0106.N0428.N0765.N1521.d020868 _root_.GD.N0106.N0428.N0765.N1529.d020802
  push_cast
  ring

theorem d029759 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1515.d029732 eta q‖ ≤ _root_.GD.N0106.N0428.N0765.N1521.d020868 q := by
  have h := _root_.GD.N0106.N0428.N0765.N1516.d029244 heta q
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029742, norm_mul, Real.norm_eq_abs,
    abs_of_pos (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta)] at h
  exact (mul_le_mul_iff_right₀ (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta)).mp h


theorem d029760 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ q, ‖_root_.GD.N0106.N0428.N0765.N1515.d029734 eta α β q‖) ≤ _root_.GD.N0106.N0428.N0765.N1515.d029736 eta α β := by
  have h := _root_.GD.N0106.N0428.N0765.N1516.d029233 heta hs
  simp only [_root_.GD.N0106.N0428.N0765.N1515.d029744, norm_mul,
    Complex.norm_of_nonneg (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta).le, integral_const_mul,
    _root_.GD.N0106.N0428.N0765.N1515.d029745] at h
  exact (mul_le_mul_iff_right₀ (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta)).mp h


theorem d029761 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1515.d029734 eta α β q‖ ≤ _root_.GD.N0106.N0428.N0765.N1515.d029737 α β * _root_.GD.N0106.N0428.N0765.N1521.d020868 q := by
  obtain ⟨hα, hβ⟩ := _root_.GD.N0106.N0428.N0765.N1537.d021535 hs
  have hp : _root_.GD.N0106.N0428.N0765.N1677.d028882 (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1550.d005477] using hs
  have ho := _root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta
  have h := _root_.GD.N0106.N0428.N0765.N1585.d005546 heta
    (show |(_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α).im| < Real.pi / 2 by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hα)
    (show |(_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β).im| < Real.pi / 2 by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hβ)
    (_root_.GD.N0106.N0428.N0765.N1512.d029184 heta hp) ho.1 ho.2
  change ‖_root_.GD.N0106.N0428.N0765.N1515.d029734 eta α β q‖ ≤ _ at h
  apply h.trans_eq
  simp only [_root_.GD.N0106.N0428.N0765.N1550.d005476, _root_.GD.N0106.N0428.N0765.N1550.d005477]
  unfold _root_.GD.N0106.N0428.N0765.N1515.d029737 _root_.GD.N0106.N0428.N0765.N1521.d020868
  ring


theorem d029762 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1515.d029736 eta α β ≤ _root_.GD.N0106.N0428.N0765.N1515.d029737 α β := by
  obtain ⟨hα, hβ⟩ := _root_.GD.N0106.N0428.N0765.N1537.d021535 hs
  have ho := _root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta
  have hg : 0 ≤ (Real.cos (β / 2))⁻¹ := inv_nonneg.mpr (_root_.GD.N0106.N0428.N0765.N1585.d005527 hβ).le
  have hK : 0 ≤ _root_.GD.N0106.N0428.N0765.N1512.d029183 α β := inv_nonneg.mpr (_root_.GD.N0106.N0428.N0765.N1538.d021232 hs).le
  have h1 := pow_le_pow_left₀ (add_nonneg hg ho.1)
    (add_le_add le_rfl ho.2) 2
  have h2 := pow_le_pow_left₀ (add_nonneg hK ho.1)
    (add_le_add le_rfl ho.2) 2
  have hρ : 0 ≤ Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) *
      Real.cos (β / 2) ^ (-(10 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1585.d005527 hα).le _)
      (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1585.d005527 hβ).le _)
  exact mul_le_mul_of_nonneg_right (add_le_add h1 h2) hρ

theorem d029763 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ q, ‖_root_.GD.N0106.N0428.N0765.N1515.d029734 eta α β q‖) ≤ _root_.GD.N0106.N0428.N0765.N1515.d029737 α β :=
  (_root_.GD.N0106.N0428.N0765.N1515.d029760 heta hs).trans (_root_.GD.N0106.N0428.N0765.N1515.d029762 heta hs)


theorem d029764 (location : ℝ) {eta h d0 d1 : ℝ}
    (heta : 0 < eta) (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi) (a₀ b₀ : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1515.d029730 location eta -
      h ^ 2 * (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1515.d029732 eta (a₀ + h * p.1, b₀ + h * p.2))| ≤
      _root_.GD.N0106.N0428.N0765.N1515.d029738 eta h d0 d1 := by
  have hp := _root_.GD.N0106.N0428.N0765.N1517.d029382 location
    heta hh hd0 hd1 haxis hmixed a₀ b₀
  simp only [_root_.GD.N0106.N0428.N0765.N1515.d029742, tsum_mul_left, _root_.GD.N0106.N0428.N0765.N1515.d029745] at hp
  rw [_root_.GD.N0106.N0428.N0765.N1515.d029748 location heta] at hp
  have hL :
      |_root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029730 location eta -
        h ^ 2 * (_root_.GD.N0106.N0428.N0765.N1515.d029729 eta * (∑' p : ℤ × ℤ,
          _root_.GD.N0106.N0428.N0765.N1515.d029732 eta (a₀ + h * p.1, b₀ + h * p.2)))| =
      _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * |_root_.GD.N0106.N0428.N0765.N1515.d029730 location eta -
        h ^ 2 * (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1515.d029732 eta (a₀ + h * p.1, b₀ + h * p.2))| := by
    rw [show _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029730 location eta -
        h ^ 2 * (_root_.GD.N0106.N0428.N0765.N1515.d029729 eta * (∑' p : ℤ × ℤ,
          _root_.GD.N0106.N0428.N0765.N1515.d029732 eta (a₀ + h * p.1, b₀ + h * p.2))) =
        _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * (_root_.GD.N0106.N0428.N0765.N1515.d029730 location eta -
          h ^ 2 * (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1515.d029732 eta (a₀ + h * p.1, b₀ + h * p.2))) by ring,
      abs_mul, abs_of_pos (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta)]
  have hB :
      (2 * (_root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029736 eta d0 0) + 2 * (_root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029736 eta 0 d0)) /
          (Real.exp (2 * Real.pi * d0 / h) - 1) +
        4 * (_root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029736 eta d1 d1) /
          (Real.exp (2 * Real.pi * d1 / h) - 1) ^ 2 =
      _root_.GD.N0106.N0428.N0765.N1515.d029729 eta * _root_.GD.N0106.N0428.N0765.N1515.d029738 eta h d0 d1 := by
    unfold _root_.GD.N0106.N0428.N0765.N1515.d029738
    ring
  rw [hL, hB] at hp
  exact (mul_le_mul_iff_right₀ (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta)).mp hp


theorem d029765 {eta hA hB : ℝ} (heta : 0 < eta)
    (hhA : 0 < hA) (hhB : 0 < hB) (a₀ b₀ : ℝ) (NA NB : ℕ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1515.d029739 eta hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB,
        _root_.GD.N0106.N0428.N0765.N1515.d029739 eta hA hB a₀ b₀ p‖ ≤ _root_.GD.N0106.N0428.N0765.N1515.d029740 hA hB a₀ b₀ NA NB := by
  have ht := _root_.GD.N0106.N0428.N0765.N1518.d029726 heta hhA hhB a₀ b₀ NA NB
  simp only [_root_.GD.N0106.N0428.N0765.N1515.d029746, tsum_mul_left, ← Finset.mul_sum,
    _root_.GD.N0106.N0428.N0765.N1515.d029747] at ht
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta)] at ht
  exact (mul_le_mul_iff_right₀ (_root_.GD.N0106.N0428.N0765.N1515.d029741 heta)).mp ht

theorem d029766 (eta h a₀ b₀ : ℝ) :
    (∑' p, _root_.GD.N0106.N0428.N0765.N1515.d029739 eta h h a₀ b₀ p) =
      h ^ 2 * (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1515.d029732 eta (a₀ + h * p.1, b₀ + h * p.2)) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1515.d029739, tsum_mul_left, pow_two, mul_comm h]


theorem d029767 (location : ℝ) {eta h d0 d1 : ℝ}
    (heta : 0 < eta) (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi)
    (a₀ b₀ : ℝ) (NA NB : ℕ) :
    |_root_.GD.N0106.N0428.N0765.N1515.d029730 location eta -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB,
        _root_.GD.N0106.N0428.N0765.N1515.d029739 eta h h a₀ b₀ p| ≤
      _root_.GD.N0106.N0428.N0765.N1515.d029738 eta h d0 d1 + _root_.GD.N0106.N0428.N0765.N1515.d029740 h h a₀ b₀ NA NB := by
  have hp := _root_.GD.N0106.N0428.N0765.N1515.d029764 location heta hh hd0 hd1 haxis hmixed a₀ b₀
  rw [← _root_.GD.N0106.N0428.N0765.N1515.d029766] at hp
  have ht := _root_.GD.N0106.N0428.N0765.N1515.d029765 heta hh hh a₀ b₀ NA NB
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (_root_.GD.N0106.N0428.N0765.N1515.d029730 location eta)
    (∑' p, _root_.GD.N0106.N0428.N0765.N1515.d029739 eta h h a₀ b₀ p)
    (∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB,
      _root_.GD.N0106.N0428.N0765.N1515.d029739 eta h h a₀ b₀ p)
  simp only [Real.norm_eq_abs] at ht htriangle
  exact htriangle.trans (add_le_add hp ht)

theorem d029768 (x : ℝ) {h d0 d1 : ℝ}
    (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi) (a₀ b₀ : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1515.d029731 x - h ^ 2 * (∑' p : ℤ × ℤ,
      _root_.GD.N0106.N0428.N0765.N1515.d029732 (Real.exp x) (a₀ + h * p.1, b₀ + h * p.2))| ≤
      _root_.GD.N0106.N0428.N0765.N1515.d029738 (Real.exp x) h d0 d1 := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1515.d029756] using
    _root_.GD.N0106.N0428.N0765.N1515.d029764 0 (Real.exp_pos x) hh hd0 hd1 haxis hmixed a₀ b₀

theorem d029769 (x : ℝ) {h d0 d1 : ℝ}
    (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi)
    (a₀ b₀ : ℝ) (NA NB : ℕ) :
    |_root_.GD.N0106.N0428.N0765.N1515.d029731 x -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB,
        _root_.GD.N0106.N0428.N0765.N1515.d029739 (Real.exp x) h h a₀ b₀ p| ≤
      _root_.GD.N0106.N0428.N0765.N1515.d029738 (Real.exp x) h d0 d1 + _root_.GD.N0106.N0428.N0765.N1515.d029740 h h a₀ b₀ NA NB := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1515.d029756] using
    _root_.GD.N0106.N0428.N0765.N1515.d029767 0 (Real.exp_pos x)
      hh hd0 hd1 haxis hmixed a₀ b₀ NA NB

end
end GD.N0106.N0428.N0765.N1515

#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029753
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029757
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029761
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029762
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029763
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029764
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029765
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029767
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029768
#print axioms _root_.GD.N0106.N0428.N0765.N1515.d029769
