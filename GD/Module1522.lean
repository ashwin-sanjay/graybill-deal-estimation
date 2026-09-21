import GD.Module1296
import GD.Module0446







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Finset
open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1634
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1616 _root_.GD.N0106.N0428.N0765.N1545
  _root_.GD.N0106.N0428.N0765.N1562 _root_.GD.N0106.N0428.N0765.N1619

def d023648 (c : ℝ) : ℝ := 1 / (1 + Real.exp c)
def d023649 (c : ℝ) : ℝ := Real.exp c * _root_.GD.N0106.N0428.N0765.N1634.d023648 c
def d023650 (c : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1634.d023649 c * _root_.GD.N0106.N0428.N0765.N1634.d023648 c
def d023651 (eta u v w c : ℝ) : ℝ :=
  v * _root_.GD.N0106.N0428.N0765.N1634.d023648 c + eta * w * _root_.GD.N0106.N0428.N0765.N1634.d023649 c + (1 + eta) * u * _root_.GD.N0106.N0428.N0765.N1634.d023650 c
def d023652 (eta u v w c : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1634.d023650 c ^ 5 * Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023650 c) *
    (1 / (_root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w c ^ 10 * Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w c)))
def d023653 (eta u v w c : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1634.d023649 c * _root_.GD.N0106.N0428.N0765.N1634.d023652 eta u v w c

theorem d023654 (c : ℝ) : _root_.GD.N0106.N0428.N0765.N1634.d023649 c = Real.sigmoid c := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005369]
  simp only [_root_.GD.N0106.N0428.N0765.N1634.d023649, _root_.GD.N0106.N0428.N0765.N1634.d023648, mul_one_div]

theorem d023655 (c : ℝ) : _root_.GD.N0106.N0428.N0765.N1634.d023648 c = 1 - Real.sigmoid c := by
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005370]
  simp only [_root_.GD.N0106.N0428.N0765.N1634.d023648, one_div]

theorem d023656 (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1634.d023650 c = Real.sigmoid c * (1 - Real.sigmoid c) := by
  rw [_root_.GD.N0106.N0428.N0765.N1634.d023650, _root_.GD.N0106.N0428.N0765.N1634.d023654, _root_.GD.N0106.N0428.N0765.N1634.d023655]

theorem d023657 (c : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1634.d023650 c := by
  rw [_root_.GD.N0106.N0428.N0765.N1634.d023656]
  exact mul_pos (Real.sigmoid_pos c) (sub_pos.mpr (Real.sigmoid_lt_one c))

theorem d023658 (eta u v w c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w c = _root_.GD.N0106.N0428.N0765.N1534.d005328 eta u v w (Real.sigmoid c) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1634.d023651, _root_.GD.N0106.N0428.N0765.N1634.d023655, _root_.GD.N0106.N0428.N0765.N1634.d023654,
    _root_.GD.N0106.N0428.N0765.N1634.d023656, _root_.GD.N0106.N0428.N0765.N1534.d005328]
  ring

theorem d023659 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) (c : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1634.d023651 eta u v w c := by
  rw [_root_.GD.N0106.N0428.N0765.N1634.d023658]
  exact _root_.GD.N0106.N0428.N0765.N1616.d020943 heta hu hv hw
    ⟨(Real.sigmoid_pos c).le, (Real.sigmoid_lt_one c).le⟩

theorem d023660 {r : ℝ} (hr : 0 < r) :
    r ^ 5 * Real.sqrt r = r * r ^ ((9 : ℝ) / 2) := by
  calc
    r ^ 5 * Real.sqrt r = r ^ ((5 : ℝ) + 1 / 2) := by
      rw [Real.rpow_add hr, Real.rpow_ofNat, Real.sqrt_eq_rpow]
    _ = r ^ ((1 : ℝ) + 9 / 2) := by norm_num
    _ = r * r ^ ((9 : ℝ) / 2) := by rw [Real.rpow_add hr, Real.rpow_one]

theorem d023661 {r : ℝ} (hr : 0 < r) :
    1 / (r ^ 10 * Real.sqrt r) = r ^ (-((21 : ℝ) / 2)) := by
  rw [Real.rpow_neg hr.le, show (21 : ℝ) / 2 = 10 + 1 / 2 by norm_num,
    Real.rpow_add hr, Real.rpow_ofNat, ← Real.sqrt_eq_rpow, one_div]

theorem d023662 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1634.d023652 eta u v w c = _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  rw [_root_.GD.N0106.N0428.N0765.N1634.d023652, _root_.GD.N0106.N0428.N0765.N1634.d023660 (_root_.GD.N0106.N0428.N0765.N1634.d023657 c),
    _root_.GD.N0106.N0428.N0765.N1634.d023661 (_root_.GD.N0106.N0428.N0765.N1634.d023659 heta hu hv hw c),
    _root_.GD.N0106.N0428.N0765.N1634.d023656, _root_.GD.N0106.N0428.N0765.N1634.d023658]
  rw [← _root_.GD.N0106.N0428.N0765.N1616.d020962 heta hu hv hw c, _root_.GD.N0106.N0428.N0765.N1534.d005329]
  ring

theorem d023663 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1634.d023653 eta u v w c = _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  rw [_root_.GD.N0106.N0428.N0765.N1634.d023653, _root_.GD.N0106.N0428.N0765.N1634.d023654, _root_.GD.N0106.N0428.N0765.N1634.d023662 heta hu hv hw,
    ← _root_.GD.N0106.N0428.N0765.N1616.d020962 heta hu hv hw c,
    ← _root_.GD.N0106.N0428.N0765.N1616.d020963 heta hu hv hw c]
  ring

theorem d023664 {eta u v w c₀ : ℝ} (heta : 0 < eta) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) (h : ℚ) (N : ℕ) (I : ℕ → _root_.GD.N0232.N0720.N1164.d006809)
    (hI : ∀ i, i < N → (I i).d006810
      (_root_.GD.N0106.N0428.N0765.N1634.d023652 eta u v w (c₀ + (i : ℝ) * (h : ℝ)))) :
    ((_root_.GD.N0106.N0428.N0765.N1545.d006837 I N).d006817 h).d006810
      (∑ i ∈ range N, (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * (h : ℝ))) := by
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006824 h
    (_root_.GD.N0106.N0428.N0765.N1545.d006838 I
      (fun i => _root_.GD.N0106.N0428.N0765.N1634.d023652 eta u v w (c₀ + (i : ℝ) * (h : ℝ))) N hI)
  simpa only [Finset.mul_sum, _root_.GD.N0106.N0428.N0765.N1634.d023662 heta hu hv hw] using hs

theorem d023665 {eta u v w c₀ : ℝ} (heta : 0 < eta) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) (h : ℚ) (N : ℕ) (I : ℕ → _root_.GD.N0232.N0720.N1164.d006809)
    (hI : ∀ i, i < N → (I i).d006810
      (_root_.GD.N0106.N0428.N0765.N1634.d023653 eta u v w (c₀ + (i : ℝ) * (h : ℝ)))) :
    ((_root_.GD.N0106.N0428.N0765.N1545.d006837 I N).d006817 h).d006810
      (∑ i ∈ range N, (h : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * (h : ℝ))) := by
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006824 h
    (_root_.GD.N0106.N0428.N0765.N1545.d006838 I
      (fun i => _root_.GD.N0106.N0428.N0765.N1634.d023653 eta u v w (c₀ + (i : ℝ) * (h : ℝ))) N hI)
  simpa only [Finset.mul_sum, _root_.GD.N0106.N0428.N0765.N1634.d023663 heta hu hv hw] using hs

theorem d023666 {eta : ℝ} (heta : 0 < eta) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) =
      _root_.GD.N0106.N0428.N0765.N1534.d005330 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 := by
  simpa only [Real.exp_log heta] using _root_.GD.N0106.N0428.N0765.N1616.d020968 (Real.log eta) a b




theorem d023667 {eta a b c₀ d h : ℝ} {N : ℕ}
    (heta : 0 < eta) (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h)
    (hε : _root_.GD.N0106.N0428.N0765.N1562.d021061 d h < 1) (S₀ S₁ : _root_.GD.N0232.N0720.N1164.d006809)
    (hS₀ : S₀.d006810 (∑ i ∈ range N,
      h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * h)))
    (hS₁ : S₁.d006810 (∑ i ∈ range N,
      h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * h)))
    (hpos : 0 < S₀.lo) (hnn : 0 ≤ S₁.lo) :
    max ((S₁.lo : ℝ) / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d h) /
      (((S₀.hi : ℝ) + _root_.GD.N0106.N0428.N0765.N1619.d021056 eta (Real.exp b) 1 c₀ h N) / (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d h))) 0 ≤
      _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ∧
    _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ≤
      min ((((S₁.hi : ℝ) + _root_.GD.N0106.N0428.N0765.N1619.d021057 eta (Real.exp b) 1 c₀ h N) / (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d h)) /
        ((S₀.lo : ℝ) / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d h))) 1 := by
  rw [_root_.GD.N0106.N0428.N0765.N1634.d023666 heta]
  exact _root_.GD.N0106.N0428.N0765.N1562.d021068 heta (by positivity)
    (Real.exp_pos b) one_pos hd hdpi hh hε hS₀.1 hS₀.2 hS₁.1 hS₁.2
    (by exact_mod_cast hpos) (by exact_mod_cast hnn)

end
end GD.N0106.N0428.N0765.N1634

#print axioms _root_.GD.N0106.N0428.N0765.N1634.d023662
#print axioms _root_.GD.N0106.N0428.N0765.N1634.d023663
#print axioms _root_.GD.N0106.N0428.N0765.N1634.d023667
