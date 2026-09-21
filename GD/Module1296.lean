import GD.Module1295
import GD.Module1293
import Mathlib.Tactic










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1562
noncomputable section

open Finset MeasureTheory _root_.GD.N0106.N0428.N0765.N1616 _root_.GD.N0106.N0428.N0765.N1619 _root_.GD.N0106.N0428.N0765.N1534


def d021061 (d h : ℝ) : ℝ :=
  2 * (Real.cos d) ^ (-21 / 2 : ℝ) /
    (Real.exp (2 * Real.pi * d / h) - 1)

theorem d021062 {d h : ℝ}
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h) :
    0 < _root_.GD.N0106.N0428.N0765.N1562.d021061 d h := by
  have hc : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hdpi⟩
  have hx : 0 < 2 * Real.pi * d / h := by positivity
  have he : 0 < Real.exp (2 * Real.pi * d / h) - 1 := by
    have := Real.one_lt_exp_iff.mpr hx
    linarith
  unfold _root_.GD.N0106.N0428.N0765.N1562.d021061
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hc _)) he

theorem d021063 {d h : ℝ}
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1562.d021061 d h := (_root_.GD.N0106.N0428.N0765.N1562.d021062 hd hdpi hh).le


private theorem d021064 (f : ℝ → ℝ) (offset h : ℝ) :
    (∑' k : ℤ, h * f (offset + (k : ℝ) * h)) =
      h * (∑' k : ℤ, f (offset + h * (k : ℝ))) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  congr 1
  ring


theorem d021065 {eta u v w d h : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h) (offset : ℝ) :
    |(∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c) -
        ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (offset + (k : ℝ) * h)| ≤
      _root_.GD.N0106.N0428.N0765.N1562.d021061 d h * ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  have hp := _root_.GD.N0106.N0428.N0765.N1561.d021034
    heta hu hv hw hd hdpi hh offset
  rw [← _root_.GD.N0106.N0428.N0765.N1562.d021064 (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w) offset h] at hp
  rw [abs_sub_comm]
  simpa only [_root_.GD.N0106.N0428.N0765.N1562.d021061] using hp


theorem d021066 {eta u v w d h : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h) (offset : ℝ) :
    |(∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c) -
        ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (offset + (k : ℝ) * h)| ≤
      _root_.GD.N0106.N0428.N0765.N1562.d021061 d h * ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  have hp := _root_.GD.N0106.N0428.N0765.N1561.d021035
    heta hu hv hw hd hdpi hh offset
  rw [← _root_.GD.N0106.N0428.N0765.N1562.d021064 (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w) offset h] at hp
  rw [abs_sub_comm]
  simpa only [_root_.GD.N0106.N0428.N0765.N1562.d021061] using hp


theorem d021067
    {eta u v w c₀ d h Sm₀ Sp₀ Sm₁ Sp₁ : ℝ} {N : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h)
    (hε : _root_.GD.N0106.N0428.N0765.N1562.d021061 d h < 1)
    (hSm₀ : Sm₀ ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h))
    (hSp₀ : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp₀)
    (hSm₁ : Sm₁ ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h))
    (hSp₁ : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp₁)
    (hpos : 0 < Sm₀) (hnn : 0 ≤ Sm₁) :
    Sm₁ / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d h) /
        ((Sp₀ + _root_.GD.N0106.N0428.N0765.N1619.d021056 eta v w c₀ h N) / (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d h)) ≤
      _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w ∧
    _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w ≤
      ((Sp₁ + _root_.GD.N0106.N0428.N0765.N1619.d021057 eta v w c₀ h N) / (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d h)) /
        (Sm₀ / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d h)) := by
  exact _root_.GD.N0106.N0428.N0765.N1619.d021058
    heta hu hv hw hh
    (_root_.GD.N0106.N0428.N0765.N1562.d021063 hd hdpi hh) hε
    (_root_.GD.N0106.N0428.N0765.N1562.d021063 hd hdpi hh) hε
    (_root_.GD.N0106.N0428.N0765.N1562.d021065 heta hu hv hw hd hdpi hh c₀)
    (_root_.GD.N0106.N0428.N0765.N1562.d021066 heta hu hv hw hd hdpi hh c₀)
    hSm₀ hSp₀ hSm₁ hSp₁ hpos hnn


theorem d021068
    {eta u v w c₀ d h Sm₀ Sp₀ Sm₁ Sp₁ : ℝ} {N : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h)
    (hε : _root_.GD.N0106.N0428.N0765.N1562.d021061 d h < 1)
    (hSm₀ : Sm₀ ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h))
    (hSp₀ : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp₀)
    (hSm₁ : Sm₁ ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h))
    (hSp₁ : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp₁)
    (hpos : 0 < Sm₀) (hnn : 0 ≤ Sm₁) :
    max (Sm₁ / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d h) /
      ((Sp₀ + _root_.GD.N0106.N0428.N0765.N1619.d021056 eta v w c₀ h N) / (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d h))) 0 ≤
      _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w ∧
    _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w ≤
      min (((Sp₁ + _root_.GD.N0106.N0428.N0765.N1619.d021057 eta v w c₀ h N) / (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d h)) /
        (Sm₀ / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d h))) 1 := by
  exact _root_.GD.N0106.N0428.N0765.N1619.d021059
    heta hu hv hw hh
    (_root_.GD.N0106.N0428.N0765.N1562.d021063 hd hdpi hh) hε
    (_root_.GD.N0106.N0428.N0765.N1562.d021063 hd hdpi hh) hε
    (_root_.GD.N0106.N0428.N0765.N1562.d021065 heta hu hv hw hd hdpi hh c₀)
    (_root_.GD.N0106.N0428.N0765.N1562.d021066 heta hu hv hw hd hdpi hh c₀)
    hSm₀ hSp₀ hSm₁ hSp₁ hpos hnn



theorem d021069
    {x a b c₀ d h Sm₀ Sp₀ Sm₁ Sp₁ : ℝ} {N : ℕ}
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h)
    (hε : _root_.GD.N0106.N0428.N0765.N1562.d021061 d h < 1)
    (hSm₀ : Sm₀ ≤ ∑ i ∈ range N,
      h * _root_.GD.N0106.N0428.N0765.N1616.d020957 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * h))
    (hSp₀ : ∑ i ∈ range N,
      h * _root_.GD.N0106.N0428.N0765.N1616.d020957 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * h) ≤ Sp₀)
    (hSm₁ : Sm₁ ≤ ∑ i ∈ range N,
      h * _root_.GD.N0106.N0428.N0765.N1616.d020958 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * h))
    (hSp₁ : ∑ i ∈ range N,
      h * _root_.GD.N0106.N0428.N0765.N1616.d020958 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
        (c₀ + (i : ℝ) * h) ≤ Sp₁)
    (hpos : 0 < Sm₀) (hnn : 0 ≤ Sm₁) :
    Sm₁ / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d h) /
        ((Sp₀ + _root_.GD.N0106.N0428.N0765.N1619.d021056 (Real.exp x) (Real.exp b) 1 c₀ h N) / (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d h)) ≤
      _root_.GD.N0106.N0428.N0765.N1529.d020799 (Real.exp x) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ∧
    _root_.GD.N0106.N0428.N0765.N1529.d020799 (Real.exp x) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ≤
      ((Sp₁ + _root_.GD.N0106.N0428.N0765.N1619.d021057 (Real.exp x) (Real.exp b) 1 c₀ h N) / (1 - _root_.GD.N0106.N0428.N0765.N1562.d021061 d h)) /
        (Sm₀ / (1 + _root_.GD.N0106.N0428.N0765.N1562.d021061 d h)) := by
  exact _root_.GD.N0106.N0428.N0765.N1619.d021060 hh
    (_root_.GD.N0106.N0428.N0765.N1562.d021063 hd hdpi hh) hε
    (_root_.GD.N0106.N0428.N0765.N1562.d021063 hd hdpi hh) hε
    (_root_.GD.N0106.N0428.N0765.N1562.d021065 (Real.exp_pos x) (by positivity) (Real.exp_pos b)
      one_pos hd hdpi hh c₀)
    (_root_.GD.N0106.N0428.N0765.N1562.d021066 (Real.exp_pos x) (by positivity) (Real.exp_pos b)
      one_pos hd hdpi hh c₀)
    hSm₀ hSp₀ hSm₁ hSp₁ hpos hnn

end
end GD.N0106.N0428.N0765.N1562

#print axioms _root_.GD.N0106.N0428.N0765.N1562.d021065
#print axioms _root_.GD.N0106.N0428.N0765.N1562.d021066
#print axioms _root_.GD.N0106.N0428.N0765.N1562.d021062
#print axioms _root_.GD.N0106.N0428.N0765.N1562.d021067
#print axioms _root_.GD.N0106.N0428.N0765.N1562.d021068
#print axioms _root_.GD.N0106.N0428.N0765.N1562.d021069
