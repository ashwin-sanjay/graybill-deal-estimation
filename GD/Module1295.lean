import GD.Module1294
import Mathlib.Tactic

















set_option autoImplicit false
set_option warningAsError true

open Finset

namespace GD.N0106.N0428.N0765.N1619
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1568 _root_.GD.N0106.N0428.N0765.N1569 _root_.GD.N0106.N0428.N0765.N1616 _root_.GD.N0106.N0428.N0765.N1534


def d021056 (eta v w c₀ h : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1568.d005509 h (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (c₀ - h)) ^ 10) (11 / 2) (c₀ - h) +
    _root_.GD.N0106.N0428.N0765.N1568.d005510 h ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-(c₀ + N * h))) ^ 10)
      (11 / 2) (c₀ + N * h)


def d021057 (eta v w c₀ h : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1568.d005509 h (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (c₀ - h)) ^ 9) (13 / 2) (c₀ - h) +
    _root_.GD.N0106.N0428.N0765.N1568.d005510 h ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-(c₀ + N * h))) ^ 9)
      (11 / 2) (c₀ + N * h)


theorem d021058 {eta u v w c₀ h ε₀ ε₁ Sm₀ Sp₀ Sm₁ Sp₁ : ℝ} {N : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (hh : 0 < h)
    (hε₀ : 0 ≤ ε₀) (hε₀1 : ε₀ < 1) (hε₁ : 0 ≤ ε₁) (hε₁1 : ε₁ < 1)
    (hrel₀ : |(∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c) -
        ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (k : ℝ) * h)| ≤ ε₀ * ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c)
    (hrel₁ : |(∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c) -
        ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (k : ℝ) * h)| ≤ ε₁ * ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c)
    (hSm₀ : Sm₀ ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h))
    (hSp₀ : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp₀)
    (hSm₁ : Sm₁ ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h))
    (hSp₁ : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp₁)
    (hpos : 0 < Sm₀) (hnn : 0 ≤ Sm₁) :
    Sm₁ / (1 + ε₁) / ((Sp₀ + _root_.GD.N0106.N0428.N0765.N1619.d021056 eta v w c₀ h N) / (1 - ε₀)) ≤ _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w ∧
      _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w ≤
        ((Sp₁ + _root_.GD.N0106.N0428.N0765.N1619.d021057 eta v w c₀ h N) / (1 - ε₁)) / (Sm₀ / (1 + ε₀)) := by
  have h0 := _root_.GD.N0106.N0428.N0765.N1569.d021054 heta hu hv hw hh hε₀ hε₀1 hrel₀ hSm₀ hSp₀
  have h1 := _root_.GD.N0106.N0428.N0765.N1569.d021055 heta hu hv hw hh hε₁ hε₁1 hrel₁ hSm₁ hSp₁
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020964 heta hu hv hw]
  exact _root_.GD.N0106.N0428.N0765.N1568.d005524 (div_pos hpos (by linarith)) (div_nonneg hnn (by linarith)) h0 h1


theorem d021059 {eta u v w c₀ h ε₀ ε₁ Sm₀ Sp₀ Sm₁ Sp₁ : ℝ} {N : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (hh : 0 < h)
    (hε₀ : 0 ≤ ε₀) (hε₀1 : ε₀ < 1) (hε₁ : 0 ≤ ε₁) (hε₁1 : ε₁ < 1)
    (hrel₀ : |(∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c) -
        ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (k : ℝ) * h)| ≤ ε₀ * ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c)
    (hrel₁ : |(∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c) -
        ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (k : ℝ) * h)| ≤ ε₁ * ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c)
    (hSm₀ : Sm₀ ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h))
    (hSp₀ : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp₀)
    (hSm₁ : Sm₁ ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h))
    (hSp₁ : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp₁)
    (hpos : 0 < Sm₀) (hnn : 0 ≤ Sm₁) :
    max (Sm₁ / (1 + ε₁) / ((Sp₀ + _root_.GD.N0106.N0428.N0765.N1619.d021056 eta v w c₀ h N) / (1 - ε₀))) 0 ≤
        _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w ∧
      _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w ≤
        min (((Sp₁ + _root_.GD.N0106.N0428.N0765.N1619.d021057 eta v w c₀ h N) / (1 - ε₁)) / (Sm₀ / (1 + ε₀))) 1 := by
  have h := _root_.GD.N0106.N0428.N0765.N1619.d021058 heta hu hv hw hh hε₀ hε₀1 hε₁ hε₁1 hrel₀ hrel₁
    hSm₀ hSp₀ hSm₁ hSp₁ hpos hnn
  have hmem := _root_.GD.N0106.N0428.N0765.N1534.d005345 heta hu hv hw
  exact ⟨max_le h.1 hmem.1.le, le_min h.2 hmem.2.le⟩




theorem d021060 {x a b c₀ h ε₀ ε₁ Sm₀ Sp₀ Sm₁ Sp₁ : ℝ} {N : ℕ} (hh : 0 < h)
    (hε₀ : 0 ≤ ε₀) (hε₀1 : ε₀ < 1) (hε₁ : 0 ≤ ε₁) (hε₁1 : ε₁ < 1)
    (hrel₀ : |(∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 c) -
        ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
          (c₀ + (k : ℝ) * h)| ≤
        ε₀ * ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 c)
    (hrel₁ : |(∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 c) -
        ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1
          (c₀ + (k : ℝ) * h)| ≤
        ε₁ * ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 c)
    (hSm₀ : Sm₀ ≤ ∑ i ∈ range N,
        h * _root_.GD.N0106.N0428.N0765.N1616.d020957 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 (c₀ + (i : ℝ) * h))
    (hSp₀ : ∑ i ∈ range N,
        h * _root_.GD.N0106.N0428.N0765.N1616.d020957 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 (c₀ + (i : ℝ) * h)
        ≤ Sp₀)
    (hSm₁ : Sm₁ ≤ ∑ i ∈ range N,
        h * _root_.GD.N0106.N0428.N0765.N1616.d020958 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 (c₀ + (i : ℝ) * h))
    (hSp₁ : ∑ i ∈ range N,
        h * _root_.GD.N0106.N0428.N0765.N1616.d020958 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 (c₀ + (i : ℝ) * h)
        ≤ Sp₁)
    (hpos : 0 < Sm₀) (hnn : 0 ≤ Sm₁) :
    Sm₁ / (1 + ε₁) / ((Sp₀ + _root_.GD.N0106.N0428.N0765.N1619.d021056 (Real.exp x) (Real.exp b) 1 c₀ h N) / (1 - ε₀)) ≤
        _root_.GD.N0106.N0428.N0765.N1529.d020799 (Real.exp x) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ∧
      _root_.GD.N0106.N0428.N0765.N1529.d020799 (Real.exp x) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) ≤
        ((Sp₁ + _root_.GD.N0106.N0428.N0765.N1619.d021057 (Real.exp x) (Real.exp b) 1 c₀ h N) / (1 - ε₁)) / (Sm₀ / (1 + ε₀)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020968]
  exact _root_.GD.N0106.N0428.N0765.N1619.d021058 (Real.exp_pos x) (by positivity) (Real.exp_pos b) one_pos hh
    hε₀ hε₀1 hε₁ hε₁1 hrel₀ hrel₁ hSm₀ hSp₀ hSm₁ hSp₁ hpos hnn

end
end GD.N0106.N0428.N0765.N1619

#print axioms _root_.GD.N0106.N0428.N0765.N1619.d021058
#print axioms _root_.GD.N0106.N0428.N0765.N1619.d021059
#print axioms _root_.GD.N0106.N0428.N0765.N1619.d021060
