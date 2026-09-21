import GD.Module0367
import GD.Module1288
import Mathlib.Tactic















set_option autoImplicit false
set_option warningAsError true

open Finset

namespace GD.N0106.N0428.N0765.N1569
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1568 _root_.GD.N0106.N0428.N0765.N1616

theorem d021036 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (c : ℝ) : v ≤ _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956
  have h1 : 0 ≤ (v + eta * w + (1 + eta) * u) * Real.exp c := by positivity
  have h2 : 0 ≤ eta * w * Real.exp c ^ 2 := by positivity
  linarith

theorem d021037 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (c : ℝ) : eta * w * Real.exp c ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956
  have h1 : 0 ≤ (v + eta * w + (1 + eta) * u) * Real.exp c := by positivity
  linarith

theorem d021038 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (c : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020957
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))
    (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c).le _)

theorem d021039 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (c : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020958
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))
    (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c).le _)


theorem d021040 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2)) ≤ v ^ (-((21 : ℝ) / 2)) :=
  Real.rpow_le_rpow_of_nonpos hv (_root_.GD.N0106.N0428.N0765.N1569.d021036 heta hu hv hw c) (by norm_num)

theorem d021041 (c : ℝ) : Real.exp c ^ 2 = Real.exp (2 * c) := by
  rw [← Real.exp_nat_mul]
  norm_num


theorem d021042 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2)) ≤
      (eta * w) ^ (-((21 : ℝ) / 2)) * Real.exp (-(21 * c)) := by
  have hew : 0 < eta * w := mul_pos heta hw
  have h : _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2)) ≤
      (eta * w * Real.exp c ^ 2) ^ (-((21 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (_root_.GD.N0106.N0428.N0765.N1569.d021037 heta hu hv hw c) (by norm_num)
  rw [Real.mul_rpow hew.le (by positivity), _root_.GD.N0106.N0428.N0765.N1569.d021041, ← Real.exp_mul] at h
  rw [show -(21 * c) = 2 * c * -(21 / 2) by ring]
  exact h


theorem d021043 {c cR : ℝ} (hc : cR ≤ c) :
    1 + Real.exp c ≤ (1 + Real.exp (-cR)) * Real.exp c := by
  have h1 : Real.exp (-c) * Real.exp c = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (-c) * Real.exp c ≤ Real.exp (-cR) * Real.exp c :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos c).le
  rw [h1] at h2
  linarith

theorem d021044 (c : ℝ) : Real.exp c ^ 10 = Real.exp (10 * c) := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem d021045 (c : ℝ) : Real.exp c ^ 9 = Real.exp (9 * c) := by
  rw [← Real.exp_nat_mul]
  norm_num


theorem d021046 {eta u v w c cL : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (hc : c ≤ cL) :
    _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c ≤
      (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp cL) ^ 10) * Real.exp (11 / 2 * c) := by
  have hpow : (1 + Real.exp c) ^ 10 ≤ (1 + Real.exp cL) ^ 10 :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.exp_le_exp.mpr hc]) 10
  have h11 : Real.exp (11 * c / 2) = Real.exp (11 / 2 * c) := by
    congr 1
    ring
  calc _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c
      = Real.exp (11 * c / 2) * (1 + Real.exp c) ^ 10 *
          _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2)) := rfl
    _ ≤ Real.exp (11 * c / 2) * (1 + Real.exp cL) ^ 10 * v ^ (-((21 : ℝ) / 2)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
          (_root_.GD.N0106.N0428.N0765.N1569.d021040 heta hu hv hw c)
          (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c).le _) (by positivity)
    _ = (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp cL) ^ 10) * Real.exp (11 / 2 * c) := by
        rw [h11]
        ring


theorem d021047 {eta u v w c cR : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (hc : cR ≤ c) :
    _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c ≤
      ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-cR)) ^ 10) *
        Real.exp (-(11 / 2 * c)) := by
  have hpow : (1 + Real.exp c) ^ 10 ≤ (1 + Real.exp (-cR)) ^ 10 * Real.exp (10 * c) := by
    have h := pow_le_pow_left₀ (by positivity) (_root_.GD.N0106.N0428.N0765.N1569.d021043 hc) 10
    rw [mul_pow, _root_.GD.N0106.N0428.N0765.N1569.d021044] at h
    exact h
  have hexp : Real.exp (-(11 / 2 * c)) =
      Real.exp (11 * c / 2) * Real.exp (10 * c) * Real.exp (-(21 * c)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c
      = Real.exp (11 * c / 2) * (1 + Real.exp c) ^ 10 *
          _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2)) := rfl
    _ ≤ Real.exp (11 * c / 2) * ((1 + Real.exp (-cR)) ^ 10 * Real.exp (10 * c)) *
          ((eta * w) ^ (-((21 : ℝ) / 2)) * Real.exp (-(21 * c))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
          (_root_.GD.N0106.N0428.N0765.N1569.d021042 heta hu hv hw c)
          (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c).le _) (by positivity)
    _ = ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-cR)) ^ 10) *
          Real.exp (-(11 / 2 * c)) := by
        rw [hexp]
        ring


theorem d021048 {eta u v w c cL : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (hc : c ≤ cL) :
    _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c ≤
      (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp cL) ^ 9) * Real.exp (13 / 2 * c) := by
  have hpow : (1 + Real.exp c) ^ 9 ≤ (1 + Real.exp cL) ^ 9 :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.exp_le_exp.mpr hc]) 9
  have h13 : Real.exp (13 * c / 2) = Real.exp (13 / 2 * c) := by
    congr 1
    ring
  calc _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c
      = Real.exp (13 * c / 2) * (1 + Real.exp c) ^ 9 *
          _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2)) := rfl
    _ ≤ Real.exp (13 * c / 2) * (1 + Real.exp cL) ^ 9 * v ^ (-((21 : ℝ) / 2)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
          (_root_.GD.N0106.N0428.N0765.N1569.d021040 heta hu hv hw c)
          (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c).le _) (by positivity)
    _ = (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp cL) ^ 9) * Real.exp (13 / 2 * c) := by
        rw [h13]
        ring


theorem d021049 {eta u v w c cR : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (hc : cR ≤ c) :
    _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c ≤
      ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-cR)) ^ 9) *
        Real.exp (-(11 / 2 * c)) := by
  have hpow : (1 + Real.exp c) ^ 9 ≤ (1 + Real.exp (-cR)) ^ 9 * Real.exp (9 * c) := by
    have h := pow_le_pow_left₀ (by positivity) (_root_.GD.N0106.N0428.N0765.N1569.d021043 hc) 9
    rw [mul_pow, _root_.GD.N0106.N0428.N0765.N1569.d021045] at h
    exact h
  have hexp : Real.exp (-(11 / 2 * c)) =
      Real.exp (13 * c / 2) * Real.exp (9 * c) * Real.exp (-(21 * c)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c
      = Real.exp (13 * c / 2) * (1 + Real.exp c) ^ 9 *
          _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2)) := rfl
    _ ≤ Real.exp (13 * c / 2) * ((1 + Real.exp (-cR)) ^ 9 * Real.exp (9 * c)) *
          ((eta * w) ^ (-((21 : ℝ) / 2)) * Real.exp (-(21 * c))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)
          (_root_.GD.N0106.N0428.N0765.N1569.d021042 heta hu hv hw c)
          (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c).le _) (by positivity)
    _ = ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-cR)) ^ 9) *
          Real.exp (-(11 / 2 * c)) := by
        rw [hexp]
        ring


theorem d021050 {eta u v w cL h : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (hh : 0 < h) :
    Summable (fun m : ℕ => h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)) ∧
      ∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m) ≤
        _root_.GD.N0106.N0428.N0765.N1568.d005509 h (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp cL) ^ 10) (11 / 2) cL :=
  _root_.GD.N0106.N0428.N0765.N1568.d005519 (by norm_num) hh (fun m => _root_.GD.N0106.N0428.N0765.N1569.d021038 heta hu hv hw _)
    (fun m => _root_.GD.N0106.N0428.N0765.N1569.d021046 heta hu hv hw (_root_.GD.N0106.N0428.N0765.N1568.d005513 cL hh.le m))


theorem d021051 {eta u v w cL h : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (hh : 0 < h) :
    Summable (fun m : ℕ => h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)) ∧
      ∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m) ≤
        _root_.GD.N0106.N0428.N0765.N1568.d005509 h (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp cL) ^ 9) (13 / 2) cL :=
  _root_.GD.N0106.N0428.N0765.N1568.d005519 (by norm_num) hh (fun m => _root_.GD.N0106.N0428.N0765.N1569.d021039 heta hu hv hw _)
    (fun m => _root_.GD.N0106.N0428.N0765.N1569.d021048 heta hu hv hw (_root_.GD.N0106.N0428.N0765.N1568.d005513 cL hh.le m))


theorem d021052 {eta u v w cR h : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (hh : 0 < h) :
    Summable (fun m : ℕ => h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)) ∧
      ∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m) ≤
        _root_.GD.N0106.N0428.N0765.N1568.d005510 h ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-cR)) ^ 10)
          (11 / 2) cR :=
  _root_.GD.N0106.N0428.N0765.N1568.d005520 (by norm_num) hh (fun m => _root_.GD.N0106.N0428.N0765.N1569.d021038 heta hu hv hw _)
    (fun m => _root_.GD.N0106.N0428.N0765.N1569.d021047 heta hu hv hw (_root_.GD.N0106.N0428.N0765.N1568.d005514 cR hh.le m))


theorem d021053 {eta u v w cR h : ℝ} (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) (hh : 0 < h) :
    Summable (fun m : ℕ => h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)) ∧
      ∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m) ≤
        _root_.GD.N0106.N0428.N0765.N1568.d005510 h ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-cR)) ^ 9)
          (11 / 2) cR :=
  _root_.GD.N0106.N0428.N0765.N1568.d005520 (by norm_num) hh (fun m => _root_.GD.N0106.N0428.N0765.N1569.d021039 heta hu hv hw _)
    (fun m => _root_.GD.N0106.N0428.N0765.N1569.d021049 heta hu hv hw (_root_.GD.N0106.N0428.N0765.N1568.d005514 cR hh.le m))


theorem d021054 {eta u v w c₀ h I ε Sm Sp : ℝ} {N : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (hh : 0 < h)
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : |I - ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (k : ℝ) * h)| ≤ ε * I)
    (hSm : Sm ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h))
    (hSp : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp) :
    Sm / (1 + ε) ≤ I ∧
      I ≤ (Sp +
        (_root_.GD.N0106.N0428.N0765.N1568.d005509 h (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (c₀ - h)) ^ 10) (11 / 2)
            (c₀ - h) +
          _root_.GD.N0106.N0428.N0765.N1568.d005510 h
            ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-(c₀ + N * h))) ^ 10) (11 / 2)
            (c₀ + N * h))) / (1 - ε) :=
  _root_.GD.N0106.N0428.N0765.N1568.d005525 (_root_.GD.N0106.N0428.N0765.N1569.d021038 heta hu hv hw) hh.le
    (_root_.GD.N0106.N0428.N0765.N1569.d021050 heta hu hv hw hh).1 (_root_.GD.N0106.N0428.N0765.N1569.d021050 heta hu hv hw hh).2
    (_root_.GD.N0106.N0428.N0765.N1569.d021052 heta hu hv hw hh).1 (_root_.GD.N0106.N0428.N0765.N1569.d021052 heta hu hv hw hh).2
    hε hε1 hrel hSm hSp


theorem d021055 {eta u v w c₀ h I ε Sm Sp : ℝ} {N : ℕ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (hh : 0 < h)
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : |I - ∑' k : ℤ, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (k : ℝ) * h)| ≤ ε * I)
    (hSm : Sm ≤ ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h))
    (hSp : ∑ i ∈ range N, h * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w (c₀ + (i : ℝ) * h) ≤ Sp) :
    Sm / (1 + ε) ≤ I ∧
      I ≤ (Sp +
        (_root_.GD.N0106.N0428.N0765.N1568.d005509 h (v ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (c₀ - h)) ^ 9) (13 / 2)
            (c₀ - h) +
          _root_.GD.N0106.N0428.N0765.N1568.d005510 h
            ((eta * w) ^ (-((21 : ℝ) / 2)) * (1 + Real.exp (-(c₀ + N * h))) ^ 9) (11 / 2)
            (c₀ + N * h))) / (1 - ε) :=
  _root_.GD.N0106.N0428.N0765.N1568.d005525 (_root_.GD.N0106.N0428.N0765.N1569.d021039 heta hu hv hw) hh.le
    (_root_.GD.N0106.N0428.N0765.N1569.d021051 heta hu hv hw hh).1 (_root_.GD.N0106.N0428.N0765.N1569.d021051 heta hu hv hw hh).2
    (_root_.GD.N0106.N0428.N0765.N1569.d021053 heta hu hv hw hh).1 (_root_.GD.N0106.N0428.N0765.N1569.d021053 heta hu hv hw hh).2
    hε hε1 hrel hSm hSp

end
end GD.N0106.N0428.N0765.N1569

#print axioms _root_.GD.N0106.N0428.N0765.N1569.d021046
#print axioms _root_.GD.N0106.N0428.N0765.N1569.d021047
#print axioms _root_.GD.N0106.N0428.N0765.N1569.d021050
#print axioms _root_.GD.N0106.N0428.N0765.N1569.d021053
#print axioms _root_.GD.N0106.N0428.N0765.N1569.d021054
#print axioms _root_.GD.N0106.N0428.N0765.N1569.d021055
