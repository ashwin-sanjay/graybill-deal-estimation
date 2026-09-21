import GD.Module0363
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic


























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set intervalIntegral

namespace GD.N0106.N0428.N0765.N1674
open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1547
noncomputable section


def d005867 (s l : ℝ) : ℝ :=
  (l * (1 - l)) ^ ((11 : ℝ) / 2) * (1 + (s - 1) * l) ^ (-((19 : ℝ) / 2))


def d005868 (s l : ℝ) : ℝ := 11 / 2 - (4 * s + 7) * l - 3 / 2 * (s - 1) * l ^ 2

section
variable {s : ℝ}

theorem d005869 (s : ℝ) : _root_.GD.N0106.N0428.N0765.N1674.d005867 s 0 = 0 := by
  unfold _root_.GD.N0106.N0428.N0765.N1674.d005867
  simp [Real.zero_rpow (by norm_num : ((11 : ℝ) / 2) ≠ 0)]

theorem d005870 (s : ℝ) : _root_.GD.N0106.N0428.N0765.N1674.d005867 s 1 = 0 := by
  unfold _root_.GD.N0106.N0428.N0765.N1674.d005867
  simp [Real.zero_rpow (by norm_num : ((11 : ℝ) / 2) ≠ 0)]

theorem d005871 (hs : 0 < s) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (_root_.GD.N0106.N0428.N0765.N1674.d005867 s) (_root_.GD.N0106.N0428.N0765.N1547.d005449 s l * _root_.GD.N0106.N0428.N0765.N1674.d005868 s l) l := by
  have hb := _root_.GD.N0106.N0428.N0765.N1547.d005457 hs hl
  have hh : 0 ≤ l * (1 - l) := mul_nonneg hl.1 (sub_nonneg.mpr hl.2)
  have h1 : HasDerivAt (fun l : ℝ => l * (1 - l)) (1 - 2 * l) l := by
    have h := (hasDerivAt_id l).mul ((hasDerivAt_id l).const_sub 1)
    have e : (1 : ℝ) * (1 - id l) + id l * -1 = 1 - 2 * l := by
      simp only [id_eq]
      ring
    exact h.congr_deriv e
  have h2 : HasDerivAt (fun l : ℝ => 1 + (s - 1) * l) (s - 1) l := by
    have h := ((hasDerivAt_id l).const_mul (s - 1)).const_add 1
    simpa using h
  have hp1 := h1.rpow_const (p := (11 : ℝ) / 2) (Or.inr (by norm_num))
  have hp2 := h2.rpow_const (p := -((19 : ℝ) / 2)) (Or.inl hb.ne')
  have h := hp1.mul hp2
  refine h.congr_deriv ?_
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005449 _root_.GD.N0106.N0428.N0765.N1674.d005868
  have e1 : (l * (1 - l)) ^ ((11 : ℝ) / 2 - 1) = (l * (1 - l)) ^ ((9 : ℝ) / 2) := by
    norm_num
  have e2 : (l * (1 - l)) ^ ((11 : ℝ) / 2) = (l * (1 - l)) ^ ((9 : ℝ) / 2) * (l * (1 - l)) := by
    rw [show ((11 : ℝ) / 2) = 9 / 2 + 1 by norm_num, Real.rpow_add' hh (by norm_num), Real.rpow_one]
  have e3 : (1 + (s - 1) * l) ^ (-((19 : ℝ) / 2) - 1) = (1 + (s - 1) * l) ^ (-((21 : ℝ) / 2)) := by
    norm_num
  have e4 : (1 + (s - 1) * l) ^ (-((19 : ℝ) / 2))
      = (1 + (s - 1) * l) ^ (-((21 : ℝ) / 2)) * (1 + (s - 1) * l) := by
    rw [show -((19 : ℝ) / 2) = -(21 / 2) + 1 by norm_num, Real.rpow_add hb, Real.rpow_one]
  rw [e1, e2, e3, e4]
  ring

theorem d005872 (hs : 0 < s) :
    ContinuousOn (fun l => _root_.GD.N0106.N0428.N0765.N1547.d005449 s l * _root_.GD.N0106.N0428.N0765.N1674.d005868 s l) (Icc 0 1) :=
  (_root_.GD.N0106.N0428.N0765.N1547.d005459 hs).mul (by unfold _root_.GD.N0106.N0428.N0765.N1674.d005868; fun_prop)

theorem d005873 (hs : 0 < s) :
    ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005449 s l * _root_.GD.N0106.N0428.N0765.N1674.d005868 s l = 0 := by
  have hint : IntervalIntegrable (fun l => _root_.GD.N0106.N0428.N0765.N1547.d005449 s l * _root_.GD.N0106.N0428.N0765.N1674.d005868 s l) volume 0 1 :=
    (_root_.GD.N0106.N0428.N0765.N1674.d005872 hs).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  rw [integral_eq_sub_of_hasDerivAt (f := _root_.GD.N0106.N0428.N0765.N1674.d005867 s)
    (f' := fun l => _root_.GD.N0106.N0428.N0765.N1547.d005449 s l * _root_.GD.N0106.N0428.N0765.N1674.d005868 s l)
    (fun l hl => _root_.GD.N0106.N0428.N0765.N1674.d005871 hs (by rwa [uIcc_of_le zero_le_one] at hl)) hint,
    _root_.GD.N0106.N0428.N0765.N1674.d005869, _root_.GD.N0106.N0428.N0765.N1674.d005870, sub_zero]


theorem d005874 (hs : 0 < s) :
    (8 * s + 14) * _root_.GD.N0106.N0428.N0765.N1547.d005452 s (fun l => l) + (3 * s - 3) * _root_.GD.N0106.N0428.N0765.N1547.d005452 s (fun l => l ^ 2) = 11 := by
  have hD := _root_.GD.N0106.N0428.N0765.N1547.d005462 hs
  have hk := (_root_.GD.N0106.N0428.N0765.N1547.d005459 hs).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hk1 : IntervalIntegrable (fun l => l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l) volume 0 1 :=
    (continuousOn_id.mul (_root_.GD.N0106.N0428.N0765.N1547.d005459 hs)).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hk2 : IntervalIntegrable (fun l => l ^ 2 * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l) volume 0 1 :=
    ((continuousOn_id.pow 2).mul (_root_.GD.N0106.N0428.N0765.N1547.d005459 hs)).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have h0 := _root_.GD.N0106.N0428.N0765.N1674.d005873 hs
  have hexp : (∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005449 s l * _root_.GD.N0106.N0428.N0765.N1674.d005868 s l)
      = 11 / 2 * (∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005449 s l)
        - (4 * s + 7) * (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l)
        - 3 / 2 * (s - 1) * ∫ l in (0 : ℝ)..1, l ^ 2 * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l := by
    have e : (fun l => _root_.GD.N0106.N0428.N0765.N1547.d005449 s l * _root_.GD.N0106.N0428.N0765.N1674.d005868 s l)
        = fun l => (11 / 2 * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l - (4 * s + 7) * (l * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l))
          - 3 / 2 * (s - 1) * (l ^ 2 * _root_.GD.N0106.N0428.N0765.N1547.d005449 s l) := by
      funext l
      unfold _root_.GD.N0106.N0428.N0765.N1674.d005868
      ring
    rw [e, integral_sub ((hk.const_mul _).sub (hk1.const_mul _)) (hk2.const_mul _),
      integral_sub (hk.const_mul _) (hk1.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hexp] at h0
  unfold _root_.GD.N0106.N0428.N0765.N1547.d005452
  simp only []
  field_simp
  linarith [h0]


def d005875 (r l : ℝ) : ℝ := (l * (1 - l)) ^ ((9 : ℝ) / 2) * (r + (1 - 2 * r) * l) ^ (-((21 : ℝ) / 2))


def d005876 (r : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (∫ l in (0 : ℝ)..1, φ l * _root_.GD.N0106.N0428.N0765.N1674.d005875 r l) / ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1674.d005875 r l

theorem d005877 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1674.d005875 r l = r ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1547.d005449 ((1 - r) / r) l := by
  have hs : 0 < (1 - r) / r := div_pos (by linarith) hr0
  have hc : r + (1 - 2 * r) * l = r * (1 + ((1 - r) / r - 1) * l) := by
    field_simp
    ring
  unfold _root_.GD.N0106.N0428.N0765.N1674.d005875 _root_.GD.N0106.N0428.N0765.N1547.d005449
  rw [hc, Real.mul_rpow hr0.le (_root_.GD.N0106.N0428.N0765.N1547.d005457 hs hl).le]
  ring

theorem d005878 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (φ : ℝ → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1674.d005876 r φ = _root_.GD.N0106.N0428.N0765.N1547.d005452 ((1 - r) / r) φ := by
  unfold _root_.GD.N0106.N0428.N0765.N1674.d005876 _root_.GD.N0106.N0428.N0765.N1547.d005452
  have hk : r ^ (-((21 : ℝ) / 2)) ≠ 0 := (Real.rpow_pos_of_pos hr0 _).ne'
  have hnum : (∫ l in (0 : ℝ)..1, φ l * _root_.GD.N0106.N0428.N0765.N1674.d005875 r l)
      = r ^ (-((21 : ℝ) / 2)) * ∫ l in (0 : ℝ)..1, φ l * _root_.GD.N0106.N0428.N0765.N1547.d005449 ((1 - r) / r) l := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    show φ l * _root_.GD.N0106.N0428.N0765.N1674.d005875 r l = r ^ (-((21 : ℝ) / 2)) * (φ l * _root_.GD.N0106.N0428.N0765.N1547.d005449 ((1 - r) / r) l)
    rw [_root_.GD.N0106.N0428.N0765.N1674.d005877 hr0 hr1 hl]
    ring
  have hden : (∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1674.d005875 r l)
      = r ^ (-((21 : ℝ) / 2)) * ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1547.d005449 ((1 - r) / r) l := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    exact _root_.GD.N0106.N0428.N0765.N1674.d005877 hr0 hr1 hl
  rw [hnum, hden, mul_div_mul_left _ _ hk]


theorem d005879 {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (8 + 6 * r) * _root_.GD.N0106.N0428.N0765.N1674.d005876 r (fun l => l) = 11 * r + (6 * r - 3) * _root_.GD.N0106.N0428.N0765.N1674.d005876 r (fun l => l ^ 2) := by
  rw [_root_.GD.N0106.N0428.N0765.N1674.d005878 hr0 hr1, _root_.GD.N0106.N0428.N0765.N1674.d005878 hr0 hr1]
  have hs : 0 < (1 - r) / r := div_pos (by linarith) hr0
  have h := _root_.GD.N0106.N0428.N0765.N1674.d005874 hs
  have e1 : (8 * ((1 - r) / r) + 14) = (8 + 6 * r) / r := by field_simp; ring
  have e2 : (3 * ((1 - r) / r) - 3) = (3 - 6 * r) / r := by field_simp; ring
  rw [e1, e2] at h
  field_simp at h
  linarith [h]

end

end
end GD.N0106.N0428.N0765.N1674
