import GD.Module0884

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0055
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441

theorem d022111 (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (s : ℝ) :
    (q ^ n) ^ s = q ^ ((n : ℝ) * s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]

theorem d022112 (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (s : ℝ) :
    (1 / q ^ n) ^ s = q ^ (-((n : ℝ) * s)) := by
  rw [one_div, Real.inv_rpow (pow_nonneg hq _), _root_.GD.N0055.d022111 q hq,
    ← Real.rpow_neg hq]

theorem d022113 (q : ℝ) (hq : 2 ≤ q) (n : ℕ) (hn : 2 ≤ n) :
    4 ≤ q ^ n := by
  calc
    (4 : ℝ) ≤ q ^ 2 := by nlinarith
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hn

theorem d022114 (q : ℝ) (hq : 2 ≤ q) (n : ℕ) (hn : 2 ≤ n) :
    0 < 1 / q ^ n ∧ 1 / q ^ n ≤ (1 / 4 : ℝ) := by
  have hq0 : 0 < q := by linarith
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) (_root_.GD.N0055.d022113 q hq n hn)⟩

def d022115 (q : ℝ) (hq : 2 ≤ q) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 / q ^ 8, by
    have hh := _root_.GD.N0055.d022114 q hq 8 (by norm_num)
    exact ⟨hh.1, by linarith [hh.2]⟩⟩

def d022116 (q : ℝ) (hq : 2 ≤ q) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 - 1 / q ^ 14, by
    have hh := _root_.GD.N0055.d022114 q hq 14 (by norm_num)
    constructor <;> linarith [hh.1, hh.2]⟩


def d022117 (q : ℝ) : Set _root_.GD.N0232.N0720.N1436.d013217 :=
  Icc (1 - 2 / q ^ 6) (1 - 1 / q ^ 6) ×ˢ Icc (q ^ 8) (2 * q ^ 8)

theorem d022118 (q : ℝ) (hq : 2 ≤ q) (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hz : z ∈ _root_.GD.N0055.d022117 q) :
    z ∈ _root_.GD.N0232.N0720.N1436.d013218 ∧ (1 / 2 : ℝ) ≤ z.1 ∧
      1 / q ^ 6 ≤ 1 - z.1 ∧ 1 - z.1 ≤ 2 / q ^ 6 := by
  have hq0 : 0 < q := by linarith
  have hp := _root_.GD.N0055.d022114 q hq 6 (by norm_num)
  have hlo := hz.1.1
  rw [show 2 / q ^ 6 = 2 * (1 / q ^ 6) by ring] at hlo
  have hhalf : (1 / 2 : ℝ) ≤ z.1 := by linarith only [hlo, hp.2]
  have hu0 : 0 < z.1 := lt_of_lt_of_le (by norm_num) hhalf
  have hu1 : z.1 < 1 := by have := hz.1.2; linarith
  refine ⟨⟨⟨hu0, hu1⟩, (pow_pos hq0 8).trans_le hz.2.1⟩, ?_, ?_, ?_⟩
  · exact hhalf
  · have := hz.1.2; linarith
  · have := hz.1.1; linarith

theorem d022119 (q : ℝ) (hq : 2 ≤ q) :
    _root_.GD.N0232.N0720.N1436.d013288 (_root_.GD.N0055.d022117 q) = ENNReal.ofReal (q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hs : MeasurableSet (_root_.GD.N0055.d022117 q) := measurableSet_Icc.prod measurableSet_Icc
  rw [_root_.GD.N0232.N0720.N1436.d013288, Measure.restrict_apply hs,
    inter_eq_self_of_subset_left (fun z hz => (_root_.GD.N0055.d022118 q hq z hz).1)]
  rw [_root_.GD.N0055.d022117, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc]
  rw [show (1 - 1 / q ^ 6) - (1 - 2 / q ^ 6) = 1 / q ^ 6 by ring,
    show 2 * q ^ 8 - q ^ 8 = q ^ 8 by ring,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / q ^ 6)]
  congr 1
  field_simp [hq0.ne']

theorem d022120 (q : ℝ) (hq : 2 ≤ q) (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hz : z ∈ _root_.GD.N0055.d022117 q) :
    _root_.GD.N0232.N0720.N1436.d013268 2 4 (_root_.GD.N0055.d022115 q hq) z ≤ 8 * q ^ 8 := by
  have hq0 : 0 < q := by linarith
  have hzD := (_root_.GD.N0055.d022118 q hq z hz).1
  have ht := _root_.GD.N0055.d022114 q hq 8 (by norm_num)
  have hfirst : (1 - z.1) / (1 - 1 / q ^ 8) ≤ 2 := by
    apply (div_le_iff₀ (by linarith [ht.2])).2
    linarith [hzD.1.1]
  have hsecond : 3 * z.1 / (1 / q ^ 8) ≤ 3 * q ^ 8 := by
    simpa only [div_div_eq_mul_div, div_one, mul_assoc, one_mul] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzD.1.2.le
        (by norm_num : (0 : ℝ) ≤ 3)) (pow_nonneg hq0.le 8)
  have hr : _root_.GD.N0232.N0720.N1436.d013268 2 4 (_root_.GD.N0055.d022115 q hq) z =
      (z.2 + (1 - z.1) / (1 - 1 / q ^ 8) + 3 * z.1 / (1 / q ^ 8)) / 2 := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013268, _root_.GD.N0232.N0720.N1436.d013267, _root_.GD.N0055.d022115]
  rw [hr]
  nlinarith [hz.2.2, _root_.GD.N0055.d022113 q hq 8 (by norm_num)]

theorem d022121 (q : ℝ) (hq : 2 ≤ q) (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hz : z ∈ _root_.GD.N0055.d022117 q) :
    _root_.GD.N0232.N0720.N1436.d013268 2 4 (_root_.GD.N0055.d022116 q hq) z ≤ 8 * q ^ 8 := by
  have hq0 : 0 < q := by linarith
  have hzb := _root_.GD.N0055.d022118 q hq z hz
  have hs := _root_.GD.N0055.d022114 q hq 14 (by norm_num)
  have hfirst : (1 - z.1) / (1 / q ^ 14) ≤ 2 * q ^ 8 := by
    calc
      _ = (1 - z.1) * q ^ 14 := by rw [div_div_eq_mul_div, div_one]
      _ ≤ (2 / q ^ 6) * q ^ 14 :=
        mul_le_mul_of_nonneg_right hzb.2.2.2 (pow_nonneg hq0.le 14)
      _ = _ := by field_simp [hq0.ne']
  have hsecond : 3 * z.1 / (1 - 1 / q ^ 14) ≤ 6 := by
    apply (div_le_iff₀ (by linarith [hs.2])).2
    linarith [hzb.1.1.2]
  have hr : _root_.GD.N0232.N0720.N1436.d013268 2 4 (_root_.GD.N0055.d022116 q hq) z =
      (z.2 + (1 - z.1) / (1 / q ^ 14) + 3 * z.1 / (1 - 1 / q ^ 14)) / 2 := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013268, _root_.GD.N0232.N0720.N1436.d013267, _root_.GD.N0055.d022116]
  rw [hr]
  nlinarith [hz.2.2, _root_.GD.N0055.d022113 q hq 8 (by norm_num)]

end
end GD.N0055

#print axioms _root_.GD.N0055.d022119
#print axioms _root_.GD.N0055.d022120
#print axioms _root_.GD.N0055.d022121
