import GD.Module1299
import Mathlib.Analysis.SpecialFunctions.Complex.Arg














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0106.N0428.N0765.N1536
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1535

def d021167 (z : ℂ) : ℂ := Complex.exp (((21 : ℝ) / 4 * z.im : ℝ) * Complex.I)
def d021168 (z : ℂ) : ℝ := Real.cos ((21 : ℝ) / 4 * |z.im|)
def d021169 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℝ := ∫ l in (0 : ℝ)..1, ‖_root_.GD.N0106.N0428.N0765.N1535.d021130 q z l‖

theorem d021170 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (l : ℝ) (z : ℂ) :
    (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).im = Real.exp z.re * Real.sin z.im * _root_.GD.N0106.N0428.N0765.N1535.d021128 q l := by
  simp [_root_.GD.N0106.N0428.N0765.N1535.d021129, Complex.mul_im, Complex.exp_im]


theorem d021171 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    min 0 z.im ≤ (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg ∧ (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg ≤ max 0 z.im := by
  have hre := _root_.GD.N0106.N0428.N0765.N1535.d021145 hq hl hz
  have harg : (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
  have hy : z.im ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (_root_.GD.N0106.N0428.N0765.N1535.d021139 hz)
  have hzero : (0 : ℝ) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have ha := _root_.GD.N0106.N0428.N0765.N1535.d021141 hq hl
  have hb := _root_.GD.N0106.N0428.N0765.N1535.d021142 hq hl
  have hc := _root_.GD.N0106.N0428.N0765.N1535.d021140 hz
  rcases le_total 0 z.im with hypos | hyneg
  · have hsin : 0 ≤ Real.sin z.im :=
      Real.sin_nonneg_of_mem_Icc ⟨hypos, by linarith [hy.2, Real.pi_pos]⟩
    have him : 0 ≤ (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).im := by
      rw [_root_.GD.N0106.N0428.N0765.N1536.d021170]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hsin) hb
    have htan0 : Real.tan 0 ≤ Real.tan (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg := by
      rw [Real.tan_zero, Complex.tan_arg]
      exact div_nonneg him hre.le
    have htany : Real.tan (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg ≤ Real.tan z.im := by
      rw [Complex.tan_arg, Real.tan_eq_sin_div_cos]
      apply (div_le_div_iff₀ hre hc).2
      rw [_root_.GD.N0106.N0428.N0765.N1536.d021170, _root_.GD.N0106.N0428.N0765.N1535.d021144]
      nlinarith [mul_nonneg hsin ha]
    simpa only [min_eq_left hypos, max_eq_right hypos] using
      And.intro ((Real.strictMonoOn_tan.le_iff_le hzero harg).mp htan0)
        ((Real.strictMonoOn_tan.le_iff_le harg hy).mp htany)
  · have hsin : Real.sin z.im ≤ 0 := by
      have h := Real.sin_nonneg_of_mem_Icc
        (show -z.im ∈ Icc (0 : ℝ) Real.pi from ⟨by linarith, by linarith [hy.1, Real.pi_pos]⟩)
      rw [Real.sin_neg] at h
      linarith
    have him : (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).im ≤ 0 := by
      rw [_root_.GD.N0106.N0428.N0765.N1536.d021170]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hsin) hb
    have htan0 : Real.tan (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg ≤ Real.tan 0 := by
      rw [Real.tan_zero, Complex.tan_arg]
      exact div_nonpos_of_nonpos_of_nonneg him hre.le
    have htany : Real.tan z.im ≤ Real.tan (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg := by
      rw [Complex.tan_arg, Real.tan_eq_sin_div_cos]
      apply (div_le_div_iff₀ hc hre).2
      rw [_root_.GD.N0106.N0428.N0765.N1536.d021170, _root_.GD.N0106.N0428.N0765.N1535.d021144]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hsin ha]
    simpa only [min_eq_right hyneg, max_eq_left hyneg] using
      And.intro ((Real.strictMonoOn_tan.le_iff_le hy harg).mp htany)
        ((Real.strictMonoOn_tan.le_iff_le harg hzero).mp htan0)

theorem d021172 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    |z.im / 2 - (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg| ≤ |z.im| / 2 := by
  have h := _root_.GD.N0106.N0428.N0765.N1536.d021171 hq hl hz
  rcases le_total 0 z.im with hy | hy
  · rw [min_eq_left hy, max_eq_right hy] at h
    rw [abs_of_nonneg hy]
    apply abs_le.mpr
    constructor <;> linarith [h.1, h.2]
  · rw [min_eq_right hy, max_eq_left hy] at h
    rw [abs_of_nonpos hy]
    apply abs_le.mpr
    constructor <;> linarith [h.1, h.2]


theorem d021173 (u : ℂ) (hu : u ≠ 0) (p y : ℝ) :
    (Complex.exp ((p * y / 2 : ℝ) * Complex.I) * u ^ (-(p : ℂ))).re =
      ‖u ^ (-(p : ℂ))‖ * Real.cos (p * (y / 2 - u.arg)) := by
  let t : ℂ := (p * y / 2 : ℝ) * Complex.I + Complex.log u * (-(p : ℂ))
  have heq : Complex.exp ((p * y / 2 : ℝ) * Complex.I) * u ^ (-(p : ℂ)) =
      Complex.exp t := by
    rw [Complex.cpow_def_of_ne_zero hu, ← Complex.exp_add]
  have him : t.im = p * (y / 2 - u.arg) := by
    simp only [t, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.log_im,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_zero]
    ring
  have hrot : ‖Complex.exp ((p * y / 2 : ℝ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hnorm : Real.exp t.re = ‖u ^ (-(p : ℂ))‖ := by
    rw [← Complex.norm_exp, ← heq, norm_mul, hrot, one_mul]
  rw [heq, Complex.exp_re, him, hnorm]

theorem d021174 (z : ℂ) : ‖_root_.GD.N0106.N0428.N0765.N1536.d021167 z‖ = 1 := by
  simp [_root_.GD.N0106.N0428.N0765.N1536.d021167, Complex.norm_exp, Complex.mul_re]

theorem d021175 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    (21 : ℝ) / 4 * |z.im| < Real.pi / 2 := by
  change |z.im| < 2 * Real.pi / 21 at hz
  linarith

theorem d021176 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : 0 < _root_.GD.N0106.N0428.N0765.N1536.d021168 z := by
  unfold _root_.GD.N0106.N0428.N0765.N1536.d021168
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have h := abs_nonneg z.im
    linarith [Real.pi_pos]
  · exact _root_.GD.N0106.N0428.N0765.N1536.d021175 hz


theorem d021177 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    (_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l).re =
      ‖_root_.GD.N0106.N0428.N0765.N1535.d021130 q z l‖ * Real.cos (((21 : ℝ) / 2) * (z.im / 2 - (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg)) := by
  let w : ℝ := (l * (1 - l)) ^ ((9 : ℝ) / 2)
  have hw : 0 ≤ w := Real.rpow_nonneg (mul_nonneg hl.1 (sub_nonneg.mpr hl.2)) _
  have hrot : _root_.GD.N0106.N0428.N0765.N1536.d021167 z = Complex.exp ((((21 : ℝ) / 2) * z.im / 2 : ℝ) * Complex.I) := by
    unfold _root_.GD.N0106.N0428.N0765.N1536.d021167
    rw [show (21 : ℝ) / 4 * z.im = ((21 : ℝ) / 2) * z.im / 2 by ring]
  have hp := _root_.GD.N0106.N0428.N0765.N1536.d021173 (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z) (_root_.GD.N0106.N0428.N0765.N1535.d021147 hq hl hz) ((21 : ℝ) / 2) z.im
  push_cast at hp hrot
  rw [← hrot] at hp
  have hmul : _root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l =
      (w : ℂ) * (_root_.GD.N0106.N0428.N0765.N1536.d021167 z * (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z) ^ (-((21 : ℂ) / 2))) := by
    unfold _root_.GD.N0106.N0428.N0765.N1535.d021130 w
    ring
  have hn : ‖_root_.GD.N0106.N0428.N0765.N1535.d021130 q z l‖ = w * ‖(_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z) ^ (-((21 : ℂ) / 2))‖ := by
    unfold _root_.GD.N0106.N0428.N0765.N1535.d021130
    rw [norm_mul, Complex.norm_of_nonneg hw]
  rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hp, hn]
  ring


theorem d021178 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    _root_.GD.N0106.N0428.N0765.N1536.d021168 z * ‖_root_.GD.N0106.N0428.N0765.N1535.d021130 q z l‖ ≤ (_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l).re := by
  rw [_root_.GD.N0106.N0428.N0765.N1536.d021177 hq hl hz]
  have ha : |((21 : ℝ) / 2) * (z.im / 2 - (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg)| ≤
      (21 : ℝ) / 4 * |z.im| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 21 / 2)]
    nlinarith [_root_.GD.N0106.N0428.N0765.N1536.d021172 hq hl hz]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg (((21 : ℝ) / 2) * (z.im / 2 - (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).arg)))
    (show (21 : ℝ) / 4 * |z.im| ≤ Real.pi by linarith [_root_.GD.N0106.N0428.N0765.N1536.d021175 hz, Real.pi_pos]) ha
  rw [Real.cos_abs] at hc
  unfold _root_.GD.N0106.N0428.N0765.N1536.d021168
  nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg (_root_.GD.N0106.N0428.N0765.N1535.d021130 q z l))]

theorem d021179 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Ioo (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : 0 < ‖_root_.GD.N0106.N0428.N0765.N1535.d021130 q z l‖ := by
  apply norm_pos_iff.mpr
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021130
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (mul_pos hl.1 (sub_pos.mpr hl.2)) _).ne'
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (_root_.GD.N0106.N0428.N0765.N1535.d021147 hq (Ioo_subset_Icc_self hl) hz))

theorem d021180 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : 0 < _root_.GD.N0106.N0428.N0765.N1536.d021169 q z := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((_root_.GD.N0106.N0428.N0765.N1535.d021150 hq hz).norm.intervalIntegrable_of_Icc zero_le_one)
    (fun l hl => _root_.GD.N0106.N0428.N0765.N1536.d021179 hq hl hz) zero_lt_one

theorem d021181 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : (_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021131 q z).re =
      ∫ l in (0 : ℝ)..1, (_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l).re := by
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021131
  rw [← intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_of_le zero_le_one]
  exact (integral_re ((_root_.GD.N0106.N0428.N0765.N1535.d021151 hq hz).1.const_mul (_root_.GD.N0106.N0428.N0765.N1536.d021167 z))).symm


theorem d021182 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : _root_.GD.N0106.N0428.N0765.N1536.d021168 z * _root_.GD.N0106.N0428.N0765.N1536.d021169 q z ≤ ‖_root_.GD.N0106.N0428.N0765.N1535.d021131 q z‖ := by
  have hk := _root_.GD.N0106.N0428.N0765.N1535.d021150 hq hz
  have hr : ContinuousOn (fun l => (_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l).re) (Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn' (continuousOn_const.mul hk)
  have hm : _root_.GD.N0106.N0428.N0765.N1536.d021168 z * _root_.GD.N0106.N0428.N0765.N1536.d021169 q z ≤ (_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021131 q z).re := by
    rw [_root_.GD.N0106.N0428.N0765.N1536.d021181 hq hz, _root_.GD.N0106.N0428.N0765.N1536.d021169, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on zero_le_one
      ((continuousOn_const.mul hk.norm).intervalIntegrable_of_Icc zero_le_one)
      (hr.intervalIntegrable_of_Icc zero_le_one) (fun l hl => _root_.GD.N0106.N0428.N0765.N1536.d021178 hq hl hz)
  calc
    _root_.GD.N0106.N0428.N0765.N1536.d021168 z * _root_.GD.N0106.N0428.N0765.N1536.d021169 q z ≤ (_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021131 q z).re := hm
    _ ≤ |(_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021131 q z).re| := le_abs_self _
    _ ≤ ‖_root_.GD.N0106.N0428.N0765.N1536.d021167 z * _root_.GD.N0106.N0428.N0765.N1535.d021131 q z‖ := Complex.abs_re_le_norm _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1535.d021131 q z‖ := by rw [norm_mul, _root_.GD.N0106.N0428.N0765.N1536.d021174, one_mul]


theorem d021183 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : _root_.GD.N0106.N0428.N0765.N1535.d021131 q z ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos (_root_.GD.N0106.N0428.N0765.N1536.d021176 hz) (_root_.GD.N0106.N0428.N0765.N1536.d021180 hq hz))
    (_root_.GD.N0106.N0428.N0765.N1536.d021182 hq hz)

theorem d021184 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : ‖_root_.GD.N0106.N0428.N0765.N1535.d021132 q z‖ ≤ _root_.GD.N0106.N0428.N0765.N1536.d021169 q z := by
  have hk := _root_.GD.N0106.N0428.N0765.N1535.d021150 hq hz
  have hn := Complex.continuous_ofReal.continuousOn.mul hk
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021132 _root_.GD.N0106.N0428.N0765.N1536.d021169
  apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
  apply intervalIntegral.integral_mono_on zero_le_one
    (hn.norm.intervalIntegrable_of_Icc zero_le_one)
    (hk.norm.intervalIntegrable_of_Icc zero_le_one)
  intro l hl
  change ‖(l : ℂ) * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l‖ ≤ ‖_root_.GD.N0106.N0428.N0765.N1535.d021130 q z l‖
  rw [norm_mul, Complex.norm_of_nonneg hl.1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hl.2 (norm_nonneg (_root_.GD.N0106.N0428.N0765.N1535.d021130 q z l))


theorem d021185 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : ‖_root_.GD.N0106.N0428.N0765.N1535.d021133 q z‖ ≤ 1 / Real.cos ((21 : ℝ) / 4 * |z.im|) := by
  have hd : 0 < ‖_root_.GD.N0106.N0428.N0765.N1535.d021131 q z‖ := norm_pos_iff.mpr (_root_.GD.N0106.N0428.N0765.N1536.d021183 hq hz)
  have hc := _root_.GD.N0106.N0428.N0765.N1536.d021176 hz
  change ‖_root_.GD.N0106.N0428.N0765.N1535.d021133 q z‖ ≤ 1 / _root_.GD.N0106.N0428.N0765.N1536.d021168 z
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021133, norm_div]
  apply (div_le_div_iff₀ hd hc).2
  have hn := mul_le_mul_of_nonneg_right (_root_.GD.N0106.N0428.N0765.N1536.d021184 hq hz) hc.le
  nlinarith [_root_.GD.N0106.N0428.N0765.N1536.d021182 hq hz]

end
end GD.N0106.N0428.N0765.N1536

#print axioms _root_.GD.N0106.N0428.N0765.N1536.d021171
#print axioms _root_.GD.N0106.N0428.N0765.N1536.d021172
#print axioms _root_.GD.N0106.N0428.N0765.N1536.d021173
#print axioms _root_.GD.N0106.N0428.N0765.N1536.d021178
#print axioms _root_.GD.N0106.N0428.N0765.N1536.d021180
#print axioms _root_.GD.N0106.N0428.N0765.N1536.d021182
#print axioms _root_.GD.N0106.N0428.N0765.N1536.d021183
#print axioms _root_.GD.N0106.N0428.N0765.N1536.d021185
