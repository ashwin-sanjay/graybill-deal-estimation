import GD.Module0359
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic


























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set intervalIntegral

namespace GD.N0106.N0428.N0765.N1618
open _root_.GD.N0106.N0428.N0765.N1534
noncomputable section


def d005722 (S xbar μ : ℝ) : ℝ := S + 11 * (μ - xbar) ^ 2


def d005723 (S₁ S₂ xbar₁ xbar₂ μ : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1618.d005722 S₁ xbar₁ μ ^ (-((11 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1618.d005722 S₂ xbar₂ μ ^ (-((11 : ℝ) / 2))


def d005724 (S₁ S₂ xbar₁ xbar₂ : ℝ) : ℝ :=
  (∫ μ, μ * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ xbar₁ xbar₂ μ) / ∫ μ, _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ xbar₁ xbar₂ μ

theorem d005725 {S : ℝ} (hS : 0 < S) (xbar μ : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1618.d005722 S xbar μ := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005722
  positivity




def d005726 (l : ℝ) : ℝ := (l * (1 - l)) ^ ((9 : ℝ) / 2)


def d005727 : ℝ := ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1618.d005726 l

theorem d005728 : Continuous _root_.GD.N0106.N0428.N0765.N1618.d005726 := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005726
  exact (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)

theorem d005729 {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0106.N0428.N0765.N1618.d005726 l :=
  Real.rpow_pos_of_pos (mul_pos hl.1 (sub_pos.mpr hl.2)) _

theorem d005730 {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1618.d005726 l :=
  Real.rpow_nonneg (mul_nonneg hl.1 (sub_nonneg.mpr hl.2)) _

theorem d005731 {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0765.N1618.d005726 l ≤ 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005726
  apply Real.rpow_le_one (mul_nonneg hl.1 (sub_nonneg.mpr hl.2)) _ (by norm_num)
  have h := mul_le_mul hl.2 (by linarith [hl.1] : 1 - l ≤ 1) (by linarith [hl.2]) zero_le_one
  simpa using h

theorem d005732 : 0 < _root_.GD.N0106.N0428.N0765.N1618.d005727 :=
  intervalIntegral_pos_of_pos_on (_root_.GD.N0106.N0428.N0765.N1618.d005728.intervalIntegrable 0 1)
    (fun _ hl => _root_.GD.N0106.N0428.N0765.N1618.d005729 hl) zero_lt_one


def d005733 (A B l : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1618.d005726 l * ((1 - l) * A + l * B) ^ (-(11 : ℝ))


def d005734 (A B x : ℝ) : ℝ := A * x + B * (1 - x)


def d005735 (A B x : ℝ) : ℝ := A * x / _root_.GD.N0106.N0428.N0765.N1618.d005734 A B x


def d005736 (A B x : ℝ) : ℝ := A * B / _root_.GD.N0106.N0428.N0765.N1618.d005734 A B x ^ 2

theorem d005737 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1618.d005734 A B x := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005734
  rcases lt_or_eq_of_le hx.2 with h | h
  · have h1 := mul_pos hB (sub_pos.mpr h)
    have h2 := mul_nonneg hA.le hx.1
    linarith
  · subst h
    simpa using hA

theorem d005738 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (_root_.GD.N0106.N0428.N0765.N1618.d005735 A B) (_root_.GD.N0106.N0428.N0765.N1618.d005736 A B x) x := by
  have hD := (_root_.GD.N0106.N0428.N0765.N1618.d005737 hA hB hx).ne'
  have hu : HasDerivAt (fun y : ℝ => A * y) A x := by
    simpa using (hasDerivAt_id x).const_mul A
  have hv : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1618.d005734 A B) (A - B) x := by
    have h := ((hasDerivAt_id x).const_mul A).add (((hasDerivAt_id x).const_sub 1).const_mul B)
    exact h.congr_deriv (by ring)
  have h := hu.div hv hD
  refine h.congr_deriv ?_
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005736
  rw [div_eq_div_iff (pow_ne_zero 2 hD) (pow_ne_zero 2 hD)]
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005734
  ring

theorem d005739 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1618.d005736 A B) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005736
  apply ContinuousOn.div continuousOn_const
  · exact ((by unfold _root_.GD.N0106.N0428.N0765.N1618.d005734; fun_prop : Continuous (_root_.GD.N0106.N0428.N0765.N1618.d005734 A B)).pow 2).continuousOn
  · intro x hx
    exact pow_ne_zero 2 (_root_.GD.N0106.N0428.N0765.N1618.d005737 hA hB hx).ne'

theorem d005740 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1618.d005735 A B x ∈ Icc (0 : ℝ) 1 := by
  have hD := _root_.GD.N0106.N0428.N0765.N1618.d005737 hA hB hx
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005735
  constructor
  · exact div_nonneg (mul_nonneg hA.le hx.1) hD.le
  · rw [div_le_one hD]
    unfold _root_.GD.N0106.N0428.N0765.N1618.d005734
    nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hx.2)]

theorem d005741 (A B : ℝ) : _root_.GD.N0106.N0428.N0765.N1618.d005735 A B 0 = 0 := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005735
  simp

theorem d005742 {A : ℝ} (hA : 0 < A) (B : ℝ) : _root_.GD.N0106.N0428.N0765.N1618.d005735 A B 1 = 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005735 _root_.GD.N0106.N0428.N0765.N1618.d005734
  simp [hA.ne']

theorem d005743 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    0 < (1 - l) * A + l * B := by
  have h := _root_.GD.N0106.N0428.N0765.N1618.d005737 hB hA hl
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005734 at h
  linarith

theorem d005744 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1618.d005733 A B) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005733
  apply _root_.GD.N0106.N0428.N0765.N1618.d005728.continuousOn.mul
  apply ContinuousOn.rpow_const (by fun_prop)
  intro x hx
  exact Or.inl (_root_.GD.N0106.N0428.N0765.N1618.d005743 hA hB hx).ne'

theorem d005745 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1618.d005733 A B (_root_.GD.N0106.N0428.N0765.N1618.d005735 A B x) * _root_.GD.N0106.N0428.N0765.N1618.d005736 A B x
      = A ^ (-((11 : ℝ) / 2)) * B ^ (-((11 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1618.d005726 x := by
  have hD := _root_.GD.N0106.N0428.N0765.N1618.d005737 hA hB hx
  have hDne := hD.ne'
  have hP : 0 < A * B := mul_pos hA hB
  have hx0 := hx.1
  have hx1 := sub_nonneg.mpr hx.2
  have hw0 : 0 ≤ x * (1 - x) := mul_nonneg hx0 hx1
  have h1 : _root_.GD.N0106.N0428.N0765.N1618.d005735 A B x * (1 - _root_.GD.N0106.N0428.N0765.N1618.d005735 A B x) = (A * B) * (x * (1 - x)) / _root_.GD.N0106.N0428.N0765.N1618.d005734 A B x ^ 2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1618.d005735
    rw [one_sub_div hDne, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hDne hDne) (pow_ne_zero 2 hDne)]
    unfold _root_.GD.N0106.N0428.N0765.N1618.d005734
    ring
  have h2 : (1 - _root_.GD.N0106.N0428.N0765.N1618.d005735 A B x) * A + _root_.GD.N0106.N0428.N0765.N1618.d005735 A B x * B = (A * B) / _root_.GD.N0106.N0428.N0765.N1618.d005734 A B x := by
    unfold _root_.GD.N0106.N0428.N0765.N1618.d005735
    rw [one_sub_div hDne, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_div_iff hDne hDne]
    unfold _root_.GD.N0106.N0428.N0765.N1618.d005734
    ring
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005733 _root_.GD.N0106.N0428.N0765.N1618.d005726 _root_.GD.N0106.N0428.N0765.N1618.d005736
  rw [h1, h2, Real.div_rpow (mul_nonneg hP.le hw0) (by positivity), Real.mul_rpow hP.le hw0,
    Real.div_rpow hP.le hD.le]
  have hD2 : (_root_.GD.N0106.N0428.N0765.N1618.d005734 A B x ^ 2) ^ ((9 : ℝ) / 2) = _root_.GD.N0106.N0428.N0765.N1618.d005734 A B x ^ 9 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hD.le]
    norm_num
  have hD11 : _root_.GD.N0106.N0428.N0765.N1618.d005734 A B x ^ (-(11 : ℝ)) = (_root_.GD.N0106.N0428.N0765.N1618.d005734 A B x ^ 11)⁻¹ := by
    rw [Real.rpow_neg hD.le]
    congr 1
    exact_mod_cast Real.rpow_natCast (_root_.GD.N0106.N0428.N0765.N1618.d005734 A B x) 11
  have hP' : (A * B) ^ ((9 : ℝ) / 2) * (A * B) ^ (-(11 : ℝ)) * (A * B)
      = (A * B) ^ (-((11 : ℝ) / 2)) := by
    have e : (A * B) ^ (-((11 : ℝ) / 2)) = (A * B) ^ ((9 : ℝ) / 2 + (-(11 : ℝ)) + 1) := by
      norm_num
    rw [e, Real.rpow_add hP, Real.rpow_add hP, Real.rpow_one]
  rw [← Real.mul_rpow hA.le hB.le, ← hP', hD2, hD11]
  field_simp


theorem d005746 {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A ^ (-((11 : ℝ) / 2)) * B ^ (-((11 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1618.d005727 = ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1618.d005733 A B l := by
  have hsub := integral_comp_mul_deriv' (a := (0 : ℝ)) (b := 1) (f := _root_.GD.N0106.N0428.N0765.N1618.d005735 A B) (f' := _root_.GD.N0106.N0428.N0765.N1618.d005736 A B)
    (g := _root_.GD.N0106.N0428.N0765.N1618.d005733 A B)
    (fun x hx => _root_.GD.N0106.N0428.N0765.N1618.d005738 hA hB (by rwa [uIcc_of_le zero_le_one] at hx))
    (by rw [uIcc_of_le zero_le_one]; exact _root_.GD.N0106.N0428.N0765.N1618.d005739 hA hB)
    (by
      rw [uIcc_of_le zero_le_one]
      refine (_root_.GD.N0106.N0428.N0765.N1618.d005744 hA hB).mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact _root_.GD.N0106.N0428.N0765.N1618.d005740 hA hB hx)
  rw [_root_.GD.N0106.N0428.N0765.N1618.d005741, _root_.GD.N0106.N0428.N0765.N1618.d005742 hA] at hsub
  rw [← hsub]
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005727
  rw [← intervalIntegral.integral_const_mul]
  apply integral_congr
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  show A ^ (-((11 : ℝ) / 2)) * B ^ (-((11 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1618.d005726 x = _root_.GD.N0106.N0428.N0765.N1618.d005733 A B (_root_.GD.N0106.N0428.N0765.N1618.d005735 A B x) * _root_.GD.N0106.N0428.N0765.N1618.d005736 A B x
  exact (_root_.GD.N0106.N0428.N0765.N1618.d005745 hA hB hx).symm




def d005747 : ℝ := ∫ x : ℝ, (1 + 11 * x ^ 2) ^ (-(11 : ℝ))

theorem d005748 {c : ℝ} (hc : 0 < c) (m : ℝ) :
    Continuous fun x : ℝ => (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ)) := by
  apply Continuous.rpow_const (by fun_prop)
  intro x
  left
  positivity

theorem d005749 {c₀ c R m : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) (hR : 0 ≤ R) (hm : |m| ≤ R)
    (x : ℝ) :
    (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ))
      ≤ (2 * (1 + 2 * R ^ 2) / (min c₀ 1) ^ 11) * (1 + x ^ 2)⁻¹ := by
  set m₀ := min c₀ 1 with hm₀
  have hm₀pos : 0 < m₀ := lt_min hc₀ one_pos
  have hm₀le1 : m₀ ≤ 1 := min_le_right _ _
  have hm₀lec : m₀ ≤ c := (min_le_left _ _).trans hc
  set y := x - m with hy
  set s := 1 + y ^ 2 with hs
  have hs1 : 1 ≤ s := by rw [hs]; nlinarith [sq_nonneg y]
  have hspos : 0 < s := by linarith
  have hbase : 0 < c + 11 * y ^ 2 := by nlinarith [sq_nonneg y]
  have hi : m₀ * s ≤ c + 11 * y ^ 2 := by rw [hs]; nlinarith [sq_nonneg y]
  have hrpow : (c + 11 * y ^ 2) ^ (-(11 : ℝ)) = ((c + 11 * y ^ 2) ^ 11)⁻¹ := by
    rw [Real.rpow_neg hbase.le]
    congr 1
    exact_mod_cast Real.rpow_natCast _ 11
  have hs11 : s ≤ s ^ 11 := le_self_pow₀ hs1 (by norm_num)
  have hpow : m₀ ^ 11 * s ≤ (c + 11 * y ^ 2) ^ 11 := by
    have h1 : m₀ ^ 11 * s ≤ m₀ ^ 11 * s ^ 11 := mul_le_mul_of_nonneg_left hs11 (by positivity)
    have h2 : (m₀ * s) ^ 11 ≤ (c + 11 * y ^ 2) ^ 11 := pow_le_pow_left₀ (by positivity) hi 11
    calc m₀ ^ 11 * s ≤ m₀ ^ 11 * s ^ 11 := h1
      _ = (m₀ * s) ^ 11 := by ring
      _ ≤ (c + 11 * y ^ 2) ^ 11 := h2
  have hiv : 1 + x ^ 2 ≤ 2 * (1 + 2 * R ^ 2) * s := by
    have hm2 : m ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs m]
      exact pow_le_pow_left₀ (abs_nonneg m) hm 2
    have hx : x = y + m := by rw [hy]; ring
    rw [hx, hs]
    nlinarith [sq_nonneg (y - m), sq_nonneg y, hm2]
  rw [hrpow]
  calc ((c + 11 * y ^ 2) ^ 11)⁻¹ ≤ (m₀ ^ 11 * s)⁻¹ := inv_anti₀ (by positivity) hpow
    _ = 1 / (m₀ ^ 11 * s) := (one_div _).symm
    _ ≤ (2 * (1 + 2 * R ^ 2)) / (m₀ ^ 11 * (1 + x ^ 2)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h := mul_le_mul_of_nonneg_left hiv (by positivity : (0 : ℝ) ≤ m₀ ^ 11)
        nlinarith [h]
    _ = (2 * (1 + 2 * R ^ 2) / m₀ ^ 11) * (1 + x ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_div]

theorem d005750 {c₀ c R m : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) (hR : 0 ≤ R) (hm : |m| ≤ R)
    (x : ℝ) :
    |x| * (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ))
      ≤ (2 * (1 + R) * (1 + 2 * R ^ 2) / (min c₀ 1) ^ 11) * (1 + x ^ 2)⁻¹ := by
  set m₀ := min c₀ 1 with hm₀
  have hm₀pos : 0 < m₀ := lt_min hc₀ one_pos
  have hm₀le1 : m₀ ≤ 1 := min_le_right _ _
  have hm₀lec : m₀ ≤ c := (min_le_left _ _).trans hc
  set y := x - m with hy
  set s := 1 + y ^ 2 with hs
  have hs1 : 1 ≤ s := by rw [hs]; nlinarith [sq_nonneg y]
  have hspos : 0 < s := by linarith
  have hbase : 0 < c + 11 * y ^ 2 := by nlinarith [sq_nonneg y]
  have hi : m₀ * s ≤ c + 11 * y ^ 2 := by rw [hs]; nlinarith [sq_nonneg y]
  have hrpow : (c + 11 * y ^ 2) ^ (-(11 : ℝ)) = ((c + 11 * y ^ 2) ^ 11)⁻¹ := by
    rw [Real.rpow_neg hbase.le]
    congr 1
    exact_mod_cast Real.rpow_natCast _ 11
  have hs11 : s ^ 2 ≤ s ^ 11 := pow_le_pow_right₀ hs1 (by norm_num)
  have hpow : m₀ ^ 11 * s ^ 2 ≤ (c + 11 * y ^ 2) ^ 11 := by
    have h1 : m₀ ^ 11 * s ^ 2 ≤ m₀ ^ 11 * s ^ 11 := mul_le_mul_of_nonneg_left hs11 (by positivity)
    have h2 : (m₀ * s) ^ 11 ≤ (c + 11 * y ^ 2) ^ 11 := pow_le_pow_left₀ (by positivity) hi 11
    calc m₀ ^ 11 * s ^ 2 ≤ m₀ ^ 11 * s ^ 11 := h1
      _ = (m₀ * s) ^ 11 := by ring
      _ ≤ (c + 11 * y ^ 2) ^ 11 := h2
  have hiv : 1 + x ^ 2 ≤ 2 * (1 + 2 * R ^ 2) * s := by
    have hm2 : m ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs m]
      exact pow_le_pow_left₀ (abs_nonneg m) hm 2
    have hx : x = y + m := by rw [hy]; ring
    rw [hx, hs]
    nlinarith [sq_nonneg (y - m), sq_nonneg y, hm2]
  have hiii : |x| ≤ (1 + R) * s := by
    have h1 : |x| ≤ |y| + R := by
      calc |x| = |y + m| := by rw [hy, sub_add_cancel]
        _ ≤ |y| + |m| := by simpa [Real.norm_eq_abs] using norm_add_le y m
        _ ≤ |y| + R := by linarith
    have h2 : |y| ≤ s := by
      rw [hs]
      nlinarith [sq_nonneg (|y| - 1), sq_abs y, abs_nonneg y]
    nlinarith [hs1, hR, h1, h2]
  rw [hrpow]
  calc |x| * ((c + 11 * y ^ 2) ^ 11)⁻¹ ≤ ((1 + R) * s) * (m₀ ^ 11 * s ^ 2)⁻¹ :=
        mul_le_mul hiii (inv_anti₀ (by positivity) hpow) (by positivity) (by positivity)
    _ = (1 + R) / (m₀ ^ 11 * s) := by
        rw [← div_eq_mul_inv, div_eq_div_iff (by positivity) (by positivity)]
        ring
    _ ≤ (2 * (1 + R) * (1 + 2 * R ^ 2)) / (m₀ ^ 11 * (1 + x ^ 2)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h := mul_le_mul_of_nonneg_left hiv (by positivity : (0 : ℝ) ≤ (1 + R) * m₀ ^ 11)
        nlinarith [h]
    _ = (2 * (1 + R) * (1 + 2 * R ^ 2) / m₀ ^ 11) * (1 + x ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_div]

theorem d005751 {c : ℝ} (hc : 0 < c) (m : ℝ) :
    Integrable fun x : ℝ => (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ)) := by
  refine (integrable_inv_one_add_sq.const_mul
    (2 * (1 + 2 * |m| ^ 2) / (min c 1) ^ 11)).mono'
    (_root_.GD.N0106.N0428.N0765.N1618.d005748 hc m).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact _root_.GD.N0106.N0428.N0765.N1618.d005749 hc le_rfl (abs_nonneg m) le_rfl x

theorem d005752 {c : ℝ} (hc : 0 < c) (m : ℝ) :
    Integrable fun x : ℝ => x * (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ)) := by
  refine (integrable_inv_one_add_sq.const_mul
    (2 * (1 + |m|) * (1 + 2 * |m| ^ 2) / (min c 1) ^ 11)).mono'
    (continuous_id.mul (_root_.GD.N0106.N0428.N0765.N1618.d005748 hc m)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact _root_.GD.N0106.N0428.N0765.N1618.d005750 hc le_rfl (abs_nonneg m) le_rfl x

theorem d005753 : 0 < _root_.GD.N0106.N0428.N0765.N1618.d005747 := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005747
  have hcont : Continuous fun x : ℝ => (1 + 11 * x ^ 2) ^ (-(11 : ℝ)) := by
    have h := _root_.GD.N0106.N0428.N0765.N1618.d005748 one_pos 0
    simpa using h
  have hint : Integrable fun x : ℝ => (1 + 11 * x ^ 2) ^ (-(11 : ℝ)) := by
    have h := _root_.GD.N0106.N0428.N0765.N1618.d005751 one_pos 0
    simpa using h
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0) hcont hint
  · intro x
    exact Real.rpow_nonneg (by positivity) _
  · norm_num

theorem d005754 {c : ℝ} (hc : 0 < c) (m : ℝ) :
    ∫ x : ℝ, (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ)) = _root_.GD.N0106.N0428.N0765.N1618.d005747 * c ^ (-((21 : ℝ) / 2)) := by
  have h1 : (∫ x : ℝ, (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ)))
      = ∫ x : ℝ, (c + 11 * x ^ 2) ^ (-(11 : ℝ)) :=
    integral_sub_right_eq_self (fun x : ℝ => (c + 11 * x ^ 2) ^ (-(11 : ℝ))) m
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have h2 : ∀ x : ℝ, (c + 11 * x ^ 2) ^ (-(11 : ℝ))
      = c ^ (-(11 : ℝ)) * (1 + 11 * ((Real.sqrt c)⁻¹ * x) ^ 2) ^ (-(11 : ℝ)) := by
    intro x
    rw [← Real.mul_rpow hc.le (by positivity)]
    congr 1
    rw [mul_pow, inv_pow, Real.sq_sqrt hc.le]
    field_simp
  rw [h1]
  simp_rw [h2]
  rw [MeasureTheory.integral_const_mul,
    Measure.integral_comp_inv_mul_left (fun y : ℝ => (1 + 11 * y ^ 2) ^ (-(11 : ℝ))) (Real.sqrt c),
    abs_of_pos hs, smul_eq_mul]
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005747
  have h3 : c ^ (-(11 : ℝ)) * Real.sqrt c = c ^ (-((21 : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc]
    norm_num
  rw [← h3]
  ring

theorem d005755 {c : ℝ} (hc : 0 < c) (m : ℝ) :
    ∫ x : ℝ, x * (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ)) = m * (_root_.GD.N0106.N0428.N0765.N1618.d005747 * c ^ (-((21 : ℝ) / 2))) := by
  have h1 : (∫ x : ℝ, x * (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ)))
      = ∫ x : ℝ, (x + m) * (c + 11 * x ^ 2) ^ (-(11 : ℝ)) := by
    rw [← integral_add_right_eq_self (fun x : ℝ => x * (c + 11 * (x - m) ^ 2) ^ (-(11 : ℝ))) m]
    simp only [add_sub_cancel_right]
  have hodd : (∫ x : ℝ, x * (c + 11 * x ^ 2) ^ (-(11 : ℝ))) = 0 := by
    have h := integral_neg_eq_self (fun x : ℝ => x * (c + 11 * x ^ 2) ^ (-(11 : ℝ))) (volume : Measure ℝ)
    simp only [neg_sq, neg_mul] at h
    rw [MeasureTheory.integral_neg] at h
    linarith
  have hi0 := _root_.GD.N0106.N0428.N0765.N1618.d005751 hc 0
  have hi1 := _root_.GD.N0106.N0428.N0765.N1618.d005752 hc 0
  have hm0 := _root_.GD.N0106.N0428.N0765.N1618.d005754 hc 0
  simp only [sub_zero] at hi0 hi1 hm0
  have hsplit : (∫ x : ℝ, (x + m) * (c + 11 * x ^ 2) ^ (-(11 : ℝ)))
      = (∫ x : ℝ, x * (c + 11 * x ^ 2) ^ (-(11 : ℝ)))
        + ∫ x : ℝ, m * (c + 11 * x ^ 2) ^ (-(11 : ℝ)) := by
    rw [← integral_add hi1 (hi0.const_mul m)]
    congr 1
    funext x
    ring
  rw [h1, hsplit, hodd, MeasureTheory.integral_const_mul, hm0, zero_add]



theorem d005756 (S₁ S₂ a b l μ : ℝ) :
    (1 - l) * _root_.GD.N0106.N0428.N0765.N1618.d005722 S₁ a μ + l * _root_.GD.N0106.N0428.N0765.N1618.d005722 S₂ b μ
      = _root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) l + 11 * (μ - ((1 - l) * a + l * b)) ^ 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005722 _root_.GD.N0106.N0428.N0765.N1534.d005295
  ring


def d005757 (S₁ S₂ a b l μ : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1618.d005726 l * (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) l + 11 * (μ - ((1 - l) * a + l * b)) ^ 2) ^ (-(11 : ℝ))

theorem d005758 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b μ : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b μ = _root_.GD.N0106.N0428.N0765.N1618.d005727⁻¹ * ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b l μ := by
  have hf := _root_.GD.N0106.N0428.N0765.N1618.d005746 (_root_.GD.N0106.N0428.N0765.N1618.d005725 hS₁ a μ) (_root_.GD.N0106.N0428.N0765.N1618.d005725 hS₂ b μ)
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005723
  rw [eq_inv_mul_iff_mul_eq₀ _root_.GD.N0106.N0428.N0765.N1618.d005732.ne', mul_comm, hf]
  congr 1
  funext l
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005733 _root_.GD.N0106.N0428.N0765.N1618.d005757
  rw [_root_.GD.N0106.N0428.N0765.N1618.d005756]

theorem d005759 (S₁ S₂ a b : ℝ) : Measurable (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b)) := by
  unfold Function.uncurry _root_.GD.N0106.N0428.N0765.N1618.d005757 _root_.GD.N0106.N0428.N0765.N1618.d005726 _root_.GD.N0106.N0428.N0765.N1534.d005295
  fun_prop

theorem d005760 (S₁ S₂ a b : ℝ) :
    Measurable (Function.uncurry fun l μ => μ * _root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b l μ) := by
  unfold Function.uncurry _root_.GD.N0106.N0428.N0765.N1618.d005757 _root_.GD.N0106.N0428.N0765.N1618.d005726 _root_.GD.N0106.N0428.N0765.N1534.d005295
  fun_prop

theorem d005761 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (Δ : ℝ) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    min S₁ S₂ ≤ _root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ Δ l := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005295
  have h1 : min S₁ S₂ ≤ S₁ := min_le_left _ _
  have h2 : min S₁ S₂ ≤ S₂ := min_le_right _ _
  have h3 : 0 ≤ 11 * l * (1 - l) * Δ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hl.1) (sub_nonneg.mpr hl.2)) (sq_nonneg Δ)
  nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hl.2), mul_le_mul_of_nonneg_left h2 hl.1]

theorem d005762 (a b : ℝ) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    |(1 - l) * a + l * b| ≤ max |a| |b| := by
  have hl0 := hl.1
  have hl1 := sub_nonneg.mpr hl.2
  calc |(1 - l) * a + l * b| ≤ |(1 - l) * a| + |l * b| := by
        simpa [Real.norm_eq_abs] using norm_add_le ((1 - l) * a) (l * b)
    _ = (1 - l) * |a| + l * |b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hl1, abs_of_nonneg hl0]
    _ ≤ (1 - l) * max |a| |b| + l * max |a| |b| := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max |a| |b| := by ring

theorem d005763 :
    ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod volume), z.1 ∈ Ioc (0 : ℝ) 1 := by
  rw [ae_iff]
  have hset : {z : ℝ × ℝ | ¬ z.1 ∈ Ioc (0 : ℝ) 1} = (Ioc (0 : ℝ) 1)ᶜ ×ˢ (univ : Set ℝ) := by
    ext z
    simp
  rw [hset, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioc, compl_inter_self,
    measure_empty, zero_mul]

theorem d005764 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b : ℝ) :
    Integrable (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b)) ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
  have hc₀ : 0 < min S₁ S₂ := lt_min hS₁ hS₂
  have hR : 0 ≤ max |a| |b| := le_trans (abs_nonneg a) (le_max_left _ _)
  set K := 2 * (1 + 2 * (max |a| |b|) ^ 2) / (min (min S₁ S₂) 1) ^ 11 with hK
  rw [uIoc_of_le zero_le_one]
  have hmaj : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * (K * (1 + z.2 ^ 2)⁻¹))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    refine Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun y : ℝ => K * (1 + y ^ 2)⁻¹) ?_ ?_
    · exact integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)
    · exact integrable_inv_one_add_sq.const_mul K
  refine hmaj.mono' (_root_.GD.N0106.N0428.N0765.N1618.d005759 S₁ S₂ a b).aestronglyMeasurable ?_
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1618.d005763] with z hz
  have hl : z.1 ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hz
  have hC := _root_.GD.N0106.N0428.N0765.N1534.d005303 hS₁ hS₂ (Δ := b - a) hl
  show ‖_root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b z.1 z.2‖ ≤ 1 * (K * (1 + z.2 ^ 2)⁻¹)
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005757
  rw [one_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1618.d005730 hl),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc _root_.GD.N0106.N0428.N0765.N1618.d005726 z.1 * (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) z.1 + 11 * (z.2 - ((1 - z.1) * a + z.1 * b)) ^ 2) ^ (-(11 : ℝ))
      ≤ 1 * (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) z.1 + 11 * (z.2 - ((1 - z.1) * a + z.1 * b)) ^ 2) ^ (-(11 : ℝ)) := by
        gcongr
        exact _root_.GD.N0106.N0428.N0765.N1618.d005731 hl
    _ = (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) z.1 + 11 * (z.2 - ((1 - z.1) * a + z.1 * b)) ^ 2) ^ (-(11 : ℝ)) :=
        one_mul _
    _ ≤ K * (1 + z.2 ^ 2)⁻¹ :=
        _root_.GD.N0106.N0428.N0765.N1618.d005749 hc₀ (_root_.GD.N0106.N0428.N0765.N1618.d005761 hS₁ hS₂ (b - a) hl) hR (_root_.GD.N0106.N0428.N0765.N1618.d005762 a b hl) z.2

theorem d005765 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b : ℝ) :
    Integrable (Function.uncurry fun l μ => μ * _root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b l μ)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
  have hc₀ : 0 < min S₁ S₂ := lt_min hS₁ hS₂
  have hR : 0 ≤ max |a| |b| := le_trans (abs_nonneg a) (le_max_left _ _)
  set K := 2 * (1 + max |a| |b|) * (1 + 2 * (max |a| |b|) ^ 2) / (min (min S₁ S₂) 1) ^ 11 with hK
  rw [uIoc_of_le zero_le_one]
  have hmaj : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * (K * (1 + z.2 ^ 2)⁻¹))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    refine Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun y : ℝ => K * (1 + y ^ 2)⁻¹) ?_ ?_
    · exact integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)
    · exact integrable_inv_one_add_sq.const_mul K
  refine hmaj.mono' (_root_.GD.N0106.N0428.N0765.N1618.d005760 S₁ S₂ a b).aestronglyMeasurable ?_
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1618.d005763] with z hz
  have hl : z.1 ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hz
  have hC := _root_.GD.N0106.N0428.N0765.N1534.d005303 hS₁ hS₂ (Δ := b - a) hl
  show ‖z.2 * _root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b z.1 z.2‖ ≤ 1 * (K * (1 + z.2 ^ 2)⁻¹)
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005757
  rw [one_mul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1618.d005730 hl),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc |z.2| * (_root_.GD.N0106.N0428.N0765.N1618.d005726 z.1 * (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) z.1 + 11 * (z.2 - ((1 - z.1) * a + z.1 * b)) ^ 2) ^ (-(11 : ℝ)))
      ≤ |z.2| * (1 * (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) z.1 + 11 * (z.2 - ((1 - z.1) * a + z.1 * b)) ^ 2) ^ (-(11 : ℝ))) := by
        gcongr
        exact _root_.GD.N0106.N0428.N0765.N1618.d005731 hl
    _ = |z.2| * (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) z.1 + 11 * (z.2 - ((1 - z.1) * a + z.1 * b)) ^ 2) ^ (-(11 : ℝ)) := by
        rw [one_mul]
    _ ≤ K * (1 + z.2 ^ 2)⁻¹ :=
        _root_.GD.N0106.N0428.N0765.N1618.d005750 hc₀ (_root_.GD.N0106.N0428.N0765.N1618.d005761 hS₁ hS₂ (b - a) hl) hR (_root_.GD.N0106.N0428.N0765.N1618.d005762 a b hl) z.2

theorem d005766 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b : ℝ) :
    ∫ μ, _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b μ = _root_.GD.N0106.N0428.N0765.N1618.d005727⁻¹ * _root_.GD.N0106.N0428.N0765.N1618.d005747 * _root_.GD.N0106.N0428.N0765.N1534.d005297 S₁ S₂ (b - a) := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1618.d005758 hS₁ hS₂ a b]
  rw [MeasureTheory.integral_const_mul, ← intervalIntegral_integral_swap (_root_.GD.N0106.N0428.N0765.N1618.d005764 hS₁ hS₂ a b)]
  have hinner : ∀ l ∈ uIcc (0 : ℝ) 1,
      (∫ μ, _root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b l μ) = _root_.GD.N0106.N0428.N0765.N1618.d005747 * _root_.GD.N0106.N0428.N0765.N1534.d005296 S₁ S₂ (b - a) l := by
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    unfold _root_.GD.N0106.N0428.N0765.N1618.d005757
    rw [MeasureTheory.integral_const_mul, _root_.GD.N0106.N0428.N0765.N1618.d005754 (_root_.GD.N0106.N0428.N0765.N1534.d005303 hS₁ hS₂ hl)]
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005296 _root_.GD.N0106.N0428.N0765.N1618.d005726
    ring
  rw [integral_congr hinner, intervalIntegral.integral_const_mul]
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005297
  ring

theorem d005767 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b : ℝ) :
    ∫ μ, μ * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b μ
      = _root_.GD.N0106.N0428.N0765.N1618.d005727⁻¹ * _root_.GD.N0106.N0428.N0765.N1618.d005747 * (a * _root_.GD.N0106.N0428.N0765.N1534.d005297 S₁ S₂ (b - a) + (b - a) * _root_.GD.N0106.N0428.N0765.N1534.d005298 S₁ S₂ (b - a)) := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1618.d005758 hS₁ hS₂ a b]
  have h : ∀ μ : ℝ, μ * (_root_.GD.N0106.N0428.N0765.N1618.d005727⁻¹ * ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b l μ)
      = _root_.GD.N0106.N0428.N0765.N1618.d005727⁻¹ * ∫ l in (0 : ℝ)..1, μ * _root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b l μ := by
    intro μ
    rw [intervalIntegral.integral_const_mul]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, ← intervalIntegral_integral_swap (_root_.GD.N0106.N0428.N0765.N1618.d005765 hS₁ hS₂ a b)]
  have hinner : ∀ l ∈ uIcc (0 : ℝ) 1,
      (∫ μ, μ * _root_.GD.N0106.N0428.N0765.N1618.d005757 S₁ S₂ a b l μ) = _root_.GD.N0106.N0428.N0765.N1618.d005747 * (((1 - l) * a + l * b) * _root_.GD.N0106.N0428.N0765.N1534.d005296 S₁ S₂ (b - a) l) := by
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    unfold _root_.GD.N0106.N0428.N0765.N1618.d005757
    have hswap : (fun μ : ℝ => μ * (_root_.GD.N0106.N0428.N0765.N1618.d005726 l *
        (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) l + 11 * (μ - ((1 - l) * a + l * b)) ^ 2) ^ (-(11 : ℝ))))
        = fun μ : ℝ => _root_.GD.N0106.N0428.N0765.N1618.d005726 l *
          (μ * (_root_.GD.N0106.N0428.N0765.N1534.d005295 S₁ S₂ (b - a) l + 11 * (μ - ((1 - l) * a + l * b)) ^ 2) ^ (-(11 : ℝ))) := by
      funext μ
      ring
    rw [hswap, MeasureTheory.integral_const_mul, _root_.GD.N0106.N0428.N0765.N1618.d005755 (_root_.GD.N0106.N0428.N0765.N1534.d005303 hS₁ hS₂ hl)]
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005296 _root_.GD.N0106.N0428.N0765.N1618.d005726
    ring
  rw [integral_congr hinner, intervalIntegral.integral_const_mul]
  have hsplit : (∫ l in (0 : ℝ)..1, ((1 - l) * a + l * b) * _root_.GD.N0106.N0428.N0765.N1534.d005296 S₁ S₂ (b - a) l)
      = a * _root_.GD.N0106.N0428.N0765.N1534.d005297 S₁ S₂ (b - a) + (b - a) * _root_.GD.N0106.N0428.N0765.N1534.d005298 S₁ S₂ (b - a) := by
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005297 _root_.GD.N0106.N0428.N0765.N1534.d005298
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← integral_add ((_root_.GD.N0106.N0428.N0765.N1534.d005306 hS₁ hS₂).const_mul a)
        ((_root_.GD.N0106.N0428.N0765.N1534.d005307 hS₁ hS₂).const_mul (b - a))]
    congr 1
    funext l
    ring
  rw [hsplit]
  ring



theorem d005768 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1618.d005724 S₁ S₂ a b = a + (b - a) * _root_.GD.N0106.N0428.N0765.N1534.d005299 S₁ S₂ (b - a) := by
  unfold _root_.GD.N0106.N0428.N0765.N1618.d005724
  rw [_root_.GD.N0106.N0428.N0765.N1618.d005767 hS₁ hS₂ a b, _root_.GD.N0106.N0428.N0765.N1618.d005766 hS₁ hS₂ a b]
  have hk : _root_.GD.N0106.N0428.N0765.N1618.d005727⁻¹ * _root_.GD.N0106.N0428.N0765.N1618.d005747 ≠ 0 := mul_ne_zero (inv_ne_zero _root_.GD.N0106.N0428.N0765.N1618.d005732.ne') _root_.GD.N0106.N0428.N0765.N1618.d005753.ne'
  have hd := (_root_.GD.N0106.N0428.N0765.N1534.d005310 (Δ := b - a) hS₁ hS₂).ne'
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005299
  rw [mul_div_mul_left _ _ hk, add_div, mul_div_cancel_right₀ _ hd, mul_div_assoc]


theorem d005769 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1618.d005724 S₁ S₂ a b = _root_.GD.N0106.N0428.N0765.N1534.d005300 a (b - a) S₁ S₂ :=
  _root_.GD.N0106.N0428.N0765.N1618.d005768 hS₁ hS₂ a b

end
end GD.N0106.N0428.N0765.N1618

#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005746
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005754
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005755
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005756
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005764
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005765
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005766
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005767
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005768
#print axioms _root_.GD.N0106.N0428.N0765.N1618.d005769
