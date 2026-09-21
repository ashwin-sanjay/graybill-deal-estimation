import GD.Module0827
import GD.Module0659
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic


















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1607
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1611 _root_.GD.N0106.N0428.N0765.N1606
open _root_.GD.N0232.N0719.N0908

abbrev d012638 := _root_.GD.N0106.N0428.N0765.N1611.d012588
abbrev d012639 (location eta : ℝ) : Measure _root_.GD.N0106.N0428.N0765.N1607.d012638 :=
  _root_.GD.N0106.N0428.N0765.N1611.d012595 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)

def d012640 (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : ℝ := _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x

def d012641 (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1534.d005299 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012591 x)

def d012642 (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1534.d005302 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012591 x)


abbrev d012643 := Fin 5 × Fin 2

def d012644 (a : Fin 5) (h : ℝ) : ℝ := h ^ (a.val + 1) * (1 - h)

def d012645 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : ℝ :=
  if j.2 = 1 then _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1607.d012641 x) * _root_.GD.N0106.N0428.N0765.N1607.d012642 x
  else -_root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1607.d012641 x)

def d012646 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : ℝ := _root_.GD.N0106.N0428.N0765.N1611.d012591 x * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x

def d012647 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : ℝ :=
  ∑ j, b j * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x

def d012648 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1611.d012593 x + _root_.GD.N0106.N0428.N0765.N1607.d012647 b x

theorem d012649 : Fintype.card _root_.GD.N0106.N0428.N0765.N1607.d012643 = 10 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1607.d012643]

@[fun_prop] theorem d012650 : Measurable _root_.GD.N0106.N0428.N0765.N1607.d012640 := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012640
  fun_prop

set_option diagnostics true in
@[fun_prop] theorem d012651 : Measurable _root_.GD.N0106.N0428.N0765.N1607.d012641 := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012641
  have hmap : Measurable (fun x : _root_.GD.N0106.N0428.N0765.N1607.d012638 =>
      ((_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x, _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x) : ℝ × ℝ × ℝ)) :=
    (_root_.GD.N0106.N0428.N0765.N1611.d012597 0).prodMk
      ((_root_.GD.N0106.N0428.N0765.N1611.d012597 1).prodMk _root_.GD.N0106.N0428.N0765.N1611.d012598)
  have hw := _root_.GD.N0106.N0428.N0765.N1534.d005350.comp hmap
  simpa only [Function.comp_def] using hw

@[fun_prop] theorem d012652 : Measurable _root_.GD.N0106.N0428.N0765.N1607.d012642 := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012642 _root_.GD.N0106.N0428.N0765.N1534.d005302
  fun_prop

@[fun_prop] theorem d012653 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : Measurable (_root_.GD.N0106.N0428.N0765.N1607.d012645 j) := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012645 _root_.GD.N0106.N0428.N0765.N1607.d012644
  split_ifs <;> fun_prop

@[fun_prop] theorem d012654 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : Measurable (_root_.GD.N0106.N0428.N0765.N1607.d012646 j) := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012646
  fun_prop

@[fun_prop] theorem d012655 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1607.d012647 b) := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012647
  fun_prop

@[fun_prop] theorem d012656 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) :=
  _root_.GD.N0106.N0428.N0765.N1611.d012600.add (_root_.GD.N0106.N0428.N0765.N1607.d012655 b)


theorem d012657 :
    (∫ u : ℝ, u⁻¹ ^ 2 ∂_root_.GD.N0121.d006346 10) = 1 / 48 := by
  unfold _root_.GD.N0121.d006346
  rw [_root_.GD.N0232.N0719.N0908.d009688 (by norm_num) (by norm_num)]
  norm_num

theorem d012658 :
    Integrable (fun u : ℝ => u⁻¹ ^ 2) (_root_.GD.N0121.d006346 10) := by
  apply Integrable.of_integral_ne_zero
  rw [_root_.GD.N0106.N0428.N0765.N1607.d012657]
  norm_num


theorem d012659 (location eta : ℝ) (heta : 0 < eta) :
    (∫ x, (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x)⁻¹ ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) = 1 / 48 := by
  have h := _root_.GD.N0106.N0428.N0765.N1607.d012657
  rw [← _root_.GD.N0106.N0428.N0765.N1606.d012631 location eta heta,
    integral_map (_root_.GD.N0106.N0428.N0765.N1611.d012597 0).aemeasurable (by fun_prop)] at h
  exact h

theorem d012660 (location eta : ℝ) (heta : 0 < eta) :
    Integrable (fun x => (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x)⁻¹ ^ 2) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  apply Integrable.of_integral_ne_zero
  rw [_root_.GD.N0106.N0428.N0765.N1607.d012659 location eta heta]
  norm_num

theorem d012661 (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    0 < _root_.GD.N0106.N0428.N0765.N1607.d012640 x := add_pos (hx 0) (hx 1)

theorem d012662 (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2 ≤ (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x)⁻¹ ^ 2 := by
  apply pow_le_pow_left₀ (inv_nonneg.mpr (_root_.GD.N0106.N0428.N0765.N1607.d012661 x hx).le)
  exact inv_anti₀ (hx 0) (le_add_of_nonneg_right (hx 1).le)


theorem d012663 (location eta : ℝ) (heta : 0 < eta) :
    Integrable (fun x => (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  apply (_root_.GD.N0106.N0428.N0765.N1607.d012660 location eta heta).mono'
  · exact (_root_.GD.N0106.N0428.N0765.N1607.d012650.inv.pow_const (2 : ℕ)).aestronglyMeasurable
  · filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0106.N0428.N0765.N1607.d012662 x hx

theorem d012664 (location eta : ℝ) (heta : 0 < eta) :
    (∫ x, (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ≤ 1 / 48 := by
  rw [← _root_.GD.N0106.N0428.N0765.N1607.d012659 location eta heta]
  apply integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1607.d012663 location eta heta)
    (_root_.GD.N0106.N0428.N0765.N1607.d012660 location eta heta)
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
  exact _root_.GD.N0106.N0428.N0765.N1607.d012662 x hx


theorem d012665 (location eta : ℝ) (heta : 0 < eta) (p : ℕ) :
    MemLp _root_.GD.N0106.N0428.N0765.N1611.d012591 p (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  have hm : MeasurePreserving _root_.GD.N0106.N0428.N0765.N1611.d012591 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)
      (gaussianReal 0 ⟨(1 + eta) / 11, by positivity⟩) :=
    ⟨_root_.GD.N0106.N0428.N0765.N1611.d012598, _root_.GD.N0106.N0428.N0765.N1606.d012630 location eta heta⟩
  have hp : MemLp (id : ℝ → ℝ) (p : ℝ≥0∞)
      (gaussianReal 0 ⟨(1 + eta) / 11, by positivity⟩) :=
    memLp_id_gaussianReal' _ (by simp)
  simpa only [Function.comp_def, id_eq] using hp.comp_measurePreserving hm

theorem d012666 (location eta : ℝ) (heta : 0 < eta) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1607.d012665 location eta heta 6).integrable_norm_pow (by norm_num)
  simpa only [Real.norm_eq_abs, (show Even (6 : ℕ) by decide).pow_abs] using h


theorem d012667 (location eta : ℝ) (heta : 0 < eta) :
    IndepFun (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6) (fun x => (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2)
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1606.d012633 location eta heta).comp
    (show Measurable (fun d : ℝ => d ^ 6) by fun_prop)
    (show Measurable (fun p : ℝ × ℝ => (p.1 + eta * p.2)⁻¹ ^ 2) by fun_prop)
  have heq (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : (_root_.GD.N0106.N0428.N0765.N1606.d012619 eta x).1 +
      eta * (_root_.GD.N0106.N0428.N0765.N1606.d012619 eta x).2 = _root_.GD.N0106.N0428.N0765.N1607.d012640 x := by
    simp only [_root_.GD.N0106.N0428.N0765.N1606.d012619, _root_.GD.N0106.N0428.N0765.N1607.d012640]
    field_simp [heta.ne']
  simpa only [Function.comp_def, heq] using h


theorem d012668 (location eta : ℝ) (heta : 0 < eta) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6 * (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2)
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) :=
  (_root_.GD.N0106.N0428.N0765.N1607.d012667 location eta heta).integrable_mul
    (_root_.GD.N0106.N0428.N0765.N1607.d012666 location eta heta)
    (_root_.GD.N0106.N0428.N0765.N1607.d012663 location eta heta)

theorem d012669 (a : Fin 5) {h : ℝ} (hh : h ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1607.d012644 a h ∈ Icc (0 : ℝ) 1 := by
  have hp0 : 0 ≤ h ^ (a.val + 1) := pow_nonneg hh.1 _
  have hp1 : h ^ (a.val + 1) ≤ 1 := pow_le_one₀ hh.1 hh.2
  constructor
  · exact mul_nonneg hp0 (sub_nonneg.mpr hh.2)
  · exact (mul_le_mul hp1 (by linarith only [hh.1] : 1 - h ≤ 1)
      (sub_nonneg.mpr hh.2) zero_le_one).trans_eq (one_mul 1)


theorem d012670 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1607.d012646 j x ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 +
      12100 * (_root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6 * (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2) := by
  have hw : _root_.GD.N0106.N0428.N0765.N1607.d012641 x ∈ Icc (0 : ℝ) 1 :=
    Ioo_subset_Icc_self (_root_.GD.N0106.N0428.N0765.N1611.d012607 x hx)
  have hp := _root_.GD.N0106.N0428.N0765.N1607.d012669 j.1 hw
  have hp2 : _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1607.d012641 x) ^ 2 ≤ 1 := pow_le_one₀ hp.1 hp.2
  have hz : 0 ≤ _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6 * (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2 := by positivity
  by_cases hj : j.2 = 1
  · have hprod := mul_le_mul_of_nonneg_left hp2
      (sq_nonneg (_root_.GD.N0106.N0428.N0765.N1611.d012591 x * _root_.GD.N0106.N0428.N0765.N1607.d012642 x))
    have he : (_root_.GD.N0106.N0428.N0765.N1611.d012591 x * _root_.GD.N0106.N0428.N0765.N1607.d012642 x) ^ 2 =
        12100 * (_root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6 * (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2) := by
      unfold _root_.GD.N0106.N0428.N0765.N1607.d012642 _root_.GD.N0106.N0428.N0765.N1534.d005302 _root_.GD.N0106.N0428.N0765.N1607.d012640
      simp only [div_eq_mul_inv]
      ring
    have hc : _root_.GD.N0106.N0428.N0765.N1607.d012646 j x ^ 2 = (_root_.GD.N0106.N0428.N0765.N1611.d012591 x * _root_.GD.N0106.N0428.N0765.N1607.d012642 x) ^ 2 *
        _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1607.d012641 x) ^ 2 := by
      simp only [_root_.GD.N0106.N0428.N0765.N1607.d012646, _root_.GD.N0106.N0428.N0765.N1607.d012645, if_pos hj]
      ring
    rw [hc]
    calc (_root_.GD.N0106.N0428.N0765.N1611.d012591 x * _root_.GD.N0106.N0428.N0765.N1607.d012642 x) ^ 2 * _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1607.d012641 x) ^ 2
        ≤ (_root_.GD.N0106.N0428.N0765.N1611.d012591 x * _root_.GD.N0106.N0428.N0765.N1607.d012642 x) ^ 2 := by simpa using hprod
      _ ≤ _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 + 12100 *
          (_root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6 * (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2) := by rw [he]; nlinarith [sq_nonneg (_root_.GD.N0106.N0428.N0765.N1611.d012591 x)]
  · have hprod := mul_le_mul_of_nonneg_left hp2 (sq_nonneg (_root_.GD.N0106.N0428.N0765.N1611.d012591 x))
    have hc : _root_.GD.N0106.N0428.N0765.N1607.d012646 j x ^ 2 = _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1607.d012641 x) ^ 2 := by
      simp only [_root_.GD.N0106.N0428.N0765.N1607.d012646, _root_.GD.N0106.N0428.N0765.N1607.d012645, if_neg hj]
      ring
    rw [hc]
    calc
      _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1607.d012641 x) ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 := by
        simpa using hprod
      _ ≤ _ := by linarith

theorem d012671 (location eta : ℝ) (heta : 0 < eta) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    MemLp (_root_.GD.N0106.N0428.N0765.N1607.d012646 j) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  apply (memLp_two_iff_integrable_sq (_root_.GD.N0106.N0428.N0765.N1607.d012654 j).aestronglyMeasurable).2
  have hmajorant := ((_root_.GD.N0106.N0428.N0765.N1607.d012665 location eta heta 2).integrable_sq).add
    ((_root_.GD.N0106.N0428.N0765.N1607.d012668 location eta heta).const_mul 12100)
  apply hmajorant.mono'
  · fun_prop
  · filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0106.N0428.N0765.N1607.d012670 j x hx

theorem d012672 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) : MemLp (_root_.GD.N0106.N0428.N0765.N1607.d012647 b) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012647
  exact memLp_finsetSum _ fun j _ => (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta j).const_mul (b j)

theorem d012673 (location eta : ℝ) (heta : 0 < eta) :
    MemLp (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  exact (memLp_two_iff_integrable_sq
    (_root_.GD.N0106.N0428.N0765.N1611.d012600.sub measurable_const).aestronglyMeasurable).2
      (_root_.GD.N0106.N0428.N0765.N1611.d012611 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta))

theorem d012674 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    MemLp (fun x => _root_.GD.N0106.N0428.N0765.N1607.d012648 b x - location) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1607.d012673 location eta heta).add
    (_root_.GD.N0106.N0428.N0765.N1607.d012672 location eta heta b)
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).2 h
  dsimp [_root_.GD.N0106.N0428.N0765.N1607.d012648]
  ring


theorem d012675 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    (∫⁻ x, ENNReal.ofReal ((_root_.GD.N0106.N0428.N0765.N1607.d012648 b x - location) ^ 2)
      ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) < ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0106.N0428.N0765.N1607.d012674 location eta heta b).integrable_sq
      (ae_of_all _ fun x => sq_nonneg _)]
  exact ENNReal.ofReal_lt_top


theorem d012676 (location eta : ℝ) (heta : 0 < eta)
    (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * _root_.GD.N0106.N0428.N0765.N1607.d012645 i x * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x)
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta i).integrable_mul
    (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta j)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp [_root_.GD.N0106.N0428.N0765.N1607.d012646]
  ring

def d012677 (location eta : ℝ) (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : ℝ :=
  ∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * _root_.GD.N0106.N0428.N0765.N1607.d012645 i x * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta


def d012678 (eta : ℝ) : ℝ := 1 / (1 + eta)

def d012679 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1611.d012591 x * (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)

theorem d012680 (eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1607.d012678 eta ∈ Icc (0 : ℝ) 1 := by
  constructor
  · unfold _root_.GD.N0106.N0428.N0765.N1607.d012678
    positivity
  · unfold _root_.GD.N0106.N0428.N0765.N1607.d012678
    exact (div_le_one (by positivity : 0 < 1 + eta)).2 (by linarith)

theorem d012681 (location eta : ℝ) (heta : 0 < eta) :
    MemLp (_root_.GD.N0106.N0428.N0765.N1607.d012679 eta) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  apply (memLp_two_iff_integrable_sq (by unfold _root_.GD.N0106.N0428.N0765.N1607.d012679; fun_prop)).2
  apply ((_root_.GD.N0106.N0428.N0765.N1607.d012665 location eta heta 2).integrable_sq).mono'
  · unfold _root_.GD.N0106.N0428.N0765.N1607.d012679
    fun_prop
  · filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
    have hw : _root_.GD.N0106.N0428.N0765.N1607.d012641 x ∈ Icc (0 : ℝ) 1 :=
      Ioo_subset_Icc_self (_root_.GD.N0106.N0428.N0765.N1611.d012607 x hx)
    have ho := _root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta
    have hab : |_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta| ≤ 1 :=
      abs_le.mpr ⟨by linarith only [hw.1, ho.2], by linarith only [hw.2, ho.1]⟩
    have hsq : (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)) hab 2
      simpa only [sq_abs, one_pow] using h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold _root_.GD.N0106.N0428.N0765.N1607.d012679
    rw [mul_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (sq_nonneg (_root_.GD.N0106.N0428.N0765.N1611.d012591 x))



theorem d012682 (location eta : ℝ) (heta : 0 < eta)
    (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x)
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1607.d012681 location eta heta).integrable_mul
    (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta j)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp [_root_.GD.N0106.N0428.N0765.N1607.d012679, _root_.GD.N0106.N0428.N0765.N1607.d012646]
  ring

def d012683 (location eta : ℝ) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : ℝ :=
  ∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x
    ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta


theorem d012684 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (x : _root_.GD.N0106.N0428.N0765.N1607.d012638) :
    _root_.GD.N0106.N0428.N0765.N1607.d012647 b x = _root_.GD.N0106.N0428.N0765.N1611.d012591 x * ∑ j, b j * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012647 _root_.GD.N0106.N0428.N0765.N1607.d012646
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem d012685 (location eta : ℝ) (heta : 0 < eta) :
    Integrable (fun x => (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ∧
    (∫ x, (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ≤ 1 / 48 ∧
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ∧
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6 * (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2)
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ∧
    (∀ j, MemLp (_root_.GD.N0106.N0428.N0765.N1607.d012646 j) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) ∧
    (∀ j, Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 *
      (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) ∧
    (∀ i j, Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * _root_.GD.N0106.N0428.N0765.N1607.d012645 i x * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x)
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) ∧
    (∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ, Measurable (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) ∧
      (∫⁻ x, ENNReal.ofReal ((_root_.GD.N0106.N0428.N0765.N1607.d012648 b x - location) ^ 2)
        ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) < ⊤) := by
  exact ⟨_root_.GD.N0106.N0428.N0765.N1607.d012663 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012664 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012666 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012668 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012682 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012676 location eta heta,
    fun b => ⟨_root_.GD.N0106.N0428.N0765.N1607.d012656 b,
      _root_.GD.N0106.N0428.N0765.N1607.d012675 location eta heta b⟩⟩

end
end GD.N0106.N0428.N0765.N1607

#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012657
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012663
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012664
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012665
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012666
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012668
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012671
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012675
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012676
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012682
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012684
#print axioms _root_.GD.N0106.N0428.N0765.N1607.d012685
