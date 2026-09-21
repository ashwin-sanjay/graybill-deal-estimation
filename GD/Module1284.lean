import GD.Module0828
import GD.Module0940














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1610
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1611 _root_.GD.N0106.N0428.N0765.N1606 _root_.GD.N0106.N0428.N0765.N1607
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0720.N1425

abbrev d020743 := _root_.GD.N0106.N0428.N0765.N1611.d012588
abbrev d020744 := _root_.GD.N0137.d008894 11 × _root_.GD.N0137.d008894 11


def d020745 (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : _root_.GD.N0106.N0428.N0765.N1610.d020744 := (x 1, x 0)

@[fun_prop] theorem d020746 : Measurable _root_.GD.N0106.N0428.N0765.N1610.d020745 := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020745
  fun_prop

theorem d020747 (location eta : ℝ) :
    (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta).map _root_.GD.N0106.N0428.N0765.N1610.d020745 =
      _root_.GD.N0107.d009030 11 11 location (Real.sqrt eta) 1 := by
  have hp := (measurePreserving_piFinTwo
    (fun i : Fin 2 => _root_.GD.N0232.N0719.d009174 11 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta i))).map_eq
  change (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta).map (fun x => (x 0, x 1)) =
    (_root_.GD.N0232.N0719.d009174 11 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta 0)).prod
      (_root_.GD.N0232.N0719.d009174 11 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta 1)) at hp
  have hfun : _root_.GD.N0106.N0428.N0765.N1610.d020745 = Prod.swap ∘ (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => (x 0, x 1)) := rfl
  rw [hfun, ← Measure.map_map measurable_swap (by fun_prop), hp, Measure.prod_swap]
  change (_root_.GD.N0232.N0719.d009174 11 location (Real.sqrt eta)).prod
    (_root_.GD.N0232.N0719.d009174 11 location 1) = _
  unfold _root_.GD.N0232.N0719.d009174 _root_.GD.N0107.d009030 _root_.GD.N0137.d008914
  exact Measure.map_prod_map _ _ (_root_.GD.N0107.d009020 11 location (Real.sqrt eta))
    (_root_.GD.N0107.d009020 11 location 1)

theorem d020748 (eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0107.d009046 11 11 (Real.sqrt eta) 1 = _root_.GD.N0106.N0428.N0765.N1607.d012678 eta := by
  unfold _root_.GD.N0107.d009046 _root_.GD.N0107.d009045 _root_.GD.N0107.d009043 _root_.GD.N0107.d009044 _root_.GD.N0106.N0428.N0765.N1607.d012678
  rw [Real.sq_sqrt heta.le]
  norm_num
  field_simp
  <;> ring

def d020749 (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : ℝ := _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / _root_.GD.N0106.N0428.N0765.N1607.d012640 x

def d020750 (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : ℝ × ℝ := (_root_.GD.N0106.N0428.N0765.N1610.d020749 x, _root_.GD.N0106.N0428.N0765.N1607.d012642 x)

def d020751 (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1534.d005299 p.1 (1 - p.1) (Real.sqrt (p.2 / 110))

def d020752 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (p : ℝ × ℝ) : ℝ :=
  if j.2 = 1 then _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1610.d020751 p) * p.2
  else -_root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 (_root_.GD.N0106.N0428.N0765.N1610.d020751 p)

@[fun_prop] theorem d020753 : Measurable _root_.GD.N0106.N0428.N0765.N1610.d020749 := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020749
  fun_prop

@[fun_prop] theorem d020754 : Measurable _root_.GD.N0106.N0428.N0765.N1610.d020750 := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020750
  fun_prop

@[fun_prop] theorem d020755 : Measurable _root_.GD.N0106.N0428.N0765.N1610.d020751 := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020751
  have hmap : Measurable (fun p : ℝ × ℝ =>
      ((p.1, 1 - p.1, Real.sqrt (p.2 / 110)) : ℝ × ℝ × ℝ)) := by
    fun_prop
  have hw := _root_.GD.N0106.N0428.N0765.N1534.d005350.comp hmap
  simpa only [Function.comp_def] using hw

@[fun_prop] theorem d020756 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1610.d020752 j) := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020752 _root_.GD.N0106.N0428.N0765.N1607.d012644
  split_ifs <;> fun_prop


theorem d020757 (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1610.d020751 (_root_.GD.N0106.N0428.N0765.N1610.d020750 x) = _root_.GD.N0106.N0428.N0765.N1607.d012641 x := by
  have hs := _root_.GD.N0106.N0428.N0765.N1607.d012661 x hx
  have hd : 0 ≤ _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 / _root_.GD.N0106.N0428.N0765.N1607.d012640 x := div_nonneg (sq_nonneg _) hs.le
  have hdelta : Real.sqrt (_root_.GD.N0106.N0428.N0765.N1607.d012642 x / 110) ^ 2 =
      (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ * _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 := by
    have hf : _root_.GD.N0106.N0428.N0765.N1607.d012642 x / 110 = _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 / _root_.GD.N0106.N0428.N0765.N1607.d012640 x := by
      unfold _root_.GD.N0106.N0428.N0765.N1607.d012642 _root_.GD.N0106.N0428.N0765.N1534.d005302 _root_.GD.N0106.N0428.N0765.N1607.d012640
      ring
    rw [hf, Real.sq_sqrt hd]
    ring
  have h := _root_.GD.N0106.N0428.N0765.N1534.d005327 (hx 0) (hx 1) (inv_pos.mpr hs) hdelta
  have hzero : (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ * _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x = _root_.GD.N0106.N0428.N0765.N1610.d020749 x := by
    unfold _root_.GD.N0106.N0428.N0765.N1610.d020749
    ring
  have hone : (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ * _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x = 1 - _root_.GD.N0106.N0428.N0765.N1610.d020749 x := by
    unfold _root_.GD.N0106.N0428.N0765.N1610.d020749
    field_simp [hs.ne']
    <;> simp only [_root_.GD.N0106.N0428.N0765.N1607.d012640]
    <;> ring
  rw [hzero, hone] at h
  exact h

theorem d020758 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (x : _root_.GD.N0106.N0428.N0765.N1610.d020743)
    (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1610.d020752 j (_root_.GD.N0106.N0428.N0765.N1610.d020750 x) = _root_.GD.N0106.N0428.N0765.N1607.d012645 j x := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020752 _root_.GD.N0106.N0428.N0765.N1607.d012645
  rw [_root_.GD.N0106.N0428.N0765.N1610.d020757 x hx]
  rfl

def d020759 (location eta : ℝ) (w : _root_.GD.N0106.N0428.N0765.N1610.d020744) : ℝ :=
  _root_.GD.N0107.d009038 11 11 location (Real.sqrt eta) 1
    (_root_.GD.N0107.d009046 11 11 (Real.sqrt eta) 1)
    (_root_.GD.N0107.d009045 11 11 (Real.sqrt eta) 1) w

def d020760 (location eta : ℝ) (w : _root_.GD.N0106.N0428.N0765.N1610.d020744) : ℝ × ℝ :=
  (_root_.GD.N0107.d009039 11 11 location (Real.sqrt eta) 1
      (_root_.GD.N0107.d009046 11 11 (Real.sqrt eta) 1) w,
    _root_.GD.N0107.d009040 11 11 location (Real.sqrt eta) 1
      (_root_.GD.N0107.d009046 11 11 (Real.sqrt eta) 1) w)

def d020761 (location eta : ℝ) (w : _root_.GD.N0106.N0428.N0765.N1610.d020744) : ℝ :=
  _root_.GD.N0107.d012732 11 11 location (_root_.GD.N0107.d009046 11 11 (Real.sqrt eta) 1) w

def d020762 (location eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1611.d012589 0 x + _root_.GD.N0106.N0428.N0765.N1607.d012678 eta * _root_.GD.N0106.N0428.N0765.N1611.d012591 x - location

@[fun_prop] theorem d020763 (location eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1610.d020759 location eta) :=
  (_root_.GD.N0107.d009041 11 11 location (Real.sqrt eta) 1
    (_root_.GD.N0107.d009046 11 11 (Real.sqrt eta) 1)
    (_root_.GD.N0107.d009045 11 11 (Real.sqrt eta) 1)).fst

@[fun_prop] theorem d020764 (location eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1610.d020760 location eta) :=
  (_root_.GD.N0107.d009041 11 11 location (Real.sqrt eta) 1
    (_root_.GD.N0107.d009046 11 11 (Real.sqrt eta) 1)
    (_root_.GD.N0107.d009045 11 11 (Real.sqrt eta) 1)).snd

@[fun_prop] theorem d020765 (location eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1610.d020761 location eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020761 _root_.GD.N0107.d012732 _root_.GD.N0107.d009090 _root_.GD.N0107.d009084
    _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  fun_prop

@[fun_prop] theorem d020766 (location eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020762
  fun_prop

theorem d020767 (location eta : ℝ) (heta : 0 < eta) (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) :
    _root_.GD.N0106.N0428.N0765.N1610.d020759 location eta (_root_.GD.N0106.N0428.N0765.N1610.d020745 x) = _root_.GD.N0106.N0428.N0765.N1611.d012591 x := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020759
  rw [_root_.GD.N0107.d012724 11 11 (by norm_num) (by norm_num)
    location (Real.sqrt eta) 1 (Real.sqrt_pos.mpr heta) zero_lt_one]
  rfl

theorem d020768 (location eta : ℝ) (heta : 0 < eta)
    (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1610.d020760 location eta (_root_.GD.N0106.N0428.N0765.N1610.d020745 x) = _root_.GD.N0106.N0428.N0765.N1610.d020750 x := by
  have hs := (_root_.GD.N0106.N0428.N0765.N1607.d012661 x hx).ne'
  have hden : _root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / 10 / 11 + _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / 10 / 11 =
      _root_.GD.N0106.N0428.N0765.N1607.d012640 x / 110 := by unfold _root_.GD.N0106.N0428.N0765.N1607.d012640; ring
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020760
  rw [_root_.GD.N0107.d012729 11 11 (by norm_num) (by norm_num)
      location (Real.sqrt eta) 1 (Real.sqrt_pos.mpr heta) zero_lt_one,
    _root_.GD.N0107.d012731 11 11 (by norm_num) (by norm_num)
      location (Real.sqrt eta) 1 (Real.sqrt_pos.mpr heta) zero_lt_one]
  apply Prod.ext
  · change (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / 10 / 11) /
      (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / 10 / 11 + _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / 10 / 11) = _root_.GD.N0106.N0428.N0765.N1610.d020749 x
    rw [hden]
    unfold _root_.GD.N0106.N0428.N0765.N1610.d020749
    field_simp [hs]
    <;> ring
  · change (_root_.GD.N0106.N0428.N0765.N1611.d012591 x) ^ 2 /
      (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x / 10 / 11 + _root_.GD.N0106.N0428.N0765.N1611.d012590 0 x / 10 / 11) = _root_.GD.N0106.N0428.N0765.N1607.d012642 x
    rw [hden]
    change _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 / (_root_.GD.N0106.N0428.N0765.N1607.d012640 x / 110) =
      110 * _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 / _root_.GD.N0106.N0428.N0765.N1607.d012640 x
    field_simp [hs]
    <;> ring

theorem d020769 (location eta : ℝ) (heta : 0 < eta) (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) :
    _root_.GD.N0106.N0428.N0765.N1610.d020761 location eta (_root_.GD.N0106.N0428.N0765.N1610.d020745 x) = _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020761
  rw [_root_.GD.N0106.N0428.N0765.N1610.d020748 eta heta]
  rfl


theorem d020770 (location eta : ℝ) (heta : 0 < eta)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (hcarrier : MemLp (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x *
      (g (_root_.GD.N0106.N0428.N0765.N1610.d020750 x) - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * (_root_.GD.N0106.N0428.N0765.N1611.d012591 x *
      (g (_root_.GD.N0106.N0428.N0765.N1610.d020750 x) - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)) ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) = 0 := by
  let f : _root_.GD.N0106.N0428.N0765.N1610.d020744 → ℝ := fun w => _root_.GD.N0106.N0428.N0765.N1610.d020759 location eta w *
    (g (_root_.GD.N0106.N0428.N0765.N1610.d020760 location eta w) - _root_.GD.N0107.d009046 11 11 (Real.sqrt eta) 1)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have heq : f ∘ _root_.GD.N0106.N0428.N0765.N1610.d020745 =ᵐ[_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta]
      (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x * (g (_root_.GD.N0106.N0428.N0765.N1610.d020750 x) - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)) := by
    filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
    dsimp [f, Function.comp_def]
    rw [_root_.GD.N0106.N0428.N0765.N1610.d020767 location eta heta, _root_.GD.N0106.N0428.N0765.N1610.d020768 location eta heta x hx,
      _root_.GD.N0106.N0428.N0765.N1610.d020748 eta heta]
  have hcomp := (memLp_congr_ae heq).2 hcarrier
  have hn := (memLp_map_measure_iff hf.aestronglyMeasurable
    _root_.GD.N0106.N0428.N0765.N1610.d020746.aemeasurable).2 hcomp
  rw [_root_.GD.N0106.N0428.N0765.N1610.d020747 location eta] at hn
  have hz := _root_.GD.N0232.N0720.N1425.d014724 11 11
    (by norm_num) (by norm_num) location (Real.sqrt eta) 1
    (Real.sqrt_pos.mpr heta) zero_lt_one g hg hn
  have hi := _root_.GD.N0107.d012742 _root_.GD.N0106.N0428.N0765.N1610.d020746
    (show Measurable (fun w => _root_.GD.N0106.N0428.N0765.N1610.d020761 location eta w * f w) by fun_prop)
    (_root_.GD.N0106.N0428.N0765.N1610.d020747 location eta)
  calc
    (∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * (_root_.GD.N0106.N0428.N0765.N1611.d012591 x *
        (g (_root_.GD.N0106.N0428.N0765.N1610.d020750 x) - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)) ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) =
        ∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020761 location eta (_root_.GD.N0106.N0428.N0765.N1610.d020745 x) * f (_root_.GD.N0106.N0428.N0765.N1610.d020745 x)
          ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [_root_.GD.N0106.N0428.N0765.N1610.d020769 location eta heta]
      exact congrArg (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * ·) hx.symm
    _ = 0 := by rw [hi]; exact hz

theorem d020771 (location eta : ℝ) :
    MemLp (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1611.d012609 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta) 0).add
    ((_root_.GD.N0106.N0428.N0765.N1611.d012610 location (_root_.GD.N0106.N0428.N0765.N1611.d012614 eta)).const_mul (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta))
  apply (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).2 h
  dsimp [_root_.GD.N0106.N0428.N0765.N1610.d020762]
  ring

theorem d020772 (location eta : ℝ) (heta : 0 < eta)
    (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) = 0 := by
  let g : ℝ × ℝ → ℝ := fun p => _root_.GD.N0106.N0428.N0765.N1607.d012678 eta + _root_.GD.N0106.N0428.N0765.N1610.d020752 j p
  have heq : (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x * (g (_root_.GD.N0106.N0428.N0765.N1610.d020750 x) - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta))
      =ᵐ[_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta] _root_.GD.N0106.N0428.N0765.N1607.d012646 j := by
    filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
    dsimp [g]
    rw [_root_.GD.N0106.N0428.N0765.N1610.d020758 j x hx]
    simp only [add_sub_cancel_left, _root_.GD.N0106.N0428.N0765.N1607.d012646]
  have hc := (memLp_congr_ae heq).2 (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta j)
  have h := _root_.GD.N0106.N0428.N0765.N1610.d020770 location eta heta g (by fun_prop) hc
  rw [← h]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  exact congrArg (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * ·) hx.symm

theorem d020773 (location eta : ℝ) (heta : 0 < eta) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x
      ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) = 0 := by
  have heq : (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x *
      (_root_.GD.N0106.N0428.N0765.N1610.d020751 (_root_.GD.N0106.N0428.N0765.N1610.d020750 x) - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta))
      =ᵐ[_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta] _root_.GD.N0106.N0428.N0765.N1607.d012679 eta := by
    filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
    rw [_root_.GD.N0106.N0428.N0765.N1610.d020757 x hx]
    rfl
  have h := _root_.GD.N0106.N0428.N0765.N1610.d020770 location eta heta _root_.GD.N0106.N0428.N0765.N1610.d020751
    _root_.GD.N0106.N0428.N0765.N1610.d020755
    ((memLp_congr_ae heq).2 (_root_.GD.N0106.N0428.N0765.N1607.d012681 location eta heta))
  rw [← h]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  exact congrArg (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * ·) hx.symm

theorem d020774 (location eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) :
    _root_.GD.N0106.N0428.N0765.N1611.d012593 x - location = _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x + _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x := by
  unfold _root_.GD.N0106.N0428.N0765.N1611.d012593 _root_.GD.N0106.N0428.N0765.N1534.d005300 _root_.GD.N0106.N0428.N0765.N1610.d020762 _root_.GD.N0106.N0428.N0765.N1607.d012679 _root_.GD.N0106.N0428.N0765.N1607.d012641
  ring

theorem d020775 (location eta : ℝ) (heta : 0 < eta) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    (∫ x, (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) =
      _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta j := by
  have ho : Integrable (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 =>
      _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    simpa only [Pi.mul_def] using
      ((_root_.GD.N0106.N0428.N0765.N1610.d020771 location eta).integrable_mul
        (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta j))
  have hc : Integrable (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 =>
      _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    simpa only [Pi.mul_def] using
      ((_root_.GD.N0106.N0428.N0765.N1607.d012681 location eta heta).integrable_mul
        (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta j))
  simp_rw [_root_.GD.N0106.N0428.N0765.N1610.d020774 location eta, add_mul]
  rw [integral_add
      (f := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x)
      (g := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x) ho hc,
    _root_.GD.N0106.N0428.N0765.N1610.d020772 location eta heta j, zero_add]
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012683
  apply integral_congr_ae
  filter_upwards [] with x
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012679 _root_.GD.N0106.N0428.N0765.N1607.d012646
  ring

def d020776 (location eta : ℝ) (d : _root_.GD.N0106.N0428.N0765.N1610.d020743 → ℝ) : ℝ :=
  ∫ x, (d x - location) ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta

theorem d020777 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    (∫ x, (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012647 b x ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) =
      ∑ j, b j * _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta j := by
  have heq (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012647 b x =
      ∑ j, b j * ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x) := by
    unfold _root_.GD.N0106.N0428.N0765.N1607.d012647
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hint (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : Integrable
      (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => b j * ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x))
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    simpa only [Pi.mul_apply] using
      (((_root_.GD.N0106.N0428.N0765.N1607.d012673 location eta heta).integrable_mul
        (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta j)).const_mul (b j))
  simp_rw [heq]
  rw [integral_finsetSum (Finset.univ : Finset _root_.GD.N0106.N0428.N0765.N1607.d012643)
    (f := fun j (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) => b j * ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x))
    (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1610.d020775 location eta heta j]

theorem d020778 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1607.d012647 b x ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) =
      ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j := by
  have heq (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : _root_.GD.N0106.N0428.N0765.N1607.d012647 b x ^ 2 =
      ∑ i, ∑ j, (b i * b j) * (_root_.GD.N0106.N0428.N0765.N1607.d012646 i x * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x) := by
    unfold _root_.GD.N0106.N0428.N0765.N1607.d012647
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hint (i j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : Integrable
      (fun x => (b i * b j) * (_root_.GD.N0106.N0428.N0765.N1607.d012646 i x * _root_.GD.N0106.N0428.N0765.N1607.d012646 j x)) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) :=
    ((_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta i).integrable_mul
      (_root_.GD.N0106.N0428.N0765.N1607.d012671 location eta heta j)).const_mul (b i * b j)
  simp_rw [heq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => hint i j]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  congr 1
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012677
  apply integral_congr_ae
  filter_upwards [] with x
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012646
  ring


theorem d020779 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) - _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 =
      2 * (∑ j, b j * _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta j) +
        ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j := by
  have herr := _root_.GD.N0106.N0428.N0765.N1607.d012673 location eta heta
  have hpert := _root_.GD.N0106.N0428.N0765.N1607.d012672 location eta heta b
  have heq (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : (_root_.GD.N0106.N0428.N0765.N1607.d012648 b x - location) ^ 2 =
      (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) ^ 2 +
        2 * ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012647 b x) + _root_.GD.N0106.N0428.N0765.N1607.d012647 b x ^ 2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1607.d012648
    ring
  have hcross : Integrable (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 =>
      2 * ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012647 b x)) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    simpa only [Pi.mul_apply] using (herr.integrable_mul hpert).const_mul (2 : ℝ)
  have hleft : Integrable (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) ^ 2 +
      2 * ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012647 b x)) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    exact herr.integrable_sq.fun_add hcross
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020776
  simp_rw [heq]
  rw [integral_add
      (f := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) ^ 2 +
        2 * ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012647 b x))
      (g := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1607.d012647 b x ^ 2) hleft hpert.integrable_sq,
    integral_add (f := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => (_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) ^ 2)
      (g := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => 2 * ((_root_.GD.N0106.N0428.N0765.N1611.d012593 x - location) * _root_.GD.N0106.N0428.N0765.N1607.d012647 b x))
      herr.integrable_sq hcross,
    integral_const_mul, _root_.GD.N0106.N0428.N0765.N1610.d020777 location eta heta b,
    _root_.GD.N0106.N0428.N0765.N1610.d020778 location eta heta b]
  ring

def d020780 (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : ℝ := _root_.GD.N0106.N0428.N0765.N1611.d012589 0 x + _root_.GD.N0106.N0428.N0765.N1611.d012591 x * _root_.GD.N0106.N0428.N0765.N1610.d020749 x

theorem d020781 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11) =ᵐ[_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta] _root_.GD.N0106.N0428.N0765.N1610.d020780 := by
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
  exact _root_.GD.N0106.N0428.N0765.N1606.d012636 x hx

theorem d020782 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) =
      _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1610.d020780 := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020776
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1610.d020781 location eta heta] with x hx
  rw [hx]

def d020783 (eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1611.d012591 x * (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)

theorem d020784 (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1610.d020749 x ∈ Icc (0 : ℝ) 1 := by
  have hs := _root_.GD.N0106.N0428.N0765.N1607.d012661 x hx
  constructor
  · exact div_nonneg (hx 0).le hs.le
  · exact (div_le_one hs).2 (le_add_of_nonneg_right (hx 1).le)

theorem d020785 (location eta : ℝ) (heta : 0 < eta) :
    MemLp (_root_.GD.N0106.N0428.N0765.N1610.d020783 eta) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  apply (memLp_two_iff_integrable_sq (by unfold _root_.GD.N0106.N0428.N0765.N1610.d020783; fun_prop)).2
  apply ((_root_.GD.N0106.N0428.N0765.N1607.d012665 location eta heta 2).integrable_sq).mono'
  · unfold _root_.GD.N0106.N0428.N0765.N1610.d020783
    fun_prop
  · filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location _ (_root_.GD.N0106.N0428.N0765.N1611.d012615 eta heta)] with x hx
    have hw := _root_.GD.N0106.N0428.N0765.N1610.d020784 x hx
    have ho := _root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta
    have hab : |_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta| ≤ 1 :=
      abs_le.mpr ⟨by linarith only [hw.1, ho.2], by linarith only [hw.2, ho.1]⟩
    have hsq : (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)) hab 2
      simpa only [sq_abs, one_pow] using h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold _root_.GD.N0106.N0428.N0765.N1610.d020783
    rw [mul_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (sq_nonneg (_root_.GD.N0106.N0428.N0765.N1611.d012591 x))

theorem d020786 (location eta : ℝ) (heta : 0 < eta) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x
      ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) = 0 :=
  _root_.GD.N0106.N0428.N0765.N1610.d020770 location eta heta Prod.fst measurable_fst
    (_root_.GD.N0106.N0428.N0765.N1610.d020785 location eta heta)

theorem d020787 (location eta : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) :
    _root_.GD.N0106.N0428.N0765.N1610.d020780 x - location = _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x + _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x := by
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020780 _root_.GD.N0106.N0428.N0765.N1610.d020762 _root_.GD.N0106.N0428.N0765.N1610.d020783
  ring

theorem d020788 (location eta : ℝ) (heta : 0 < eta) :
    MemLp (fun x => _root_.GD.N0106.N0428.N0765.N1610.d020780 x - location) 2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1610.d020787 location eta]
  exact (_root_.GD.N0106.N0428.N0765.N1610.d020771 location eta).add (_root_.GD.N0106.N0428.N0765.N1610.d020785 location eta heta)

theorem d020789 (location eta : ℝ) (heta : 0 < eta) :
    MemLp (fun x => _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11) x - location)
      2 (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  apply (memLp_congr_ae ?_).2 (_root_.GD.N0106.N0428.N0765.N1610.d020788 location eta heta)
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1610.d020781 location eta heta] with x hx
  rw [hx]

theorem d020790 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 =
      (∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) +
        ∫ x, _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta := by
  have ho := _root_.GD.N0106.N0428.N0765.N1610.d020771 location eta
  have hc := _root_.GD.N0106.N0428.N0765.N1607.d012681 location eta heta
  have hcross : Integrable (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 =>
      2 * (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x))
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    simpa only [Pi.mul_apply] using (ho.integrable_mul hc).const_mul (2 : ℝ)
  have hleft : Integrable (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x ^ 2 +
      2 * (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x))
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    exact ho.integrable_sq.fun_add hcross
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020776
  simp_rw [_root_.GD.N0106.N0428.N0765.N1610.d020774 location eta, add_sq, mul_assoc]
  rw [integral_add
      (f := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x ^ 2 +
        2 * (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x))
      (g := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x ^ 2) hleft hc.integrable_sq,
    integral_add (f := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x ^ 2)
      (g := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => 2 * (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x))
      ho.integrable_sq hcross]
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1610.d020773 location eta heta]
  ring

theorem d020791 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1610.d020780 =
      (∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) +
        ∫ x, _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta := by
  have ho := _root_.GD.N0106.N0428.N0765.N1610.d020771 location eta
  have hc := _root_.GD.N0106.N0428.N0765.N1610.d020785 location eta heta
  have hcross : Integrable (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 =>
      2 * (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x))
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    simpa only [Pi.mul_apply] using (ho.integrable_mul hc).const_mul (2 : ℝ)
  have hleft : Integrable (fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x ^ 2 +
      2 * (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x))
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
    exact ho.integrable_sq.fun_add hcross
  unfold _root_.GD.N0106.N0428.N0765.N1610.d020776
  simp_rw [_root_.GD.N0106.N0428.N0765.N1610.d020787 location eta, add_sq, mul_assoc]
  rw [integral_add
      (f := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x ^ 2 +
        2 * (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x))
      (g := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x ^ 2) hleft hc.integrable_sq,
    integral_add (f := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => _root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x ^ 2)
      (g := fun x : _root_.GD.N0106.N0428.N0765.N1610.d020743 => 2 * (_root_.GD.N0106.N0428.N0765.N1610.d020762 location eta x * _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x))
      ho.integrable_sq hcross]
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1610.d020786 location eta heta]
  ring


theorem d020792 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 - _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1610.d020780 =
      ∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * ((_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 -
        (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2) ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta := by
  rw [_root_.GD.N0106.N0428.N0765.N1610.d020790 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1610.d020791 location eta heta]
  have heq (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) : _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 *
      ((_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2) =
      _root_.GD.N0106.N0428.N0765.N1607.d012679 eta x ^ 2 - _root_.GD.N0106.N0428.N0765.N1610.d020783 eta x ^ 2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1607.d012679 _root_.GD.N0106.N0428.N0765.N1610.d020783
    ring
  simp_rw [heq]
  rw [integral_sub (_root_.GD.N0106.N0428.N0765.N1607.d012681 location eta heta).integrable_sq
    (_root_.GD.N0106.N0428.N0765.N1610.d020785 location eta heta).integrable_sq]
  ring


theorem d020793 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) =
      ∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * ((_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 -
        (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2) ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta := by
  rw [_root_.GD.N0106.N0428.N0765.N1610.d020782 location eta heta]
  exact _root_.GD.N0106.N0428.N0765.N1610.d020792 location eta heta

theorem d020794 (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (x : _root_.GD.N0106.N0428.N0765.N1610.d020743) :
    _root_.GD.N0106.N0428.N0765.N1607.d012648 b x = _root_.GD.N0106.N0428.N0765.N1611.d012593 x + _root_.GD.N0106.N0428.N0765.N1611.d012591 x * ∑ j, b j * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x := by
  rw [_root_.GD.N0106.N0428.N0765.N1607.d012648, _root_.GD.N0106.N0428.N0765.N1607.d012684]


theorem d020795 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) =
      ∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * ((_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 -
        (_root_.GD.N0106.N0428.N0765.N1610.d020749 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2) ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ∧
    Integrable (fun x => (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ∧
    (∫ x, (_root_.GD.N0106.N0428.N0765.N1607.d012640 x)⁻¹ ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ≤ 1 / 48 ∧
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 6) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) ∧
    (∀ j, Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 *
      (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) ∧
    (∀ i j, Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * _root_.GD.N0106.N0428.N0765.N1607.d012645 i x * _root_.GD.N0106.N0428.N0765.N1607.d012645 j x)
      (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) ∧
    (∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ, Measurable (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) ∧
      (∫⁻ x, ENNReal.ofReal ((_root_.GD.N0106.N0428.N0765.N1607.d012648 b x - location) ^ 2)
        ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) < ⊤ ∧
      _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) - _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 =
        2 * (∑ j, b j * _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta j) +
          ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1607.d012677 location eta i j) := by
  exact ⟨_root_.GD.N0106.N0428.N0765.N1610.d020793 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012663 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012664 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012666 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012682 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1607.d012676 location eta heta,
    fun b => ⟨_root_.GD.N0106.N0428.N0765.N1607.d012656 b, _root_.GD.N0106.N0428.N0765.N1607.d012675 location eta heta b,
      _root_.GD.N0106.N0428.N0765.N1610.d020779 location eta heta b⟩⟩

end
end GD.N0106.N0428.N0765.N1610

#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020747
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020757
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020770
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020772
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020775
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020779
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020792
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020793
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020794
#print axioms _root_.GD.N0106.N0428.N0765.N1610.d020795
