import GD.Module1316
import GD.Module0346
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1592
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663 _root_.GD.N0106.N0428.N0765.N1672 _root_.GD.N0106.N0428.N0765.N1526
open _root_.GD.N0106.N0428.N0765.N1591

def d022705 (axis : Bool) (w z : ℂ) : ℂ := if axis then z else w
def d022706 (axis : Bool) (w z : ℂ) : ℂ := if axis then w else z

def d022707 (axis : Bool) (w : ℂ) : Set ℂ :=
  {z | ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im < Real.pi}

def d022708 (axis : Bool) (w z : ℂ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1526.d021443 (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im

def d022709 (num : Bool) (e x : ℝ) : ℂ :=
  if num then ((x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x : ℝ) : ℂ) else 1

def d022710 (num axis : Bool) (e : ℝ) (w z : ℂ) (x : ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1592.d022709 num e x * _root_.GD.N0106.N0428.N0765.N1591.d021498 e x (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z)

def d022711 (num axis : Bool) (e : ℝ) (w z : ℂ) (x : ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1592.d022709 num e x *
    (if axis then _root_.GD.N0106.N0428.N0765.N1591.d021506 e x z w else _root_.GD.N0106.N0428.N0765.N1591.d021507 e x w z)

def d022712 (num axis : Bool) (e : ℝ) (w z : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1592.d022710 num axis e w z x

def d022713 (num axis : Bool) (e : ℝ) (w z : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1592.d022711 num axis e w z x

theorem d022714 (axis : Bool) (w : ℂ) : IsOpen (_root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) := by
  have hc : Continuous (fun z : ℂ => ((21 : ℝ) / 2) *
      _root_.GD.N0106.N0428.N0765.N1538.d021192 (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im) := by
    cases axis <;> unfold _root_.GD.N0106.N0428.N0765.N1592.d022705 _root_.GD.N0106.N0428.N0765.N1592.d022706 _root_.GD.N0106.N0428.N0765.N1538.d021192
      <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  exact isOpen_lt hc continuous_const

theorem d022715 (axis : Bool) (w : ℂ) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1592.d022708 axis w) (_root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) := by
  have hb : Continuous (fun z => _root_.GD.N0106.N0428.N0765.N1526.d021442 (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im) := by
    cases axis <;> unfold _root_.GD.N0106.N0428.N0765.N1592.d022705 _root_.GD.N0106.N0428.N0765.N1592.d022706 _root_.GD.N0106.N0428.N0765.N1526.d021442 _root_.GD.N0106.N0428.N0765.N1538.d021192
      <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  apply hb.continuousOn.rpow_const
  intro z hz
  apply Or.inl
  apply (_root_.GD.N0106.N0428.N0765.N1526.d021444 _ _ _ _).ne'
  have hw0 := _root_.GD.N0106.N0428.N0765.N1538.d021193 (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im
  change ((21 : ℝ) / 2) * _ < Real.pi at hz
  linarith

theorem d022716 (num axis : Bool) {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Ioo (0 : ℝ) 1) {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1592.d022710 num axis e w q x)
      (_root_.GD.N0106.N0428.N0765.N1592.d022711 num axis e w z x) z := by
  cases axis
  · exact (_root_.GD.N0106.N0428.N0765.N1591.d021509 he hx hz).const_mul (_root_.GD.N0106.N0428.N0765.N1592.d022709 num e x)
  · exact (_root_.GD.N0106.N0428.N0765.N1591.d021508 he hx hz).const_mul (_root_.GD.N0106.N0428.N0765.N1592.d022709 num e x)

theorem d022717 (num axis : Bool) {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Ioo (0 : ℝ) 1) {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    ‖_root_.GD.N0106.N0428.N0765.N1592.d022710 num axis e w z x‖ ≤ _root_.GD.N0106.N0428.N0765.N1592.d022708 axis w z := by
  have hw0 := _root_.GD.N0106.N0428.N0765.N1538.d021193 (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im
  have hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im < Real.pi := by
    change ((21 : ℝ) / 2) * _ < Real.pi at hz
    linarith
  cases num
  · simpa only [_root_.GD.N0106.N0428.N0765.N1592.d022710, _root_.GD.N0106.N0428.N0765.N1592.d022709, Bool.false_eq_true, if_false, one_mul,
      _root_.GD.N0106.N0428.N0765.N1592.d022708, ← _root_.GD.N0106.N0428.N0765.N1591.d021502] using
      _root_.GD.N0106.N0428.N0765.N1526.d021449 he hx (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re
        (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im hw
  · simpa only [_root_.GD.N0106.N0428.N0765.N1592.d022710, _root_.GD.N0106.N0428.N0765.N1592.d022709, if_true, _root_.GD.N0106.N0428.N0765.N1592.d022708, ← _root_.GD.N0106.N0428.N0765.N1591.d021502,
      _root_.GD.N0106.N0428.N0765.N1526.d021450] using
      _root_.GD.N0106.N0428.N0765.N1526.d021451 he hx (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re
        (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im hw

theorem d022718 (c : ℂ) : Measurable (fun x : ℂ => x ^ c) := by
  simp only [Complex.cpow_def]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Complex.measurable_exp.comp (Complex.measurable_log.mul_const c))

theorem d022719 (e : ℝ) : Measurable (fun x : ℝ =>
    (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10 : ℝ) : ℂ)) := by
  apply Continuous.measurable
  have hp := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 9 / 2)).comp
    (show Continuous (fun x : ℝ => x * (1 - x)) by fun_prop)
  exact Complex.continuous_ofReal.comp (hp.mul (by unfold _root_.GD.N0106.N0428.N0765.N1663.d021403; fun_prop))

theorem d022720 (e : ℝ) (z w : ℂ) : Measurable (fun x => _root_.GD.N0106.N0428.N0765.N1591.d021498 e x z w) := by
  exact (_root_.GD.N0106.N0428.N0765.N1592.d022719 e).mul ((_root_.GD.N0106.N0428.N0765.N1592.d022718 _).comp
    (show Measurable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1591.d021497 e x z w) by unfold _root_.GD.N0106.N0428.N0765.N1591.d021497; fun_prop))

theorem d022721 (e : ℝ) (z w : ℂ) : Measurable (fun x => _root_.GD.N0106.N0428.N0765.N1591.d021506 e x z w) := by
  unfold _root_.GD.N0106.N0428.N0765.N1591.d021506
  exact (_root_.GD.N0106.N0428.N0765.N1592.d022719 e).mul ((measurable_const.mul ((_root_.GD.N0106.N0428.N0765.N1592.d022718 _).comp
    (show Measurable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1591.d021497 e x z w) by unfold _root_.GD.N0106.N0428.N0765.N1591.d021497; fun_prop))).mul
    (show Measurable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1591.d021499 e x z w) by unfold _root_.GD.N0106.N0428.N0765.N1591.d021499; fun_prop))

theorem d022722 (e : ℝ) (z w : ℂ) : Measurable (fun x => _root_.GD.N0106.N0428.N0765.N1591.d021507 e x z w) := by
  unfold _root_.GD.N0106.N0428.N0765.N1591.d021507
  exact (_root_.GD.N0106.N0428.N0765.N1592.d022719 e).mul ((measurable_const.mul ((_root_.GD.N0106.N0428.N0765.N1592.d022718 _).comp
    (show Measurable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1591.d021497 e x z w) by unfold _root_.GD.N0106.N0428.N0765.N1591.d021497; fun_prop))).mul
    (show Measurable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1591.d021500 e x z w) by unfold _root_.GD.N0106.N0428.N0765.N1591.d021500; fun_prop))

theorem d022723 (num : Bool) (e : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1592.d022709 num e) := by
  cases num <;> unfold _root_.GD.N0106.N0428.N0765.N1592.d022709 _root_.GD.N0106.N0428.N0765.N1663.d021403
    <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

theorem d022724 (num axis : Bool) (e : ℝ) (w z : ℂ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1592.d022710 num axis e w z) :=
  (_root_.GD.N0106.N0428.N0765.N1592.d022723 num e).mul (_root_.GD.N0106.N0428.N0765.N1592.d022720 e _ _)

theorem d022725 (num axis : Bool) (e : ℝ) (w z : ℂ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1592.d022711 num axis e w z) := by
  cases axis
  · exact (_root_.GD.N0106.N0428.N0765.N1592.d022723 num e).mul (_root_.GD.N0106.N0428.N0765.N1592.d022722 e w z)
  · exact (_root_.GD.N0106.N0428.N0765.N1592.d022723 num e).mul (_root_.GD.N0106.N0428.N0765.N1592.d022721 e z w)



theorem d022726 (num axis : Bool) {e : ℝ} (he : 0 ≤ e)
    {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    HasDerivAt (_root_.GD.N0106.N0428.N0765.N1592.d022712 num axis e w) (_root_.GD.N0106.N0428.N0765.N1592.d022713 num axis e w z) z := by
  apply (_root_.GD.N0106.N0428.N0764.d005147
    (_root_.GD.N0106.N0428.N0765.N1592.d022714 axis w) (_root_.GD.N0106.N0428.N0765.N1592.d022715 axis w)
    (fun q _ => (_root_.GD.N0106.N0428.N0765.N1592.d022724 num axis e w q).aestronglyMeasurable)
    (fun q _ => (_root_.GD.N0106.N0428.N0765.N1592.d022725 num axis e w q).aestronglyMeasurable)
    ?_ hz).2
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  intro q hq
  exact ⟨_root_.GD.N0106.N0428.N0765.N1592.d022716 num axis he hx hq, _root_.GD.N0106.N0428.N0765.N1592.d022717 num axis he hx hq⟩


theorem d022727 (axis : Bool) (e : ℝ) (w z : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1592.d022712 false axis e w z = _root_.GD.N0106.N0428.N0765.N1672.d021423 e
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im := by
  simp only [_root_.GD.N0106.N0428.N0765.N1592.d022712, _root_.GD.N0106.N0428.N0765.N1672.d021423, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, _root_.GD.N0106.N0428.N0765.N1592.d022710, _root_.GD.N0106.N0428.N0765.N1592.d022709, Bool.false_eq_true,
    if_false, one_mul, ← _root_.GD.N0106.N0428.N0765.N1591.d021502]

theorem d022728 (axis : Bool) (e : ℝ) (w z : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1592.d022712 true axis e w z = _root_.GD.N0106.N0428.N0765.N1672.d021424 e
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).re
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z).im := by
  simp only [_root_.GD.N0106.N0428.N0765.N1592.d022712, _root_.GD.N0106.N0428.N0765.N1672.d021424, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, _root_.GD.N0106.N0428.N0765.N1592.d022710, _root_.GD.N0106.N0428.N0765.N1592.d022709, if_true, ← _root_.GD.N0106.N0428.N0765.N1591.d021502]


theorem d022729 (axis : Bool) {e : ℝ} (he : 0 ≤ e)
    {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1672.d021423 e
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w q).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q).re
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w q).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q).im)
      (_root_.GD.N0106.N0428.N0765.N1592.d022713 false axis e w z) z := by
  have h := _root_.GD.N0106.N0428.N0765.N1592.d022726 false axis he hz
  change HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1592.d022712 false axis e w q) _ z at h
  simpa only [_root_.GD.N0106.N0428.N0765.N1592.d022727] using h


theorem d022730 (axis : Bool) {e : ℝ} (he : 0 ≤ e)
    {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1672.d021424 e
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w q).re (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q).re
      (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w q).im (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q).im)
      (_root_.GD.N0106.N0428.N0765.N1592.d022713 true axis e w z) z := by
  have h := _root_.GD.N0106.N0428.N0765.N1592.d022726 true axis he hz
  change HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1592.d022712 true axis e w q) _ z at h
  simpa only [_root_.GD.N0106.N0428.N0765.N1592.d022728] using h

end
end GD.N0106.N0428.N0765.N1592
#print axioms _root_.GD.N0106.N0428.N0765.N1592.d022726
