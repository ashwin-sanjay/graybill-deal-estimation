import GD.Module0870
import GD.Module0884
import Mathlib.MeasureTheory.Function.Holder














open MeasureTheory Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1266

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1271

abbrev d013712 := _root_.GD.N0232.N0720.N1290.d004131 × _root_.GD.N0232.N0720.N1290.d004131

def d013713 (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1290.d004131 := ⟨t.1, t.2.1.le, t.2.2.le⟩

def d013714 (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) : ℝ :=
  (1 - (p.2 : ℝ)) * ((p.1 : ℝ) * (1 - t.1) + (1 - (p.1 : ℝ)) * t.1) +
    (p.2 : ℝ) * _root_.GD.N0232.N0720.N1271.d013403 t.1

theorem d013715 (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1271.d013403 t.1 ≤ _root_.GD.N0232.N0720.N1266.d013714 t p := by
  have hbase : _root_.GD.N0232.N0720.N1271.d013403 t.1 ≤
      (p.1 : ℝ) * (1 - t.1) + (1 - (p.1 : ℝ)) * t.1 := by
    have hnonneg := add_nonneg
      (mul_nonneg p.1.2.1 (sq_nonneg (1 - t.1)))
      (mul_nonneg (sub_nonneg.mpr p.1.2.2) (sq_nonneg t.1))
    unfold _root_.GD.N0232.N0720.N1271.d013403
    nlinarith
  have h := mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr p.2.2.2)
  unfold _root_.GD.N0232.N0720.N1266.d013714
  nlinarith

theorem d013716 (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) :
    0 < _root_.GD.N0232.N0720.N1266.d013714 t p :=
  (_root_.GD.N0232.N0720.N1271.d013408 t.2.1 t.2.2).trans_le (_root_.GD.N0232.N0720.N1266.d013715 t p)

@[fun_prop] theorem d013717 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1266.d013712 ↦ _root_.GD.N0232.N0720.N1266.d013714 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1266.d013714 _root_.GD.N0232.N0720.N1271.d013403
  fun_prop

def d013718 (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) : ℝ :=
  16 * (_root_.GD.N0232.N0720.N1271.d013403 t.1) ^ 2 * _root_.GD.N0232.N0720.N1266.d013714 t p ^ (-(5 / 2 : ℝ)) /
    _root_.GD.N0232.N0720.N1266.d013714 _root_.GD.N0232.N0720.N1441.d013677 p ^ (-(5 / 2 : ℝ))

theorem d013719 (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) :
    0 < _root_.GD.N0232.N0720.N1266.d013718 t p := by
  unfold _root_.GD.N0232.N0720.N1266.d013718
  exact div_pos (mul_pos (mul_pos (by norm_num)
    (sq_pos_of_pos (_root_.GD.N0232.N0720.N1271.d013408 t.2.1 t.2.2)))
    (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1266.d013716 t p) _))
    (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1266.d013716 _root_.GD.N0232.N0720.N1441.d013677 p) _)

@[fun_prop] theorem d013720 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1266.d013712 ↦ _root_.GD.N0232.N0720.N1266.d013718 p.1 p.2) := by
  have hK : Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1266.d013712 ↦
      _root_.GD.N0232.N0720.N1266.d013714 p.1 p.2 ^ (-(5 / 2 : ℝ))) :=
    _root_.GD.N0232.N0720.N1266.d013717.rpow_const (fun p ↦ Or.inl (_root_.GD.N0232.N0720.N1266.d013716 _ _).ne')
  have hK0 : Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1266.d013712 ↦
      _root_.GD.N0232.N0720.N1266.d013714 _root_.GD.N0232.N0720.N1441.d013677 p.2 ^ (-(5 / 2 : ℝ))) :=
    (_root_.GD.N0232.N0720.N1266.d013717.comp (continuous_const.prodMk continuous_snd)).rpow_const
      (fun p ↦ Or.inl (_root_.GD.N0232.N0720.N1266.d013716 _ _).ne')
  exact ((continuous_const.mul (by unfold _root_.GD.N0232.N0720.N1271.d013403; fun_prop)).mul hK).div hK0
    (fun p ↦ (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1266.d013716 _root_.GD.N0232.N0720.N1441.d013677 p.2) _).ne')

def d013721 (t : _root_.GD.N0232.N0720.N1441.d013676) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) where
  toFun := _root_.GD.N0232.N0720.N1266.d013718 t
  continuous_toFun := _root_.GD.N0232.N0720.N1266.d013720.comp (continuous_const.prodMk continuous_id)

@[fun_prop] theorem d013722 : Continuous _root_.GD.N0232.N0720.N1266.d013721 := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact _root_.GD.N0232.N0720.N1266.d013720

def d013723 (a : ℝ) : _root_.GD.N0232.N0720.N1290.d004131 :=
  ⟨max 0 (min 1 a), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem d013724 : Measurable _root_.GD.N0232.N0720.N1266.d013723 := by
  apply Measurable.subtype_mk
  exact measurable_const.max (measurable_const.min measurable_id)

theorem d013725 {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1266.d013723 a : ℝ) = a := by
  simp [_root_.GD.N0232.N0720.N1266.d013723, min_eq_right ha.2, max_eq_right ha.1]



def d013726 (x : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1266.d013712 :=
  (_root_.GD.N0232.N0720.N1266.d013723 x.1, _root_.GD.N0232.N0720.N1266.d013723 (x.2 / (1 + x.2)))

theorem d013727 : Measurable _root_.GD.N0232.N0720.N1266.d013726 := by
  exact (_root_.GD.N0232.N0720.N1266.d013724.comp measurable_fst).prodMk
    (_root_.GD.N0232.N0720.N1266.d013724.comp (measurable_snd.div (measurable_const.add measurable_snd)))

theorem d013728 {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    ((_root_.GD.N0232.N0720.N1266.d013726 x).1 : ℝ) = x.1 ∧ ((_root_.GD.N0232.N0720.N1266.d013726 x).2 : ℝ) = x.2 / (1 + x.2) := by
  have hx2 : 0 < x.2 := hx.2
  refine ⟨_root_.GD.N0232.N0720.N1266.d013725 ⟨hx.1.1.le, hx.1.2.le⟩, ?_⟩
  apply _root_.GD.N0232.N0720.N1266.d013725
  constructor
  · exact div_nonneg hx2.le (by linarith)
  · apply (div_le_one (by linarith : 0 < 1 + x.2)).mpr
    linarith

theorem d013729 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1266.d013714 t (_root_.GD.N0232.N0720.N1266.d013726 x) = _root_.GD.N0232.N0720.N1271.d013404 x (_root_.GD.N0232.N0720.N1266.d013713 t) / (1 + x.2) := by
  obtain ⟨hr, hs⟩ := _root_.GD.N0232.N0720.N1266.d013728 hx
  have hx2 : 0 < x.2 := hx.2
  simp only [_root_.GD.N0232.N0720.N1266.d013714, hr, hs, _root_.GD.N0232.N0720.N1271.d013404, _root_.GD.N0232.N0720.N1266.d013713]
  field_simp [show 1 + x.2 ≠ 0 by linarith]
  ring

theorem d013730 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x) =
      16 * (_root_.GD.N0232.N0720.N1271.d013403 t.1) ^ 2 * _root_.GD.N0232.N0720.N1271.d013404 x (_root_.GD.N0232.N0720.N1266.d013713 t) ^ (-(5 / 2 : ℝ)) /
        _root_.GD.N0232.N0720.N1271.d013404 x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-(5 / 2 : ℝ)) := by
  have hx2 : 0 < x.2 := hx.2
  have hs : 0 < 1 + x.2 := by linarith
  have hp := _root_.GD.N0232.N0720.N1271.d013407 hx (_root_.GD.N0232.N0720.N1266.d013713 t)
  have hp0 := _root_.GD.N0232.N0720.N1271.d013407 hx (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677)
  unfold _root_.GD.N0232.N0720.N1266.d013718
  rw [_root_.GD.N0232.N0720.N1266.d013729 hx t, _root_.GD.N0232.N0720.N1266.d013729 hx _root_.GD.N0232.N0720.N1441.d013677,
    Real.div_rpow hp.le hs.le, Real.div_rpow hp0.le hs.le]
  have hz : (1 + x.2) ^ (-(5 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
  field_simp [hz, (Real.rpow_pos_of_pos hp0 _).ne']


theorem d013731
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1436.d013273 2 2 t.1 x =
      _root_.GD.N0232.N0720.N1436.d013273 2 2 (1 / 2) x * _root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x) := by
  have ht := _root_.GD.N0232.N0720.N1271.d013413 hx (_root_.GD.N0232.N0720.N1266.d013713 t) t.2.1 t.2.2
  have hm := _root_.GD.N0232.N0720.N1271.d013413 hx (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677)
    (by norm_num [_root_.GD.N0232.N0720.N1266.d013713, _root_.GD.N0232.N0720.N1441.d013677]) (by norm_num [_root_.GD.N0232.N0720.N1266.d013713, _root_.GD.N0232.N0720.N1441.d013677])
  change _root_.GD.N0232.N0720.N1436.d013273 2 2 t.1 x = _ at ht
  change _root_.GD.N0232.N0720.N1436.d013273 2 2 (1 / 2) x = _ at hm
  rw [ht, hm, _root_.GD.N0232.N0720.N1266.d013730 hx t]
  have hp0 := _root_.GD.N0232.N0720.N1271.d013407 hx (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677)
  have hv0 : _root_.GD.N0232.N0720.N1271.d013403 (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677 : ℝ) = (1 / 4 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1266.d013713, _root_.GD.N0232.N0720.N1441.d013677, _root_.GD.N0232.N0720.N1271.d013403]
  have hvt : _root_.GD.N0232.N0720.N1271.d013403 (_root_.GD.N0232.N0720.N1266.d013713 t : ℝ) = _root_.GD.N0232.N0720.N1271.d013403 t.1 := rfl
  rw [hv0, hvt]
  field_simp [(Real.rpow_pos_of_pos hp0 (-(5 / 2 : ℝ))).ne']
  ring

theorem d013732 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Measurable (fun x ↦ _root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x)) :=
  (_root_.GD.N0232.N0720.N1266.d013721 t).continuous.measurable.comp _root_.GD.N0232.N0720.N1266.d013727



theorem d013733 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013678 2 2 t = (_root_.GD.N0232.N0720.N1441.d013679 2 2).withDensity
      (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x))) := by
  unfold _root_.GD.N0232.N0720.N1441.d013678 _root_.GD.N0232.N0720.N1441.d013679 _root_.GD.N0232.N0720.N1436.d013289
  rw [← withDensity_mul _
    (_root_.GD.N0232.N0720.N1436.d013279 2 2 (1 / 2)).ennreal_ofReal
    (_root_.GD.N0232.N0720.N1266.d013732 t).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  simp only [Pi.mul_apply]
  rw [_root_.GD.N0232.N0720.N1266.d013731 hx t]
  exact ENNReal.ofReal_mul (_root_.GD.N0232.N0720.N1436.d013286 (by omega : 2 ≤ 2)
    (by omega : 2 ≤ 2) (by norm_num) (by norm_num) hx).le

theorem d013734 (t : _root_.GD.N0232.N0720.N1441.d013676) (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    (∫ x, f x ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 t) =
      ∫ x, _root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x) * f x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2 := by
  rw [_root_.GD.N0232.N0720.N1266.d013733,
    integral_withDensity_eq_integral_toReal_smul
      (_root_.GD.N0232.N0720.N1266.d013732 t).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1266.d013719 t (_root_.GD.N0232.N0720.N1266.d013726 x)).le, smul_eq_mul])

end
end GD.N0232.N0720.N1266

#print axioms _root_.GD.N0232.N0720.N1266.d013722
#print axioms _root_.GD.N0232.N0720.N1266.d013731
