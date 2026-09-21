import GD.Module0872
import GD.Module0885









open MeasureTheory Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1312

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1271 (d013403 d013408)
open _root_.GD.N0232.N0720.N1266
  (d013712 d013713 d013726 d013727 d013728)
open _root_.GD.N0232.N0720.N1336

variable (m n : ℕ)

def d013793 (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) : ℝ :=
  (1 - (p.2 : ℝ)) * (((n - 1 : ℕ) : ℝ) * (p.1 : ℝ) * (1 - t.1) +
    ((m - 1 : ℕ) : ℝ) * (1 - (p.1 : ℝ)) * t.1) +
      (p.2 : ℝ) * _root_.GD.N0232.N0720.N1271.d013403 t.1

theorem d013794 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1271.d013403 t.1 ≤ _root_.GD.N0232.N0720.N1312.d013793 m n t p := by
  have hm1 : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m - 1 by omega)
  have hn1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - 1 by omega)
  have hX := mul_le_mul_of_nonneg_right hn1
    (mul_nonneg p.1.2.1 (sub_pos.mpr t.2.2).le)
  have hY := mul_le_mul_of_nonneg_right hm1
    (mul_nonneg (sub_nonneg.mpr p.1.2.2) t.2.1.le)
  have hbase : (p.1 : ℝ) * (1 - t.1) + (1 - (p.1 : ℝ)) * t.1 ≤
      ((n - 1 : ℕ) : ℝ) * (p.1 : ℝ) * (1 - t.1) +
        ((m - 1 : ℕ) : ℝ) * (1 - (p.1 : ℝ)) * t.1 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr p.2.2.2)
  have hb := _root_.GD.N0232.N0720.N1266.d013715 t p
  unfold _root_.GD.N0232.N0720.N1312.d013793 _root_.GD.N0232.N0720.N1266.d013714 at *
  linarith

theorem d013795 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) :
    0 < _root_.GD.N0232.N0720.N1312.d013793 m n t p :=
  (_root_.GD.N0232.N0720.N1271.d013408 t.2.1 t.2.2).trans_le (_root_.GD.N0232.N0720.N1312.d013794 m n hm hn t p)

@[fun_prop] theorem d013796 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1266.d013712 ↦ _root_.GD.N0232.N0720.N1312.d013793 m n p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1312.d013793 _root_.GD.N0232.N0720.N1271.d013403
  fun_prop

def d013797 (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) : ℝ :=
  _root_.GD.N0232.N0720.N1336.d013426 m n t.1 * _root_.GD.N0232.N0720.N1312.d013793 m n t p ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n) /
    (_root_.GD.N0232.N0720.N1336.d013426 m n _root_.GD.N0232.N0720.N1441.d013677.1 *
      _root_.GD.N0232.N0720.N1312.d013793 m n _root_.GD.N0232.N0720.N1441.d013677 p ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n))

theorem d013798 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (p : _root_.GD.N0232.N0720.N1266.d013712) :
    0 < _root_.GD.N0232.N0720.N1312.d013797 m n t p :=
  div_pos
    (mul_pos (_root_.GD.N0232.N0720.N1336.d013427 m n t.2.1 t.2.2)
      (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1312.d013795 m n hm hn t p) _))
    (mul_pos (_root_.GD.N0232.N0720.N1336.d013427 m n _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2)
      (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1312.d013795 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 p) _))

@[fun_prop] theorem d013799 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1266.d013712 ↦ _root_.GD.N0232.N0720.N1312.d013797 m n p.1 p.2) := by
  have hK : Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1266.d013712 ↦
      _root_.GD.N0232.N0720.N1312.d013793 m n p.1 p.2 ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)) :=
    (_root_.GD.N0232.N0720.N1312.d013796 m n).rpow_const
      (fun p ↦ Or.inl (_root_.GD.N0232.N0720.N1312.d013795 m n hm hn _ _).ne')
  have hK0 : Continuous (fun p : _root_.GD.N0232.N0720.N1441.d013676 × _root_.GD.N0232.N0720.N1266.d013712 ↦
      _root_.GD.N0232.N0720.N1312.d013793 m n _root_.GD.N0232.N0720.N1441.d013677 p.2 ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)) :=
    ((_root_.GD.N0232.N0720.N1312.d013796 m n).comp (continuous_const.prodMk continuous_snd)).rpow_const
      (fun p ↦ Or.inl (_root_.GD.N0232.N0720.N1312.d013795 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 p.2).ne')
  exact (((_root_.GD.N0232.N0720.N1336.d013428 m n).comp continuous_fst).mul hK).div
    (continuous_const.mul hK0) (fun p ↦ (mul_pos
      (_root_.GD.N0232.N0720.N1336.d013427 m n _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2)
      (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1312.d013795 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 p.2) _)).ne')

def d013800 (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0232.N0720.N1441.d013676) : C(_root_.GD.N0232.N0720.N1266.d013712, ℝ) where
  toFun := _root_.GD.N0232.N0720.N1312.d013797 m n t
  continuous_toFun := (_root_.GD.N0232.N0720.N1312.d013799 m n hm hn).comp
    (continuous_const.prodMk continuous_id)

@[fun_prop] theorem d013801 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Continuous (_root_.GD.N0232.N0720.N1312.d013800 m n hm hn) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact _root_.GD.N0232.N0720.N1312.d013799 m n hm hn

theorem d013802 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1312.d013793 m n t (_root_.GD.N0232.N0720.N1266.d013726 x) = _root_.GD.N0232.N0720.N1336.d013420 m n x (_root_.GD.N0232.N0720.N1266.d013713 t) / (1 + x.2) := by
  obtain ⟨hr, hs⟩ := _root_.GD.N0232.N0720.N1266.d013728 hx
  have hx2 : 0 < x.2 := hx.2
  simp only [_root_.GD.N0232.N0720.N1312.d013793, hr, hs, _root_.GD.N0232.N0720.N1336.d013420, _root_.GD.N0232.N0720.N1266.d013713]
  field_simp [show 1 + x.2 ≠ 0 by linarith]
  ring

theorem d013803 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x) =
      _root_.GD.N0232.N0720.N1336.d013426 m n t.1 * _root_.GD.N0232.N0720.N1336.d013420 m n x (_root_.GD.N0232.N0720.N1266.d013713 t) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n) /
        (_root_.GD.N0232.N0720.N1336.d013426 m n _root_.GD.N0232.N0720.N1441.d013677.1 *
          _root_.GD.N0232.N0720.N1336.d013420 m n x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)) := by
  have hx2 : 0 < x.2 := hx.2
  have hs : 0 < 1 + x.2 := by linarith
  have hp := _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx (_root_.GD.N0232.N0720.N1266.d013713 t)
  have hp0 := _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677)
  unfold _root_.GD.N0232.N0720.N1312.d013797
  rw [_root_.GD.N0232.N0720.N1312.d013802 m n hx t, _root_.GD.N0232.N0720.N1312.d013802 m n hx _root_.GD.N0232.N0720.N1441.d013677,
    Real.div_rpow hp.le hs.le, Real.div_rpow hp0.le hs.le]
  have hz : (1 + x.2) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
  have hF := (_root_.GD.N0232.N0720.N1336.d013427 m n _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2).ne'
  field_simp [hz, hF, (Real.rpow_pos_of_pos hp0 _).ne']

theorem d013804 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1436.d013273 m n t.1 x =
      _root_.GD.N0232.N0720.N1436.d013273 m n (1 / 2) x * _root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x) := by
  have ht := _root_.GD.N0232.N0720.N1336.d013431 m n hm hn hx (_root_.GD.N0232.N0720.N1266.d013713 t) t.2.1 t.2.2
  have hmid := _root_.GD.N0232.N0720.N1336.d013431 m n hm hn hx (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677)
    _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2
  change _root_.GD.N0232.N0720.N1436.d013273 m n t.1 x = _ at ht
  change _root_.GD.N0232.N0720.N1436.d013273 m n (1 / 2) x = _ at hmid
  rw [ht, hmid, _root_.GD.N0232.N0720.N1312.d013803 m n hm hn hx t]
  have hp0 := _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677)
  have hF := (_root_.GD.N0232.N0720.N1336.d013427 m n _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2).ne'
  have hcancel (a b c d e : ℝ) (hde : d * e ≠ 0) :
      a * b * c = (a * d * e) * (b * c / (d * e)) := by
    calc
      a * b * c = a * (b * c) := by ring
      _ = a * ((b * c / (d * e)) * (d * e)) := by rw [div_mul_cancel₀ _ hde]
      _ = (a * d * e) * (b * c / (d * e)) := by ring
  exact hcancel _ _ _ _ _ (mul_ne_zero hF (Real.rpow_pos_of_pos hp0 _).ne')

theorem d013805 (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Measurable (fun x ↦ _root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x)) :=
  (_root_.GD.N0232.N0720.N1312.d013800 m n hm hn t).continuous.measurable.comp _root_.GD.N0232.N0720.N1266.d013727

theorem d013806 (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013678 m n t = (_root_.GD.N0232.N0720.N1441.d013679 m n).withDensity
      (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x))) := by
  unfold _root_.GD.N0232.N0720.N1441.d013678 _root_.GD.N0232.N0720.N1441.d013679 _root_.GD.N0232.N0720.N1436.d013289
  rw [← withDensity_mul _ (_root_.GD.N0232.N0720.N1436.d013279 m n (1 / 2)).ennreal_ofReal
    (_root_.GD.N0232.N0720.N1312.d013805 m n hm hn t).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  simp only [Pi.mul_apply]
  rw [_root_.GD.N0232.N0720.N1312.d013804 m n hm hn hx t]
  exact ENNReal.ofReal_mul (_root_.GD.N0232.N0720.N1436.d013286 hm hn
    (by norm_num) (by norm_num) hx).le

theorem d013807 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    (∫ x, f x ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) =
      ∫ x, _root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x) * f x ∂_root_.GD.N0232.N0720.N1441.d013679 m n := by
  rw [_root_.GD.N0232.N0720.N1312.d013806 m n hm hn,
    integral_withDensity_eq_integral_toReal_smul
      (_root_.GD.N0232.N0720.N1312.d013805 m n hm hn t).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1312.d013798 m n hm hn t (_root_.GD.N0232.N0720.N1266.d013726 x)).le, smul_eq_mul])

theorem d013808 (hm : 2 ≤ m) (hn : 2 ≤ n) (p : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1312.d013797 m n _root_.GD.N0232.N0720.N1441.d013677 p = 1 := by
  apply div_self
  exact (mul_pos (_root_.GD.N0232.N0720.N1336.d013427 m n _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2)
    (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1312.d013795 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 p) _)).ne'

end
end GD.N0232.N0720.N1312

#print axioms _root_.GD.N0232.N0720.N1312.d013801
#print axioms _root_.GD.N0232.N0720.N1312.d013806
