import GD.Module1570














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0106.N0428.N0770.N1722
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1724
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1435
open _root_.GD.N0232.N0720.N1434


def d024329 (sigma zeta : ℝ) : ℝ :=
  (3 * (sigma ^ 2 + zeta ^ 2) / (4 * Real.pi)) *
    (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta * (1 - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) ^ 2


def d024330 (mu sigma zeta : ℝ) : Measure _root_.GD.N0106.N0428.N0770.N1724.d024295 :=
  (_root_.GD.N0107.d009030 2 2 mu sigma zeta).withDensity
    (fun w => ENNReal.ofReal (_root_.GD.N0107.d009090 2 2 w ^ 2))

theorem d024331 (sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) : 0 < _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta := by
  have hq : 0 < _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta :=
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have hq' : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta < 1 :=
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  unfold _root_.GD.N0106.N0428.N0770.N1722.d024329
  exact mul_pos (div_pos (by positivity) (mul_pos (by norm_num) Real.pi_pos))
    (sq_pos_of_pos (mul_pos hq (sub_pos.mpr hq')))

theorem d024332 (sigma zeta : ℝ) :
    _root_.GD.N0107.d009045 2 2 sigma zeta = (sigma ^ 2 + zeta ^ 2) / 2 := by
  unfold _root_.GD.N0107.d009045 _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
  norm_num only [Nat.cast_ofNat]
  ring



theorem d024333 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    Measure.map (_root_.GD.N0107.d009035 2 2 mu sigma zeta (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta))
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      (gaussianReal 0 1).prod
        ((_root_.GD.N0121.d006346 1).prod
          (_root_.GD.N0121.d006346 1)) := by
  have h := _root_.GD.N0107.d009037 2 2 (by norm_num) (by norm_num)
    mu sigma zeta hsigma.ne' hzeta.ne' (e := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)
    (_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta).le
    (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta).le
  simpa only [_root_.GD.N0125.d008841,
    _root_.GD.N0125.d008840, _root_.GD.N0121.d006346,
    Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one, _root_.GD.N0106.N0428.N0770.N1724.d024296, _root_.GD.N0107.d009035,
    _root_.GD.N0137.d008935, _root_.GD.N0107.d009032, _root_.GD.N0107.d009033, _root_.GD.N0107.d009034,
    Function.comp_def] using h



theorem d024334 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    Measure.map (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 =>
      (2 * _root_.GD.N0107.d009090 2 2 w ^ 2 / (sigma ^ 2 + zeta ^ 2),
        (_root_.GD.N0107.d009085 w.1 / sigma ^ 2,
          _root_.GD.N0107.d009085 w.2 / zeta ^ 2)))
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      (_root_.GD.N0121.d006346 1).prod
        ((_root_.GD.N0121.d006346 1).prod
          (_root_.GD.N0121.d006346 1)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0121.d006346 1) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  let q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta
  let V := _root_.GD.N0107.d009045 2 2 sigma zeta
  have hV : 0 < V := _root_.GD.N0107.d009049 (by norm_num) (by norm_num) hsigma hzeta
  have hS : sigma ^ 2 + zeta ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hsquare (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) :
      _root_.GD.N0107.d009032 2 2 mu sigma zeta q w ^ 2 =
        2 * _root_.GD.N0107.d009090 2 2 w ^ 2 / (sigma ^ 2 + zeta ^ 2) := by
    have hD := congrArg (fun x : ℝ => x ^ 2)
      (_root_.GD.N0107.d012724 2 2 (by norm_num) (by norm_num)
        mu sigma zeta hsigma hzeta w)
    change (Real.sqrt V * _root_.GD.N0107.d009032 2 2 mu sigma zeta q w) ^ 2 = _ at hD
    rw [mul_pow, Real.sq_sqrt hV.le] at hD
    dsimp only [V] at hD
    rw [_root_.GD.N0106.N0428.N0770.N1722.d024332] at hD
    field_simp [hS]
    nlinarith only [hD]
  have hfun : (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 =>
      (2 * _root_.GD.N0107.d009090 2 2 w ^ 2 / (sigma ^ 2 + zeta ^ 2),
        (_root_.GD.N0107.d009085 w.1 / sigma ^ 2, _root_.GD.N0107.d009085 w.2 / zeta ^ 2))) =
      Prod.map (fun z : ℝ => z ^ 2) id ∘ _root_.GD.N0107.d009035 2 2 mu sigma zeta q := by
    funext w
    change (2 * _root_.GD.N0107.d009090 2 2 w ^ 2 / (sigma ^ 2 + zeta ^ 2),
        (_root_.GD.N0107.d009085 w.1 / sigma ^ 2, _root_.GD.N0107.d009085 w.2 / zeta ^ 2)) =
      (_root_.GD.N0107.d009032 2 2 mu sigma zeta q w ^ 2,
        (_root_.GD.N0107.d009033 2 2 mu sigma zeta w, _root_.GD.N0107.d009034 2 2 mu sigma zeta w))
    rw [hsquare, _root_.GD.N0107.d012725 2 2 (by norm_num),
      _root_.GD.N0107.d012726 2 2 (by norm_num)]
  rw [hfun, ← Measure.map_map (by fun_prop) (_root_.GD.N0107.d009036 _ _ _ _ _ _),
    _root_.GD.N0106.N0428.N0770.N1722.d024333 mu sigma zeta hsigma hzeta,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    _root_.GD.N0121.d006355, Measure.map_id]



theorem d024335 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1724.d024300 =ᵐ[_root_.GD.N0107.d009030 2 2 mu sigma zeta]
      (fun w => (_root_.GD.N0107.d009039 2 2 mu sigma zeta (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) w,
        _root_.GD.N0107.d009040 2 2 mu sigma zeta (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) w)) := by
  have hraw : HasLaw (_root_.GD.N0107.d009035 2 2 mu sigma zeta (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta))
      (_root_.GD.N0125.d008840 (1 / 2) (1 / 2))
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta) := by
    refine ⟨(_root_.GD.N0107.d009036 _ _ _ _ _ _).aemeasurable, ?_⟩
    simpa only [_root_.GD.N0125.d008840, _root_.GD.N0121.d006346,
      Nat.cast_ofNat, Nat.cast_one] using _root_.GD.N0106.N0428.N0770.N1722.d024333 mu sigma zeta hsigma hzeta
  have hpos := (hraw.ae_iff (by fun_prop)).2
    (_root_.GD.N0119.d009073
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hpos] with w hw
  have hx : 0 < _root_.GD.N0107.d009085 w.1 := by
    have h := hw.1
    change 0 < _root_.GD.N0107.d009033 2 2 mu sigma zeta w at h
    rw [_root_.GD.N0107.d012725 2 2 (by norm_num)] at h
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos hsigma)).mp h
  have hy : 0 < _root_.GD.N0107.d009085 w.2 := by
    have h := hw.2
    change 0 < _root_.GD.N0107.d009034 2 2 mu sigma zeta w at h
    rw [_root_.GD.N0107.d012726 2 2 (by norm_num)] at h
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos hzeta)).mp h
  have hsum : _root_.GD.N0107.d009085 w.1 + _root_.GD.N0107.d009085 w.2 ≠ 0 :=
    (add_pos hx hy).ne'
  change _root_.GD.N0106.N0428.N0770.N1724.d024300 w =
    (_root_.GD.N0107.d009039 2 2 mu sigma zeta (_root_.GD.N0107.d009046 2 2 sigma zeta) w,
      _root_.GD.N0107.d009040 2 2 mu sigma zeta (_root_.GD.N0107.d009046 2 2 sigma zeta) w)
  rw [_root_.GD.N0107.d012729 2 2 (by norm_num) (by norm_num)
    mu sigma zeta hsigma hzeta,
    _root_.GD.N0107.d012731 2 2 (by norm_num) (by norm_num)
    mu sigma zeta hsigma hzeta]
  simp only [_root_.GD.N0106.N0428.N0770.N1724.d024300, _root_.GD.N0106.N0428.N0770.N1724.d024299, _root_.GD.N0106.N0428.N0770.N1724.d024298, if_neg hsum,
    _root_.GD.N0107.d009091, _root_.GD.N0107.d009093, _root_.GD.N0107.d009092]
  norm_num only [Nat.cast_ofNat]
  apply Prod.ext <;> field_simp [hsum] <;> ring



theorem d024336 {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (phi : (ℝ × ℝ) → ℝ) (hphi : Measurable phi) :
    _root_.GD.N0120.d008809 (1 / 2) (1 / 2) q phi =
      ∫ x, phi x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 q := by
  rw [_root_.GD.N0125.d008860
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [← _root_.GD.N0125.d008873
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)]
  have hmap := _root_.GD.N0232.N0720.N1434.d013563
    (m := 2) (n := 2) (by norm_num) (by norm_num) hq0 hq1
  norm_num only [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, Nat.reduceSub, Nat.cast_ofNat] at hmap
  rw [← hmap, integral_map (_root_.GD.N0232.N0720.N1435.d013471 q).aemeasurable
    hphi.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [_root_.GD.N0232.N0720.N1434.d013553]




theorem d024337 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ) (hphi : Measurable phi) :
    (∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)
      ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      _root_.GD.N0107.d009045 2 2 sigma zeta *
        ∫ x, phi x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) := by
  have h := _root_.GD.N0107.d009052 2 2 (by norm_num) (by norm_num)
    mu sigma zeta hsigma hzeta phi hphi
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at h
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024336
    (_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta)
    (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta) phi hphi] at h
  change (∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)
    ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      _root_.GD.N0107.d009045 2 2 sigma zeta *
        ∫ x, phi x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 (_root_.GD.N0107.d009046 2 2 sigma zeta)
  rw [← h]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0106.N0428.N0770.N1722.d024335 mu sigma zeta hsigma hzeta] with w hw
  rw [hw, _root_.GD.N0107.d012724 2 2 (by norm_num) (by norm_num)
    mu sigma zeta hsigma hzeta]
  rfl


theorem d024338 (sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    {x : ℝ × ℝ} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0107.d009045 2 2 sigma zeta * _root_.GD.N0232.N0720.N1436.d013273 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x := by
  rw [_root_.GD.N0232.N0720.N1435.d013489 (m := 2) (n := 2)
    (t := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) (by norm_num) (by norm_num)
    (_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta)
    (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta) hx]
  norm_num only [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one]
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024332]
  exact _root_.GD.N0106.N0428.N0770.N1725.d024177 (sigma ^ 2 + zeta ^ 2)
    ⟨(_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta).le,
      (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta).le⟩ hx.1 hx.2



theorem d024339 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    IsFiniteMeasure (_root_.GD.N0106.N0428.N0770.N1722.d024330 mu sigma zeta) := by
  have hsq := (_root_.GD.N0106.N0428.N0770.N1724.d024319 mu sigma zeta hsigma hzeta).integrable_sq
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hsq (ae_of_all _ fun w => sq_nonneg _)]
  exact ENNReal.ofReal_ne_top



theorem d024340 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    Measure.map _root_.GD.N0106.N0428.N0770.N1724.d024300 (_root_.GD.N0106.N0428.N0770.N1722.d024330 mu sigma zeta) =
      ENNReal.ofReal (_root_.GD.N0107.d009045 2 2 sigma zeta) •
        _root_.GD.N0232.N0720.N1436.d013289 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) := by
  letI := _root_.GD.N0106.N0428.N0770.N1722.d024339 mu sigma zeta hsigma hzeta
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1436.d013289 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) :=
    _root_.GD.N0232.N0720.N1434.d013564 (by norm_num) (by norm_num)
      (_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta)
      (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta)
  letI : IsFiniteMeasure (ENNReal.ofReal (_root_.GD.N0107.d009045 2 2 sigma zeta) •
      _root_.GD.N0232.N0720.N1436.d013289 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [← measureReal_def, ← measureReal_def, ← integral_indicator_one hs,
    ← integral_indicator_one hs]
  let phi : (ℝ × ℝ) → ℝ := s.indicator (fun _ => 1)
  have hphi : Measurable phi := measurable_const.indicator hs
  change (∫ x, phi x ∂Measure.map _root_.GD.N0106.N0428.N0770.N1724.d024300 (_root_.GD.N0106.N0428.N0770.N1722.d024330 mu sigma zeta)) = _
  rw [integral_map _root_.GD.N0106.N0428.N0770.N1724.d024310.aemeasurable hphi.aestronglyMeasurable]
  unfold _root_.GD.N0106.N0428.N0770.N1722.d024330
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => ENNReal.ofReal (_root_.GD.N0107.d009090 2 2 w ^ 2)) from
      (_root_.GD.N0106.N0428.N0770.N1724.d024308.fst.pow_const 2).ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024337 mu sigma zeta hsigma hzeta phi hphi,
    integral_smul_measure]
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0107.d009049 (by norm_num) (by norm_num) hsigma hzeta).le]
  rfl


theorem d024341 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ w, ENNReal.ofReal (_root_.GD.N0107.d009090 2 2 w ^ 2) * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)
      ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta) *
        ∫⁻ x in _root_.GD.N0232.N0720.N1436.d013218, ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x) * phi x := by
  let V := _root_.GD.N0107.d009045 2 2 sigma zeta
  let q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta
  let K := _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta
  have hV : 0 ≤ V := (_root_.GD.N0107.d009049 (by norm_num) (by norm_num) hsigma hzeta).le
  have hK : 0 ≤ K := (_root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hsigma hzeta).le
  have hweighted : (∫⁻ w, ENNReal.ofReal (_root_.GD.N0107.d009090 2 2 w ^ 2) *
      phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      ∫⁻ x, phi x ∂Measure.map _root_.GD.N0106.N0428.N0770.N1724.d024300 (_root_.GD.N0106.N0428.N0770.N1722.d024330 mu sigma zeta) := by
    rw [lintegral_map hphi _root_.GD.N0106.N0428.N0770.N1724.d024310]
    unfold _root_.GD.N0106.N0428.N0770.N1722.d024330
    simpa only [Function.comp_def, Pi.mul_apply] using
      (lintegral_withDensity_eq_lintegral_mul (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (show Measurable (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => ENNReal.ofReal (_root_.GD.N0107.d009090 2 2 w ^ 2)) from
          (_root_.GD.N0106.N0428.N0770.N1724.d024308.fst.pow_const 2).ennreal_ofReal)
        (hphi.comp _root_.GD.N0106.N0428.N0770.N1724.d024310)).symm
  rw [hweighted, _root_.GD.N0106.N0428.N0770.N1722.d024340 mu sigma zeta hsigma hzeta,
    lintegral_smul_measure]
  unfold _root_.GD.N0232.N0720.N1436.d013289
  rw [lintegral_withDensity_eq_lintegral_mul _
    (_root_.GD.N0232.N0720.N1436.d013279 2 2 q).ennreal_ofReal hphi]
  change ENNReal.ofReal V * (∫⁻ x, ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 q x) *
    phi x ∂_root_.GD.N0232.N0720.N1436.d013288) = _
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  rw [← mul_assoc, ← ENNReal.ofReal_mul hV,
    _root_.GD.N0106.N0428.N0770.N1722.d024338 sigma zeta hsigma hzeta hx,
    ENNReal.ofReal_mul hK, mul_assoc]



theorem d024342 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ) (hphi : Measurable phi) :
    (∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)
      ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta *
        ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * phi x := by
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024337 mu sigma zeta hsigma hzeta phi hphi]
  unfold _root_.GD.N0232.N0720.N1436.d013289
  rw [integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0232.N0720.N1436.d013279 _ _ _).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2) (t := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)
      (by norm_num) (by norm_num)
    (_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta)
    (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta) hx).le]
  simp only [smul_eq_mul]
  rw [← mul_assoc, _root_.GD.N0106.N0428.N0770.N1722.d024338 sigma zeta hsigma hzeta hx, mul_assoc]


theorem d024343 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ) (hphi : Measurable phi) :
    Integrable (fun w => _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w))
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta) ↔
      Integrable phi (_root_.GD.N0232.N0720.N1436.d013289 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) := by
  have h := integrable_map_measure
    (μ := _root_.GD.N0106.N0428.N0770.N1722.d024330 mu sigma zeta)
    (f := _root_.GD.N0106.N0428.N0770.N1724.d024300) hphi.aestronglyMeasurable _root_.GD.N0106.N0428.N0770.N1724.d024310.aemeasurable
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024340 mu sigma zeta hsigma hzeta,
    integrable_smul_measure
      (ENNReal.ofReal_ne_zero_iff.mpr (_root_.GD.N0107.d009049 (by norm_num) (by norm_num) hsigma hzeta))
      ENNReal.ofReal_ne_top] at h
  unfold _root_.GD.N0106.N0428.N0770.N1722.d024330 at h
  rw [integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => ENNReal.ofReal (_root_.GD.N0107.d009090 2 2 w ^ 2)) from
      (_root_.GD.N0106.N0428.N0770.N1724.d024308.fst.pow_const 2).ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h
  simpa only [Function.comp_apply, smul_eq_mul, ENNReal.toReal_ofReal (sq_nonneg _)] using h.symm


theorem d024344 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ) (hphi : Measurable phi) :
    Integrable (fun w => _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w))
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta) ↔
      IntegrableOn (fun x => _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * phi x) _root_.GD.N0232.N0720.N1436.d013218 volume := by
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024343 mu sigma zeta hsigma hzeta phi hphi]
  unfold _root_.GD.N0232.N0720.N1436.d013289
  rw [integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0232.N0720.N1436.d013279 _ _ _).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  let V := _root_.GD.N0107.d009045 2 2 sigma zeta
  let K := _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta
  have hV : 0 < V := _root_.GD.N0107.d009049 (by norm_num) (by norm_num) hsigma hzeta
  have hK : 0 < K := _root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hsigma hzeta
  have heq : (fun x => (ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x)).toReal • phi x)
      =ᵐ[_root_.GD.N0232.N0720.N1436.d013288]
      (fun x => (K / V) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * phi x)) := by
    filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
    rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2) (t := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)
      (by norm_num) (by norm_num)
      (_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta)
      (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta) hx).le]
    have hd := _root_.GD.N0106.N0428.N0770.N1722.d024338 sigma zeta hsigma hzeta hx
    change V * _root_.GD.N0232.N0720.N1436.d013273 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x = K * _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x at hd
    have hpdf : _root_.GD.N0232.N0720.N1436.d013273 2 2 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x =
        (K * _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x) / V := by
      apply (eq_div_iff hV.ne').2
      exact (mul_comm _ _).trans hd
    simp only [smul_eq_mul]
    rw [hpdf]
    ring
  rw [integrable_congr heq]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (div_ne_zero hK.ne' hV.ne')) _

end
end GD.N0106.N0428.N0770.N1722

#print axioms _root_.GD.N0106.N0428.N0770.N1722.d024333
#print axioms _root_.GD.N0106.N0428.N0770.N1722.d024334
#print axioms _root_.GD.N0106.N0428.N0770.N1722.d024335
#print axioms _root_.GD.N0106.N0428.N0770.N1722.d024336
#print axioms _root_.GD.N0106.N0428.N0770.N1722.d024340
#print axioms _root_.GD.N0106.N0428.N0770.N1722.d024341
#print axioms _root_.GD.N0106.N0428.N0770.N1722.d024342
#print axioms _root_.GD.N0106.N0428.N0770.N1722.d024344
