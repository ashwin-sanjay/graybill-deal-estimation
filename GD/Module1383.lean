import GD.Module1382
import GD.Module0941
import GD.Module1376








set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0186
noncomputable section

open _root_.GD.N0183 _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1213


def d022292 (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  15 * Real.sqrt p.2 /
    (t * (1 - t) *
      (p.2 + 2 * (1 - p.1) / (1 - t) + 2 * p.1 / t) ^ (7 / 2 : ℝ))

def d022293 (t : ℝ) (p : ℝ × ℝ) : ℝ := _root_.GD.N0186.d022292 t p / (t * (1 - t))


def d022294 (mu sigma zeta : ℝ) : Measure _root_.GD.N0183.d022241 :=
  (_root_.GD.N0107.d009030 3 3 mu sigma zeta).withDensity
    (fun w => ENNReal.ofReal (_root_.GD.N0183.d022246 w ^ 2 / _root_.GD.N0183.d022243 sigma zeta))

theorem d022295 (e : ℝ) : Measurable (_root_.GD.N0186.d022292 e) := by
  have hr : Measurable (fun x : ℝ => x ^ (7 / 2 : ℝ)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const fun x hx => Or.inl hx
  have hb : Measurable (fun p : ℝ × ℝ =>
      p.2 + 2 * (1 - p.1) / (1 - e) + 2 * p.1 / e) := by fun_prop
  exact ((Real.continuous_sqrt.measurable.comp measurable_snd).const_mul 15).div
    (measurable_const.mul (hr.comp hb))

theorem d022296 {e : ℝ} (he : e ∈ Ioo (0 : ℝ) 1)
    {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0183.d022251) :
    _root_.GD.N0186.d022292 e p = _root_.GD.N0232.N0720.N1436.d013273 3 3 e p := by
  rcases p with ⟨u, s⟩
  have hq : 0 < s + _root_.GD.N0062.d022142 e u :=
    add_pos hp.2 (_root_.GD.N0062.d022143 he hp.1)
  rw [_root_.GD.N0062.d022145 he hp.1 hp.2]
  unfold _root_.GD.N0186.d022292
  rw [show s + 2 * (1 - u) / (1 - e) + 2 * u / e =
    s + _root_.GD.N0062.d022142 e u by unfold _root_.GD.N0062.d022142; ring]
  rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num,
    Real.rpow_add hq, Real.rpow_ofNat, ← Real.sqrt_eq_rpow]
  ring

theorem d022297 : Real.Gamma (7 / 2 : ℝ) / Real.Gamma (3 / 2 : ℝ) = 15 / 4 := by
  have hg : Real.Gamma (3 / 2 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).ne'
  rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (5 / 2 : ℝ) ≠ 0),
    show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  field_simp [hg]
  <;> norm_num

theorem d022298 (r u s : ℝ) :
    _root_.GD.N0232.N0720.N1435.d013435 ![r, u, s] =
      ![r * (1 - u), r * u, r * s] := by
  ext i
  fin_cases i <;> rfl

theorem d022299 (z : Fin 3 → ℝ) :
    HasFDerivAt _root_.GD.N0232.N0720.N1435.d013435
      (_root_.GD.N0232.N0720.N1435.d013448 z) z :=
  _root_.GD.N0232.N0720.N1435.d013449 z

theorem d022300 (z : Fin 3 → ℝ) :
    (_root_.GD.N0232.N0720.N1435.d013448 z).det =
      (z 0) ^ 2 :=
  _root_.GD.N0232.N0720.N1435.d013450 z

theorem d022301 {e : ℝ} (he : e ∈ Ioo (0 : ℝ) 1)
    {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0183.d022251) :
    (∫ r : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1436.d013272 3 3 e p r) = _root_.GD.N0186.d022292 e p := by
  rw [_root_.GD.N0232.N0720.N1436.d013285 (by norm_num) (by norm_num) he.1 he.2 hp]
  exact (_root_.GD.N0186.d022296 he hp).symm


theorem d022302 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (F : X → Y) (hF : Measurable F)
    (q : Y → ℝ≥0∞) (hq : Measurable q) :
    (P.withDensity (fun x => q (F x))).map F = (P.map F).withDensity q := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs),
    withDensity_apply _ hs, setLIntegral_map hs hq hF]


theorem d022303 :
    (_root_.GD.N0121.d006346 1).withDensity ENNReal.ofReal =
      _root_.GD.N0125.d008851 := by
  rw [← _root_.GD.N0121.d006355]
  rw [← _root_.GD.N0186.d022302 (gaussianReal 0 1) (fun z : ℝ => z ^ 2)
    (by fun_prop) ENNReal.ofReal (by fun_prop)]
  exact _root_.GD.N0125.d008867



theorem d022304 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    (_root_.GD.N0186.d022294 mu sigma zeta).map (_root_.GD.N0183.d022250 sigma zeta) =
      _root_.GD.N0125.d008851.prod
        ((expMeasure (1 / (1 - _root_.GD.N0183.d022244 sigma zeta))).prod
          (expMeasure (1 / _root_.GD.N0183.d022244 sigma zeta))) := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  letI : IsProbabilityMeasure (expMeasure (1 / (1 - _root_.GD.N0183.d022244 sigma zeta))) :=
    isProbabilityMeasure_expMeasure (one_div_pos.mpr (sub_pos.mpr hp.2.2))
  letI : IsProbabilityMeasure (expMeasure (1 / _root_.GD.N0183.d022244 sigma zeta)) :=
    isProbabilityMeasure_expMeasure (one_div_pos.mpr hp.2.1)
  have hmap := _root_.GD.N0186.d022302 (_root_.GD.N0107.d009030 3 3 mu sigma zeta)
    (_root_.GD.N0183.d022250 sigma zeta) (_root_.GD.N0183.d022258 sigma zeta)
    (fun b : _root_.GD.N0183.d022242 => ENNReal.ofReal b.1) (by fun_prop)
  change (_root_.GD.N0186.d022294 mu sigma zeta).map (_root_.GD.N0183.d022250 sigma zeta) = _ at hmap
  rw [_root_.GD.N0183.d022263 mu sigma zeta hsigma hzeta,
    ← prod_withDensity_left (show Measurable ENNReal.ofReal by fun_prop),
    _root_.GD.N0186.d022303] at hmap
  exact hmap

theorem d022305 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) (w : _root_.GD.N0183.d022241) :
    _root_.GD.N0232.N0720.N1213.d014727 3 3 mu sigma zeta w = _root_.GD.N0183.d022254 (_root_.GD.N0183.d022249 w) := by
  unfold _root_.GD.N0232.N0720.N1213.d014727
  rw [_root_.GD.N0107.d012729
      3 3 (by norm_num) (by norm_num) mu sigma zeta hsigma hzeta w,
    _root_.GD.N0107.d012731
      3 3 (by norm_num) (by norm_num) mu sigma zeta hsigma hzeta w]
  rfl

theorem d022306 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0186.d022294 mu sigma zeta =
      (ENNReal.ofReal (_root_.GD.N0183.d022243 sigma zeta))⁻¹ • _root_.GD.N0232.N0720.N1213.d014730 3 3 mu sigma zeta := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have hm : Measurable (fun w : _root_.GD.N0183.d022241 =>
      _root_.GD.N0107.d009038 3 3 mu sigma zeta (_root_.GD.N0107.d009046 3 3 sigma zeta)
        (_root_.GD.N0107.d009045 3 3 sigma zeta) w) :=
    measurable_fst.comp (_root_.GD.N0107.d009041 3 3 mu sigma zeta
      (_root_.GD.N0107.d009046 3 3 sigma zeta) (_root_.GD.N0107.d009045 3 3 sigma zeta))
  unfold _root_.GD.N0186.d022294 _root_.GD.N0232.N0720.N1213.d014730
  rw [← withDensity_smul _ (hm.pow_const 2).ennreal_ofReal]
  congr 1
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [_root_.GD.N0107.d012724
    3 3 (by norm_num) (by norm_num) mu sigma zeta hsigma hzeta w,
    ENNReal.ofReal_div_of_pos hp.1]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, _root_.GD.N0183.d022246, mul_comm]

theorem d022307 {e : ℝ} (he : e ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1436.d013289 3 3 e =
      (volume.restrict _root_.GD.N0183.d022251).withDensity (fun p => ENNReal.ofReal (_root_.GD.N0186.d022292 e p)) := by
  unfold _root_.GD.N0232.N0720.N1436.d013289 _root_.GD.N0232.N0720.N1436.d013288
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
  rw [_root_.GD.N0186.d022296 he hp]


theorem d022308 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    (_root_.GD.N0186.d022294 mu sigma zeta).map (fun w => _root_.GD.N0183.d022254 (_root_.GD.N0183.d022249 w)) =
      (volume.restrict _root_.GD.N0183.d022251).withDensity (fun p => ENNReal.ofReal (_root_.GD.N0186.d022292 (_root_.GD.N0183.d022244 sigma zeta) p)) := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have hc : (fun w => _root_.GD.N0183.d022254 (_root_.GD.N0183.d022249 w)) = _root_.GD.N0232.N0720.N1213.d014727 3 3 mu sigma zeta := by
    funext w
    exact (_root_.GD.N0186.d022305 mu sigma zeta hsigma hzeta w).symm
  rw [hc, _root_.GD.N0186.d022306 mu sigma zeta hsigma hzeta,
    Measure.map_smul,
    _root_.GD.N0232.N0720.N1213.d014731
      3 3 (by norm_num) (by norm_num) mu sigma zeta hsigma hzeta,
    smul_smul]
  have hv : ENNReal.ofReal (_root_.GD.N0183.d022243 sigma zeta) ≠ 0 := by
    simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hp.1
  change ((ENNReal.ofReal (_root_.GD.N0183.d022243 sigma zeta))⁻¹ * ENNReal.ofReal (_root_.GD.N0183.d022243 sigma zeta)) •
    _root_.GD.N0232.N0720.N1436.d013289 3 3 (_root_.GD.N0183.d022244 sigma zeta) = _
  rw [ENNReal.inv_mul_cancel hv (ENNReal.ofReal_ne_top), one_smul]
  exact _root_.GD.N0186.d022307 hp.2

theorem d022309 {e : ℝ} (he : e ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ p in _root_.GD.N0183.d022251, ENNReal.ofReal (_root_.GD.N0186.d022292 e p)) = 1 := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1436.d013289 3 3 e) :=
    _root_.GD.N0232.N0720.N1434.d013564
      (by norm_num) (by norm_num) he.1 he.2
  have h := measure_univ (μ := _root_.GD.N0232.N0720.N1436.d013289 3 3 e)
  rw [_root_.GD.N0186.d022307 he, withDensity_apply _ MeasurableSet.univ] at h
  simpa using h



def d022310 (g : _root_.GD.N0183.d022251 → ℝ) (p : ℝ × ℝ) : ℝ := by
  classical
  exact if hp : p ∈ _root_.GD.N0183.d022251 then g ⟨p, hp⟩ else 1 / 2

theorem d022311 (g : _root_.GD.N0183.d022251 → ℝ) (hg : Measurable g) : Measurable (_root_.GD.N0186.d022310 g) := by
  classical
  exact hg.dite measurable_const (measurableSet_Ioo.prod measurableSet_Ioi)

theorem d022312 (g : _root_.GD.N0183.d022251 → ℝ) {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0183.d022251) :
    _root_.GD.N0186.d022310 g p = g ⟨p, hp⟩ := by
  simp [_root_.GD.N0186.d022310, hp]

theorem d022313 (g : _root_.GD.N0183.d022251 → ℝ)
    {w : _root_.GD.N0183.d022241} (hw : w ∈ _root_.GD.N0183.d022253) :
    _root_.GD.N0183.d022275 g (_root_.GD.N0183.d022249 w) = _root_.GD.N0186.d022310 g (_root_.GD.N0183.d022254 (_root_.GD.N0183.d022249 w)) := by
  have hb : _root_.GD.N0183.d022249 w ∈ _root_.GD.N0183.d022252 := hw
  simp [_root_.GD.N0183.d022275, hb, _root_.GD.N0183.d022272, _root_.GD.N0183.d022270, _root_.GD.N0186.d022310,
    _root_.GD.N0183.d022268 hw]



def d022314 (e : ℝ) (g : _root_.GD.N0183.d022251 → ℝ) : ℝ :=
  ∫ p in _root_.GD.N0183.d022251, _root_.GD.N0186.d022293 e p * (_root_.GD.N0186.d022310 g p - e) ^ 2

theorem d022315 {e : ℝ} (he : e ∈ Ioo (0 : ℝ) 1)
    (g : _root_.GD.N0183.d022251 → ℝ) :
    _root_.GD.N0186.d022314 e g = (∫ p, (_root_.GD.N0186.d022310 g p - e) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 3 3 e) /
      (e * (1 - e)) := by
  have hJ : (∫ p, (_root_.GD.N0186.d022310 g p - e) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 3 3 e) =
      ∫ p in _root_.GD.N0183.d022251, _root_.GD.N0186.d022292 e p * (_root_.GD.N0186.d022310 g p - e) ^ 2 := by
    rw [_root_.GD.N0186.d022307 he,
      integral_withDensity_eq_integral_toReal_smul (_root_.GD.N0186.d022295 e).ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioi)] with p hp
    have hf : 0 ≤ _root_.GD.N0186.d022292 e p := by
      rw [_root_.GD.N0186.d022296 he hp]
      exact (_root_.GD.N0232.N0720.N1436.d013286 (by norm_num) (by norm_num) he.1 he.2 hp).le
    rw [ENNReal.toReal_ofReal hf, smul_eq_mul]
  rw [hJ]
  unfold _root_.GD.N0186.d022314 _root_.GD.N0186.d022293
  rw [← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by ring

theorem d022316 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (g : _root_.GD.N0183.d022251 → ℝ) (hg : Measurable g) :
    (∫ w, _root_.GD.N0183.d022246 w ^ 2 * (_root_.GD.N0183.d022275 g (_root_.GD.N0183.d022249 w) - _root_.GD.N0183.d022244 sigma zeta) ^ 2
      ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta) =
      _root_.GD.N0183.d022243 sigma zeta * ∫ p, (_root_.GD.N0186.d022310 g p - _root_.GD.N0183.d022244 sigma zeta) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 3 3 (_root_.GD.N0183.d022244 sigma zeta) := by
  have hJ := _root_.GD.N0232.N0720.N1213.d014729
    3 3 (by norm_num) (by norm_num) mu sigma zeta hsigma hzeta
    (fun p => (_root_.GD.N0186.d022310 g p - _root_.GD.N0183.d022244 sigma zeta) ^ 2)
    (((_root_.GD.N0186.d022311 g hg).sub measurable_const).pow_const 2)
  have hd : _root_.GD.N0107.d009038 3 3 mu sigma zeta (_root_.GD.N0107.d009046 3 3 sigma zeta)
      (_root_.GD.N0107.d009045 3 3 sigma zeta) = _root_.GD.N0183.d022246 := by
    funext w
    exact _root_.GD.N0107.d012724 3 3 (by norm_num) (by norm_num)
      mu sigma zeta hsigma hzeta w
  have hc : _root_.GD.N0232.N0720.N1213.d014727 3 3 mu sigma zeta =
      fun w => _root_.GD.N0183.d022254 (_root_.GD.N0183.d022249 w) := by
    funext w
    exact _root_.GD.N0186.d022305 mu sigma zeta hsigma hzeta w
  rw [hd, hc] at hJ
  calc
    _ = ∫ w, _root_.GD.N0183.d022246 w ^ 2 * (_root_.GD.N0186.d022310 g (_root_.GD.N0183.d022254 (_root_.GD.N0183.d022249 w)) - _root_.GD.N0183.d022244 sigma zeta) ^ 2
        ∂_root_.GD.N0107.d009030 3 3 mu sigma zeta := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0183.d022267 mu sigma zeta hsigma hzeta] with w hw
      rw [_root_.GD.N0186.d022313 g hw]
    _ = _ := hJ



theorem d022317 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (g : _root_.GD.N0183.d022251 → ℝ) (hg : Measurable g) (hgb : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    Measurable (_root_.GD.N0183.d022276 g) ∧
      MemLp (fun w => _root_.GD.N0183.d022276 g w - mu) 2 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) ∧
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 3 3 mu sigma zeta) (fun w => _root_.GD.N0183.d022276 g w - mu) /
        _root_.GD.N0183.d022245 sigma zeta = 1 + _root_.GD.N0186.d022314 (_root_.GD.N0183.d022244 sigma zeta) g := by
  have hp := _root_.GD.N0183.d022256 sigma zeta hsigma hzeta
  have hR := _root_.GD.N0183.d022290 mu sigma zeta hsigma hzeta g hg hgb
  refine ⟨hR.1, hR.2.1, ?_⟩
  rw [hR.2.2, _root_.GD.N0186.d022316 mu sigma zeta hsigma hzeta g hg,
    _root_.GD.N0186.d022315 hp.2 g]
  unfold _root_.GD.N0183.d022245
  have h1 : 1 - _root_.GD.N0183.d022244 sigma zeta ≠ 0 := (sub_pos.mpr hp.2.2).ne'
  field_simp [hp.1.ne', hp.2.1.ne', h1]
  <;> ring

end
end GD.N0186

#print axioms _root_.GD.N0186.d022295
#print axioms _root_.GD.N0186.d022296
#print axioms _root_.GD.N0186.d022297
#print axioms _root_.GD.N0186.d022298
#print axioms _root_.GD.N0186.d022299
#print axioms _root_.GD.N0186.d022300
#print axioms _root_.GD.N0186.d022301
#print axioms _root_.GD.N0186.d022302
#print axioms _root_.GD.N0186.d022303
#print axioms _root_.GD.N0186.d022304
#print axioms _root_.GD.N0186.d022305
#print axioms _root_.GD.N0186.d022306
#print axioms _root_.GD.N0186.d022307
#print axioms _root_.GD.N0186.d022308
#print axioms _root_.GD.N0186.d022309
#print axioms _root_.GD.N0186.d022311
#print axioms _root_.GD.N0186.d022312
#print axioms _root_.GD.N0186.d022313
#print axioms _root_.GD.N0186.d022315
#print axioms _root_.GD.N0186.d022316
#print axioms _root_.GD.N0186.d022317
