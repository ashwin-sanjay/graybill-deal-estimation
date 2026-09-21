import GD.Module0611






















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0125

noncomputable section

open _root_.GD.N0124
open _root_.GD.N0116
open _root_.GD.N0120
open _root_.GD.N0141

variable {Ω : Type*} [MeasurableSpace Ω]



def d008840 (α β : ℝ) : Measure _root_.GD.N0124.d006387 :=
  (gaussianReal 0 1).prod
    ((gammaMeasure α α).prod (gammaMeasure β β))


def d008841
    (P : Measure Ω) (Z Rx Ry : Ω → ℝ) (α β : ℝ) : Prop :=
  P.map (fun ω => (Z ω, (Rx ω, Ry ω))) = _root_.GD.N0125.d008840 α β


def d008842 (p : _root_.GD.N0124.d006387) : _root_.GD.N0124.d006387 :=
  (p.2.1, (p.2.2, p.1 ^ 2))


def d008843 (e : ℝ) (p : _root_.GD.N0124.d006387) : ℝ :=
  (1 - e) * p.2.1 + e * p.2.2


def d008844 (e : ℝ) (p : _root_.GD.N0124.d006387) : ℝ :=
  e * p.2.2 / _root_.GD.N0125.d008843 e p


def d008845 (e : ℝ) (p : _root_.GD.N0124.d006387) : ℝ :=
  p.1 ^ 2 / _root_.GD.N0125.d008843 e p

theorem d008846 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    ((_root_.GD.N0124.d006391 e (_root_.GD.N0125.d008842 p)).1,
      (_root_.GD.N0124.d006391 e (_root_.GD.N0125.d008842 p)).2.1) =
      (_root_.GD.N0125.d008844 e p, _root_.GD.N0125.d008845 e p) := by
  rfl


def d008847
    (P : Measure Ω) (D L F : Ω → ℝ)
    (α β e Sigma : ℝ) : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, Measurable φ →
    (∫ ω, D ω ^ 2 * φ (L ω, F ω) ∂P)
      = Sigma * _root_.GD.N0120.d008809 α β e φ


def d008848 (α β : ℝ) : Measure _root_.GD.N0124.d006387 :=
  (volume.restrict _root_.GD.N0124.d006388).withDensity
    (fun p => ENNReal.ofReal (_root_.GD.N0116.d006510 α β p))


def d008849 (α β : ℝ) : Measure _root_.GD.N0124.d006387 :=
  (_root_.GD.N0125.d008840 α β).withDensity
    (fun p => ENNReal.ofReal (p.1 ^ 2))




def d008850 (α β : ℝ) : Prop :=
  (_root_.GD.N0125.d008849 α β).map _root_.GD.N0125.d008842 = _root_.GD.N0125.d008848 α β



def d008851 : Measure ℝ :=
  gammaMeasure ((3 : ℝ) / 2) ((1 : ℝ) / 2)



def d008852 (α β : ℝ) : Measure _root_.GD.N0124.d006387 :=
  (gammaMeasure α α).prod
    ((gammaMeasure β β).prod _root_.GD.N0125.d008851)


def d008853 : Measure ℝ :=
  (gaussianReal 0 1).withDensity
    (fun z => ENNReal.ofReal (z ^ 2))

theorem d008854 : Measurable _root_.GD.N0125.d008842 := by
  unfold _root_.GD.N0125.d008842
  fun_prop

theorem d008855 (e : ℝ) : Measurable (_root_.GD.N0125.d008843 e) := by
  unfold _root_.GD.N0125.d008843
  fun_prop

theorem d008856 (e : ℝ) : Measurable (_root_.GD.N0125.d008844 e) := by
  unfold _root_.GD.N0125.d008844
  exact measurable_const.mul measurable_snd.snd
    |>.div (_root_.GD.N0125.d008855 e)

theorem d008857 (e : ℝ) : Measurable (_root_.GD.N0125.d008845 e) := by
  unfold _root_.GD.N0125.d008845
  exact (measurable_fst.pow_const 2).div (_root_.GD.N0125.d008855 e)

theorem d008858 (e : ℝ) : Measurable (_root_.GD.N0124.d006391 e) := by
  unfold _root_.GD.N0124.d006391 _root_.GD.N0124.d006390
  fun_prop

theorem d008859 (e : ℝ) :
    Measurable (fun p : _root_.GD.N0124.d006387 => (_root_.GD.N0125.d008844 e p, _root_.GD.N0125.d008845 e p)) := by
  exact (_root_.GD.N0125.d008856 e).prodMk (_root_.GD.N0125.d008857 e)

theorem d008860
    {α β e : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (φ : ℝ × ℝ → ℝ) :
    _root_.GD.N0120.d008809 α β e φ =
      ∫ p : _root_.GD.N0124.d006387,
        φ ((_root_.GD.N0124.d006391 e p).1, (_root_.GD.N0124.d006391 e p).2.1) ∂_root_.GD.N0125.d008848 α β := by
  unfold _root_.GD.N0120.d008809 _root_.GD.N0125.d008848
  rw [integral_withDensity_eq_integral_toReal_smul
    (by
      unfold _root_.GD.N0116.d006510 _root_.GD.N0116.d006506
        _root_.GD.N0123.d006499
      fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)
    (fun p : _root_.GD.N0124.d006387 =>
      φ ((_root_.GD.N0124.d006391 e p).1, (_root_.GD.N0124.d006391 e p).2.1))]
  apply integral_congr_ae
  filter_upwards
    [ae_restrict_mem _root_.GD.N0123.d006491]
      with p hp
  have hnonneg : 0 ≤ _root_.GD.N0116.d006510 α β p := by
    unfold _root_.GD.N0116.d006510 _root_.GD.N0116.d006506
      _root_.GD.N0123.d006499
    have hx : 0 ≤ p.1 ^ (α - 1) :=
      Real.rpow_nonneg (le_of_lt hp.1) _
    have hy : 0 ≤ p.2.1 ^ (β - 1) :=
      Real.rpow_nonneg (le_of_lt hp.2.1) _
    have hw : 0 ≤ p.2.2 ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (le_of_lt hp.2.2) _
    have hc : 0 ≤ _root_.GD.N0116.d006506 α β := by
      unfold _root_.GD.N0116.d006506
      positivity
    positivity
  rw [ENNReal.toReal_ofReal hnonneg]
  simp only [smul_eq_mul]
  ring



theorem d008861 :
    Real.Gamma ((3 : ℝ) / 2) = Real.sqrt Real.pi / 2 := by
  have h := Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)
  rw [Real.Gamma_one_half_eq] at h
  convert h using 1 <;> ring

theorem d008862 :
    (1 / 2 : ℝ) ^ ((3 : ℝ) / 2) /
        Real.Gamma ((3 : ℝ) / 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [_root_.GD.N0125.d008861]
  have htwo : (0 : ℝ) < 2 := by norm_num
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    Real.inv_rpow htwo.le]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
    Real.rpow_add htwo, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

theorem d008863
    {w : ℝ} (hw : 0 < w) :
    gammaPDFReal ((3 : ℝ) / 2) ((1 : ℝ) / 2) w =
      _root_.GD.N0122.d006380 w := by
  rw [gammaPDFReal, if_pos hw.le, _root_.GD.N0125.d008862]
  unfold _root_.GD.N0122.d006380
  rw [show ((3 : ℝ) / 2 - 1) = (1 : ℝ) / 2 by ring]
  rw [show -((1 : ℝ) / 2 * w) = -(w / 2) by ring]

theorem d008864 {w : ℝ} (hw : w ≤ 0) :
    gammaPDFReal ((3 : ℝ) / 2) ((1 : ℝ) / 2) w = 0 := by
  rcases hw.eq_or_lt with rfl | hw
  · rw [gammaPDFReal, if_pos le_rfl]
    have hexp : ((3 : ℝ) / 2 - 1) ≠ 0 := by norm_num
    rw [Real.zero_rpow hexp]
    ring
  · simp [gammaPDFReal, not_le.mpr hw]

theorem d008865 (f : ℝ → ℝ) :
    (∫ w : ℝ, f w ∂_root_.GD.N0125.d008851)
      =
    ∫ w : ℝ in Ioi 0,
      _root_.GD.N0122.d006380 w * f w := by
  unfold _root_.GD.N0125.d008851
  rw [gammaMeasure]
  change
    (∫ w : ℝ, f w
      ∂volume.withDensity
        (fun w => ENNReal.ofReal
          (gammaPDFReal ((3 : ℝ) / 2) ((1 : ℝ) / 2) w))) =
    ∫ w : ℝ in Ioi 0,
      _root_.GD.N0122.d006380 w * f w
  rw [integral_withDensity_eq_integral_toReal_smul
      ((measurable_gammaPDFReal
        ((3 : ℝ) / 2) ((1 : ℝ) / 2)).ennreal_ofReal)
      (ae_of_all _ fun w => by simp [gammaPDF])]
  simp only [gammaPDF,
    ENNReal.toReal_ofReal
      (gammaPDFReal_nonneg
        (by norm_num : 0 < (3 : ℝ) / 2)
        (by norm_num : 0 < (1 : ℝ) / 2) _),
    smul_eq_mul]
  calc
    (∫ w : ℝ,
        gammaPDFReal ((3 : ℝ) / 2) ((1 : ℝ) / 2) w * f w)
        =
      ∫ w : ℝ in Ioi 0,
        gammaPDFReal ((3 : ℝ) / 2) ((1 : ℝ) / 2) w * f w := by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro w hw
          have hw' : w ≤ 0 := by
            simpa only [mem_compl_iff, mem_Ioi, not_lt] using hw
          rw [_root_.GD.N0125.d008864 hw', zero_mul]
    _ =
      ∫ w : ℝ in Ioi 0,
        _root_.GD.N0122.d006380 w * f w := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro w hw
          change gammaPDFReal ((3 : ℝ) / 2) ((1 : ℝ) / 2) w * f w =
            _root_.GD.N0122.d006380 w * f w
          rw [_root_.GD.N0125.d008863 hw]

theorem d008866 :
    IsFiniteMeasure _root_.GD.N0125.d008853 := by
  unfold _root_.GD.N0125.d008853
  exact isFiniteMeasure_withDensity_ofReal
    _root_.GD.N0142.d008833.hasFiniteIntegral

theorem d008867 :
    _root_.GD.N0125.d008853.map (fun z : ℝ => z ^ 2) =
      _root_.GD.N0125.d008851 := by
  letI : IsFiniteMeasure _root_.GD.N0125.d008853 :=
    _root_.GD.N0125.d008866
  letI : IsProbabilityMeasure _root_.GD.N0125.d008851 := by
    unfold _root_.GD.N0125.d008851
    exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (by fun_prop)
    f.continuous.aestronglyMeasurable]
  unfold _root_.GD.N0125.d008853
  rw [integral_withDensity_eq_integral_toReal_smul
    (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  rw [_root_.GD.N0125.d008865]
  apply _root_.GD.N0122.d006386
  exact _root_.GD.N0142.d008834.mul_bdd
    ((f.continuous.comp (continuous_pow 2)).aestronglyMeasurable)
    (ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs, abs_sq] using
        f.norm_coe_le_norm (z ^ 2))



theorem d008868
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    _root_.GD.N0125.d008849 α β =
      _root_.GD.N0125.d008853.prod
        ((gammaMeasure α α).prod (gammaMeasure β β)) := by
  unfold _root_.GD.N0125.d008849 _root_.GD.N0125.d008840 _root_.GD.N0125.d008853
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaMeasure β β) :=
    isProbabilityMeasure_gammaMeasure hβ hβ
  symm
  exact prod_withDensity_left (by fun_prop)

theorem d008869
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (_root_.GD.N0125.d008849 α β).map _root_.GD.N0125.d008842 =
      _root_.GD.N0125.d008852 α β := by
  letI : IsFiniteMeasure _root_.GD.N0125.d008853 :=
    _root_.GD.N0125.d008866
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaMeasure β β) :=
    isProbabilityMeasure_gammaMeasure hβ hβ
  letI : IsProbabilityMeasure _root_.GD.N0125.d008851 := by
    unfold _root_.GD.N0125.d008851
    exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  rw [_root_.GD.N0125.d008868 hα hβ]
  let residual : Measure (ℝ × ℝ) :=
    (gammaMeasure α α).prod (gammaMeasure β β)
  have hfirst :
      (_root_.GD.N0125.d008853.prod residual).map
          (Prod.map (fun z : ℝ => z ^ 2) id)
        =
      _root_.GD.N0125.d008851.prod residual := by
    rw [← Measure.map_prod_map _root_.GD.N0125.d008853 residual
      (by fun_prop) measurable_id]
    rw [_root_.GD.N0125.d008867, Measure.map_id]
  have hfun :
      _root_.GD.N0125.d008842 =
        ((MeasurableEquiv.prodAssoc :
          ((ℝ × ℝ) × ℝ) ≃ᵐ _root_.GD.N0124.d006387) ∘
          Prod.swap) ∘ Prod.map (fun z : ℝ => z ^ 2) id := by
    funext p
    rfl
  rw [hfun]
  calc
    Measure.map
          (((MeasurableEquiv.prodAssoc :
              ((ℝ × ℝ) × ℝ) ≃ᵐ _root_.GD.N0124.d006387) ∘
            Prod.swap) ∘ Prod.map (fun z : ℝ => z ^ 2) id)
          (_root_.GD.N0125.d008853.prod
            ((gammaMeasure α α).prod (gammaMeasure β β)))
        =
      Measure.map
        (MeasurableEquiv.prodAssoc :
          ((ℝ × ℝ) × ℝ) ≃ᵐ _root_.GD.N0124.d006387)
        (Measure.map Prod.swap
          (Measure.map (Prod.map (fun z : ℝ => z ^ 2) id)
            (_root_.GD.N0125.d008853.prod residual))) := by
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map
          (MeasurableEquiv.prodAssoc :
            ((ℝ × ℝ) × ℝ) ≃ᵐ _root_.GD.N0124.d006387)
          (Measure.map Prod.swap (_root_.GD.N0125.d008851.prod residual)) := by
            rw [hfirst]
    _ = _root_.GD.N0125.d008852 α β := by
      rw [Measure.prod_swap, Measure.prodAssoc_prod]
      rfl



def d008870 (a r : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun x => ENNReal.ofReal (gammaPDFReal a r x))

theorem d008871
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    gammaMeasure a r = _root_.GD.N0125.d008870 a r := by
  unfold gammaMeasure _root_.GD.N0125.d008870
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬x ≠ 0} = {(0 : ℝ)} := by
      ext x
      simp
    rw [hset]
    exact measure_singleton 0
  filter_upwards [hzero] with x hx
  by_cases hxp : 0 < x
  · simp [hxp, gammaPDF]
  · have hxneg : x < 0 := lt_of_le_of_ne (not_lt.mp hxp) hx
    simp [gammaPDF, gammaPDFReal, not_le.mpr hxneg, hxp]

theorem d008872
    {α β x y w : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hx : 0 < x) (hy : 0 < y) (hw : 0 < w) :
    gammaPDFReal α α x *
        (gammaPDFReal β β y *
          _root_.GD.N0122.d006380 w)
      =
    _root_.GD.N0116.d006510 α β (x, y, w) := by
  rw [gammaPDFReal, if_pos hx.le, gammaPDFReal, if_pos hy.le]
  unfold _root_.GD.N0122.d006380
  rw [← _root_.GD.N0125.d008862]
  have hhalf :
      (1 / 2 : ℝ) ^ ((3 : ℝ) / 2) =
        ((2 : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num : 0 ≤ (2 : ℝ))]
  rw [hhalf]
  unfold _root_.GD.N0116.d006510 _root_.GD.N0116.d006506
    _root_.GD.N0123.d006499
  simp only [Prod.fst, Prod.snd]
  have hexp :
      Real.exp (-(α * x)) *
          (Real.exp (-(β * y)) * Real.exp (-(w / 2)))
        =
      Real.exp (-(α * x + β * y + w / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hGa : Real.Gamma α ≠ 0 :=
    (Real.Gamma_pos_of_pos hα).ne'
  have hGb : Real.Gamma β ≠ 0 :=
    (Real.Gamma_pos_of_pos hβ).ne'
  have hG3 : Real.Gamma ((3 : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h2p : (2 : ℝ) ^ ((3 : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  calc
    α ^ α / Real.Gamma α * x ^ (α - 1) *
          Real.exp (-(α * x)) *
          (β ^ β / Real.Gamma β * y ^ (β - 1) *
            Real.exp (-(β * y)) *
            ((2 ^ ((3 : ℝ) / 2))⁻¹ /
              Real.Gamma ((3 : ℝ) / 2) *
              w ^ ((1 : ℝ) / 2) * Real.exp (-(w / 2))))
        =
      (α ^ α / Real.Gamma α * x ^ (α - 1) *
        (β ^ β / Real.Gamma β * y ^ (β - 1) *
          ((2 ^ ((3 : ℝ) / 2))⁻¹ /
            Real.Gamma ((3 : ℝ) / 2) *
            w ^ ((1 : ℝ) / 2)))) *
        (Real.exp (-(α * x)) *
          (Real.exp (-(β * y)) * Real.exp (-(w / 2)))) := by ring
    _ =
      (α ^ α / Real.Gamma α * x ^ (α - 1) *
        (β ^ β / Real.Gamma β * y ^ (β - 1) *
          ((2 ^ ((3 : ℝ) / 2))⁻¹ /
            Real.Gamma ((3 : ℝ) / 2) *
            w ^ ((1 : ℝ) / 2)))) *
        Real.exp (-(α * x + β * y + w / 2)) := by rw [hexp]
    _ =
      α ^ α * β ^ β /
          (2 ^ ((3 : ℝ) / 2) * Real.Gamma α *
            Real.Gamma β * Real.Gamma ((3 : ℝ) / 2)) *
        (x ^ (α - 1) * y ^ (β - 1) * w ^ ((1 : ℝ) / 2) *
          Real.exp (-(α * x + β * y + w / 2))) := by
            field_simp [hGa, hGb, hG3, h2p]

theorem d008873
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    _root_.GD.N0125.d008852 α β = _root_.GD.N0125.d008848 α β := by
  rw [_root_.GD.N0125.d008852, _root_.GD.N0125.d008851,
    _root_.GD.N0125.d008871 hα hα,
    _root_.GD.N0125.d008871 hβ hβ,
    _root_.GD.N0125.d008871
      (by norm_num : 0 < (3 : ℝ) / 2)
      (by norm_num : 0 < (1 : ℝ) / 2)]
  unfold _root_.GD.N0125.d008870
  rw [prod_withDensity
      (by fun_prop :
        Measurable (fun x : ℝ =>
          ENNReal.ofReal (gammaPDFReal β β x)))
      (by fun_prop :
        Measurable (fun w : ℝ =>
          ENNReal.ofReal
            (gammaPDFReal ((3 : ℝ) / 2) ((1 : ℝ) / 2) w)))]
  rw [prod_withDensity
      (by fun_prop :
        Measurable (fun x : ℝ =>
          ENNReal.ofReal (gammaPDFReal α α x)))
      (by fun_prop)]
  have hSource :
      _root_.GD.N0124.d006388 =
        Ioi (0 : ℝ) ×ˢ (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    ext p
    simp [_root_.GD.N0124.d006388]
  have hbase :
      (volume.restrict (Ioi (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod
            (volume.restrict (Ioi (0 : ℝ))))
        =
      volume.restrict _root_.GD.N0124.d006388 := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    rw [← Measure.volume_eq_prod ℝ ℝ]
    rw [← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    rw [hSource]
  rw [hbase]
  unfold _root_.GD.N0125.d008848
  apply withDensity_congr_ae
  filter_upwards
    [ae_restrict_mem _root_.GD.N0123.d006491]
      with p hp
  have hgx :
      0 ≤ gammaPDFReal α α p.1 :=
    gammaPDFReal_nonneg hα hα p.1
  have hgy :
      0 ≤ gammaPDFReal β β p.2.1 :=
    gammaPDFReal_nonneg hβ hβ p.2.1
  have hgw :
      0 ≤ gammaPDFReal ((3 : ℝ) / 2) ((1 : ℝ) / 2) p.2.2 :=
    gammaPDFReal_nonneg (by norm_num) (by norm_num) p.2.2
  rw [_root_.GD.N0125.d008863 hp.2.2]
  rw [← ENNReal.ofReal_mul hgy,
    ← ENNReal.ofReal_mul hgx]
  rw [_root_.GD.N0125.d008872 hα hβ hp.1 hp.2.1 hp.2.2]

theorem d008874
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    _root_.GD.N0125.d008850 α β := by
  unfold _root_.GD.N0125.d008850
  rw [_root_.GD.N0125.d008869 hα hβ,
    _root_.GD.N0125.d008873 hα hβ]






theorem d008875
    {P : Measure Ω} {Z Rx Ry D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hSigma : 0 ≤ Sigma)
    (hrawMeas : Measurable (fun ω => (Z ω, (Rx ω, Ry ω))))
    (hJoint : _root_.GD.N0125.d008841 P Z Rx Ry α β)
    (hD : ∀ ω, D ω = Real.sqrt Sigma * Z ω)
    (hL : ∀ ω, L ω =
      e * Ry ω / ((1 - e) * Rx ω + e * Ry ω))
    (hF : ∀ ω, F ω =
      Z ω ^ 2 / ((1 - e) * Rx ω + e * Ry ω))
    (hTransport : _root_.GD.N0125.d008850 α β) :
    _root_.GD.N0125.d008847 P D L F α β e Sigma := by
  intro φ hφ
  let raw : Ω → _root_.GD.N0124.d006387 := fun ω => (Z ω, (Rx ω, Ry ω))
  let ψ : _root_.GD.N0124.d006387 → ℝ := fun p =>
    p.1 ^ 2 * φ (_root_.GD.N0125.d008844 e p, _root_.GD.N0125.d008845 e p)
  have hψ : Measurable ψ := by
    dsimp [ψ]
    exact (measurable_fst.pow_const 2).mul
      (hφ.comp (_root_.GD.N0125.d008859 e))
  have hsqrt : (Real.sqrt Sigma) ^ 2 = Sigma :=
    Real.sq_sqrt hSigma
  have hpoint :
      (fun ω => D ω ^ 2 * φ (L ω, F ω)) =
        (fun ω => Sigma * ψ (raw ω)) := by
    funext ω
    rw [hD ω, hL ω, hF ω]
    dsimp [ψ, raw, _root_.GD.N0125.d008844, _root_.GD.N0125.d008845, _root_.GD.N0125.d008843]
    rw [mul_pow, hsqrt]
    ring
  rw [hpoint, integral_const_mul]
  congr 1
  have hmap :
      (∫ p : _root_.GD.N0124.d006387, ψ p ∂P.map raw) =
        ∫ ω, ψ (raw ω) ∂P := by
    exact integral_map hrawMeas.aemeasurable
      (hψ.aestronglyMeasurable)
  rw [← hmap]
  change (∫ p : _root_.GD.N0124.d006387, ψ p ∂P.map raw) = _
  rw [hJoint]
  have hweight :
      (∫ p : _root_.GD.N0124.d006387, ψ p ∂_root_.GD.N0125.d008840 α β) =
        ∫ p : _root_.GD.N0124.d006387,
          φ (_root_.GD.N0125.d008844 e p, _root_.GD.N0125.d008845 e p) ∂_root_.GD.N0125.d008849 α β := by
    unfold _root_.GD.N0125.d008849
    rw [integral_withDensity_eq_integral_toReal_smul
      (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)
      (fun p : _root_.GD.N0124.d006387 => φ (_root_.GD.N0125.d008844 e p, _root_.GD.N0125.d008845 e p))]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
    rfl
  rw [hweight]
  have hsourceMeas :
      Measurable (fun p : _root_.GD.N0124.d006387 =>
        φ ((_root_.GD.N0124.d006391 e p).1, (_root_.GD.N0124.d006391 e p).2.1)) := by
    exact hφ.comp
      ((_root_.GD.N0125.d008858 e).fst.prodMk
        (_root_.GD.N0125.d008858 e).snd.fst)
  have hmapSource :
      (∫ p : _root_.GD.N0124.d006387,
          φ ((_root_.GD.N0124.d006391 e p).1, (_root_.GD.N0124.d006391 e p).2.1)
            ∂(_root_.GD.N0125.d008849 α β).map _root_.GD.N0125.d008842)
        =
      ∫ p : _root_.GD.N0124.d006387,
          φ ((_root_.GD.N0124.d006391 e (_root_.GD.N0125.d008842 p)).1,
            (_root_.GD.N0124.d006391 e (_root_.GD.N0125.d008842 p)).2.1)
            ∂_root_.GD.N0125.d008849 α β := by
    exact integral_map _root_.GD.N0125.d008854.aemeasurable
      hsourceMeas.aestronglyMeasurable
  have hpair :
      (fun p : _root_.GD.N0124.d006387 => φ (_root_.GD.N0125.d008844 e p, _root_.GD.N0125.d008845 e p)) =
        (fun p : _root_.GD.N0124.d006387 =>
          φ ((_root_.GD.N0124.d006391 e (_root_.GD.N0125.d008842 p)).1,
            (_root_.GD.N0124.d006391 e (_root_.GD.N0125.d008842 p)).2.1)) := by
    funext p
    rw [_root_.GD.N0125.d008846]
  rw [hpair, ← hmapSource]
  rw [hTransport]
  rw [← _root_.GD.N0125.d008860 hα hβ]




theorem d008876
    {P : Measure Ω} {Z Rx Ry D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hSigma : 0 ≤ Sigma)
    (hrawMeas : Measurable (fun ω => (Z ω, (Rx ω, Ry ω))))
    (hJoint : _root_.GD.N0125.d008841 P Z Rx Ry α β)
    (hD : ∀ ω, D ω = Real.sqrt Sigma * Z ω)
    (hL : ∀ ω, L ω =
      e * Ry ω / ((1 - e) * Rx ω + e * Ry ω))
    (hF : ∀ ω, F ω =
      Z ω ^ 2 / ((1 - e) * Rx ω + e * Ry ω)) :
    _root_.GD.N0125.d008847 P D L F α β e Sigma :=
  _root_.GD.N0125.d008875
    hα hβ hSigma hrawMeas hJoint hD hL hF
      (_root_.GD.N0125.d008874 hα hβ)



theorem d008847.d008877
    {P : Measure Ω} {D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (hLaw :
      _root_.GD.N0125.d008847 P D L F α β e Sigma)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q) :
    _root_.GD.N0141.d006687 P D L (fun ω => q (L ω, F ω)) e =
      Sigma * _root_.GD.N0120.d008814 α β e q := by
  unfold _root_.GD.N0125.d008847 at hLaw
  unfold _root_.GD.N0141.d006687 _root_.GD.N0120.d008814 _root_.GD.N0120.d008809
  have h := hLaw (fun p => (p.1 - e) * q p) (by fun_prop)
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with ω
    ring
  · rfl

theorem d008847.d008878
    {P : Measure Ω} {D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (hLaw :
      _root_.GD.N0125.d008847 P D L F α β e Sigma)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q) :
    _root_.GD.N0141.d006688 P D (fun ω => q (L ω, F ω)) =
      Sigma * _root_.GD.N0120.d008815 α β e q := by
  unfold _root_.GD.N0125.d008847 at hLaw
  unfold _root_.GD.N0141.d006688 _root_.GD.N0120.d008815 _root_.GD.N0120.d008809
  exact hLaw (fun p => q p ^ 2) (by fun_prop)




theorem d008879
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (q : ℝ × ℝ → ℝ)
    {atomic smear densityError energy C M : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (hSigma : 0 < Sigma)
    (hq : Measurable q)
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun ω => D ω * (L ω - e)) 2 P)
    (hCarrier : MemLp (fun ω => D ω * q (L ω, F ω)) 2 P)
    (hIndep :
      IndepFun U (fun ω => (D ω, (L ω, F ω))) P)
    (hCentered : ∫ ω, U ω ∂P = 0)
    (hLaw :
      _root_.GD.N0125.d008847 P D L F α β e Sigma)
    (hTraceTarget :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          ((p.1 - e) * q (p.1, p.2.1)) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume)
    (hEnergyTarget :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          q (p.1, p.2.1) ^ 2 *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume)
    (hTraceTargetIter :
      (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389,
          ((p.1 - e) * q (p.1, p.2.1)) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        =
      ∫ l : ℝ in Ioo 0 1,
        ∫ f : ℝ in Ioi 0,
          ∫ H : ℝ in Ioi 0,
            ((l - e) * q (l, f)) *
              (H ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (l, f, H)))
    (hEnergyTargetIter :
      (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389,
          q (p.1, p.2.1) ^ 2 *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        =
      ∫ l : ℝ in Ioo 0 1,
        ∫ f : ℝ in Ioi 0,
          ∫ H : ℝ in Ioi 0,
            q (l, f) ^ 2 *
              (H ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (l, f, H)))
    (hC : 0 < C) (hM : 0 < M)
    (hAtomic : atomic ≤ -(3 * C / 4))
    (hSmear : |smear| ≤ C / 16)
    (hDensity : |densityError| ≤ C / 16)
    (hReducedTrace :
      _root_.GD.N0120.d008816 α β e q = atomic + smear + densityError)
    (hReducedEnergy :
      _root_.GD.N0120.d008817 α β e q = energy)
    (hEnergyCeiling : energy ≤ M) :
    _root_.GD.N0141.d006684 P
        (_root_.GD.N0141.d006686 U D L (fun ω => q (L ω, F ω))
          e ((C / 2) / M))
      < _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) := by
  let t : ℝ := _root_.GD.N0120.d008814 α β e q
  let a : ℝ := _root_.GD.N0120.d008815 α β e q
  apply
    _root_.GD.N0120.d008828
      (P := P) (U := U) (D := D) (L := L) (F := F)
      (α := α) (β := β) (e := e) (Sigma := Sigma)
      q (fun _ => t) (fun _ => a)
      hα hβ he0 he1 hSigma hq hU hWeight hCarrier hIndep hCentered
  · rw [_root_.GD.N0142.d008837]
    exact hLaw.d008877 q hq
  · rw [_root_.GD.N0142.d008837]
    exact hLaw.d008878 q hq
  · exact _root_.GD.N0142.d008838 t
  · exact _root_.GD.N0142.d008838 a
  · exact _root_.GD.N0142.d008836 t
  · exact _root_.GD.N0142.d008836 a
  · exact hTraceTarget
  · exact hEnergyTarget
  · exact hTraceTargetIter
  · exact hEnergyTargetIter
  · exact hC
  · exact hM
  · exact hAtomic
  · exact hSmear
  · exact hDensity
  · exact hReducedTrace
  · exact hReducedEnergy
  · exact hEnergyCeiling

end

end GD.N0125
