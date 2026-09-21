import GD.Module0177
import GD.Module0877

set_option warningAsError true
set_option autoImplicit false












open MeasureTheory Set Filter Topology

namespace GD.N0232.N0720.N1241

noncomputable section

open _root_.GD.N0232.N0720.N1240 _root_.GD.N0232.N0720.N1238
open _root_.GD.N0232.N0720.N1239 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434

def d013565 (z : _root_.GD.N0232.N0720.N1238.d002103) : _root_.GD.N0232.N0720.N1436.d013217 :=
  (z.val.1 + 1 / 2, z.val.2)

theorem d013566 : IsOpenEmbedding _root_.GD.N0232.N0720.N1241.d013565 := by
  have hs : IsOpen {z : ℝ × ℝ |
      z.1 ∈ Ioo (-1 / 4 : ℝ) (1 / 4) ∧ z.2 ∈ Ioo (0 : ℝ) (1 / 4)} :=
    isOpen_Ioo.prod isOpen_Ioo
  convert! (Homeomorph.addRight ((1 / 2 : ℝ), (0 : ℝ))).isOpenEmbedding.comp
    hs.isOpenEmbedding_subtypeVal using 1
  funext z
  apply Prod.ext <;> simp [_root_.GD.N0232.N0720.N1241.d013565]

theorem d013567 (z : _root_.GD.N0232.N0720.N1238.d002103) :
    _root_.GD.N0232.N0720.N1241.d013565 z ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  refine ⟨⟨?_, ?_⟩, z.property.2.1⟩ <;>
    dsimp [_root_.GD.N0232.N0720.N1241.d013565] <;> linarith [z.property.1.1, z.property.1.2]

def d013568 : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  _root_.GD.N0232.N0720.N1436.d013289 2 2 (1 / 2)

instance d013569 : IsProbabilityMeasure _root_.GD.N0232.N0720.N1241.d013568 :=
  _root_.GD.N0232.N0720.N1434.d013564 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

def d013570 : Measure _root_.GD.N0232.N0720.N1238.d002103 :=
  _root_.GD.N0232.N0720.N1241.d013568.comap _root_.GD.N0232.N0720.N1241.d013565

instance d013571 : IsFiniteMeasure _root_.GD.N0232.N0720.N1241.d013570 := by
  unfold _root_.GD.N0232.N0720.N1241.d013570
  infer_instance

instance d013572 : Measure.IsOpenPosMeasure _root_.GD.N0232.N0720.N1241.d013570 where
  open_pos U hU hUne := by
    have he := _root_.GD.N0232.N0720.N1241.d013566
    rw [_root_.GD.N0232.N0720.N1241.d013570, he.measurableEmbedding.comap_apply]
    have ho : IsOpen (_root_.GD.N0232.N0720.N1241.d013565 '' U) := he.isOpen_iff_image_isOpen.mp hU
    have hs : _root_.GD.N0232.N0720.N1241.d013565 '' U ⊆ _root_.GD.N0232.N0720.N1436.d013218 := by
      rintro _ ⟨z, _, rfl⟩
      exact _root_.GD.N0232.N0720.N1241.d013567 z
    have hv : volume (_root_.GD.N0232.N0720.N1241.d013565 '' U) ≠ 0 :=
      ho.measure_ne_zero volume (hUne.image _root_.GD.N0232.N0720.N1241.d013565)
    have hr : _root_.GD.N0232.N0720.N1436.d013288 (_root_.GD.N0232.N0720.N1241.d013565 '' U) ≠ 0 := by
      rw [_root_.GD.N0232.N0720.N1436.d013288, Measure.restrict_apply ho.measurableSet,
        inter_eq_left.mpr hs]
      exact hv
    have habs : _root_.GD.N0232.N0720.N1436.d013288 ≪ _root_.GD.N0232.N0720.N1241.d013568 :=
      _root_.GD.N0232.N0720.N1436.d013291
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact fun hzero ↦ hr (habs hzero)

theorem d013573 :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070,
      c ≤ _root_.GD.N0232.N0720.N1239.d002125 _root_.GD.N0232.N0720.N1241.d013570 ρ :=
  _root_.GD.N0232.N0720.N1239.d002129 _root_.GD.N0232.N0720.N1241.d013570

def d013574 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070)
    (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  (_root_.GD.N0232.N0720.N1240.d002100 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) p.1 p.2 - p.1) ^ 2

theorem d013575 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070)
    (z : _root_.GD.N0232.N0720.N1238.d002103) :
    _root_.GD.N0232.N0720.N1241.d013574 ρ (_root_.GD.N0232.N0720.N1241.d013565 z) = _root_.GD.N0232.N0720.N1238.d002112 ρ z ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1241.d013574 _root_.GD.N0232.N0720.N1241.d013565 _root_.GD.N0232.N0720.N1238.d002112
  rw [_root_.GD.N0232.N0720.N1240.d002101 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)
    (show z.val.1 + 1 / 2 ∈ Icc (1 / 4 : ℝ) (3 / 4) from
      ⟨by linarith [z.property.1.1], by linarith [z.property.1.2]⟩)
    ⟨by linarith [z.property.2.1], z.property.2.2.le⟩]

theorem d013576
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    _root_.GD.N0232.N0720.N1239.d002125 _root_.GD.N0232.N0720.N1241.d013570 ρ =
      ∫ p in range _root_.GD.N0232.N0720.N1241.d013565, _root_.GD.N0232.N0720.N1241.d013574 ρ p ∂_root_.GD.N0232.N0720.N1241.d013568 := by
  have he := _root_.GD.N0232.N0720.N1241.d013566.measurableEmbedding
  calc
    _root_.GD.N0232.N0720.N1239.d002125 _root_.GD.N0232.N0720.N1241.d013570 ρ =
        ∫ z, _root_.GD.N0232.N0720.N1241.d013574 ρ (_root_.GD.N0232.N0720.N1241.d013565 z) ∂_root_.GD.N0232.N0720.N1241.d013570 := by
      apply integral_congr_ae
      exact ae_of_all _root_.GD.N0232.N0720.N1241.d013570 fun z ↦ (_root_.GD.N0232.N0720.N1241.d013575 ρ z).symm
    _ = ∫ p, _root_.GD.N0232.N0720.N1241.d013574 ρ p ∂_root_.GD.N0232.N0720.N1241.d013570.map _root_.GD.N0232.N0720.N1241.d013565 :=
      (he.integral_map _).symm
    _ = _ := by rw [_root_.GD.N0232.N0720.N1241.d013570, he.map_comap]

def d013577 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (_root_.GD.N0232.N0720.N1241.d013574 ρ p) ∂_root_.GD.N0232.N0720.N1241.d013568

theorem d013578
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1239.d002125 _root_.GD.N0232.N0720.N1241.d013570 ρ) ≤
      _root_.GD.N0232.N0720.N1241.d013577 ρ := by
  have he := _root_.GD.N0232.N0720.N1241.d013566.measurableEmbedding
  calc
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1239.d002125 _root_.GD.N0232.N0720.N1241.d013570 ρ) =
        ∫⁻ z, ENNReal.ofReal (_root_.GD.N0232.N0720.N1238.d002112 ρ z ^ 2) ∂_root_.GD.N0232.N0720.N1241.d013570 :=
      ofReal_integral_eq_lintegral_ofReal
        (_root_.GD.N0232.N0720.N1239.d002126 _root_.GD.N0232.N0720.N1241.d013570 ρ)
        (ae_of_all _root_.GD.N0232.N0720.N1241.d013570 fun _ ↦ sq_nonneg _)
    _ = ∫⁻ z, ENNReal.ofReal (_root_.GD.N0232.N0720.N1241.d013574 ρ (_root_.GD.N0232.N0720.N1241.d013565 z))
        ∂_root_.GD.N0232.N0720.N1241.d013570 := by
      apply lintegral_congr
      intro z
      rw [_root_.GD.N0232.N0720.N1241.d013575]
    _ = ∫⁻ p, ENNReal.ofReal (_root_.GD.N0232.N0720.N1241.d013574 ρ p)
        ∂_root_.GD.N0232.N0720.N1241.d013570.map _root_.GD.N0232.N0720.N1241.d013565 := by
      simpa only [Function.comp_def] using
        (he.lintegral_map (μ := _root_.GD.N0232.N0720.N1241.d013570)
          (fun p ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1241.d013574 ρ p))).symm
    _ = ∫⁻ p in range _root_.GD.N0232.N0720.N1241.d013565, ENNReal.ofReal (_root_.GD.N0232.N0720.N1241.d013574 ρ p)
        ∂_root_.GD.N0232.N0720.N1241.d013568 := by rw [_root_.GD.N0232.N0720.N1241.d013570, he.map_comap]
    _ ≤ _root_.GD.N0232.N0720.N1241.d013577 ρ := lintegral_mono' Measure.restrict_le_self le_rfl



theorem d013579 :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070,
      ENNReal.ofReal c ≤ _root_.GD.N0232.N0720.N1241.d013577 ρ := by
  obtain ⟨c, hc, hfloor⟩ := _root_.GD.N0232.N0720.N1241.d013573
  exact ⟨c, hc, fun ρ ↦ (ENNReal.ofReal_le_ofReal (hfloor ρ)).trans
    (_root_.GD.N0232.N0720.N1241.d013578 ρ)⟩

theorem d013580 (x : _root_.GD.N0232.N0720.N1240.d002070)
    {p : _root_.GD.N0232.N0720.N1436.d013217} (hp : p ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) p.1 p.2 := by
  have ht : 0 ≤ (x : ℝ) + 1 / 2 := by linarith [x.property.1]
  have ht' : (x : ℝ) + 1 / 2 ≤ 1 := by linarith [x.property.2]
  by_cases hz : (x : ℝ) + 1 / 2 = 0
  · simp only [_root_.GD.N0232.N0720.N1240.d002099, hz, zero_mul, sub_zero, one_mul, zero_add]
    exact hp.1.1
  · have htpos : 0 < (x : ℝ) + 1 / 2 := lt_of_le_of_ne ht (Ne.symm hz)
    unfold _root_.GD.N0232.N0720.N1240.d002099
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos
        (mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht')) hp.2.le)
        (mul_pos htpos (sub_pos.mpr hp.1.2)))
      (mul_nonneg (sub_nonneg.mpr ht') hp.1.1.le)

theorem d013581
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) {p : _root_.GD.N0232.N0720.N1436.d013217}
    (hp : p ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1240.d002100 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) p.1 p.2 ∈ Icc (0 : ℝ) 1 := by
  let w : _root_.GD.N0232.N0720.N1240.d002070 → ℝ := fun x ↦
    Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) p.1 p.2) (-5 / 2)
  have hw : Continuous w := by
    apply (show Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦
      _root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) p.1 p.2) from by unfold _root_.GD.N0232.N0720.N1240.d002099; fun_prop).rpow_const
    exact fun x ↦ Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1241.d013580 x hp))
  have hwpos (x : _root_.GD.N0232.N0720.N1240.d002070) : 0 < w x :=
    Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1241.d013580 x hp) _
  have hi : Integrable w (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    simpa using hw.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070))
      (μ := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))
  have hni : Integrable (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ ((x : ℝ) + 1 / 2) * w x)
      (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    have hn : Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ ((x : ℝ) + 1 / 2) * w x) :=
      (continuous_subtype_val.add continuous_const).mul hw
    simpa using hn.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070))
      (μ := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))
  have hd : 0 < ∫ x, w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    apply (integral_pos_iff_support_of_nonneg (fun x ↦ (hwpos x).le) hi).2
    have hs : Function.support w = univ := by
      ext x
      simp [Function.mem_support, ne_of_gt (hwpos x)]
    rw [hs]
    simp
  have hn0 : 0 ≤ ∫ x, ((x : ℝ) + 1 / 2) * w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (by linarith [x.property.1]) (hwpos x).le
  have hnle : (∫ x, ((x : ℝ) + 1 / 2) * w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) ≤
      (∫ x, w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) := by
    apply integral_mono hni hi
    intro x
    exact mul_le_of_le_one_left (hwpos x).le (by linarith [x.property.2])
  exact ⟨div_nonneg hn0 hd.le, (div_le_one hd).mpr hnle⟩

private theorem d013582 (q : ℝ) : Measurable (fun x : ℝ ↦ Real.rpow x q) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const fun x hx ↦ Or.inl hx

theorem d013583 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    Measurable (_root_.GD.N0232.N0720.N1241.d013574 ρ) := by
  have hw : Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × _root_.GD.N0232.N0720.N1240.d002070 ↦
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 ((z.2 : ℝ) + 1 / 2) z.1.1 z.1.2) (-5 / 2)) := by
    apply (_root_.GD.N0232.N0720.N1241.d013582 (-5 / 2)).comp
    unfold _root_.GD.N0232.N0720.N1240.d002099
    fun_prop
  have hn : Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × _root_.GD.N0232.N0720.N1240.d002070 ↦
      ((z.2 : ℝ) + 1 / 2) *
        Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 ((z.2 : ℝ) + 1 / 2) z.1.1 z.1.2) (-5 / 2)) :=
    (show Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × _root_.GD.N0232.N0720.N1240.d002070 ↦
      (z.2 : ℝ) + 1 / 2) from by fun_prop).mul hw
  have hiw := hw.stronglyMeasurable.integral_prod_right' (ν := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))
  have hin := hn.stronglyMeasurable.integral_prod_right' (ν := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))
  exact ((hin.measurable.div hiw.measurable).sub measurable_fst).pow_const 2

theorem d013584 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    Integrable (_root_.GD.N0232.N0720.N1241.d013574 ρ) _root_.GD.N0232.N0720.N1241.d013568 := by
  apply (integrable_const (1 : ℝ)).mono' (_root_.GD.N0232.N0720.N1241.d013583 ρ).aestronglyMeasurable
  have hae : ∀ᵐ p ∂_root_.GD.N0232.N0720.N1241.d013568, p ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
    apply (_root_.GD.N0232.N0720.N1436.d013290 2 2 (1 / 2)).ae_le
    exact ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219
  filter_upwards [hae] with p hp
  have h := _root_.GD.N0232.N0720.N1241.d013581 ρ hp
  have habs : |_root_.GD.N0232.N0720.N1240.d002100 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) p.1 p.2 - p.1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [h.1, h.2, hp.1.1, hp.1.2]
  unfold _root_.GD.N0232.N0720.N1241.d013574
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (_root_.GD.N0232.N0720.N1240.d002100 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) p.1 p.2 - p.1),
    mul_nonneg (sub_nonneg.mpr habs) (add_nonneg (abs_nonneg
      (_root_.GD.N0232.N0720.N1240.d002100 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) p.1 p.2 - p.1))
        (by norm_num : (0 : ℝ) ≤ 1))]



theorem d013585 :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070,
      c ≤ ∫ p, _root_.GD.N0232.N0720.N1241.d013574 ρ p ∂_root_.GD.N0232.N0720.N1241.d013568 := by
  obtain ⟨c, hc, hfloor⟩ := _root_.GD.N0232.N0720.N1241.d013579
  refine ⟨c, hc, fun ρ ↦ ?_⟩
  have hi := _root_.GD.N0232.N0720.N1241.d013584 ρ
  have h := hfloor ρ
  rw [_root_.GD.N0232.N0720.N1241.d013577,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _root_.GD.N0232.N0720.N1241.d013568 fun _ ↦ sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by
    exact integral_nonneg fun _ ↦ sq_nonneg _)).mp h

end

end GD.N0232.N0720.N1241

#print axioms _root_.GD.N0232.N0720.N1241.d013572
#print axioms _root_.GD.N0232.N0720.N1241.d013573
#print axioms _root_.GD.N0232.N0720.N1241.d013576
#print axioms _root_.GD.N0232.N0720.N1241.d013579
#print axioms _root_.GD.N0232.N0720.N1241.d013584
#print axioms _root_.GD.N0232.N0720.N1241.d013585
