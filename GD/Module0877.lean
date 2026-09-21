import GD.Module0873









open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1434

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1435
open _root_.GD.N0124

theorem d013553
    (t : ℝ) (z : _root_.GD.N0124.d006387) :
    _root_.GD.N0232.N0720.N1435.d013470 t z =
      ((_root_.GD.N0124.d006391 t z).1,
        (_root_.GD.N0124.d006391 t z).2.1) := by
  unfold _root_.GD.N0232.N0720.N1435.d013470 _root_.GD.N0232.N0720.N1435.d013468
    _root_.GD.N0232.N0720.N1435.d013462 _root_.GD.N0232.N0720.N1435.d013457 _root_.GD.N0232.N0720.N1435.d013460
    _root_.GD.N0124.d006391 _root_.GD.N0124.d006390
  rfl



theorem d013554
    {α β t C : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (ht0 : 0 < t) (ht1 : t < 1)
    (φ : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hφ : Measurable φ)
    (hC : ∀ x, |φ x| ≤ C) :
    _root_.GD.N0120.d008809 α β t φ =
      _root_.GD.N0120.d008810 α β t φ := by
  let g : _root_.GD.N0124.d006387 → ℝ := fun p =>
    φ (p.1, p.2.1) * (p.2.2 ^ 2 / (t * (1 - t))) *
      _root_.GD.N0116.d006510 α β
        (_root_.GD.N0124.d006392 t p)
  have hg : IntegrableOn g _root_.GD.N0124.d006389 volume :=
    _root_.GD.N0108.d008885
      hα hβ ht0 ht1 φ hφ hC
  exact _root_.GD.N0120.d008824
    hα hβ ht0 ht1 φ hg
      (_root_.GD.N0143.d006698 g hg)



theorem d013555 :
    (MeasurableEquiv.prodAssoc :
      (_root_.GD.N0232.N0720.N1436.d013217 × ℝ) ≃ᵐ _root_.GD.N0124.d006387) ''
        (_root_.GD.N0232.N0720.N1436.d013218 ×ˢ Set.Ioi 0) =
      _root_.GD.N0124.d006389 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change 0 < q.1.1 ∧ q.1.1 < 1 ∧ 0 < q.1.2 ∧ 0 < q.2
    exact ⟨hq.1.1.1, hq.1.1.2, hq.1.2, hq.2⟩
  · intro hp
    refine ⟨MeasurableEquiv.prodAssoc.symm p, ?_,
      MeasurableEquiv.prodAssoc.apply_symm_apply p⟩
    change ((p.1, p.2.1) ∈ _root_.GD.N0232.N0720.N1436.d013218) ∧ p.2.2 ∈ Set.Ioi 0
    exact ⟨⟨⟨hp.1, hp.2.1⟩, hp.2.2.1⟩, hp.2.2.2⟩



theorem d013556
    {α β t C : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (ht0 : 0 < t) (ht1 : t < 1)
    (φ : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hφ : Measurable φ)
    (hC : ∀ x, |φ x| ≤ C) :
    IntegrableOn
      (fun x => φ x * _root_.GD.N0116.d006511 α β t x)
      _root_.GD.N0232.N0720.N1436.d013218 volume := by
  let g : _root_.GD.N0124.d006387 → ℝ := fun p =>
    φ (p.1, p.2.1) * (p.2.2 ^ 2 / (t * (1 - t))) *
      _root_.GD.N0116.d006510 α β
        (_root_.GD.N0124.d006392 t p)
  let g' : _root_.GD.N0232.N0720.N1436.d013217 × ℝ → ℝ := fun q =>
    g (MeasurableEquiv.prodAssoc q)
  have hg : IntegrableOn g _root_.GD.N0124.d006389 volume :=
    _root_.GD.N0108.d008885
      hα hβ ht0 ht1 φ hφ hC
  have hAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        (_root_.GD.N0232.N0720.N1436.d013217 × ℝ) ≃ᵐ _root_.GD.N0124.d006387)
      (volume : Measure (_root_.GD.N0232.N0720.N1436.d013217 × ℝ))
      (volume : Measure _root_.GD.N0124.d006387) := by
    simpa [Measure.volume_eq_prod] using
      (measurePreserving_prodAssoc
        (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ))
  have hg' : IntegrableOn g'
      (_root_.GD.N0232.N0720.N1436.d013218 ×ˢ Set.Ioi 0) volume := by
    have htransport :=
      (hAssoc.integrableOn_image
        MeasurableEquiv.prodAssoc.measurableEmbedding
        (f := g) (s := _root_.GD.N0232.N0720.N1436.d013218 ×ˢ Set.Ioi 0)).mp
    apply htransport
    simpa [_root_.GD.N0232.N0720.N1434.d013555] using hg
  have hg'restrict : Integrable g'
      ((volume.restrict _root_.GD.N0232.N0720.N1436.d013218).prod
        (volume.restrict (Set.Ioi 0))) := by
    simpa only [IntegrableOn, Measure.prod_restrict,
      Measure.volume_eq_prod] using hg'
  have hmarg := hg'restrict.integral_prod_left
  apply hmarg.congr
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219]
    with x hx
  have hradial := _root_.GD.N0116.d006516
    hα hβ ht0 ht1 hx.1.1 hx.1.2 hx.2 φ
  change
    (∫ H : ℝ in Set.Ioi 0,
      φ x * (H ^ 2 / (t * (1 - t))) *
        _root_.GD.N0116.d006510 α β
          (_root_.GD.N0124.d006392 t (x.1, x.2, H))) =
      φ x * _root_.GD.N0116.d006511 α β t x
  exact hradial



theorem d013557
    {α β t C : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (ht0 : 0 < t) (ht1 : t < 1)
    (φ : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hφ : Measurable φ)
    (hC : ∀ x, |φ x| ≤ C) :
    _root_.GD.N0120.d008810 α β t φ =
      ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        φ x * _root_.GD.N0116.d006511 α β t x := by
  have hInt := _root_.GD.N0232.N0720.N1434.d013556
    hα hβ ht0 ht1 φ hφ hC
  rw [show _root_.GD.N0232.N0720.N1436.d013218 = Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioi 0 by rfl]
    at hInt ⊢
  unfold _root_.GD.N0120.d008810
  exact (setIntegral_prod
    (fun x => φ x * _root_.GD.N0116.d006511 α β t x)
    hInt).symm



theorem d013558
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t C : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (φ : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hφ : Measurable φ)
    (hC : ∀ x, |φ x| ≤ C) :
    (∫ x, φ x ∂_root_.GD.N0232.N0720.N1436.d013289 m n t) =
      _root_.GD.N0120.d008810
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t φ := by
  let α := _root_.GD.N0232.N0720.N1436.d013207 m
  let β := _root_.GD.N0232.N0720.N1436.d013208 n
  have hα : 0 < α := _root_.GD.N0232.N0720.N1436.d013211 hm
  have hβ : 0 < β := _root_.GD.N0232.N0720.N1436.d013212 hn
  calc
    (∫ x, φ x ∂_root_.GD.N0232.N0720.N1436.d013289 m n t) =
        ∫ x,
          (ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 m n t x)).toReal • φ x
            ∂_root_.GD.N0232.N0720.N1436.d013288 := by
      unfold _root_.GD.N0232.N0720.N1436.d013289
      rw [integral_withDensity_eq_integral_toReal_smul
        (_root_.GD.N0232.N0720.N1436.d013279 m n t).ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    _ = ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          φ x * _root_.GD.N0232.N0720.N1436.d013273 m n t x := by
      unfold _root_.GD.N0232.N0720.N1436.d013288
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219]
        with x hx
      rw [ENNReal.toReal_ofReal
        (_root_.GD.N0232.N0720.N1436.d013286 hm hn ht0 ht1 hx).le]
      simp [smul_eq_mul, mul_comm]
    _ = ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          φ x * _root_.GD.N0116.d006511 α β t x := by
      apply setIntegral_congr_fun _root_.GD.N0232.N0720.N1436.d013219
      intro x hx
      change φ x * _root_.GD.N0232.N0720.N1436.d013273 m n t x =
        φ x * _root_.GD.N0116.d006511 α β t x
      rw [_root_.GD.N0232.N0720.N1435.d013489
        hm hn ht0 ht1 hx]
    _ = _root_.GD.N0120.d008810 α β t φ := by
      symm
      exact _root_.GD.N0232.N0720.N1434.d013557
        hα hβ ht0 ht1 φ hφ hC



theorem d013559
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t C : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (φ : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hφ : Measurable φ)
    (hC : ∀ x, |φ x| ≤ C) :
    Integrable φ (_root_.GD.N0232.N0720.N1436.d013289 m n t) := by
  have hInv := _root_.GD.N0232.N0720.N1434.d013556
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)
    ht0 ht1 φ hφ hC
  unfold _root_.GD.N0232.N0720.N1436.d013289
  apply (integrable_withDensity_iff_integrable_smul₀'
    (μ := _root_.GD.N0232.N0720.N1436.d013288)
    (f := fun x => ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 m n t x))
    (_root_.GD.N0232.N0720.N1436.d013279 m n t).ennreal_ofReal.aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).2
  unfold _root_.GD.N0232.N0720.N1436.d013288
  apply hInv.congr
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219]
    with x hx
  rw [ENNReal.toReal_ofReal
      (_root_.GD.N0232.N0720.N1436.d013286 hm hn ht0 ht1 hx).le,
    _root_.GD.N0232.N0720.N1435.d013489 hm hn ht0 ht1 hx]
  simp [smul_eq_mul, mul_comm]

theorem d013560
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1436.d013289 m n t) := by
  have hOne : Integrable (fun _ : _root_.GD.N0232.N0720.N1436.d013217 => (1 : ℝ))
      (_root_.GD.N0232.N0720.N1436.d013289 m n t) :=
    _root_.GD.N0232.N0720.N1434.d013559 hm hn ht0 ht1
      (C := 1) (fun _ => (1 : ℝ)) measurable_const (fun _ => by norm_num)
  exact (integrable_const_iff_isFiniteMeasure one_ne_zero).mp hOne



theorem d013561
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t C : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (φ : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hφ : Measurable φ)
    (hC : ∀ x, |φ x| ≤ C) :
    (∫ x, φ x ∂_root_.GD.N0232.N0720.N1435.d013483 m n t) =
      _root_.GD.N0120.d008810
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t φ := by
  rw [← _root_.GD.N0232.N0720.N1435.d013486 hm hn ht0 ht1]
  rw [integral_map (_root_.GD.N0232.N0720.N1435.d013471 t).aemeasurable
    hφ.aestronglyMeasurable]
  rw [_root_.GD.N0125.d008873
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)]
  simp_rw [_root_.GD.N0232.N0720.N1434.d013553]
  rw [← _root_.GD.N0125.d008860
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)]
  exact _root_.GD.N0232.N0720.N1434.d013554
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)
    ht0 ht1 φ hφ hC



theorem d013562
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1435.d013483 m n t =
      _root_.GD.N0232.N0720.N1436.d013289 m n t := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1435.d013483 m n t) :=
    _root_.GD.N0232.N0720.N1435.d013485 hm hn ht0 ht1
  letI : IsFiniteMeasure (_root_.GD.N0232.N0720.N1436.d013289 m n t) :=
    _root_.GD.N0232.N0720.N1434.d013560 hm hn ht0 ht1
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [← measureReal_def, ← measureReal_def,
    ← integral_indicator_one hs, ← integral_indicator_one hs]
  let φ : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
    s.indicator (fun _ => (1 : ℝ))
  have hφ : Measurable φ := Measurable.indicator measurable_const hs
  have hbound : ∀ x, |φ x| ≤ (1 : ℝ) := by
    intro x
    by_cases hx : x ∈ s <;> simp [φ, hx]
  change (∫ x, φ x ∂_root_.GD.N0232.N0720.N1435.d013483 m n t) =
    ∫ x, φ x ∂_root_.GD.N0232.N0720.N1436.d013289 m n t
  exact
    (_root_.GD.N0232.N0720.N1434.d013561
      hm hn ht0 ht1 φ hφ hbound).trans
      (_root_.GD.N0232.N0720.N1434.d013558
        hm hn ht0 ht1 φ hφ hbound).symm



theorem d013563
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Measure.map (_root_.GD.N0232.N0720.N1435.d013470 t)
        (_root_.GD.N0125.d008852
          (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)) =
      _root_.GD.N0232.N0720.N1436.d013289 m n t := by
  calc
    Measure.map (_root_.GD.N0232.N0720.N1435.d013470 t)
        (_root_.GD.N0125.d008852
          (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)) =
        _root_.GD.N0232.N0720.N1435.d013483 m n t :=
      _root_.GD.N0232.N0720.N1435.d013486 hm hn ht0 ht1
    _ = _root_.GD.N0232.N0720.N1436.d013289 m n t :=
      _root_.GD.N0232.N0720.N1434.d013562
        hm hn ht0 ht1

theorem d013564
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1436.d013289 m n t) := by
  rw [← _root_.GD.N0232.N0720.N1434.d013562
    hm hn ht0 ht1]
  exact _root_.GD.N0232.N0720.N1435.d013485
    hm hn ht0 ht1

end

end N1434
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1434.d013553
#print axioms _root_.GD.N0232.N0720.N1434.d013554
#print axioms _root_.GD.N0232.N0720.N1434.d013556
#print axioms _root_.GD.N0232.N0720.N1434.d013558
#print axioms _root_.GD.N0232.N0720.N1434.d013562
#print axioms _root_.GD.N0232.N0720.N1434.d013563
#print axioms _root_.GD.N0232.N0720.N1434.d013564
