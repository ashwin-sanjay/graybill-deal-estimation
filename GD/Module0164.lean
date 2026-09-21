import GD.Module0163
















open MeasureTheory Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1057

noncomputable section

open _root_.GD.N0232.N0720.N1060


def d001899 (m u l target t : ℝ) : ℝ :=
  t * l ^ 2 * (u - target) ^ 2 / (m + t * l)



theorem d001900
    (m u l target t : ℝ) (hm : 0 < m) (hl : 0 ≤ l) (ht : 0 < t) :
    0 ≤ _root_.GD.N0232.N0720.N1057.d001899 m u l target t ∧
      _root_.GD.N0232.N0720.N1057.d001899 m u l target t ≤ l * (u - target) ^ 2 := by
  have hden : 0 < m + t * l := by positivity
  constructor
  · unfold _root_.GD.N0232.N0720.N1057.d001899
    positivity
  · unfold _root_.GD.N0232.N0720.N1057.d001899
    rw [div_le_iff₀ hden]
    have hnonneg : 0 ≤ l * (u - target) ^ 2 * m := by positivity
    calc
      t * l ^ 2 * (u - target) ^ 2 ≤
          t * l ^ 2 * (u - target) ^ 2 +
            l * (u - target) ^ 2 * m :=
        le_add_of_nonneg_right hnonneg
      _ = l * (u - target) ^ 2 * (m + t * l) := by ring



theorem d001901
    (m u l target : ℝ) (hm : 0 < m) :
    Tendsto (fun t : ℝ ↦ _root_.GD.N0232.N0720.N1057.d001899 m u l target t)
      (𝓝[>] 0) (nhds 0) := by
  have hcont : ContinuousAt
      (fun t : ℝ ↦ t * l ^ 2 * (u - target) ^ 2 / (m + t * l)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using ne_of_gt hm
  simpa [_root_.GD.N0232.N0720.N1057.d001899] using
    hcont.tendsto.mono_left nhdsWithin_le_nhds





theorem d001902
    {X : Type*} [MeasurableSpace X]
    (measure : Measure X) (m u l target : X → ℝ)
    (hm_meas : Measurable m) (hu_meas : Measurable u)
    (hl_meas : Measurable l) (htarget_meas : Measurable target)
    (hm : ∀ᵐ x ∂measure, 0 < m x)
    (hl : ∀ᵐ x ∂measure, 0 ≤ l x)
    (henvelope : Integrable
      (fun x ↦ l x * (u x - target x) ^ 2) measure) :
    Tendsto
      (fun t : ℝ ↦ ∫ x,
        _root_.GD.N0232.N0720.N1057.d001899 (m x) (u x) (l x) (target x) t ∂measure)
      (𝓝[>] 0) (nhds 0) := by
  have hdct :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := measure) (l := 𝓝[>] (0 : ℝ))
      (F := fun t x ↦
        _root_.GD.N0232.N0720.N1057.d001899 (m x) (u x) (l x) (target x) t)
      (f := fun _x ↦ (0 : ℝ))
      (fun x ↦ l x * (u x - target x) ^ 2)
      (Filter.Eventually.of_forall fun t ↦
        ((((hl_meas.pow_const 2).const_mul t).mul
          ((hu_meas.sub htarget_meas).pow_const 2)).div
            (hm_meas.add (hl_meas.const_mul t))).aestronglyMeasurable)
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        filter_upwards [hm, hl] with x hmx hlx
        change ‖_root_.GD.N0232.N0720.N1057.d001899
          (m x) (u x) (l x) (target x) t‖ ≤
            l x * (u x - target x) ^ 2
        rw [Real.norm_eq_abs,
          abs_of_nonneg (_root_.GD.N0232.N0720.N1057.d001900
            (m x) (u x) (l x) (target x) t hmx hlx ht).1]
        exact (_root_.GD.N0232.N0720.N1057.d001900
          (m x) (u x) (l x) (target x) t hmx hlx ht).2)
      henvelope
      (by
        filter_upwards [hm] with x hmx
        exact _root_.GD.N0232.N0720.N1057.d001901
          (m x) (u x) (l x) (target x) hmx)
  simpa only [integral_zero] using hdct





theorem d001903
    {X : Type*} [MeasurableSpace X]
    (measure : Measure X) (s m u l target : X → ℝ)
    (hm_meas : Measurable m) (hu_meas : Measurable u)
    (hl_meas : Measurable l) (htarget_meas : Measurable target)
    (hm : ∀ᵐ x ∂measure, 0 < m x)
    (hl : ∀ᵐ x ∂measure, 0 ≤ l x)
    (hgradient : Integrable
      (fun x ↦ _root_.GD.N0232.N0720.N1060.d001883 (s x) (u x) (l x) (target x)) measure)
    (henvelope : Integrable
      (fun x ↦ l x * (u x - target x) ^ 2) measure) :
    Tendsto
      (fun t : ℝ ↦ ∫ x,
        (_root_.GD.N0232.N0720.N1060.d001882 (s x) (m x) (u x) (l x) (target x) t -
          _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x)) / t ∂measure)
      (𝓝[>] 0)
      (nhds (∫ x, _root_.GD.N0232.N0720.N1060.d001883 (s x) (u x) (l x) (target x) ∂measure)) := by
  have hremainder := _root_.GD.N0232.N0720.N1057.d001902
    measure m u l target hm_meas hu_meas hl_meas htarget_meas hm hl henvelope
  have hsum : Tendsto
      (fun t : ℝ ↦
        (∫ x, _root_.GD.N0232.N0720.N1060.d001883 (s x) (u x) (l x) (target x) ∂measure) +
          ∫ x, _root_.GD.N0232.N0720.N1057.d001899 (m x) (u x) (l x) (target x) t
            ∂measure)
      (𝓝[>] 0)
      (nhds ((∫ x, _root_.GD.N0232.N0720.N1060.d001883 (s x) (u x) (l x) (target x) ∂measure) + 0)) :=
    tendsto_const_nhds.add hremainder
  have heq :
      (fun t : ℝ ↦ ∫ x,
        (_root_.GD.N0232.N0720.N1060.d001882 (s x) (m x) (u x) (l x) (target x) t -
          _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x)) / t ∂measure) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ ↦
        (∫ x, _root_.GD.N0232.N0720.N1060.d001883 (s x) (u x) (l x) (target x) ∂measure) +
          ∫ x, _root_.GD.N0232.N0720.N1057.d001899 (m x) (u x) (l x) (target x) t
            ∂measure) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hremMeas : AEStronglyMeasurable
        (fun x ↦ _root_.GD.N0232.N0720.N1057.d001899 (m x) (u x) (l x) (target x) t)
        measure :=
      ((((hl_meas.pow_const 2).const_mul t).mul
          ((hu_meas.sub htarget_meas).pow_const 2)).div
        (hm_meas.add (hl_meas.const_mul t))).aestronglyMeasurable
    have hrem : Integrable
        (fun x ↦ _root_.GD.N0232.N0720.N1057.d001899 (m x) (u x) (l x) (target x) t)
        measure := by
      apply henvelope.mono' hremMeas
      filter_upwards [hm, hl] with x hmx hlx
      change ‖_root_.GD.N0232.N0720.N1057.d001899
        (m x) (u x) (l x) (target x) t‖ ≤
          l x * (u x - target x) ^ 2
      rw [Real.norm_eq_abs,
        abs_of_nonneg (_root_.GD.N0232.N0720.N1057.d001900
          (m x) (u x) (l x) (target x) t hmx hlx ht).1]
      exact (_root_.GD.N0232.N0720.N1057.d001900
        (m x) (u x) (l x) (target x) t hmx hlx ht).2
    rw [← integral_add hgradient hrem]
    apply integral_congr_ae
    filter_upwards [hm, hl] with x hmx hlx
    simpa [_root_.GD.N0232.N0720.N1057.d001899] using _root_.GD.N0232.N0720.N1060.d001886
      (s x) (m x) (u x) (l x) (target x) t ht.ne'
        (ne_of_gt (add_pos_of_pos_of_nonneg hmx (mul_nonneg ht.le hlx)))
  simpa only [add_zero] using hsum.congr' heq.symm






theorem d001904
    {X : Type*} [MeasurableSpace X]
    (measure : Measure X) (s m u l target : X → ℝ)
    (hm_meas : Measurable m) (hu_meas : Measurable u)
    (hl_meas : Measurable l) (htarget_meas : Measurable target)
    (hm : ∀ᵐ x ∂measure, 0 < m x)
    (hl : ∀ᵐ x ∂measure, 0 ≤ l x)
    (hbase : Integrable
      (fun x ↦ _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x)) measure)
    (hgradient : Integrable
      (fun x ↦ _root_.GD.N0232.N0720.N1060.d001883 (s x) (u x) (l x) (target x)) measure)
    (henvelope : Integrable
      (fun x ↦ l x * (u x - target x) ^ 2) measure)
    (hgradient_neg :
      (∫ x, _root_.GD.N0232.N0720.N1060.d001883 (s x) (u x) (l x) (target x) ∂measure) < 0) :
    ∃ t : ℝ, 0 < t ∧
      (∫ x, _root_.GD.N0232.N0720.N1060.d001882
        (s x) (m x) (u x) (l x) (target x) t ∂measure) <
      ∫ x, _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x) ∂measure := by
  let secant : ℝ → X → ℝ := fun t x ↦
    (_root_.GD.N0232.N0720.N1060.d001882 (s x) (m x) (u x) (l x) (target x) t -
      _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x)) / t
  have hsecantLimit : Tendsto
      (fun t : ℝ ↦ ∫ x, secant t x ∂measure)
      (𝓝[>] 0)
      (nhds (∫ x, _root_.GD.N0232.N0720.N1060.d001883 (s x) (u x) (l x) (target x) ∂measure)) := by
    simpa only [secant] using _root_.GD.N0232.N0720.N1057.d001903
      measure s m u l target hm_meas hu_meas hl_meas htarget_meas
        hm hl hgradient henvelope
  have hsecantNeg : ∀ᶠ t in (𝓝[>] (0 : ℝ)),
      (∫ x, secant t x ∂measure) < 0 :=
    hsecantLimit.eventually (Iio_mem_nhds hgradient_neg)
  have hpositive : ∀ᶠ t in (𝓝[>] (0 : ℝ)), 0 < t :=
    self_mem_nhdsWithin
  obtain ⟨t, ht, htsecant⟩ :=
    (hpositive.and hsecantNeg).exists
  refine ⟨t, ht, ?_⟩
  have hremMeas : AEStronglyMeasurable
      (fun x ↦ _root_.GD.N0232.N0720.N1057.d001899 (m x) (u x) (l x) (target x) t)
      measure :=
    ((((hl_meas.pow_const 2).const_mul t).mul
        ((hu_meas.sub htarget_meas).pow_const 2)).div
      (hm_meas.add (hl_meas.const_mul t))).aestronglyMeasurable
  have hrem : Integrable
      (fun x ↦ _root_.GD.N0232.N0720.N1057.d001899 (m x) (u x) (l x) (target x) t)
      measure := by
    apply henvelope.mono' hremMeas
    filter_upwards [hm, hl] with x hmx hlx
    change ‖_root_.GD.N0232.N0720.N1057.d001899
      (m x) (u x) (l x) (target x) t‖ ≤
        l x * (u x - target x) ^ 2
    rw [Real.norm_eq_abs,
      abs_of_nonneg (_root_.GD.N0232.N0720.N1057.d001900
        (m x) (u x) (l x) (target x) t hmx hlx ht).1]
    exact (_root_.GD.N0232.N0720.N1057.d001900
      (m x) (u x) (l x) (target x) t hmx hlx ht).2
  have hsecant : Integrable (secant t) measure := by
    have hsum := hgradient.add hrem
    refine hsum.congr ?_
    filter_upwards [hm, hl] with x hmx hlx
    symm
    simpa only [secant, _root_.GD.N0232.N0720.N1057.d001899, Pi.add_apply] using
      _root_.GD.N0232.N0720.N1060.d001886
        (s x) (m x) (u x) (l x) (target x) t ht.ne'
          (ne_of_gt (add_pos_of_pos_of_nonneg hmx (mul_nonneg ht.le hlx)))
  calc
    (∫ x, _root_.GD.N0232.N0720.N1060.d001882
        (s x) (m x) (u x) (l x) (target x) t ∂measure) =
        ∫ x, _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x) +
          t * secant t x ∂measure := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [secant]
      field_simp [ht.ne']
      <;> ring
    _ = (∫ x, _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x) ∂measure) +
        ∫ x, t * secant t x ∂measure :=
      integral_add hbase (hsecant.const_mul t)
    _ = (∫ x, _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x) ∂measure) +
        t * (∫ x, secant t x ∂measure) := by
      rw [integral_const_mul]
    _ < ∫ x, _root_.GD.N0232.N0720.N1060.d001880 (s x) (m x) (u x) ∂measure := by
      nlinarith

end

end N1057
end N0720
end N0232
end GD
