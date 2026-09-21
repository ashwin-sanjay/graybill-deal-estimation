import GD.Module0010
import GD.Module0029
import GD.Module0733
















open Filter MeasureTheory Set

namespace GD
namespace N0232
namespace N0719
namespace N0840

noncomputable section

open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0107
open _root_.GD.N0232.N0719.N0841
open _root_.GD.N0230.N0655

variable (k : ℕ) (sizes : Fin k → ℕ)



theorem d011026
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Continuous d)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    Continuous (fun g : _root_.GD.N0230.N0655.d000349 ↦
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 g.2 d omega) := by
  have hscale : Continuous (fun g : _root_.GD.N0230.N0655.d000349 ↦ (g.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hscale_ne : ∀ g : _root_.GD.N0230.N0655.d000349, (g.2 : ℝ) ≠ 0 :=
    fun g ↦ ne_of_gt g.2.property
  have hinv : Continuous (fun g : _root_.GD.N0230.N0655.d000349 ↦ ((g.2 : ℝ)⁻¹)) :=
    hscale.inv₀ hscale_ne
  have hinverseShift : Continuous (fun g : _root_.GD.N0230.N0655.d000349 ↦
      _root_.GD.N0232.N0719.N0842.d010906 g.1 (g.2 : ℝ)) := by
    unfold _root_.GD.N0232.N0719.N0842.d010906
    exact (hinv.mul continuous_fst).neg
  have hparameters : Continuous (fun g : _root_.GD.N0230.N0655.d000349 ↦
      (_root_.GD.N0232.N0719.N0842.d010906 g.1 (g.2 : ℝ), ((g.2 : ℝ)⁻¹))) :=
    hinverseShift.prodMk hinv
  have hobservation : Continuous (fun g : _root_.GD.N0230.N0655.d000349 ↦
      _root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 (g.2 : ℝ) omega) := by
    exact (_root_.GD.N0232.N0719.N0841.d011022 k sizes omega).comp hparameters
  unfold _root_.GD.N0232.N0719.N0842.d010911
  exact continuous_fst.add (hscale.mul (hd.comp hobservation))



theorem d011027
    (parameter : ℕ → _root_.GD.N0230.N0655.d000349)
    (limitParameter : _root_.GD.N0230.N0655.d000349)
    (hparameter : Tendsto parameter atTop (nhds limitParameter))
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Continuous d) :
    TendstoInMeasure (_root_.GD.N0232.N0719.d009182 k sizes)
      (fun n ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes
        (parameter n).1 (parameter n).2 d)
      atTop
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes
        limitParameter.1 limitParameter.2 d) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have hcontinuous : Continuous (_root_.GD.N0232.N0719.N0842.d010911 k sizes
        (parameter n).1 (parameter n).2 d) := by
      unfold _root_.GD.N0232.N0719.N0842.d010911
      exact continuous_const.add (continuous_const.mul
        (hd.comp (_root_.GD.N0232.N0719.N0841.d011021 k sizes _ _)))
    exact hcontinuous.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega ↦
      (_root_.GD.N0232.N0719.N0840.d011026 k sizes d hd omega).continuousAt.tendsto.comp
        hparameter











theorem d011028
    (parameter : ℕ → _root_.GD.N0230.N0655.d000349)
    (limitParameter : _root_.GD.N0230.N0655.d000349)
    (hparameter : Tendsto parameter atTop (nhds limitParameter))
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (huniformApproximation : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ, Continuous h ∧
        (∀ᶠ n in atTop,
          (_root_.GD.N0232.N0719.d009182 k sizes).real
            {omega |
              ε ≤ dist
                (_root_.GD.N0232.N0719.N0842.d010911 k sizes
                  (parameter n).1 (parameter n).2 d omega)
                (_root_.GD.N0232.N0719.N0842.d010911 k sizes
                  (parameter n).1 (parameter n).2 h omega)} < δ) ∧
        (_root_.GD.N0232.N0719.d009182 k sizes).real
          {omega |
            ε ≤ dist
              (_root_.GD.N0232.N0719.N0842.d010911 k sizes
                limitParameter.1 limitParameter.2 h omega)
              (_root_.GD.N0232.N0719.N0842.d010911 k sizes
                limitParameter.1 limitParameter.2 d omega)} < δ) :
    TendstoInMeasure (_root_.GD.N0232.N0719.d009182 k sizes)
      (fun n ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes
        (parameter n).1 (parameter n).2 d)
      atTop
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes
        limitParameter.1 limitParameter.2 d) := by
  apply
    _root_.GD.N0230.N0562.d000067
  intro ε hε δ hδ
  obtain ⟨h, hh, hmoving, hlimit⟩ :=
    huniformApproximation ε hε δ hδ
  exact ⟨
    (fun n ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes
      (parameter n).1 (parameter n).2 h),
    _root_.GD.N0232.N0719.N0842.d010911 k sizes
      limitParameter.1 limitParameter.2 h,
    _root_.GD.N0232.N0719.N0840.d011027
      k sizes parameter limitParameter hparameter h hh,
    hmoving,
    hlimit⟩














theorem d011029
    (parameter : ℕ → _root_.GD.N0230.N0655.d000349)
    (limitParameter : _root_.GD.N0230.N0655.d000349)
    (hparameter : Tendsto parameter atTop (nhds limitParameter))
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hdMeasurable : Measurable d)
    {p : ENNReal} (hpTop : p ≠ ⊤) (hpZero : p ≠ 0)
    (hdLp : MemLp d p
      ((_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes
          limitParameter.1 limitParameter.2)))
    (hregular :
      ((_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes
          limitParameter.1 limitParameter.2)).WeaklyRegular)
    (hsetwiseUpper : ∀ s : Set (_root_.GD.N0232.N0719.d009173 k sizes), MeasurableSet s →
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ n in atTop,
          (_root_.GD.N0232.N0719.d009182 k sizes).real
              (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 ⁻¹' s) <
            (_root_.GD.N0232.N0719.d009182 k sizes).real
              (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 ⁻¹' s) + δ) :
    TendstoInMeasure (_root_.GD.N0232.N0719.d009182 k sizes)
      (fun n ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes
        (parameter n).1 (parameter n).2 d)
      atTop
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes
        limitParameter.1 limitParameter.2 d) := by
  let nu : Measure (_root_.GD.N0232.N0719.d009173 k sizes) :=
    (_root_.GD.N0232.N0719.d009182 k sizes).map
      (_root_.GD.N0232.N0719.N0842.d010907 k sizes
        limitParameter.1 limitParameter.2)
  letI : nu.WeaklyRegular := hregular
  have hscaleTendsto : Tendsto
      (fun n ↦ ((parameter n).2 : ℝ)) atTop
      (nhds ((limitParameter.2 : Set.Ioi (0 : ℝ)) : ℝ)) := by
    exact ((continuous_subtype_val.comp continuous_snd).tendsto
      limitParameter).comp hparameter
  let B : ℝ := 2 * (limitParameter.2 : ℝ)
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (by norm_num) limitParameter.2.property
  have hlimitScaleB : (limitParameter.2 : ℝ) < B := by
    dsimp [B]
    linarith [limitParameter.2.property]
  have hscaleBound : ∀ᶠ n in atTop, ((parameter n).2 : ℝ) < B :=
    hscaleTendsto.eventually (Iio_mem_nhds hlimitScaleB)
  apply _root_.GD.N0232.N0719.N0840.d011028
    k sizes parameter limitParameter hparameter d
  intro ε hε δ hδ
  have hεB : 0 < ε / B := div_pos hε hB
  have hδtwo : 0 < δ / 2 := by positivity
  obtain ⟨h, hh, hsmall⟩ :=
    _root_.GD.N0230.N0588.d000066
        nu hpTop hpZero d hdLp (ε / B) (δ / 2) hεB hδtwo
  let s : Set (_root_.GD.N0232.N0719.d009173 k sizes) :=
    {y | ε / B ≤ dist (d y) (h y)}
  have hs : MeasurableSet s := by
    exact measurableSet_le measurable_const (hdMeasurable.dist hh.measurable)
  have hmapReal :
      nu.real s =
        (_root_.GD.N0232.N0719.d009182 k sizes).real
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes
            limitParameter.1 limitParameter.2 ⁻¹' s) := by
    dsimp [nu]
    change
      ((Measure.map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes
          limitParameter.1 limitParameter.2)
        (_root_.GD.N0232.N0719.d009182 k sizes)) s).toReal =
      ((_root_.GD.N0232.N0719.d009182 k sizes)
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes
          limitParameter.1 limitParameter.2 ⁻¹' s)).toReal
    rw [Measure.map_apply
      (_root_.GD.N0232.N0719.N0842.d010908 k sizes _ _) hs]
  have hsmallLimit :
      (_root_.GD.N0232.N0719.d009182 k sizes).real
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes
            limitParameter.1 limitParameter.2 ⁻¹' s) < δ / 2 := by
    rw [← hmapReal]
    exact hsmall
  have hupper := hsetwiseUpper s hs (δ / 2) hδtwo
  refine ⟨h, hh, ?_, ?_⟩
  · filter_upwards [hscaleBound, hupper] with n hnScale hnUpper
    have hsubset :
        {omega |
          ε ≤ dist
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes
              (parameter n).1 (parameter n).2 d omega)
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes
              (parameter n).1 (parameter n).2 h omega)} ⊆
          _root_.GD.N0232.N0719.N0842.d010907 k sizes
              (parameter n).1 (parameter n).2 ⁻¹' s := by
      intro omega homega
      have hdistance :
          dist
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes
              (parameter n).1 (parameter n).2 d omega)
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes
              (parameter n).1 (parameter n).2 h omega) =
            ((parameter n).2 : ℝ) *
              dist
                (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                  (parameter n).1 (parameter n).2 omega))
                (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                  (parameter n).1 (parameter n).2 omega)) := by
        rw [Real.dist_eq]
        unfold _root_.GD.N0232.N0719.N0842.d010911
        rw [show
          (parameter n).1 + (parameter n).2 *
                d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                  (parameter n).1 (parameter n).2 omega) -
              ((parameter n).1 + (parameter n).2 *
                h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                  (parameter n).1 (parameter n).2 omega)) =
            (parameter n).2 *
              (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 omega) -
               h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 omega)) by ring]
        rw [abs_mul, abs_of_pos (parameter n).2.property, Real.dist_eq]
      change ε ≤ dist
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes
          (parameter n).1 (parameter n).2 d omega)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes
          (parameter n).1 (parameter n).2 h omega) at homega
      rw [hdistance] at homega
      change ε / B ≤
        dist
          (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
            (parameter n).1 (parameter n).2 omega))
          (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
            (parameter n).1 (parameter n).2 omega))
      apply (div_le_iff₀ hB).2
      calc
        ε ≤ ((parameter n).2 : ℝ) *
            dist
              (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 omega))
              (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 omega)) := homega
        _ ≤ B *
            dist
              (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 omega))
              (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 omega)) :=
          mul_le_mul_of_nonneg_right (le_of_lt hnScale) dist_nonneg
        _ = dist
              (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 omega))
              (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                (parameter n).1 (parameter n).2 omega)) * B := mul_comm _ _
    have hmeasure :=
      measureReal_mono (μ := _root_.GD.N0232.N0719.d009182 k sizes) hsubset
    have hmoving :
        (_root_.GD.N0232.N0719.d009182 k sizes).real
          {omega |
            ε ≤ dist
              (_root_.GD.N0232.N0719.N0842.d010911 k sizes
                (parameter n).1 (parameter n).2 d omega)
              (_root_.GD.N0232.N0719.N0842.d010911 k sizes
                (parameter n).1 (parameter n).2 h omega)} < δ := by
      calc
        _ ≤ (_root_.GD.N0232.N0719.d009182 k sizes).real
            (_root_.GD.N0232.N0719.N0842.d010907 k sizes
              (parameter n).1 (parameter n).2 ⁻¹' s) := hmeasure
        _ < (_root_.GD.N0232.N0719.d009182 k sizes).real
              (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 ⁻¹' s) + δ / 2 := hnUpper
        _ < δ := by linarith
    exact hmoving
  · have hsubset :
        {omega |
          ε ≤ dist
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes
              limitParameter.1 limitParameter.2 h omega)
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes
              limitParameter.1 limitParameter.2 d omega)} ⊆
          _root_.GD.N0232.N0719.N0842.d010907 k sizes
              limitParameter.1 limitParameter.2 ⁻¹' s := by
      intro omega homega
      have hdistance :
          dist
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes
              limitParameter.1 limitParameter.2 h omega)
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes
              limitParameter.1 limitParameter.2 d omega) =
            (limitParameter.2 : ℝ) *
              dist
                (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                  limitParameter.1 limitParameter.2 omega))
                (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                  limitParameter.1 limitParameter.2 omega)) := by
        rw [dist_comm, Real.dist_eq]
        unfold _root_.GD.N0232.N0719.N0842.d010911
        rw [show
          limitParameter.1 + limitParameter.2 *
                d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                  limitParameter.1 limitParameter.2 omega) -
              (limitParameter.1 + limitParameter.2 *
                h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                  limitParameter.1 limitParameter.2 omega)) =
            limitParameter.2 *
              (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 omega) -
               h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 omega)) by ring]
        rw [abs_mul, abs_of_pos limitParameter.2.property, Real.dist_eq]
      change ε ≤ dist
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes
          limitParameter.1 limitParameter.2 h omega)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes
          limitParameter.1 limitParameter.2 d omega) at homega
      rw [hdistance] at homega
      change ε / B ≤
        dist
          (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
            limitParameter.1 limitParameter.2 omega))
          (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
            limitParameter.1 limitParameter.2 omega))
      apply (div_le_iff₀ hB).2
      calc
        ε ≤ (limitParameter.2 : ℝ) *
            dist
              (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 omega))
              (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 omega)) := homega
        _ ≤ B *
            dist
              (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 omega))
              (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 omega)) :=
          mul_le_mul_of_nonneg_right (le_of_lt hlimitScaleB) dist_nonneg
        _ = dist
              (d (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 omega))
              (h (_root_.GD.N0232.N0719.N0842.d010907 k sizes
                limitParameter.1 limitParameter.2 omega)) * B := mul_comm _ _
    exact (measureReal_mono (μ := _root_.GD.N0232.N0719.d009182 k sizes) hsubset).trans_lt
      (hsmallLimit.trans (half_lt_self hδ))

end

end N0840
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0840.d011026
#print axioms _root_.GD.N0232.N0719.N0840.d011027
#print axioms _root_.GD.N0232.N0719.N0840.d011028
#print axioms _root_.GD.N0232.N0719.N0840.d011029
