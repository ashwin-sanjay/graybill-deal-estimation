import GD.Module1718

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0093
noncomputable section
open _root_.GD.N0213.N0527
open _root_.GD.N0213.N0488 (d028223)
open _root_.GD.N0033
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0938 _root_.GD.N0232.N0719.N0877 _root_.GD.N0232.N0719.N0939

theorem d028716 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ)
    (hint : ∀ n, Integrable (f n) μ) (hnn : ∀ n, 0 ≤ᵐ[μ] f n)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop atTop) :
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop atTop := by
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  have hfat' : (∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂μ) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ) atTop :=
    lintegral_liminf_le' (fun n => (hint n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have htop : (∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂μ) = ⊤ := by
    calc
      _ = ∫⁻ _ω, (⊤ : ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact (ENNReal.tendsto_ofReal_nhds_top.mpr hω).liminf_eq
      _ = ⊤ := by simp
  rw [htop] at hfat'
  have ht := tendsto_of_le_liminf_of_limsup_le hfat' (show limsup
    (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ) atTop ≤ ⊤ from le_top)
  simpa only [← ofReal_integral_eq_lintegral_ofReal (hint _) (hnn _)] using ht

theorem d028717 {s e a C : ℝ}
    (hs : 0 < s) (he : 0 < e) (ha : 0 < a) (hC : 0 ≤ C) :
    Integrable (_root_.GD.N0213.N0527.d028204 e a C) (gammaMeasure s s) := by
  letI := isProbabilityMeasure_gammaMeasure hs hs
  apply (integrable_const (1 / e)).mono'
  · exact (show Measurable (_root_.GD.N0213.N0527.d028204 e a C) by unfold _root_.GD.N0213.N0527.d028204; fun_prop).aestronglyMeasurable
  · filter_upwards [_root_.GD.N0232.N0719.N0910.d010286 hs hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0093.d028710 he.le a C x)]
    exact _root_.GD.N0213.N0488.d028223 _ _ _ _ he ha hC hx.le

theorem d028718
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (a C : Ω → ℝ) (ha : Measurable a) (hC : Measurable C)
    (hpositive : ∀ᵐ ω ∂μ, 0 < a ω ∧ 0 ≤ C ω)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ∫ x, _root_.GD.N0213.N0527.d028204 (e n) (a ω) (C ω) x
      ∂gammaMeasure s s ∂μ) atTop atTop := by
  letI := isProbabilityMeasure_gammaMeasure hs hs
  have hnn (n : ℕ) (ω : Ω) : 0 ≤ ∫ x, _root_.GD.N0213.N0527.d028204 (e n) (a ω) (C ω) x ∂gammaMeasure s s :=
    integral_nonneg (_root_.GD.N0093.d028710 (he n).le _ _)
  apply _root_.GD.N0093.d028716
  · intro n
    apply (integrable_const (1 / e n)).mono'
    · have hm : StronglyMeasurable (fun p : Ω × ℝ => _root_.GD.N0213.N0527.d028204 (e n) (a p.1) (C p.1) p.2) := by
        unfold _root_.GD.N0213.N0527.d028204
        fun_prop
      exact hm.integral_prod_right'.aestronglyMeasurable
    · filter_upwards [hpositive] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn n ω)]
      calc
        _ ≤ ∫ _x, (1 / e n : ℝ) ∂gammaMeasure s s := by
          apply integral_mono_ae (_root_.GD.N0093.d028717 hs (he n) hω.1 hω.2) (integrable_const _)
          filter_upwards [_root_.GD.N0232.N0719.N0910.d010286 hs hs] with x hx
          exact _root_.GD.N0213.N0488.d028223 _ _ _ _ (he n) hω.1 hω.2 hx.le
        _ = _ := by simp
  · exact fun n => ae_of_all _ (hnn n)
  · filter_upwards [hpositive] with ω hω
    exact _root_.GD.N0093.d028715 hs hs1 _ _ hω.1 hω.2 e he he0

theorem d028719 {k : ℕ}
    (shape : Fin (k + 1) → ℝ) (hs : ∀ i, 0 < shape i)
    (i : Fin (k + 1)) (j : Fin k) (hi : shape i < 1)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ l, _root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a l)
      (_root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a i) ∂_root_.GD.N0033.d028239 shape) atTop atTop := by
  let μ : Fin (k + 1) → Measure ℝ := fun l => gammaMeasure (shape l) (shape l)
  let ν := _root_.GD.N0033.d028239 (fun l => shape (i.succAbove l))
  letI (l : Fin (k + 1)) : IsProbabilityMeasure (μ l) :=
    isProbabilityMeasure_gammaMeasure (hs l) (hs l)
  have hpos : ∀ᵐ b ∂ν, ∀ l, 0 < b l := _root_.GD.N0033.d028240 _ (fun l => hs (i.succAbove l))
  have hC : ∀ᵐ b ∂ν, 0 < b j ∧ 0 ≤ _root_.GD.N0033.d028248 j b := by
    filter_upwards [hpos] with b hb
    exact ⟨hb j, Finset.sum_nonneg fun l _ => _root_.GD.N0033.d028242 j b hb l⟩
  have havg := _root_.GD.N0093.d028718 ν (hs i) hi
    (fun b => b j) (_root_.GD.N0033.d028248 j) (by fun_prop) (_root_.GD.N0033.d028249 j) hC e he he0
  convert havg using 1
  funext n
  let g : ℝ × (Fin k → ℝ) → ℝ := fun p => _root_.GD.N0213.N0527.d028204 (e n) (p.2 j) (_root_.GD.N0033.d028248 j p.2) p.1
  have hsplit := (measurePreserving_piFinSuccAbove μ i).integral_comp' g
  have hg : Integrable g ((μ i).prod ν) := by
    apply (integrable_const (1 / e n)).mono'
    · exact (show Measurable g by unfold g _root_.GD.N0213.N0527.d028204; fun_prop).aestronglyMeasurable
    · filter_upwards [
        (Measure.quasiMeasurePreserving_fst (μ := μ i) (ν := ν)).ae
          (_root_.GD.N0232.N0719.N0910.d010286 (hs i) (hs i)),
        (Measure.quasiMeasurePreserving_snd (μ := μ i) (ν := ν)).ae hC] with p hp hb
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0093.d028710 (he n).le _ _ _)]
      exact _root_.GD.N0213.N0488.d028223 _ _ _ _ (he n) hb.1 hb.2 hp.le
  calc
    _ = ∫ a, g (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i a) ∂_root_.GD.N0033.d028239 shape := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0033.d028240 shape hs] with a ha
      exact _root_.GD.N0033.d028251 i j a (ha i).ne' (e n)
    _ = ∫ p, g p ∂((μ i).prod ν) := hsplit
    _ = _ := by rw [integral_prod_symm g hg]

#print axioms _root_.GD.N0093.d028716
#print axioms _root_.GD.N0093.d028718
#print axioms _root_.GD.N0093.d028719
end
end GD.N0093
