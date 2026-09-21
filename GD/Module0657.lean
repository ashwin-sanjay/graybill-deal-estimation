import GD.Module0649




















open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0960

noncomputable section









theorem d009679
    {x m V : ℝ} (hx : 0 ≤ x) (hm : 0 ≤ m) (hV : 0 < V) :
    1 / (m + V) - (x - m) / (m + V) ^ 2 ≤
      1 / (x + V) := by
  have hxV : 0 < x + V := add_pos_of_nonneg_of_pos hx hV
  have hmV : 0 < m + V := add_pos_of_nonneg_of_pos hm hV
  rw [le_div_iff₀ hxV]
  field_simp [hxV.ne', hmV.ne']
  nlinarith [sq_nonneg (x - m)]








theorem d009680
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (Z : X → ℝ)
    (hZ : Integrable Z μ)
    (hZ_nonneg : ∀ᵐ x ∂μ, 0 ≤ Z x)
    {m V : ℝ} (hm : 0 ≤ m) (hV : 0 < V)
    (hmean : (∫ x, Z x ∂μ) ≤ m)
    (hreciprocal :
      Integrable (fun x => 1 / (Z x + V)) μ) :
    1 / (m + V) ≤
      ∫ x, 1 / (Z x + V) ∂μ := by
  let T : X → ℝ :=
    fun x =>
      1 / (m + V) - (Z x - m) / (m + V) ^ 2
  have hZsub : Integrable (fun x => Z x - m) μ :=
    hZ.sub (integrable_const m)
  have hZdiv :
      Integrable (fun x => (Z x - m) / (m + V) ^ 2) μ :=
    hZsub.div_const ((m + V) ^ 2)
  have hT : Integrable T μ := by
    dsimp [T]
    exact
      (integrable_const (1 / (m + V))).sub
        hZdiv
  have hpoint :
      ∀ᵐ x ∂μ, T x ≤ 1 / (Z x + V) := by
    filter_upwards [hZ_nonneg] with x hx
    exact _root_.GD.N0232.N0719.N0960.d009679 hx hm hV
  have hintegral :
      (∫ x, T x ∂μ) ≤
        ∫ x, 1 / (Z x + V) ∂μ :=
    integral_mono_ae hT hreciprocal hpoint
  have hTIntegral :
      (∫ x, T x ∂μ) =
        1 / (m + V) -
          ((∫ x, Z x ∂μ) - m) / (m + V) ^ 2 := by
    dsimp [T]
    have hconstIntegral :
        (∫ _ : X, 1 / (m + V) ∂μ) = 1 / (m + V) := by
      simp
    have hsubIntegral :
        (∫ x, Z x - m ∂μ) = (∫ x, Z x ∂μ) - m := by
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        integral_sub hZ (integrable_const m)
    have hdivIntegral :
        (∫ x, (Z x - m) / (m + V) ^ 2 ∂μ) =
          ((∫ x, Z x ∂μ) - m) / (m + V) ^ 2 := by
      rw [integral_div]
      exact congrArg (fun z : ℝ => z / (m + V) ^ 2) hsubIntegral
    calc
      (∫ x, 1 / (m + V) - (Z x - m) / (m + V) ^ 2 ∂μ) =
          (∫ _ : X, 1 / (m + V) ∂μ) -
            ∫ x, (Z x - m) / (m + V) ^ 2 ∂μ := by
        exact integral_sub (integrable_const _) hZdiv
      _ = 1 / (m + V) -
          ((∫ x, Z x ∂μ) - m) / (m + V) ^ 2 := by
        rw [hconstIntegral, hdivIntegral]
  have hquotient :
      ((∫ x, Z x ∂μ) - m) / (m + V) ^ 2 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hmean) (sq_nonneg (m + V))
  rw [hTIntegral] at hintegral
  have hbase :
      1 / (m + V) ≤
        1 / (m + V) -
          ((∫ x, Z x ∂μ) - m) / (m + V) ^ 2 := by
    linarith
  exact hbase.trans hintegral

end

end GD.N0232.N0719.N0960
