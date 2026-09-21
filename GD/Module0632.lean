import GD.Module0629
import Mathlib.MeasureTheory.Integral.Pi









open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0932

noncomputable section

section FiniteProduct

variable {ι : Type*} [Fintype ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]


def d009190
    (f : (i : ι) → X i → ℝ) (x : (i : ι) → X i) : ℝ :=
  ∏ i, f i (x i)

@[fun_prop]
theorem d009191
    (f : (i : ι) → X i → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (_root_.GD.N0232.N0719.N0932.d009190 f) := by
  unfold _root_.GD.N0232.N0719.N0932.d009190
  exact Finset.measurable_prod _ fun i _ ↦
    (hf i).comp (measurable_pi_apply i)




theorem d009192
    (μ ν : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (f : (i : ι) → X i → ℝ)
    (hfmeas : ∀ i, Measurable (f i))
    (hfnonneg : ∀ i x, 0 ≤ f i x)
    (hfintegrable : ∀ i, Integrable (f i) (μ i))
    (hν : ∀ i,
      ν i = (μ i).withDensity (fun x ↦ ENNReal.ofReal (f i x))) :
    Measure.pi ν =
      (Measure.pi μ).withDensity
        (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0719.N0932.d009190 f x)) := by
  apply Measure.pi_eq
  intro s hs
  have hrect : MeasurableSet (Set.pi Set.univ s) :=
    MeasurableSet.pi Set.countable_univ fun i _ ↦ hs i
  rw [withDensity_apply _ hrect]
  have hindicator_nonneg :
      ∀ i x, 0 ≤ (s i).indicator (f i) x := by
    intro i x
    by_cases hx : x ∈ s i
    · simp [hx, hfnonneg i x]
    · simp [hx]
  have hfactor :
      (Set.pi Set.univ s).indicator (_root_.GD.N0232.N0719.N0932.d009190 f) =
        fun x ↦ ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · have hxi : ∀ i, x i ∈ s i := by
        simpa [Set.mem_pi] using hx
      simp [hx, _root_.GD.N0232.N0719.N0932.d009190, hxi]
    · have hnot : ∃ i, x i ∉ s i := by
        simpa [Set.mem_pi] using hx
      obtain ⟨i, hi⟩ := hnot
      simp [hx, _root_.GD.N0232.N0719.N0932.d009190, hi,
        Finset.prod_eq_zero (Finset.mem_univ i)]
  rw [← lintegral_indicator hrect]
  rw [show
      (Set.pi Set.univ s).indicator
          (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0719.N0932.d009190 f x)) =
        fun x ↦ ENNReal.ofReal
          ((Set.pi Set.univ s).indicator
            (_root_.GD.N0232.N0719.N0932.d009190 f) x) by
      funext x
      by_cases hx : x ∈ Set.pi Set.univ s <;> simp [hx]]
  rw [hfactor]
  have hcoord_integrable :
      ∀ i, Integrable ((s i).indicator (f i)) (μ i) := by
    intro i
    exact (integrable_indicator_iff (hs i)).2
      (hfintegrable i).integrableOn
  have hproduct_integrable :
      Integrable
        (fun x : (i : ι) → X i ↦
          ∏ i, (s i).indicator (f i) (x i))
        (Measure.pi μ) :=
    Integrable.fintype_prod_dep hcoord_integrable
  rw [← ofReal_integral_eq_lintegral_ofReal
    hproduct_integrable
    (ae_of_all (Measure.pi μ) fun x ↦
      Finset.prod_nonneg fun i _ ↦ hindicator_nonneg i (x i))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ ↦ integral_nonneg (hindicator_nonneg i))]
  apply Finset.prod_congr rfl
  intro i _
  calc
    ENNReal.ofReal (∫ x, (s i).indicator (f i) x ∂μ i) =
        ∫⁻ x, ENNReal.ofReal ((s i).indicator (f i) x) ∂μ i :=
      ofReal_integral_eq_lintegral_ofReal
        (hcoord_integrable i)
        (ae_of_all (μ i) (hindicator_nonneg i))
    _ = ∫⁻ x, (s i).indicator
          (fun y ↦ ENNReal.ofReal (f i y)) x ∂μ i := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ s i <;> simp [hx]
    _ = (μ i).withDensity
          (fun x ↦ ENNReal.ofReal (f i x)) (s i) := by
      rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
    _ = ν i (s i) := by rw [hν i]

end FiniteProduct


def d009193 (scale : ℝ) : ℝ≥0 :=
  ⟨scale ^ 2, sq_nonneg scale⟩

@[simp]
theorem d009194 (scale : ℝ) :
    (_root_.GD.N0232.N0719.N0932.d009193 scale : ℝ) = scale ^ 2 := by
  rfl

@[simp]
theorem d009195 : _root_.GD.N0232.N0719.N0932.d009193 1 = 1 := by
  apply NNReal.eq
  change (1 : ℝ) ^ 2 = (1 : ℝ)
  norm_num

theorem d009196 {scale : ℝ} (hscale : scale ≠ 0) :
    _root_.GD.N0232.N0719.N0932.d009193 scale ≠ 0 := by
  intro hzero
  have hsquare := congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) hzero
  change scale ^ 2 = 0 at hsquare
  exact hscale (sq_eq_zero_iff.mp hsquare)


def d009197 (location scale x : ℝ) : ℝ≥0∞ :=
  gaussianPDF location (_root_.GD.N0232.N0719.N0932.d009193 scale) x / gaussianPDF 0 1 x

@[fun_prop]
theorem d009198 (location scale : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0932.d009197 location scale) := by
  unfold _root_.GD.N0232.N0719.N0932.d009197
  exact (measurable_gaussianPDF location (_root_.GD.N0232.N0719.N0932.d009193 scale)).div
    (measurable_gaussianPDF 0 1)

theorem d009199 (location scale x : ℝ) :
    _root_.GD.N0232.N0719.N0932.d009197 location scale x ≠ ∞ := by
  unfold _root_.GD.N0232.N0719.N0932.d009197
  exact ENNReal.div_ne_top gaussianPDF_ne_top
    (ne_of_gt (gaussianPDF_pos 0 one_ne_zero x))

theorem d009200
    (location scale x : ℝ) (hscale : scale ≠ 0) :
    0 < _root_.GD.N0232.N0719.N0932.d009197 location scale x := by
  unfold _root_.GD.N0232.N0719.N0932.d009197
  exact ENNReal.div_pos
    (ne_of_gt (gaussianPDF_pos location
      (_root_.GD.N0232.N0719.N0932.d009196 hscale) x))
    gaussianPDF_ne_top



theorem d009201
    (location scale : ℝ) (hscale : scale ≠ 0) :
    gaussianReal location (_root_.GD.N0232.N0719.N0932.d009193 scale) =
      (gaussianReal 0 1).withDensity
        (_root_.GD.N0232.N0719.N0932.d009197 location scale) := by
  rw [gaussianReal_of_var_ne_zero location
      (_root_.GD.N0232.N0719.N0932.d009196 hscale),
    gaussianReal_of_var_ne_zero 0 one_ne_zero,
    ← withDensity_mul volume
      (measurable_gaussianPDF 0 1)
      (_root_.GD.N0232.N0719.N0932.d009198 location scale)]
  congr 1
  funext x
  simp only [Pi.mul_apply, _root_.GD.N0232.N0719.N0932.d009197]
  exact (ENNReal.mul_div_cancel
    (ne_of_gt (gaussianPDF_pos 0 one_ne_zero x))
    gaussianPDF_ne_top).symm


theorem d009202 (location scale x : ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0932.d009197 location scale x :=
  bot_le



theorem d009203 (x : ℝ) :
    Continuous (fun θ : ℝ × Set.Ioi (0 : ℝ) ↦
      _root_.GD.N0232.N0719.N0932.d009197 θ.1 θ.2 x) := by
  unfold _root_.GD.N0232.N0719.N0932.d009197 gaussianPDF
  apply (ENNReal.continuous_div_const (gaussianPDF 0 1 x)
    (ne_of_gt (gaussianPDF_pos 0 one_ne_zero x))).comp
  apply ENNReal.continuous_ofReal.comp
  unfold gaussianPDFReal _root_.GD.N0232.N0719.N0932.d009193
  let denom : ℝ × Set.Ioi (0 : ℝ) → ℝ := fun θ ↦
    Real.sqrt (2 * Real.pi * (θ.2 : ℝ) ^ 2)
  have hdenom_cont : Continuous denom := by
    dsimp [denom]
    fun_prop
  have hdenom_ne : ∀ θ, denom θ ≠ 0 := by
    intro θ
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have hθ : 0 < (θ.2 : ℝ) := θ.2.property
    positivity
  have hfront : Continuous (fun θ ↦ (denom θ)⁻¹) :=
    hdenom_cont.inv₀ hdenom_ne
  let exponent : ℝ × Set.Ioi (0 : ℝ) → ℝ := fun θ ↦
    -(x - θ.1) ^ 2 / (2 * (θ.2 : ℝ) ^ 2)
  have hexponent : Continuous exponent := by
    dsimp [exponent]
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro θ
      have hθ : 0 < (θ.2 : ℝ) := θ.2.property
      positivity
  change Continuous (fun θ ↦
    (denom θ)⁻¹ * Real.exp (exponent θ))
  exact hfront.mul (Real.continuous_exp.comp hexponent)


def d009204 (location scale x : ℝ) : ℝ :=
  (_root_.GD.N0232.N0719.N0932.d009197 location scale x).toReal

theorem d009205 (location scale x : ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0932.d009204 location scale x :=
  ENNReal.toReal_nonneg

@[fun_prop]
theorem d009206 (location scale : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0932.d009204 location scale) := by
  unfold _root_.GD.N0232.N0719.N0932.d009204
  exact (_root_.GD.N0232.N0719.N0932.d009198 location scale).ennreal_toReal

@[simp]
theorem d009207 (location scale x : ℝ) :
    ENNReal.ofReal (_root_.GD.N0232.N0719.N0932.d009204 location scale x) =
      _root_.GD.N0232.N0719.N0932.d009197 location scale x := by
  unfold _root_.GD.N0232.N0719.N0932.d009204
  exact ENNReal.ofReal_toReal (_root_.GD.N0232.N0719.N0932.d009199 location scale x)



theorem d009208
    (location scale : ℝ) (hscale : scale ≠ 0) :
    Integrable (_root_.GD.N0232.N0719.N0932.d009204 location scale) (gaussianReal 0 1) := by
  apply integrable_toReal_of_lintegral_ne_top
    (_root_.GD.N0232.N0719.N0932.d009198 location scale).aemeasurable
  have hmeasure := congrArg (fun μ : Measure ℝ ↦ μ Set.univ)
    (_root_.GD.N0232.N0719.N0932.d009201 location scale hscale)
  rw [withDensity_apply _ MeasurableSet.univ] at hmeasure
  simp only [MeasureTheory.Measure.restrict_univ] at hmeasure
  have hlintegral :
      ∫⁻ x, _root_.GD.N0232.N0719.N0932.d009197 location scale x ∂gaussianReal 0 1 = 1 := by
    simpa using hmeasure.symm
  rw [hlintegral]
  exact ENNReal.one_ne_top

@[fun_prop]
theorem d009209 (x : ℝ) :
    Continuous (fun θ : ℝ × Set.Ioi (0 : ℝ) ↦
      _root_.GD.N0232.N0719.N0932.d009204 θ.1 θ.2 x) := by
  unfold _root_.GD.N0232.N0719.N0932.d009204
  change Continuous
    (ENNReal.toReal ∘ fun θ : ℝ × Set.Ioi (0 : ℝ) ↦
      _root_.GD.N0232.N0719.N0932.d009197 θ.1 θ.2 x)
  rw [continuous_iff_continuousAt]
  intro θ
  have hlike : Tendsto
      (fun η : ℝ × Set.Ioi (0 : ℝ) ↦
        _root_.GD.N0232.N0719.N0932.d009197 η.1 η.2 x)
      (nhds θ) (nhds (_root_.GD.N0232.N0719.N0932.d009197 θ.1 θ.2 x)) :=
    (_root_.GD.N0232.N0719.N0932.d009203 x).continuousAt
  exact (ENNReal.continuousAt_toReal
    (_root_.GD.N0232.N0719.N0932.d009199 θ.1 θ.2 x)).tendsto.comp hlike


theorem d009210
    (location scale : ℝ) :
    (gaussianReal 0 1).map (fun x : ℝ ↦ location + scale * x) =
      gaussianReal location (_root_.GD.N0232.N0719.N0932.d009193 scale) := by
  calc
    (gaussianReal 0 1).map (fun x : ℝ ↦ location + scale * x) =
        ((gaussianReal 0 1).map (fun x : ℝ ↦ scale * x)).map
          (fun x : ℝ ↦ location + x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
    _ = (gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 scale)).map
          (fun x : ℝ ↦ location + x) := by
      rw [gaussianReal_map_const_mul]
      simp only [mul_zero, mul_one]
      have hv :
          (.mk (scale ^ 2) (sq_nonneg scale) : ℝ≥0) =
            _root_.GD.N0232.N0719.N0932.d009193 scale := by
        apply NNReal.eq
        rfl
      rw [hv]
    _ = gaussianReal location (_root_.GD.N0232.N0719.N0932.d009193 scale) := by
      rw [gaussianReal_map_const_add]
      simp



theorem d009211
    (n : ℕ) (location scale : ℝ) :
    _root_.GD.N0232.N0719.d009174 n location scale =
      Measure.pi (fun _ : Fin n ↦
        gaussianReal location (_root_.GD.N0232.N0719.N0932.d009193 scale)) := by
  unfold _root_.GD.N0232.N0719.d009174 _root_.GD.N0137.d008895
    _root_.GD.N0140.d006650
    _root_.GD.N0107.d009018
  rw [Measure.pi_map_pi (fun _ ↦ (by fun_prop :
    AEMeasurable (fun x : ℝ ↦ location + scale * x)
      (gaussianReal 0 1)))]
  congr 1
  funext i
  exact _root_.GD.N0232.N0719.N0932.d009210 location scale



theorem d009212 (n : ℕ) :
    _root_.GD.N0232.N0719.d009174 n 0 1 = _root_.GD.N0137.d008895 n := by
  rw [_root_.GD.N0232.N0719.N0932.d009211]
  unfold _root_.GD.N0137.d008895
    _root_.GD.N0140.d006650
  congr 1
  funext i
  rw [_root_.GD.N0232.N0719.N0932.d009195]


def d009213
    (n : ℕ) (location scale : ℝ)
    (x : _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0232.N0719.N0932.d009190
    (fun _ : Fin n ↦ _root_.GD.N0232.N0719.N0932.d009204 location scale) x

@[fun_prop]
theorem d009214
    (n : ℕ) (location scale : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0932.d009213 n location scale) := by
  exact _root_.GD.N0232.N0719.N0932.d009191 _
    (fun _ ↦ _root_.GD.N0232.N0719.N0932.d009206 location scale)

theorem d009215
    (n : ℕ) (location scale : ℝ)
    (x : _root_.GD.N0137.d008894 n) :
    0 ≤ _root_.GD.N0232.N0719.N0932.d009213 n location scale x := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  exact Finset.prod_nonneg fun i _ ↦
    _root_.GD.N0232.N0719.N0932.d009205 location scale (x i)

theorem d009216
    (n : ℕ) (location scale : ℝ) (hscale : scale ≠ 0) :
    Integrable (_root_.GD.N0232.N0719.N0932.d009213 n location scale)
      (_root_.GD.N0137.d008895 n) := by
  unfold _root_.GD.N0232.N0719.N0932.d009213
    _root_.GD.N0137.d008895
    _root_.GD.N0140.d006650
  exact Integrable.fintype_prod
    (fun _ ↦ _root_.GD.N0232.N0719.N0932.d009208 location scale hscale)


theorem d009217
    (n : ℕ) (location scale : ℝ) (hscale : scale ≠ 0) :
    _root_.GD.N0232.N0719.d009174 n location scale =
      (_root_.GD.N0137.d008895 n).withDensity
        (fun x ↦ ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0932.d009213 n location scale x)) := by
  rw [_root_.GD.N0232.N0719.N0932.d009211]
  unfold _root_.GD.N0137.d008895
    _root_.GD.N0140.d006650
  apply _root_.GD.N0232.N0719.N0932.d009192
    (fun _ : Fin n ↦ gaussianReal 0 1)
    (fun _ : Fin n ↦ gaussianReal location (_root_.GD.N0232.N0719.N0932.d009193 scale))
    (fun _ : Fin n ↦ _root_.GD.N0232.N0719.N0932.d009204 location scale)
  · intro i
    exact _root_.GD.N0232.N0719.N0932.d009206 location scale
  · intro i x
    exact _root_.GD.N0232.N0719.N0932.d009205 location scale x
  · intro i
    exact _root_.GD.N0232.N0719.N0932.d009208 location scale hscale
  · intro i
    simpa only [_root_.GD.N0232.N0719.N0932.d009207] using
      _root_.GD.N0232.N0719.N0932.d009201 location scale hscale

@[fun_prop]
theorem d009218
    (n : ℕ) (x : _root_.GD.N0137.d008894 n) :
    Continuous (fun θ : ℝ × Set.Ioi (0 : ℝ) ↦
      _root_.GD.N0232.N0719.N0932.d009213 n θ.1 θ.2 x) := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  exact continuous_finsetProd Finset.univ fun i _ ↦
    _root_.GD.N0232.N0719.N0932.d009209 (x i)


def d009219
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ)
    (x : _root_.GD.N0232.N0719.d009172 k sampleSize) : ℝ :=
  _root_.GD.N0232.N0719.N0932.d009190
    (fun i ↦ _root_.GD.N0232.N0719.N0932.d009213
      (sampleSize i) location (scale i)) x

@[fun_prop]
theorem d009220
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ) :
    Measurable
      (_root_.GD.N0232.N0719.N0932.d009219 k sampleSize location scale) := by
  exact _root_.GD.N0232.N0719.N0932.d009191 _ fun i ↦
    _root_.GD.N0232.N0719.N0932.d009214
      (sampleSize i) location (scale i)

theorem d009221
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ)
    (x : _root_.GD.N0232.N0719.d009172 k sampleSize) :
    0 ≤ _root_.GD.N0232.N0719.N0932.d009219
      k sampleSize location scale x := by
  unfold _root_.GD.N0232.N0719.N0932.d009219 _root_.GD.N0232.N0719.N0932.d009190
  exact Finset.prod_nonneg fun i _ ↦
    _root_.GD.N0232.N0719.N0932.d009215
      (sampleSize i) location (scale i) (x i)



theorem d009222
    (k : ℕ) (sampleSize : Fin k → ℕ) :
    _root_.GD.N0232.N0719.d009182 k sampleSize =
      Measure.pi (fun i ↦
        _root_.GD.N0137.d008895 (sampleSize i)) := by
  unfold _root_.GD.N0232.N0719.d009182 _root_.GD.N0232.N0719.d009176
  congr 1
  funext i
  exact _root_.GD.N0232.N0719.N0932.d009212 (sampleSize i)



theorem d009223
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    _root_.GD.N0232.N0719.d009176 k sampleSize location scale =
      (_root_.GD.N0232.N0719.d009182 k sampleSize).withDensity
        (fun x ↦ ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0932.d009219
            k sampleSize location scale x)) := by
  rw [_root_.GD.N0232.N0719.N0932.d009222]
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N0932.d009219
  apply _root_.GD.N0232.N0719.N0932.d009192
    (fun i ↦ _root_.GD.N0137.d008895 (sampleSize i))
    (fun i ↦ _root_.GD.N0232.N0719.d009174 (sampleSize i) location (scale i))
    (fun i ↦ _root_.GD.N0232.N0719.N0932.d009213
      (sampleSize i) location (scale i))
  · intro i
    exact _root_.GD.N0232.N0719.N0932.d009214
      (sampleSize i) location (scale i)
  · intro i x
    exact _root_.GD.N0232.N0719.N0932.d009215
      (sampleSize i) location (scale i) x
  · intro i
    exact _root_.GD.N0232.N0719.N0932.d009216
      (sampleSize i) location (scale i) (hscale i).ne'
  · intro i
    exact _root_.GD.N0232.N0719.N0932.d009217
      (sampleSize i) location (scale i) (hscale i).ne'



abbrev d009224 (k : ℕ) :=
  ℝ × (∀ i : Fin k, Set.Ioi (0 : ℝ))




def d009225
    {k : ℕ} (i : Fin k) :
    _root_.GD.N0232.N0719.N0932.d009224 k → ℝ × Set.Ioi (0 : ℝ) :=
  fun θ ↦ (θ.1, θ.2 i)

@[fun_prop]
theorem d009226
    {k : ℕ} (i : Fin k) :
    Continuous (_root_.GD.N0232.N0719.N0932.d009225 i) := by
  exact continuous_fst.prodMk
    ((continuous_apply i).comp continuous_snd)

@[fun_prop]
theorem d009227
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (x : _root_.GD.N0232.N0719.d009172 k sampleSize) :
    Continuous (fun θ : _root_.GD.N0232.N0719.N0932.d009224 k ↦
      _root_.GD.N0232.N0719.N0932.d009219 k sampleSize θ.1
        (fun i ↦ θ.2 i) x) := by
  change Continuous (fun θ : _root_.GD.N0232.N0719.N0932.d009224 k ↦
    ∏ i, ∏ j, _root_.GD.N0232.N0719.N0932.d009204 θ.1 (θ.2 i) (x i j))
  apply continuous_finsetProd Finset.univ
  intro i hi
  apply continuous_finsetProd Finset.univ
  intro j hj
  change Continuous
    ((fun η : ℝ × Set.Ioi (0 : ℝ) ↦
        _root_.GD.N0232.N0719.N0932.d009204 η.1 η.2 (x i j)) ∘
      _root_.GD.N0232.N0719.N0932.d009225 i)
  exact (_root_.GD.N0232.N0719.N0932.d009209 (x i j)).comp
    (_root_.GD.N0232.N0719.N0932.d009226 i)



theorem d009228
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (x : _root_.GD.N0232.N0719.d009172 k sampleSize) :
    Continuous (fun θ : _root_.GD.N0232.N0719.N0932.d009224 k ↦
      ENNReal.ofReal
        (_root_.GD.N0232.N0719.N0932.d009219 k sampleSize θ.1
          (fun i ↦ θ.2 i) x)) :=
  ENNReal.continuous_ofReal.comp
    (_root_.GD.N0232.N0719.N0932.d009227 k sampleSize x)

end

end N0932
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0932.d009201
#print axioms _root_.GD.N0232.N0719.N0932.d009203
#print axioms _root_.GD.N0232.N0719.N0932.d009192
#print axioms _root_.GD.N0232.N0719.N0932.d009223
#print axioms _root_.GD.N0232.N0719.N0932.d009227
