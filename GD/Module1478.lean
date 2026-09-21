import GD.Module1474
import GD.Module0437

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0415
noncomputable section

open _root_.GD.N0101.N0351 _root_.GD.N0101.N0357
open _root_.GD.N0230.N0665
open _root_.GD.N0232.N0719.N0954

variable {k : ℕ}

@[fun_prop] theorem d023227 :
    Measurable (_root_.GD.N0230.N0665.d000407 : (Fin k → ℝ) → Fin k → ℝ) := by
  unfold _root_.GD.N0230.N0665.d000407 _root_.GD.N0230.N0665.d000406
  fun_prop

theorem d023228 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) :
    ∀ᵐ t ∂_root_.GD.N0101.N0357.d023160 a β, t ∈ _root_.GD.N0101.N0357.d023158 :=
  _root_.GD.N0101.N0357.d023165 a _ ha (fun i => mul_pos (ha i) (hβ i))

theorem d023229 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) : IsProbabilityMeasure (_root_.GD.N0101.N0357.d023160 a β) := by
  letI (i : Fin k) := isProbabilityMeasure_gammaMeasure (ha i) (mul_pos (ha i) (hβ i))
  unfold _root_.GD.N0101.N0357.d023160 _root_.GD.N0232.N0719.N0954.d009342
  infer_instance


theorem d023230 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) {c : ℝ} (hc : 0 < c) :
    (_root_.GD.N0101.N0357.d023160 a β).map (fun t => c⁻¹ • t) = _root_.GD.N0101.N0357.d023160 a (c • β) := by
  have hsingle (i : Fin k) :
      (gammaMeasure (a i) (a i * β i)).map (fun x : ℝ => c⁻¹ * x) =
        gammaMeasure (a i) (a i * (c • β) i) := by
    simpa only [Pi.smul_apply, smul_eq_mul, div_inv_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using _root_.GD.N0232.N0719.N0954.d009354 (ha i) (mul_pos (ha i) (hβ i))
        (inv_pos.mpr hc)
  letI (i : Fin k) : IsProbabilityMeasure
      ((gammaMeasure (a i) (a i * β i)).map (fun x : ℝ => c⁻¹ * x)) := by
    rw [hsingle i]
    exact isProbabilityMeasure_gammaMeasure (ha i) (mul_pos (ha i) (mul_pos hc (hβ i)))
  unfold _root_.GD.N0101.N0357.d023160 _root_.GD.N0232.N0719.N0954.d009342
  change (Measure.pi (fun i => gammaMeasure (a i) (a i * β i))).map
      (fun t i => c⁻¹ * t i) = _
  rw [Measure.pi_map_pi (μ := fun i => gammaMeasure (a i) (a i * β i))
    (f := fun (_ : Fin k) (x : ℝ) => c⁻¹ * x)
    (fun _ => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  funext i
  exact hsingle i

theorem d023231 (β v : Fin k → ℝ) (c : ℝ) :
    _root_.GD.N0101.N0351.d023186 (c • β) v = c⁻¹ * _root_.GD.N0101.N0351.d023186 β v := by
  simp only [_root_.GD.N0101.N0351.d023186, Pi.smul_apply, smul_eq_mul, mul_inv_rev, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d023232 [NeZero k] {β t : Fin k → ℝ}
    (hβ : β ∈ _root_.GD.N0101.N0357.d023158) (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0101.N0351.d023186 β (_root_.GD.N0230.N0665.d000407 t) ≤ ∑ i, (β i)⁻¹ := by
  apply Finset.sum_le_sum
  intro i _
  have hp0 := (_root_.GD.N0101.N0406.d006756 ht i).le
  have hp1 := _root_.GD.N0101.N0406.d006757 ht i
  apply mul_le_of_le_one_right (inv_nonneg.mpr (hβ i).le)
  nlinarith

theorem d023233 [NeZero k] (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β ≤ ENNReal.ofReal (∑ i, (β i)⁻¹) := by
  letI := _root_.GD.N0101.N0415.d023229 a ha hβ
  calc
    _ ≤ ∫⁻ _t, ENNReal.ofReal (∑ i, (β i)⁻¹) ∂_root_.GD.N0101.N0357.d023160 a β := by
      apply lintegral_mono_ae
      filter_upwards [_root_.GD.N0101.N0415.d023228 a ha hβ] with t ht
      exact ENNReal.ofReal_le_ofReal (_root_.GD.N0101.N0415.d023232 hβ ht)
    _ = _ := by simp

theorem d023234 [NeZero k] (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) : _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0101.N0415.d023233 a ha hβ)


theorem d023235 [NeZero k] (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 (c • β) =
      ENNReal.ofReal c⁻¹ * _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β := by
  unfold _root_.GD.N0101.N0351.d023188
  rw [← _root_.GD.N0101.N0415.d023230 a ha hβ hc,
    lintegral_map (show Measurable (fun t => ENNReal.ofReal
      (_root_.GD.N0101.N0351.d023186 (c • β) (_root_.GD.N0230.N0665.d000407 t))) by unfold _root_.GD.N0101.N0351.d023186; fun_prop) (by fun_prop)]
  calc
    _ = ∫⁻ t, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (_root_.GD.N0230.N0665.d000407 t)) ∂_root_.GD.N0101.N0357.d023160 a β := by
      apply lintegral_congr_ae
      filter_upwards [_root_.GD.N0101.N0415.d023228 a ha hβ] with t ht
      rw [show _root_.GD.N0230.N0665.d000407 (c⁻¹ • t) = _root_.GD.N0230.N0665.d000407 t from
        _root_.GD.N0230.N0665.d000417 ht (inv_pos.mpr hc), _root_.GD.N0101.N0415.d023231,
        ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem d023236 [NeZero k] (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) {c : ℝ} (hc : 0 < c) :
    (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 (c • β)).toReal =
      c⁻¹ * (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β).toReal := by
  rw [_root_.GD.N0101.N0415.d023235 a ha hβ hc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le)]

theorem d023237 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (μ : Measure (Fin k → ℝ)) (hμ : ∀ᵐ β ∂μ, β ∈ _root_.GD.N0101.N0357.d023158) :
    AEMeasurable (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407) μ := by
  apply _root_.GD.N0101.N0351.d023197 a a ha ha μ hμ
  unfold Function.uncurry _root_.GD.N0101.N0351.d023186
  fun_prop

theorem d023238
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (μ : Measure (Fin k → ℝ)) (hμ : ∀ᵐ β ∂μ, β ∈ _root_.GD.N0101.N0357.d023158) :
    AEStronglyMeasurable (fun β => (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β).toReal) μ :=
  (_root_.GD.N0101.N0415.d023237 a ha μ hμ).ennreal_toReal.aestronglyMeasurable


def d023239 (a β : Fin k → ℝ) : ℝ := by
  classical
  exact if β ∈ _root_.GD.N0101.N0357.d023158 then (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β).toReal else 0

theorem d023240 (a β : Fin k → ℝ) : 0 ≤ _root_.GD.N0101.N0415.d023239 a β := by
  unfold _root_.GD.N0101.N0415.d023239
  split_ifs <;> positivity

theorem d023241 (a : Fin k → ℝ) {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0101.N0415.d023239 a β = (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β).toReal := by
  simp only [_root_.GD.N0101.N0415.d023239, if_pos hβ]

theorem d023242 (a : Fin k → ℝ)
    (μ : Measure (Fin k → ℝ)) (hμ : ∀ᵐ β ∂μ, β ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0101.N0415.d023239 a =ᵐ[μ] fun β => (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β).toReal :=
  hμ.mono (fun _ hβ => _root_.GD.N0101.N0415.d023241 a hβ)

theorem d023243 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    Measurable (_root_.GD.N0101.N0415.d023239 a) := by
  classical
  let F : (Fin k → ℝ) → ℝ≥0∞ := fun β => ∫⁻ t in _root_.GD.N0101.N0357.d023158,
    ENNReal.ofReal (_root_.GD.N0232.N0719.N0954.d009343 a (fun i => a i * β i) t) *
      ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (_root_.GD.N0230.N0665.d000407 t))
  have hF : Measurable F :=
    ((_root_.GD.N0101.N0351.d023196 a a).ennreal_ofReal.mul
      (show Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
        ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 z.1 (_root_.GD.N0230.N0665.d000407 z.2))) by unfold _root_.GD.N0101.N0351.d023186; fun_prop)).lintegral_prod_right
  have heq : _root_.GD.N0101.N0415.d023239 a = fun β => if β ∈ _root_.GD.N0101.N0357.d023158 then (F β).toReal else 0 := by
    funext β
    by_cases hβ : β ∈ _root_.GD.N0101.N0357.d023158
    · simp only [_root_.GD.N0101.N0415.d023239, if_pos hβ]
      congr 1
      exact _root_.GD.N0101.N0357.d023170 a _ ha
        (fun i => mul_pos (ha i) (hβ i)) _
    · simp only [_root_.GD.N0101.N0415.d023239, if_neg hβ]
  rw [heq]
  exact Measurable.ite _root_.GD.N0101.N0357.d023159 hF.ennreal_toReal measurable_const


theorem d023244 [NeZero k] (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {c : ℝ} (hc : 0 < c) (β : Fin k → ℝ) :
    _root_.GD.N0101.N0415.d023239 a (c • β) = c⁻¹ * _root_.GD.N0101.N0415.d023239 a β := by
  have hscale : c • β ∈ _root_.GD.N0101.N0357.d023158 ↔ β ∈ _root_.GD.N0101.N0357.d023158 := by
    simp only [_root_.GD.N0101.N0357.d023158, mem_setOf_eq, Pi.smul_apply, smul_eq_mul,
      mul_pos_iff_of_pos_left hc]
  by_cases hβ : β ∈ _root_.GD.N0101.N0357.d023158
  · rw [_root_.GD.N0101.N0415.d023241 a (hscale.mpr hβ), _root_.GD.N0101.N0415.d023241 a hβ]
    exact _root_.GD.N0101.N0415.d023236 a ha hβ hc
  · simp only [_root_.GD.N0101.N0415.d023239, if_neg hβ, if_neg (hscale.not.mpr hβ), mul_zero]

end
end GD.N0101.N0415

#print axioms _root_.GD.N0101.N0415.d023230
#print axioms _root_.GD.N0101.N0415.d023234
#print axioms _root_.GD.N0101.N0415.d023235
#print axioms _root_.GD.N0101.N0415.d023236
#print axioms _root_.GD.N0101.N0415.d023237
#print axioms _root_.GD.N0101.N0415.d023238
#print axioms _root_.GD.N0101.N0415.d023243
#print axioms _root_.GD.N0101.N0415.d023244
