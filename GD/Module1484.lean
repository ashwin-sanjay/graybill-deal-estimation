import GD.Module0499
import GD.Module0663
import GD.Module0724
import GD.Module0699
import GD.Module0632
import GD.Module0287

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace GD.N0072
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0885 _root_.GD.N0232.N0719.N0980
open _root_.GD.N0232.N0719.N0932 _root_.GD.N0232.N0719.N0910 _root_.GD.N0107

variable {k : ℕ}



def d023291 (sizes : Fin k → ℕ)
    (w : (Fin k → ℝ) → Fin k → ℝ) (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0885.d009311 (w (_root_.GD.N0232.N0719.N0900.d009103 k sizes z)) (_root_.GD.N0232.N0719.N0900.d009102 k sizes z)


def d023292 (sizes : Fin k → ℕ)
    (w : (Fin k → ℝ) → Fin k → ℝ) (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0885.d009311 (w (fun i => _root_.GD.N0107.d009085 (z i))) (_root_.GD.N0232.N0719.N0900.d009102 k sizes z)

theorem d023293 (sizes : Fin k → ℕ)
    (hn : ∀ i, 0 < sizes i) (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    (fun i => (sizes i : ℝ) * _root_.GD.N0232.N0719.N0900.d009103 k sizes z i) =
      fun i => _root_.GD.N0107.d009085 (z i) := by
  funext i
  unfold _root_.GD.N0232.N0719.N0900.d009103
  field_simp [Nat.cast_ne_zero.mpr (hn i).ne']

theorem d023294 (sizes : Fin k → ℕ)
    (hn : ∀ i, 0 < sizes i) (w : (Fin k → ℝ) → Fin k → ℝ) :
    _root_.GD.N0072.d023292 sizes w =
      _root_.GD.N0072.d023291 sizes (fun t => w (fun i => (sizes i : ℝ) * t i)) := by
  funext z
  simp only [_root_.GD.N0072.d023292, _root_.GD.N0072.d023291, _root_.GD.N0072.d023293 sizes hn]

@[fun_prop] theorem d023295 (sizes : Fin k → ℕ)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w) :
    Measurable (_root_.GD.N0072.d023291 sizes w) := by
  unfold _root_.GD.N0072.d023291 _root_.GD.N0232.N0719.N0885.d009311
  fun_prop


theorem d023296 (m : ℝ) (v : Fin k → ℝ≥0) (p : Fin k → ℝ)
    (hp : ∑ i, p i = 1) :
    (∫ y, (_root_.GD.N0232.N0719.N0885.d009311 p y - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = _root_.GD.N0072.d007621 (fun i => v i) p := by
  have hc : cov[_root_.GD.N0232.N0719.N0885.d009311 p, _root_.GD.N0232.N0719.N0885.d009311 p; _root_.GD.N0232.N0719.N0980.d009697 m v] =
      _root_.GD.N0072.d007621 (fun i => v i) p := by
    change cov[_root_.GD.N0232.N0719.N0885.d009311 p, fun y => ∑ i, p i * y i; _] = _
    rw [covariance_fun_sum_right]
    · simp_rw [covariance_const_mul_right, _root_.GD.N0232.N0719.N0885.d009319]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · exact fun i => (_root_.GD.N0232.N0719.N0885.d009315 m v i).memLp_two.const_mul (p i)
    · exact (_root_.GD.N0232.N0719.N0885.d009318 m v p).memLp_two
  rw [covariance_self (_root_.GD.N0232.N0719.N0885.d009318 m v p).aemeasurable,
    variance_eq_integral (_root_.GD.N0232.N0719.N0885.d009318 m v p).aemeasurable,
    _root_.GD.N0232.N0719.N0980.d009700, hp, one_mul] at hc
  exact hc



theorem d023297 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) =
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ)) (w t))
        ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale := by
  let F : ((Fin k → ℝ) × (Fin k → ℝ)) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal ((_root_.GD.N0232.N0719.N0885.d009311 (w z.2) z.1 - θ.location) ^ 2)
  have hF : Measurable F := by unfold F _root_.GD.N0232.N0719.N0885.d009311; fun_prop
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009300 k sizes θ.location θ.scale) := by
    unfold _root_.GD.N0232.N0719.N0933.d009300
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ.scale
  change (∫⁻ z, F (_root_.GD.N0232.N0719.N0933.d009304 k sizes z)
    ∂_root_.GD.N0232.N0719.d009176 k sizes θ.location θ.scale) = _
  rw [← lintegral_map hF (_root_.GD.N0232.N0719.N0933.d009308 k sizes),
    _root_.GD.N0232.N0719.N0933.d009309 k sizes hn,
    lintegral_prod_symm' F hF]
  apply lintegral_congr
  intro t
  rw [_root_.GD.N0232.N0719.N0933.d009302 k sizes hn]
  let v : Fin k → ℝ≥0 := _root_.GD.N0232.N0719.N0885.d009329 sizes θ.scale
  have h2 := (_root_.GD.N0232.N0719.N0885.d009318 θ.location v (w t)).memLp_two
  have hint : Integrable (fun y => (_root_.GD.N0232.N0719.N0885.d009311 (w t) y - θ.location) ^ 2)
      (_root_.GD.N0232.N0719.N0980.d009697 θ.location v) := by
    simpa only [Pi.sub_apply] using (h2.sub (memLp_const θ.location)).integrable_sq
  change (∫⁻ y, ENNReal.ofReal ((_root_.GD.N0232.N0719.N0885.d009311 (w t) y - θ.location) ^ 2)
    ∂_root_.GD.N0232.N0719.N0980.d009697 θ.location v) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => sq_nonneg _),
    _root_.GD.N0072.d023296 θ.location v (w t) (hunit t)]
  rfl


theorem d023298 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ ≪ (volume : Measure (_root_.GD.N0232.N0719.N0859.d010811 k sizes)) := by
  simp only [_root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.d009176, _root_.GD.N0232.N0719.N0932.d009211]
  apply _root_.GD.N0235.d004256
  intro i
  apply _root_.GD.N0235.d004256
  intro j
  exact gaussianReal_absolutelyContinuous θ.location
    (_root_.GD.N0232.N0719.N0932.d009196 (θ.scale_pos i).ne')

theorem d023299 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (volume : Measure (_root_.GD.N0232.N0719.N0859.d010811 k sizes)) ≪ _root_.GD.N0232.N0719.N0859.d010812 k sizes θ := by
  simp only [_root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.d009176, _root_.GD.N0232.N0719.N0932.d009211]
  apply _root_.GD.N0235.d004256
  intro i
  apply _root_.GD.N0235.d004256
  intro j
  exact gaussianReal_absolutelyContinuous' θ.location
    (_root_.GD.N0232.N0719.N0932.d009196 (θ.scale_pos i).ne')

theorem d023300 (sizes : Fin k → ℕ) (θ η : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ ≪ _root_.GD.N0232.N0719.N0859.d010812 k sizes η :=
  (_root_.GD.N0072.d023298 sizes θ).trans
    (_root_.GD.N0072.d023299 sizes η)

theorem d023301 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ).map (_root_.GD.N0232.N0719.N0900.d009103 k sizes) =
      _root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009300 k sizes θ.location θ.scale) := by
    unfold _root_.GD.N0232.N0719.N0933.d009300
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ.scale
  have h := congrArg (fun μ => μ.map Prod.snd)
    (_root_.GD.N0232.N0719.N0933.d009309 k sizes hn θ.location θ.scale)
  rw [Measure.map_map measurable_snd (_root_.GD.N0232.N0719.N0933.d009308 k sizes),
    Measure.map_snd_prod] at h
  have hfun : Prod.snd ∘ _root_.GD.N0232.N0719.N0933.d009304 k sizes = _root_.GD.N0232.N0719.N0900.d009103 k sizes := by
    funext z
    exact congrArg (fun s : _root_.GD.N0232.N0719.N0900.d009096 k => s.meanVariance)
      (_root_.GD.N0232.N0719.N0933.d009307 k sizes z)
  rw [hfun] at h
  simpa only [_root_.GD.N0232.N0719.N0859.d010812, measure_univ, one_smul] using h

end
end GD.N0072

#print axioms _root_.GD.N0072.d023296
#print axioms _root_.GD.N0072.d023294
#print axioms _root_.GD.N0072.d023297
#print axioms _root_.GD.N0072.d023300
#print axioms _root_.GD.N0072.d023301
