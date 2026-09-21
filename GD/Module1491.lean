import GD.Module1486

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0021
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0072
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962

attribute [fun_prop] _root_.GD.N0021.d023314

variable {k : ℕ}

def d023346 (sizes : Fin k → ℕ) (i : Fin k) : ℝ := (sizes i - 1 : ℕ) / 2
def d023347 (sizes : Fin k → ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (_root_.GD.N0021.d023346 sizes i) (_root_.GD.N0021.d023346 sizes i)

theorem d023348 (sizes : Fin k → ℕ) (hn : ∀ i, 4 ≤ sizes i) (i : Fin k) :
    1 < _root_.GD.N0021.d023346 sizes i := by
  have h : 2 < sizes i - 1 := by have := hn i; omega
  have hr : (2 : ℝ) < (sizes i - 1 : ℕ) := by exact_mod_cast h
  unfold _root_.GD.N0021.d023346
  linarith

theorem d023349 (sizes : Fin k → ℕ) (hn : ∀ i, 4 ≤ sizes i) :
    Integrable (_root_.GD.N0021.d023316 (k := k)) (_root_.GD.N0021.d023347 sizes) := by
  have hs (i : Fin k) : 0 < _root_.GD.N0021.d023346 sizes i := lt_trans zero_lt_one (_root_.GD.N0021.d023348 sizes hn i)
  letI (i : Fin k) : IsProbabilityMeasure
      (gammaMeasure (_root_.GD.N0021.d023346 sizes i) (_root_.GD.N0021.d023346 sizes i)) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  letI : IsProbabilityMeasure (_root_.GD.N0021.d023347 sizes) := by
    unfold _root_.GD.N0021.d023347
    infer_instance
  have hpos := _root_.GD.N0232.N0719.N0910.d010287 hs hs
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : j = i
  · subst j
    apply (integrable_const (1 : ℝ)).congr
    filter_upwards [hpos] with q hq
    exact (div_self (hq i).ne').symm
  · simpa only [_root_.GD.N0232.N0719.N0877.d020693, if_neg hij, _root_.GD.N0021.d023347] using
      _root_.GD.N0232.N0719.N0877.d020695 (_root_.GD.N0021.d023346 sizes) (_root_.GD.N0021.d023346 sizes)
        hs hs i (fun j _ => _root_.GD.N0021.d023348 sizes hn j) j

def d023350 (sizes : Fin k → ℕ) : ℝ :=
  ∫ q, _root_.GD.N0021.d023316 q ∂_root_.GD.N0021.d023347 sizes

theorem d023351 (sizes : Fin k → ℕ) (hn : ∀ i, 4 ≤ sizes i) :
    0 ≤ _root_.GD.N0021.d023350 sizes := by
  have hs (i : Fin k) : 0 < _root_.GD.N0021.d023346 sizes i := lt_trans zero_lt_one (_root_.GD.N0021.d023348 sizes hn i)
  apply integral_nonneg_of_ae
  filter_upwards [_root_.GD.N0232.N0719.N0910.d010287 hs hs] with q hq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => (div_pos (hq i) (hq j)).le

theorem d023352 (sizes : Fin k → ℕ) (hn : ∀ i, 4 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MeasurePreserving (fun q : Fin k → ℝ => fun i =>
      (θ.scale i ^ 2 / (sizes i : ℝ)) * q i)
      (_root_.GD.N0021.d023347 sizes) (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) := by
  have hs (i : Fin k) : 0 < _root_.GD.N0021.d023346 sizes i := lt_trans zero_lt_one (_root_.GD.N0021.d023348 sizes hn i)
  letI (i : Fin k) : IsProbabilityMeasure
      (gammaMeasure (_root_.GD.N0021.d023346 sizes i) (_root_.GD.N0021.d023346 sizes i)) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  refine ⟨by fun_prop, ?_⟩
  change (Measure.pi fun i => gammaMeasure (_root_.GD.N0021.d023346 sizes i) (_root_.GD.N0021.d023346 sizes i)).map
    (fun q i => _root_.GD.N0232.N0719.N0933.d009287 (sizes i) (θ.scale i) (q i)) = _
  rw [Measure.pi_map_pi]
  · rfl
  · intro i
    exact (_root_.GD.N0232.N0719.N0933.d009294 (sizes i) (θ.scale i)).aemeasurable



theorem d023353 (sizes : Fin k → ℕ) (hk : 0 < k)
    (hn : ∀ i, 4 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤
      ENNReal.ofReal (_root_.GD.N0021.d023350 sizes * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
  have hn2 (i : Fin k) : 2 ≤ sizes i := le_trans (by norm_num) (hn i)
  have hv (i : Fin k) : 0 < θ.scale i ^ 2 / (sizes i : ℝ) :=
    div_pos (sq_pos_of_pos (θ.scale_pos i)) (Nat.cast_pos.mpr (by have := hn i; omega))
  have hs (i : Fin k) : 0 < _root_.GD.N0021.d023346 sizes i := lt_trans zero_lt_one (_root_.GD.N0021.d023348 sizes hn i)
  have hpos := _root_.GD.N0232.N0719.N0910.d010287 hs hs
  have hmp := _root_.GD.N0021.d023352 sizes hn θ
  rw [_root_.GD.N0021.d023315, _root_.GD.N0072.d023297 sizes hn2 _
    _root_.GD.N0021.d023314 (fun t => _root_.GD.N0232.N0719.N0900.d009131 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)))]
  rw [← hmp.map_eq, lintegral_map]
  · have ho : (∑ i, (θ.scale i ^ 2 / (sizes i : ℝ))⁻¹)⁻¹ = _root_.GD.N0232.N0719.N0963.d012141 k sizes θ := by
      simp only [_root_.GD.N0232.N0719.N0963.d012141, _root_.GD.N0232.N0719.N0838.d012097,
        _root_.GD.N0232.N0719.N0838.d012096, inv_div]
    calc
      (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ))
          (_root_.GD.N0021.d023313 (fun i => (θ.scale i ^ 2 / (sizes i : ℝ)) * q i))) ∂_root_.GD.N0021.d023347 sizes) ≤
          ∫⁻ q, ENNReal.ofReal (_root_.GD.N0021.d023316 q * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) ∂_root_.GD.N0021.d023347 sizes := by
        apply lintegral_mono_ae
        filter_upwards [hpos] with q hq
        apply ENNReal.ofReal_le_ofReal
        simpa only [ho] using _root_.GD.N0021.d023319 hk _ q hv hq
      _ = ENNReal.ofReal (_root_.GD.N0021.d023350 sizes * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
        rw [← ofReal_integral_eq_lintegral_ofReal ((_root_.GD.N0021.d023349 sizes hn).mul_const _)]
        · rw [integral_mul_const]
          rfl
        · filter_upwards [hpos] with q hq
          exact mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
            (div_pos (hq i) (hq j)).le) (_root_.GD.N0232.N0719.N0963.d012142 k sizes θ)
  · exact ENNReal.measurable_ofReal.comp (by unfold _root_.GD.N0072.d007621; fun_prop)
  · exact hmp.measurable

theorem d023354 (sizes : Fin k → ℕ) (hk : 0 < k)
    (hn : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤ ENNReal.ofReal (_root_.GD.N0021.d023350 sizes) := by
  apply iSup_le
  intro θ
  apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes hk (fun i => by have := hn i; omega)
    _ (_root_.GD.N0021.d023351 sizes hn) θ _).mpr
  exact _root_.GD.N0021.d023353 sizes hk hn θ

theorem d023355 (sizes : Fin k → ℕ) (hk : 0 < k)
    (hn : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0021.d023354 sizes hk hn)

end
end GD.N0021

#print axioms _root_.GD.N0021.d023349
#print axioms _root_.GD.N0021.d023353
#print axioms _root_.GD.N0021.d023355
