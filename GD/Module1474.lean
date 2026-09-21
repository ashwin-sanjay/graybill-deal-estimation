import GD.Module1472
import GD.Module1467

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0351
noncomputable section

open _root_.GD.N0101.N0357
open _root_.GD.N0213.N0495
open _root_.GD.N0213.N0523
open _root_.GD.N0225.N0539
open _root_.GD.N0232.N0719.N0954

variable {k : ℕ}

def d023186 (β v : Fin k → ℝ) : ℝ := ∑ i, (β i)⁻¹ * v i ^ 2

def d023187 (L : ℝ) (β v : Fin k → ℝ) : ℝ :=
  _root_.GD.N0101.N0351.d023186 β v * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 β) ^ 2

def d023188 (a : Fin k → ℝ) (w : (Fin k → ℝ) → Fin k → ℝ)
    (β : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (w t)) ∂_root_.GD.N0101.N0357.d023160 a β

def d023189 (a : Fin k → ℝ) (ρ L : ℝ)
    (w : (Fin k → ℝ) → Fin k → ℝ) (t : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ β, ENNReal.ofReal (_root_.GD.N0101.N0351.d023187 L β (w t)) ∂_root_.GD.N0101.N0357.d023161 a ρ t

def d023190 (a : Fin k → ℝ) (ρ L : ℝ)
    (w : (Fin k → ℝ) → Fin k → ℝ) (t : Fin k → ℝ) : ℝ :=
  ∫ β, _root_.GD.N0101.N0351.d023187 L β (w t) ∂_root_.GD.N0101.N0357.d023161 a ρ t

def d023191 (a : Fin k → ℝ) (ρ : ℝ) : Measure (Fin k → ℝ) :=
  (volume.restrict _root_.GD.N0101.N0357.d023158).withDensity (fun t => ENNReal.ofReal (_root_.GD.N0101.N0357.d023162 a ρ t))

theorem d023192 {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) (v : Fin k → ℝ) :
    0 ≤ _root_.GD.N0101.N0351.d023186 β v :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (inv_nonneg.mpr (hβ i).le) (sq_nonneg _))

theorem d023193 (a : Fin k → ℝ) (ρ : ℝ) :
    Measurable (_root_.GD.N0101.N0357.d023162 a ρ) := by
  unfold _root_.GD.N0101.N0357.d023162 _root_.GD.N0213.N0523.d023145
  fun_prop

theorem d023194 (α : Fin k → ℝ) (L : ℝ) :
    ∀ᵐ β ∂_root_.GD.N0225.N0539.d008058 α L, β ∈ _root_.GD.N0101.N0357.d023158 :=
  (withDensity_absolutelyContinuous (_root_.GD.N0225.N0539.d008044 α) _).ae_le (_root_.GD.N0225.N0539.d008050 α)

theorem d023195 (a : Fin k → ℝ) (ρ : ℝ) :
    ∀ᵐ t ∂_root_.GD.N0101.N0351.d023191 a ρ, t ∈ _root_.GD.N0101.N0357.d023158 :=
  (withDensity_absolutelyContinuous (volume.restrict _root_.GD.N0101.N0357.d023158) _).ae_le
    (ae_restrict_mem _root_.GD.N0101.N0357.d023159)

theorem d023196 (b a : Fin k → ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
      _root_.GD.N0232.N0719.N0954.d009343 b (fun i => a i * z.1 i) z.2) := by
  unfold _root_.GD.N0232.N0719.N0954.d009343
  apply Finset.measurable_prod
  intro i _
  unfold gammaPDFReal
  apply Measurable.ite
  · exact measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
  · fun_prop
  · exact measurable_const



theorem d023197
    (b a : Fin k → ℝ) (hb : ∀ i, 0 < b i) (ha : ∀ i, 0 < a i)
    (μ : Measure (Fin k → ℝ)) (hμ : ∀ᵐ t ∂μ, t ∈ _root_.GD.N0101.N0357.d023158)
    (F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    AEMeasurable (fun t => ∫⁻ β, F t β
      ∂_root_.GD.N0232.N0719.N0954.d009342 b (fun i => a i * t i)) μ := by
  have hm : Measurable (fun t => ∫⁻ β in _root_.GD.N0101.N0357.d023158,
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0954.d009343 b (fun i => a i * t i) β) * F t β) :=
    ((_root_.GD.N0101.N0351.d023196 b a).ennreal_ofReal.mul hF).lintegral_prod_right
  apply hm.aemeasurable.congr
  filter_upwards [hμ] with t ht
  exact (_root_.GD.N0101.N0357.d023170 b _ hb (fun i => mul_pos (ha i) (ht i)) _).symm

theorem d023198 (a α : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (L : ℝ) (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w) :
    AEMeasurable (_root_.GD.N0101.N0351.d023188 a w) (_root_.GD.N0225.N0539.d008058 α L) := by
  apply _root_.GD.N0101.N0351.d023197 a a ha ha _ (_root_.GD.N0101.N0351.d023194 α L)
  unfold Function.uncurry _root_.GD.N0101.N0351.d023186
  fun_prop

theorem d023199
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w) :
    AEMeasurable (_root_.GD.N0101.N0351.d023189 a ρ L w) (_root_.GD.N0101.N0351.d023191 a ρ) := by
  apply _root_.GD.N0101.N0351.d023197 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ) a
    (fun i => zero_lt_one.trans (_root_.GD.N0213.N0523.d023146 (ha i) hρ)) ha _
    (_root_.GD.N0101.N0351.d023195 a ρ)
  unfold Function.uncurry _root_.GD.N0101.N0351.d023187 _root_.GD.N0101.N0351.d023186 _root_.GD.N0101.N0402.d023084 _root_.GD.N0213.N0495.d007174
  fun_prop



theorem d023200
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w) :
    (∫⁻ β, _root_.GD.N0101.N0351.d023188 a w β ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) =
      ∫⁻ t, _root_.GD.N0101.N0351.d023189 a ρ L w t ∂_root_.GD.N0101.N0351.d023191 a ρ := by
  have hcut : Measurable (fun β : Fin k → ℝ =>
      ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2)) := by
    unfold _root_.GD.N0213.N0495.d007174
    fun_prop
  calc
    _ = ∫⁻ β, ∫⁻ t, ENNReal.ofReal (_root_.GD.N0101.N0351.d023187 L β (w t))
        ∂_root_.GD.N0101.N0357.d023160 a β ∂_root_.GD.N0225.N0539.d008044 (fun i => 1 - ρ * a i) := by
      rw [_root_.GD.N0225.N0539.d008058, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hcut
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      simp only [Pi.mul_apply]
      apply lintegral_congr
      intro β
      unfold _root_.GD.N0101.N0351.d023188
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro t
      change ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 β) ^ 2) *
        ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (w t)) = _
      rw [_root_.GD.N0101.N0351.d023187, mul_comm (_root_.GD.N0101.N0351.d023186 β (w t)), ENNReal.ofReal_mul (sq_nonneg _)]
    _ = ∫⁻ t in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0101.N0357.d023162 a ρ t) *
        _root_.GD.N0101.N0351.d023189 a ρ L w t := by
      apply _root_.GD.N0101.N0357.d023171 a ρ ha hρ
      unfold Function.uncurry _root_.GD.N0101.N0351.d023187 _root_.GD.N0101.N0351.d023186 _root_.GD.N0101.N0402.d023084 _root_.GD.N0213.N0495.d007174
      fun_prop
    _ = _ := by
      rw [_root_.GD.N0101.N0351.d023191, lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (_root_.GD.N0101.N0351.d023193 a ρ).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      rfl

theorem d023201
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) (v : Fin k → ℝ) :
    Integrable (fun β => _root_.GD.N0101.N0351.d023187 L β v) (_root_.GD.N0101.N0357.d023161 a ρ t) := by
  have hi (i : Fin k) :
      Integrable (fun β => ((β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 β) ^ 2) * v i ^ 2)
        (_root_.GD.N0101.N0357.d023161 a ρ t) :=
    (_root_.GD.N0101.N0402.d023088
      (fun i => a i * (1 - ρ)) (fun i => a i * t i)
      (fun i => mul_pos (ha i) (sub_pos.mpr hρ)) (fun i => mul_pos (ha i) (ht i)) L i).mul_const _
  apply (integrable_finsetSum Finset.univ (fun i _ => hi i)).congr
  filter_upwards with β
  unfold _root_.GD.N0101.N0351.d023187 _root_.GD.N0101.N0351.d023186
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d023202
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0101.N0351.d023189 a ρ L w t = ENNReal.ofReal (_root_.GD.N0101.N0351.d023190 a ρ L w t) := by
  apply (ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0101.N0351.d023201 a ρ L ha hρ ht (w t)) _).symm
  filter_upwards [_root_.GD.N0101.N0357.d023165 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)
    (fun i => a i * t i) (fun i => zero_lt_one.trans (_root_.GD.N0213.N0523.d023146 (ha i) hρ))
    (fun i => mul_pos (ha i) (ht i))] with β hβ
  exact mul_nonneg (_root_.GD.N0101.N0351.d023192 hβ (w t)) (sq_nonneg _)

theorem d023203
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    0 ≤ _root_.GD.N0101.N0351.d023190 a ρ L w t := by
  apply integral_nonneg_of_ae
  filter_upwards [_root_.GD.N0101.N0357.d023165 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)
    (fun i => a i * t i) (fun i => zero_lt_one.trans (_root_.GD.N0213.N0523.d023146 (ha i) hρ))
    (fun i => mul_pos (ha i) (ht i))] with β hβ
  exact mul_nonneg (_root_.GD.N0101.N0351.d023192 hβ (w t)) (sq_nonneg _)

theorem d023204
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) :
    _root_.GD.N0101.N0351.d023190 a ρ L w =ᵐ[_root_.GD.N0101.N0351.d023191 a ρ]
      fun t => (_root_.GD.N0101.N0351.d023189 a ρ L w t).toReal := by
  filter_upwards [_root_.GD.N0101.N0351.d023195 a ρ] with t ht
  rw [_root_.GD.N0101.N0351.d023202 a ρ L ha hρ w ht,
    ENNReal.toReal_ofReal (_root_.GD.N0101.N0351.d023203 a ρ L ha hρ w ht)]



theorem d023205
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hfinite : (∫⁻ β, _root_.GD.N0101.N0351.d023188 a w β
      ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) ≠ ⊤) :
    Integrable (fun β => (_root_.GD.N0101.N0351.d023188 a w β).toReal)
        (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) ∧
      Integrable (_root_.GD.N0101.N0351.d023190 a ρ L w) (_root_.GD.N0101.N0351.d023191 a ρ) ∧
      (∫ β, (_root_.GD.N0101.N0351.d023188 a w β).toReal ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) =
        ∫ t, _root_.GD.N0101.N0351.d023190 a ρ L w t ∂_root_.GD.N0101.N0351.d023191 a ρ := by
  have hm := _root_.GD.N0101.N0351.d023198 a (fun i => 1 - ρ * a i) ha L w hw
  have hpm := _root_.GD.N0101.N0351.d023199 a ρ L ha hρ w hw
  have heq := _root_.GD.N0101.N0351.d023200 a ρ L ha hρ w hw
  have hpfinite : (∫⁻ t, _root_.GD.N0101.N0351.d023189 a ρ L w t ∂_root_.GD.N0101.N0351.d023191 a ρ) ≠ ⊤ := by
    rw [← heq]
    exact hfinite
  have hae := _root_.GD.N0101.N0351.d023204 a ρ L ha hρ w
  refine ⟨integrable_toReal_of_lintegral_ne_top hm hfinite,
    (integrable_toReal_of_lintegral_ne_top hpm hpfinite).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_toReal hm (ae_lt_top' hm hfinite),
    integral_toReal hpm (ae_lt_top' hpm hpfinite), heq]




theorem d023206
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (p w : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p) (hw : Measurable w)
    (hfinite : (∫⁻ β, _root_.GD.N0101.N0351.d023188 a p β
      ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) ≠ ⊤)
    (hdom : ∀ β ∈ _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0351.d023188 a w β ≤ _root_.GD.N0101.N0351.d023188 a p β) :
    Integrable (fun β => (_root_.GD.N0101.N0351.d023188 a p β).toReal - (_root_.GD.N0101.N0351.d023188 a w β).toReal)
        (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) ∧
      Integrable (fun t => _root_.GD.N0101.N0351.d023190 a ρ L p t - _root_.GD.N0101.N0351.d023190 a ρ L w t)
        (_root_.GD.N0101.N0351.d023191 a ρ) ∧
      (∫ β, (_root_.GD.N0101.N0351.d023188 a p β).toReal - (_root_.GD.N0101.N0351.d023188 a w β).toReal
        ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) =
      ∫ t, _root_.GD.N0101.N0351.d023190 a ρ L p t - _root_.GD.N0101.N0351.d023190 a ρ L w t ∂_root_.GD.N0101.N0351.d023191 a ρ := by
  have hwfinite : (∫⁻ β, _root_.GD.N0101.N0351.d023188 a w β
      ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfinite
    apply lintegral_mono_ae
    filter_upwards [_root_.GD.N0101.N0351.d023194 (fun i => 1 - ρ * a i) L] with β hβ
    exact hdom β hβ
  obtain ⟨hpi, hppi, hpeq⟩ := _root_.GD.N0101.N0351.d023205 a ρ L ha hρ p hp hfinite
  obtain ⟨hwi, hpwi, hweq⟩ := _root_.GD.N0101.N0351.d023205 a ρ L ha hρ w hw hwfinite
  refine ⟨hpi.sub hwi, hppi.sub hpwi, ?_⟩
  rw [integral_sub hpi hwi, integral_sub hppi hpwi, hpeq, hweq]

end
end GD.N0101.N0351

#print axioms _root_.GD.N0101.N0351.d023197
#print axioms _root_.GD.N0101.N0351.d023198
#print axioms _root_.GD.N0101.N0351.d023199
#print axioms _root_.GD.N0101.N0351.d023200
#print axioms _root_.GD.N0101.N0351.d023201
#print axioms _root_.GD.N0101.N0351.d023202
#print axioms _root_.GD.N0101.N0351.d023205
#print axioms _root_.GD.N0101.N0351.d023206
