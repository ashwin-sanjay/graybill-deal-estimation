import GD.Module1477
import GD.Module1476
import GD.Module0541
import GD.Module1478

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0416
noncomputable section

open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0230.N0665
open _root_.GD.N0213.N0523
open _root_.GD.N0225.N0539
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0351 _root_.GD.N0101.N0358
open _root_.GD.N0101.N0405 _root_.GD.N0101.N0415 _root_.GD.N0101.N0401

variable {k : ℕ} [NeZero k]

theorem d023245 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1) {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    (∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) *
      ENNReal.ofReal (_root_.GD.N0101.N0405.d023221 (_root_.GD.N0230.N0665.d000407 t) β) ∂_root_.GD.N0101.N0357.d023161 a ρ t) ≤
      ENNReal.ofReal (_root_.GD.N0101.N0405.d023224 a (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)) *
        ∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0101.N0357.d023161 a ρ t := by
  have hb (i : Fin k) : 1 < _root_.GD.N0213.N0523.d023144 (a i) ρ := _root_.GD.N0213.N0523.d023146 (ha i) hρ
  have hr (i : Fin k) : 0 < a i * t i := mul_pos (ha i) (ht i)
  unfold _root_.GD.N0101.N0357.d023161
  rw [_root_.GD.N0101.N0358.d023215 _ _ (fun i => zero_lt_one.trans (hb i)) hr,
    _root_.GD.N0101.N0358.d023216 _ _ (fun i => zero_lt_one.trans (hb i)) hr]
  have h := _root_.GD.N0101.N0405.d023226 a (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ) t ha hb ht
  rw [show (fun i => 1 + a i * t i) = (fun i => a i * t i + 1) by funext i; ring] at h
  exact (mul_le_mul_right h _).trans_eq (mul_comm _ _)



theorem d023246 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1) :
    (∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i)) * (∑ i, β i) * _root_.GD.N0101.N0415.d023239 a β)
      ∂_root_.GD.N0225.N0539.d008044 (fun i => 1 - ρ * a i)) ≤
      ENNReal.ofReal (_root_.GD.N0101.N0405.d023224 a (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)) *
        ∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0225.N0539.d008044 (fun i => 1 - ρ * a i) := by
  let F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞ := fun β t =>
    ENNReal.ofReal (Real.exp (-(∑ i, β i))) * ENNReal.ofReal (_root_.GD.N0101.N0405.d023221 (_root_.GD.N0230.N0665.d000407 t) β)
  have hF : Measurable (Function.uncurry F) := by
    unfold F Function.uncurry _root_.GD.N0101.N0405.d023221 _root_.GD.N0101.N0351.d023186
    fun_prop
  have hleft : (∫⁻ β, ENNReal.ofReal
      (Real.exp (-(∑ i, β i)) * (∑ i, β i) * _root_.GD.N0101.N0415.d023239 a β)
      ∂_root_.GD.N0225.N0539.d008044 (fun i => 1 - ρ * a i)) =
      ∫⁻ β, ∫⁻ t, F β t ∂_root_.GD.N0101.N0357.d023160 a β ∂_root_.GD.N0225.N0539.d008044 (fun i => 1 - ρ * a i) := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0225.N0539.d008050 (fun i => 1 - ρ * a i)] with β hβ
    have hR : 0 ≤ ∑ i, β i := Finset.sum_nonneg (fun i _ => (hβ i).le)
    rw [_root_.GD.N0101.N0415.d023241 a hβ,
      ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) hR),
      ENNReal.ofReal_toReal (_root_.GD.N0101.N0415.d023234 a ha hβ)]
    unfold _root_.GD.N0101.N0351.d023188 F _root_.GD.N0101.N0405.d023221
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_mul hR]
    exact mul_assoc _ _ _
  have hnorm :
      (∫⁻ t in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0101.N0357.d023162 a ρ t) *
        ∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0101.N0357.d023161 a ρ t) =
      ∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0225.N0539.d008044 (fun i => 1 - ρ * a i) := by
    rw [← _root_.GD.N0101.N0357.d023171 a ρ ha hρ
      (fun β _ => ENNReal.ofReal (Real.exp (-(∑ i, β i)))) (by fun_prop)]
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0225.N0539.d008050 (fun i => 1 - ρ * a i)] with β hβ
    letI := _root_.GD.N0101.N0415.d023229 a ha hβ
    simp
  rw [hleft, _root_.GD.N0101.N0357.d023171 a ρ ha hρ F hF]
  calc
    _ ≤ ∫⁻ t in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0101.N0357.d023162 a ρ t) *
        (ENNReal.ofReal (_root_.GD.N0101.N0405.d023224 a (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)) *
          ∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0101.N0357.d023161 a ρ t) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
      exact mul_le_mul_right (_root_.GD.N0101.N0416.d023245 a ρ ha hρ ht) _
    _ = ENNReal.ofReal (_root_.GD.N0101.N0405.d023224 a (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)) *
        (∫⁻ t in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0101.N0357.d023162 a ρ t) *
          ∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0101.N0357.d023161 a ρ t) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro t
      ac_rfl
    _ = _ := by rw [hnorm]

theorem d023247 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1) :
    (∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i)) * (∑ i, β i) * _root_.GD.N0101.N0415.d023239 a β)
      ∂_root_.GD.N0225.N0539.d008044 (fun i => 1 - ρ * a i)) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (_root_.GD.N0101.N0401.d008075 _ hα hsum))
      (_root_.GD.N0101.N0416.d023246 a ρ ha hρ)

end
end GD.N0101.N0416

#print axioms _root_.GD.N0101.N0416.d023245
#print axioms _root_.GD.N0101.N0416.d023246
#print axioms _root_.GD.N0101.N0416.d023247
