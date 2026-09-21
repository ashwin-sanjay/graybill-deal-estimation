import GD.Module1474

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0351
noncomputable section

open _root_.GD.N0101.N0357
open _root_.GD.N0225.N0539

variable {k : ℕ}



theorem d023207
    (a : Fin k → ℝ) (ρ : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (f : (Fin k → ℝ) → ℝ) :
    (∫ t, f t ∂_root_.GD.N0101.N0351.d023191 a ρ) =
      ∫ t in _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0357.d023162 a ρ t * f t := by
  rw [_root_.GD.N0101.N0351.d023191, integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0101.N0351.d023193 a ρ).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
  rw [ENNReal.toReal_ofReal (_root_.GD.N0101.N0357.d023163 a ρ ha hρ ht).le, smul_eq_mul]

theorem d023208
    (a : Fin k → ℝ) (ρ : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (f : (Fin k → ℝ) → ℝ) :
    Integrable f (_root_.GD.N0101.N0351.d023191 a ρ) ↔
      Integrable (fun t => _root_.GD.N0101.N0357.d023162 a ρ t * f t) (volume.restrict _root_.GD.N0101.N0357.d023158) := by
  rw [_root_.GD.N0101.N0351.d023191, integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0101.N0351.d023193 a ρ).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
  rw [ENNReal.toReal_ofReal (_root_.GD.N0101.N0357.d023163 a ρ ha hρ ht).le, smul_eq_mul]



theorem d023209
    (a : Fin k → ℝ) (ρ L : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (p w : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p) (hw : Measurable w)
    (hfinite : (∫⁻ β, _root_.GD.N0101.N0351.d023188 a p β
      ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) ≠ ⊤)
    (hdom : ∀ β ∈ _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0351.d023188 a w β ≤ _root_.GD.N0101.N0351.d023188 a p β) :
    Integrable (fun β => (_root_.GD.N0101.N0351.d023188 a p β).toReal - (_root_.GD.N0101.N0351.d023188 a w β).toReal)
        (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) ∧
      Integrable (fun t => _root_.GD.N0101.N0357.d023162 a ρ t *
        (_root_.GD.N0101.N0351.d023190 a ρ L p t - _root_.GD.N0101.N0351.d023190 a ρ L w t)) (volume.restrict _root_.GD.N0101.N0357.d023158) ∧
      (∫ β, (_root_.GD.N0101.N0351.d023188 a p β).toReal - (_root_.GD.N0101.N0351.d023188 a w β).toReal
        ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) =
      ∫ t in _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0357.d023162 a ρ t *
        (_root_.GD.N0101.N0351.d023190 a ρ L p t - _root_.GD.N0101.N0351.d023190 a ρ L w t) := by
  obtain ⟨hgap, hpost, heq⟩ := _root_.GD.N0101.N0351.d023206 a ρ L ha hρ p w hp hw hfinite hdom
  refine ⟨hgap, (_root_.GD.N0101.N0351.d023208 a ρ ha hρ _).mp hpost, ?_⟩
  exact heq.trans (_root_.GD.N0101.N0351.d023207 a ρ ha hρ _)

end
end GD.N0101.N0351

#print axioms _root_.GD.N0101.N0351.d023207
#print axioms _root_.GD.N0101.N0351.d023208
#print axioms _root_.GD.N0101.N0351.d023209
