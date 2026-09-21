import GD.Module1471
import GD.Module0539
import GD.Module0640
import GD.Module0699










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0357
noncomputable section

open _root_.GD.N0213.N0523
open _root_.GD.N0225.N0539
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0910

variable {k : ℕ}

def d023158 : Set (Fin k → ℝ) := {z | ∀ i, 0 < z i}

theorem d023159 : MeasurableSet (_root_.GD.N0101.N0357.d023158 (k := k)) := by
  simp only [_root_.GD.N0101.N0357.d023158, setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)

def d023160 (a β : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  _root_.GD.N0232.N0719.N0954.d009342 a (fun i => a i * β i)

def d023161 (a : Fin k → ℝ) (ρ : ℝ) (t : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  _root_.GD.N0232.N0719.N0954.d009342 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ) (fun i => a i * t i)

def d023162 (a : Fin k → ℝ) (ρ : ℝ) (t : Fin k → ℝ) : ℝ :=
  ∏ i, _root_.GD.N0213.N0523.d023145 (a i) ρ (t i)

theorem d023163 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1) {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    0 < _root_.GD.N0101.N0357.d023162 a ρ t := by
  apply Finset.prod_pos
  intro i _
  unfold _root_.GD.N0213.N0523.d023145
  have hshape : 0 < _root_.GD.N0213.N0523.d023144 (a i) ρ :=
    zero_lt_one.trans (_root_.GD.N0213.N0523.d023146 (ha i) hρ)
  exact mul_pos
    (mul_pos (div_pos (Real.rpow_pos_of_pos (ha i) _) (Real.Gamma_pos_of_pos (ha i)))
      (Real.rpow_pos_of_pos (ht i) _))
    (div_pos (Real.Gamma_pos_of_pos hshape)
      (Real.rpow_pos_of_pos (mul_pos (ha i) (ht i)) _))

theorem d023164
    (a : Fin k → ℝ) (ρ : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    {β t : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0232.N0719.N0954.d009343 a (fun i => a i * β i) t *
        _root_.GD.N0225.N0539.d008043 (fun i => 1 - ρ * a i) β =
      _root_.GD.N0101.N0357.d023162 a ρ t *
        _root_.GD.N0232.N0719.N0954.d009343 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)
          (fun i => a i * t i) β := by
  unfold _root_.GD.N0232.N0719.N0954.d009343 _root_.GD.N0225.N0539.d008043 _root_.GD.N0101.N0357.d023162
  rw [if_pos (show ∀ i, 0 < β i from hβ),
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [show (1 - ρ * a i) - 1 = -ρ * a i by ring]
  exact _root_.GD.N0213.N0523.d023147 (ha i) hρ (ht i) (hβ i)

theorem d023165 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    ∀ᵐ z ∂_root_.GD.N0232.N0719.N0954.d009342 a r, z ∈ _root_.GD.N0101.N0357.d023158 := by
  letI (i : Fin k) := isProbabilityMeasure_gammaMeasure (ha i) (hr i)
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun j => gammaMeasure (a j) (r j)) i).quasiMeasurePreserving.ae
    (_root_.GD.N0232.N0719.N0910.d010286 (ha i) (hr i))

theorem d023166 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    _root_.GD.N0232.N0719.N0954.d009342 a r = (volume.restrict _root_.GD.N0101.N0357.d023158).withDensity
      (fun z => ENNReal.ofReal (_root_.GD.N0232.N0719.N0954.d009343 a r z)) := by
  calc
    _ = (_root_.GD.N0232.N0719.N0954.d009342 a r).restrict _root_.GD.N0101.N0357.d023158 :=
      (Measure.restrict_eq_self_of_ae_mem (_root_.GD.N0101.N0357.d023165 a r ha hr)).symm
    _ = _ := by rw [_root_.GD.N0232.N0719.N0954.d009363 ha hr, restrict_withDensity _root_.GD.N0101.N0357.d023159]

theorem d023167 (α : Fin k → ℝ) :
    _root_.GD.N0225.N0539.d008044 α = (volume.restrict _root_.GD.N0101.N0357.d023158).withDensity (fun β => ENNReal.ofReal (_root_.GD.N0225.N0539.d008043 α β)) := by
  calc
    _ = (_root_.GD.N0225.N0539.d008044 α).restrict _root_.GD.N0101.N0357.d023158 :=
      (Measure.restrict_eq_self_of_ae_mem (_root_.GD.N0225.N0539.d008050 α)).symm
    _ = _ := by rw [_root_.GD.N0225.N0539.d008044, restrict_withDensity _root_.GD.N0101.N0357.d023159]

theorem d023168 (a r : Fin k → ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0954.d009343 a r) := by
  unfold _root_.GD.N0232.N0719.N0954.d009343
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gammaPDFReal (a i) (r i)).comp (measurable_pi_apply i)

theorem d023169 (a : Fin k → ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
      _root_.GD.N0232.N0719.N0954.d009343 a (fun i => a i * z.1 i) z.2) := by
  unfold _root_.GD.N0232.N0719.N0954.d009343
  apply Finset.measurable_prod
  intro i _
  unfold gammaPDFReal
  apply Measurable.ite
  · exact measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
  · fun_prop
  · exact measurable_const

theorem d023170 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) (f : (Fin k → ℝ) → ℝ≥0∞) :
    (∫⁻ z, f z ∂_root_.GD.N0232.N0719.N0954.d009342 a r) =
      ∫⁻ z in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0232.N0719.N0954.d009343 a r z) * f z := by
  rw [_root_.GD.N0101.N0357.d023166 a r ha hr]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (_root_.GD.N0101.N0357.d023168 a r).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) f



theorem d023171
    (a : Fin k → ℝ) (ρ : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ β, ∫⁻ t, F β t ∂_root_.GD.N0101.N0357.d023160 a β ∂_root_.GD.N0225.N0539.d008044 (fun i => 1 - ρ * a i)) =
      ∫⁻ t in _root_.GD.N0101.N0357.d023158, ENNReal.ofReal (_root_.GD.N0101.N0357.d023162 a ρ t) *
        ∫⁻ β, F β t ∂_root_.GD.N0101.N0357.d023161 a ρ t := by
  let α : Fin k → ℝ := fun i => 1 - ρ * a i
  let ν : Measure (Fin k → ℝ) := volume.restrict _root_.GD.N0101.N0357.d023158
  let J : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞ := fun β t =>
    ENNReal.ofReal (_root_.GD.N0225.N0539.d008043 α β) *
      (ENNReal.ofReal (_root_.GD.N0232.N0719.N0954.d009343 a (fun i => a i * β i) t) * F β t)
  have hJ : Measurable (Function.uncurry J) :=
    (((_root_.GD.N0225.N0539.d008046 α).comp measurable_fst).ennreal_ofReal).mul
      ((_root_.GD.N0101.N0357.d023169 a).ennreal_ofReal.mul hF)
  have hshape (i : Fin k) : 0 < _root_.GD.N0213.N0523.d023144 (a i) ρ :=
    zero_lt_one.trans (_root_.GD.N0213.N0523.d023146 (ha i) hρ)
  calc
    _ = ∫⁻ β, (∫⁻ t in _root_.GD.N0101.N0357.d023158,
        ENNReal.ofReal (_root_.GD.N0232.N0719.N0954.d009343 a (fun i => a i * β i) t) * F β t) ∂_root_.GD.N0225.N0539.d008044 α := by
      apply lintegral_congr_ae
      filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
      exact _root_.GD.N0101.N0357.d023170 a _ ha (fun i => mul_pos (ha i) (hβ i)) _
    _ = ∫⁻ β, ∫⁻ t, J β t ∂ν ∂ν := by
      rw [_root_.GD.N0101.N0357.d023167 α,
        lintegral_withDensity_eq_lintegral_mul_non_measurable _
          (_root_.GD.N0225.N0539.d008046 α).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply lintegral_congr
      intro β
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ t, ∫⁻ β, J β t ∂ν ∂ν := lintegral_lintegral_swap hJ.aemeasurable
    _ = _ := by
      apply setLIntegral_congr_fun _root_.GD.N0101.N0357.d023159
      intro t ht
      change (∫⁻ β, J β t ∂ν) = ENNReal.ofReal (_root_.GD.N0101.N0357.d023162 a ρ t) *
        (∫⁻ β, F β t ∂_root_.GD.N0232.N0719.N0954.d009342 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)
          (fun i => a i * t i))
      rw [_root_.GD.N0101.N0357.d023170 _ _ hshape
        (fun i => mul_pos (ha i) (ht i)),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun _root_.GD.N0101.N0357.d023159
      intro β hβ
      have heq := _root_.GD.N0101.N0357.d023164 a ρ ha hρ hβ ht
      have hw : 0 ≤ _root_.GD.N0225.N0539.d008043 α β := _root_.GD.N0225.N0539.d008045 α β
      have he : 0 ≤ _root_.GD.N0101.N0357.d023162 a ρ t := (_root_.GD.N0101.N0357.d023163 a ρ ha hρ ht).le
      change ENNReal.ofReal (_root_.GD.N0225.N0539.d008043 α β) * (_ * F β t) = _ * (_ * F β t)
      rw [← mul_assoc, ← ENNReal.ofReal_mul hw, mul_comm (_root_.GD.N0225.N0539.d008043 α β), heq,
        ENNReal.ofReal_mul he, mul_assoc]

end
end GD.N0101.N0357

#print axioms _root_.GD.N0101.N0357.d023164
#print axioms _root_.GD.N0101.N0357.d023166
#print axioms _root_.GD.N0101.N0357.d023171
