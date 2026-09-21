import GD.Module1571
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic









































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0106.N0428.N0770.N1721
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1724
open _root_.GD.N0106.N0428.N0770.N1722
open _root_.GD.N0232.N0720.N1436




theorem d024345 (q : ℝ) : Measurable fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024169 q p.1 p.2 := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
  fun_prop


theorem d024346 (q : ℝ) : Measurable (_root_.GD.N0106.N0428.N0770.N1725.d024170 q) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024170
  refine Measurable.mul ?_ ?_
  · exact (measurable_snd.div (measurable_fst.mul (measurable_const.sub measurable_fst))).sqrt
  · exact (_root_.GD.N0106.N0428.N0770.N1721.d024345 q).pow_const _








theorem d024347 (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in _root_.GD.N0232.N0720.N1436.d013218, g x) = ∫⁻ e in Ioo (0 : ℝ) 1, ∫⁻ F in Ioi (0 : ℝ), g (e, F) := by
  unfold _root_.GD.N0232.N0720.N1436.d013218
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod g hg.aemeasurable



theorem d024348 (f : ℝ × ℝ → ℝ)
    (hf : IntegrableOn f _root_.GD.N0232.N0720.N1436.d013218 volume) :
    (∫ x in _root_.GD.N0232.N0720.N1436.d013218, f x) = ∫ e in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ), f (e, F) := by
  unfold _root_.GD.N0232.N0720.N1436.d013218 at hf ⊢
  rw [Measure.volume_eq_prod] at hf ⊢
  exact setIntegral_prod f hf




theorem d024349 (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    IntegrableOn f _root_.GD.N0232.N0720.N1436.d013218 volume ↔
      (∀ᵐ e ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        IntegrableOn (fun F => f (e, F)) (Ioi (0 : ℝ)) volume) ∧
      IntegrableOn (fun e => ∫ F in Ioi (0 : ℝ), ‖f (e, F)‖) (Ioo (0 : ℝ) 1) volume := by
  unfold _root_.GD.N0232.N0720.N1436.d013218
  rw [Measure.volume_eq_prod]
  simp only [IntegrableOn]
  rw [← Measure.prod_restrict]
  exact integrable_prod_iff hf.aestronglyMeasurable





theorem d024350 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ w, ENNReal.ofReal (_root_.GD.N0107.d009090 2 2 w ^ 2) * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)
      ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta) *
        ∫⁻ e in Ioo (0 : ℝ) 1, ∫⁻ F in Ioi (0 : ℝ),
          ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) (e, F)) * phi (e, F) := by
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024341 mu sigma zeta hsigma hzeta phi hphi,
    _root_.GD.N0106.N0428.N0770.N1721.d024347 _ ((_root_.GD.N0106.N0428.N0770.N1721.d024346 _).ennreal_ofReal.mul hphi)]






theorem d024351 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ) (hphi : Measurable phi)
    (hint : Integrable (fun w => _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w))
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta)) :
    (∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)
      ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta *
        ∫ e in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ), _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) (e, F) * phi (e, F) := by
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024342 mu sigma zeta hsigma hzeta phi hphi,
    _root_.GD.N0106.N0428.N0770.N1721.d024348 _
      ((_root_.GD.N0106.N0428.N0770.N1722.d024344 mu sigma zeta hsigma hzeta phi hphi).mp hint)]




theorem d024352 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ) (hphi : Measurable phi) :
    Integrable (fun w => _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w))
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta) ↔
      (∀ᵐ e ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        IntegrableOn (fun F => _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) (e, F) * phi (e, F)) (Ioi (0 : ℝ)) volume) ∧
      IntegrableOn (fun e => ∫ F in Ioi (0 : ℝ), ‖_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) (e, F) * phi (e, F)‖)
        (Ioo (0 : ℝ) 1) volume := by
  rw [_root_.GD.N0106.N0428.N0770.N1722.d024344 mu sigma zeta hsigma hzeta phi hphi]
  exact _root_.GD.N0106.N0428.N0770.N1721.d024349 _ ((_root_.GD.N0106.N0428.N0770.N1721.d024346 _).mul hphi)




theorem d024353 (g : ℝ → ℝ) :
    (∫ e in Ioo (0 : ℝ) 1, g e) = ∫ e in (0 : ℝ)..1, g e := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]


theorem d024354 (g : ℝ → ℝ) :
    (∫ e in Ioo (0 : ℝ) 1, g e) = ∫ e in Icc (0 : ℝ) 1, g e :=
  integral_Icc_eq_integral_Ioo.symm


theorem d024355 (h : ℝ → ℝ) :
    (∫ F in Ioi (0 : ℝ), h F) = ∫ F in Ici (0 : ℝ), h F :=
  setIntegral_congr_set (Ioi_ae_eq_Ici' (measure_singleton (0 : ℝ)))


theorem d024356 (g : ℝ → ℝ≥0∞) :
    (∫⁻ e in Ioo (0 : ℝ) 1, g e) = ∫⁻ e in Ioc (0 : ℝ) 1, g e :=
  setLIntegral_congr (Ioo_ae_eq_Ioc' (measure_singleton (1 : ℝ)))


theorem d024357 (g : ℝ → ℝ≥0∞) :
    (∫⁻ e in Ioo (0 : ℝ) 1, g e) = ∫⁻ e in Icc (0 : ℝ) 1, g e :=
  setLIntegral_congr (Ioo_ae_eq_Icc' (measure_singleton (0 : ℝ)) (measure_singleton (1 : ℝ)))


theorem d024358 (h : ℝ → ℝ≥0∞) :
    (∫⁻ F in Ioi (0 : ℝ), h F) = ∫⁻ F in Ici (0 : ℝ), h F :=
  setLIntegral_congr (Ioi_ae_eq_Ici' (measure_singleton (0 : ℝ)))



theorem d024359 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (phi : (ℝ × ℝ) → ℝ) (hphi : Measurable phi)
    (hint : Integrable (fun w => _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w))
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta)) :
    (∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 * phi (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)
      ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta *
        ∫ e in (0 : ℝ)..1, ∫ F in Ioi (0 : ℝ), _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) (e, F) * phi (e, F) := by
  rw [_root_.GD.N0106.N0428.N0770.N1721.d024351 mu sigma zeta hsigma hzeta phi hphi hint,
    _root_.GD.N0106.N0428.N0770.N1721.d024353]

end
end GD.N0106.N0428.N0770.N1721

#print axioms _root_.GD.N0106.N0428.N0770.N1721.d024346
#print axioms _root_.GD.N0106.N0428.N0770.N1721.d024347
#print axioms _root_.GD.N0106.N0428.N0770.N1721.d024348
#print axioms _root_.GD.N0106.N0428.N0770.N1721.d024349
#print axioms _root_.GD.N0106.N0428.N0770.N1721.d024350
#print axioms _root_.GD.N0106.N0428.N0770.N1721.d024351
#print axioms _root_.GD.N0106.N0428.N0770.N1721.d024352
#print axioms _root_.GD.N0106.N0428.N0770.N1721.d024359
