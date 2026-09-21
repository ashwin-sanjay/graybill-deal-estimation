import GD.Module1470
import GD.Module1682
import GD.Module1688

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0101.N0389
noncomputable section

open _root_.GD.N0213
open _root_.GD.N0213.N0509 _root_.GD.N0213.N0510 _root_.GD.N0213.N0508
open _root_.GD.N0213.N0516

variable {k : ℕ}



theorem d028495
    (a r : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    (_root_.GD.N0213.N0510.d023122 a r).withDensity
        (fun β => ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2)) =
      ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 a r) • _root_.GD.N0213.N0510.d023126 a r := by
  have hZ := (_root_.GD.N0213.N0510.d023128 a r ha hr).2
  rw [_root_.GD.N0213.N0510.d023126, ← withDensity_smul _
    (_root_.GD.N0213.N0510.d023127 a r)]
  congr 1
  funext β
  change ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2) =
    ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 a r) *
      ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2 / _root_.GD.N0213.N0510.d023124 a r)
  rw [← ENNReal.ofReal_mul hZ.le]
  congr 1
  field_simp [hZ.ne']



theorem d028496
    (a t : Fin k → ℝ) (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0213.N0508.d028430 a t =
      ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 a (fun i => a i * t i)) •
        _root_.GD.N0213.N0510.d023126 a (fun i => a i * t i) := by
  rw [_root_.GD.N0213.N0508.d028434]
  exact _root_.GD.N0101.N0389.d028495 a _ ha (fun i => mul_pos (ha i) (ht i))


theorem d028497
    (a t : Fin k → ℝ) (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i)
    (f : (Fin k → ℝ) → ℝ≥0∞) :
    (∫⁻ β, f β ∂_root_.GD.N0213.N0508.d028430 a t) =
      ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 a (fun i => a i * t i)) *
        ∫⁻ β, f β ∂_root_.GD.N0213.N0510.d023126 a (fun i => a i * t i) := by
  rw [_root_.GD.N0101.N0389.d028496 a t ha ht,
    lintegral_smul_measure, smul_eq_mul]


theorem d028498
    (a t : Fin k → ℝ) (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i)
    (f : (Fin k → ℝ) → ℝ) :
    Integrable f (_root_.GD.N0213.N0508.d028430 a t) ↔
      Integrable f (_root_.GD.N0213.N0510.d023126 a (fun i => a i * t i)) := by
  rw [_root_.GD.N0101.N0389.d028496 a t ha ht]
  exact integrable_smul_measure
    (ENNReal.ofReal_pos.mpr (_root_.GD.N0213.N0510.d023128 a _ ha (fun i => mul_pos (ha i) (ht i))).2).ne'
    ENNReal.ofReal_ne_top



theorem d028499
    (a t : Fin k → ℝ) (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i)
    (f : (Fin k → ℝ) → ℝ) :
    (∫ β, f β ∂_root_.GD.N0213.N0508.d028430 a t) =
      _root_.GD.N0213.N0510.d023124 a (fun i => a i * t i) *
        ∫ β, f β ∂_root_.GD.N0213.N0510.d023126 a (fun i => a i * t i) := by
  rw [_root_.GD.N0101.N0389.d028496 a t ha ht, integral_smul_measure,
    ENNReal.toReal_ofReal (_root_.GD.N0213.N0510.d023128 a _ ha (fun i => mul_pos (ha i) (ht i))).2.le,
    smul_eq_mul]




theorem d028500
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => F z.1 z.2)) :
    (∫⁻ β, ∫⁻ t, F β t ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0508.d028429 a) =
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 a (fun i => a i * t i)) *
        (∫⁻ β, F β t ∂_root_.GD.N0213.N0510.d023126 a (fun i => a i * t i))
        ∂_root_.GD.N0213.N0516.d028413 a 0 := by
  rw [_root_.GD.N0213.N0508.d028433 a ha F hF]
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0213.N0494.d028485 a 0] with t ht
  exact _root_.GD.N0101.N0389.d028497 a t ha ht (fun β => F β t)



theorem d028501
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ≥0∞)
    (hF : Measurable (fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => F z.1 z.2)) :
    (∫⁻ β, ∫⁻ t, F β t ∂_root_.GD.N0213.N0516.d028411 (![1, 1, 2] : Fin 3 → ℝ) β
      ∂_root_.GD.N0213.N0508.d028429 (![1, 1, 2] : Fin 3 → ℝ)) =
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 (![1, 1, 2] : Fin 3 → ℝ)
          (fun i => (![1, 1, 2] : Fin 3 → ℝ) i * t i)) *
        (∫⁻ β, F β t ∂_root_.GD.N0213.N0510.d023126 (![1, 1, 2] : Fin 3 → ℝ)
          (fun i => (![1, 1, 2] : Fin 3 → ℝ) i * t i))
        ∂_root_.GD.N0213.N0516.d028413 (![1, 1, 2] : Fin 3 → ℝ) 0 := by
  apply _root_.GD.N0101.N0389.d028500 _ _ F hF
  intro i
  fin_cases i <;> norm_num

end
end GD.N0101.N0389

#print axioms _root_.GD.N0101.N0389.d028495
#print axioms _root_.GD.N0101.N0389.d028496
#print axioms _root_.GD.N0101.N0389.d028497
#print axioms _root_.GD.N0101.N0389.d028498
#print axioms _root_.GD.N0101.N0389.d028499
#print axioms _root_.GD.N0101.N0389.d028500
#print axioms _root_.GD.N0101.N0389.d028501
