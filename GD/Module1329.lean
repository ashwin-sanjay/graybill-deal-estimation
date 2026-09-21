import GD.Module0498
import GD.Module0432
import GD.Module0640

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0044
noncomputable section

open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0043

variable {k : ℕ}


theorem d021655 {shape rate : Fin k → ℝ}
    (hshape : ∀ j, 0 < shape j) (hrate : ∀ j, 0 < rate j)
    (i : Fin k) {M : ℝ} (hM : 1 ≤ M) :
    ENNReal.ofReal (M ^ (-shape i)) • _root_.GD.N0232.N0719.N0954.d009342 shape rate ≤
      _root_.GD.N0232.N0719.N0954.d009342 shape (Function.update rate i (rate i / M)) := by
  letI (j : Fin k) : IsProbabilityMeasure (gammaMeasure (shape j) (rate j)) :=
    isProbabilityMeasure_gammaMeasure (hshape j) (hrate j)
  apply _root_.GD.N0044.d007611 (fun j => gammaMeasure (shape j) (rate j))
    (fun j => gammaMeasure (shape j) (Function.update rate i (rate i / M) j))
    i ENNReal.ofReal_ne_top
  · simpa only [Function.update_self] using _root_.GD.N0043.d006730 (hshape i) (hrate i) hM
  · intro j hj
    simp only [Function.update_of_ne hj, le_refl]


theorem d021656 {shape rate : Fin k → ℝ}
    (hshape : ∀ j, 0 < shape j) (hrate : ∀ j, 0 < rate j)
    (i : Fin k) {M : ℝ} (hM : 1 ≤ M) (f : (Fin k → ℝ) → ℝ≥0∞) :
    ENNReal.ofReal (M ^ (-shape i)) * (∫⁻ x, f x ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate) ≤
      ∫⁻ x, f x ∂_root_.GD.N0232.N0719.N0954.d009342 shape (Function.update rate i (rate i / M)) := by
  have h := lintegral_mono' (f := f) (_root_.GD.N0044.d021655 hshape hrate i hM) le_rfl
  simpa only [lintegral_smul_measure, smul_eq_mul] using h


theorem d021657 {shape rate : Fin k → ℝ}
    (hshape : ∀ j, 0 < shape j) (hrate : ∀ j, 0 < rate j)
    (i : Fin k) {M : ℝ} (hM : 1 ≤ M) (f : (Fin k → ℝ) → ℝ≥0∞) :
    ENNReal.ofReal (M ^ (1 - shape i)) * (∫⁻ x, f x ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate) ≤
      ENNReal.ofReal M *
        (∫⁻ x, f x ∂_root_.GD.N0232.N0719.N0954.d009342 shape (Function.update rate i (rate i / M))) := by
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have h := _root_.GD.N0044.d021656 hshape hrate i hM f
  have hpow : M ^ (1 - shape i) = M * M ^ (-shape i) := by
    rw [sub_eq_add_neg, Real.rpow_add hMp, Real.rpow_one]
  rw [hpow, ENNReal.ofReal_mul hMp.le, mul_assoc]
  exact mul_le_mul_right h _



theorem d021658 {shape v : Fin k → ℝ}
    (hshape : ∀ j, 0 < shape j) (hv : ∀ j, 0 < v j)
    (i : Fin k) {M : ℝ} (hM : 1 ≤ M) :
    ENNReal.ofReal (M ^ (-shape i)) •
        _root_.GD.N0232.N0719.N0954.d009342 shape (fun j => shape j / v j) ≤
      _root_.GD.N0232.N0719.N0954.d009342 shape (fun j => shape j / Function.update v i (v i * M) j) := by
  have heq : Function.update (fun j => shape j / v j) i ((shape i / v i) / M) =
      (fun j => shape j / Function.update v i (v i * M) j) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, div_mul_eq_div_div]
    · simp only [Function.update_of_ne hj]
  rw [← heq]
  exact _root_.GD.N0044.d021655 hshape (fun j => div_pos (hshape j) (hv j)) i hM

end
end GD.N0044

#print axioms _root_.GD.N0044.d021655
#print axioms _root_.GD.N0044.d021656
#print axioms _root_.GD.N0044.d021657
#print axioms _root_.GD.N0044.d021658
