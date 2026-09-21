import GD.Module1468
import GD.Module1680

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0213.N0521
noncomputable section
open _root_.GD.N0213.N0495 _root_.GD.N0213.N0513
open _root_.GD.N0232.N0719.N0910 _root_.GD.N0051
open _root_.GD.N0230.N0665

variable {k : ℕ}

def d028475 (β w : Fin k → ℝ) : ℝ := ∑ i, (β i)⁻¹ * w i ^ 2

theorem d028476 (β w : Fin k → ℝ) (hβ : ∀ i, 0 < β i) : 0 ≤ _root_.GD.N0213.N0521.d028475 β w :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (inv_nonneg.mpr (hβ i).le) (sq_nonneg _))

theorem d028477 (s r : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) (L : ℝ) (i : Fin k) :
    Integrable (fun β : Fin k → ℝ => (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2)
      (Measure.pi fun j => gammaMeasure (s j + 1) (r j)) := by
  letI (j : Fin k) :=
    isProbabilityMeasure_gammaMeasure (by have := hs j; linarith : 0 < s j + 1) (hr j)
  have hi : Integrable (fun x : ℝ => x⁻¹) (gammaMeasure (s i + 1) (r i)) := by
    simpa only [Real.rpow_neg_one] using
      _root_.GD.N0051.d022782 (by have := hs i; linarith : 0 < s i + 1) (hr i)
        (u := -1) (by have := hs i; linarith)
  apply (integrable_comp_eval hi).norm.mono'
    ((show Measurable (fun β : Fin k → ℝ => (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2)
      by unfold _root_.GD.N0213.N0495.d007174; fun_prop).aestronglyMeasurable)
  filter_upwards with β
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (_root_.GD.N0213.N0519.d007983 L _)

theorem d028478 (β w : Fin k → ℝ) (L : ℝ) :
    _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β w =
      ∑ i, ((β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2) * w i ^ 2 := by
  unfold _root_.GD.N0213.N0521.d028475
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d028479 (s r w : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) (L : ℝ) :
    Integrable (fun β : Fin k → ℝ => _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β w)
      (Measure.pi fun j => gammaMeasure (s j + 1) (r j)) := by
  simp_rw [_root_.GD.N0213.N0521.d028478]
  exact integrable_finsetSum _ (fun i _ => (_root_.GD.N0213.N0521.d028477 s r hs hr L i).mul_const _)

theorem d028480 (s r w : Fin k → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) (L : ℝ) :
    (∫⁻ β : Fin k → ℝ, ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β w)
      ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j))) =
      ENNReal.ofReal (∑ i,
        (∫ β : Fin k → ℝ, (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2
          ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j))) * w i ^ 2) := by
  have hn : ∀ᵐ β : Fin k → ℝ ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j)),
      0 ≤ _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β w := by
    filter_upwards [_root_.GD.N0232.N0719.N0910.d010287
      (shape := fun j => s j + 1) (rate := r)
      (fun j => by have := hs j; linarith) hr] with β hβ
    exact mul_nonneg (sq_nonneg _) (_root_.GD.N0213.N0521.d028476 β w hβ)
  rw [← ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0213.N0521.d028479 s r w hs hr L) hn]
  congr 1
  simp_rw [_root_.GD.N0213.N0521.d028478]
  rw [integral_finsetSum _
    (fun i _ => (_root_.GD.N0213.N0521.d028477 s r hs hr L i).mul_const _)]
  simp only [integral_mul_const]

def d028481 (s t : Fin k → ℝ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else
    4 * (s i ^ 2)⁻¹ / (c * (t i + t j)) +
      4 * (s j ^ 2)⁻¹ / (c * (t i + t j))

theorem d028482 (s t : Fin k → ℝ) (c D : ℝ) :
    (∑ i, ∑ j, if i = j then 0 else
      4 * (D / s i ^ 2 + D / s j ^ 2) / (c * (t i + t j))) =
        D * _root_.GD.N0213.N0521.d028481 s t c := by
  unfold _root_.GD.N0213.N0521.d028481
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem d028483 (s t : Fin k → ℝ) {c : ℝ}
    (ht : ∀ i, 0 < t i) (hc : 0 < c) : 0 ≤ _root_.GD.N0213.N0521.d028481 s t c := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (sq_nonneg _)))
        (mul_pos hc (add_pos (ht i) (ht j))).le)
      (div_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (sq_nonneg _)))
        (mul_pos hc (add_pos (ht i) (ht j))).le)

theorem d028484 {k : ℕ} (s t w : Fin (k + 1) → ℝ) {c L : ℝ}
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hc : 0 < c) (hL : 0 < L)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    let μ := Measure.pi fun i => gammaMeasure (s i + 1) (c * s i * t i)
    (∫⁻ β : Fin (k + 1) → ℝ,
      ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β (_root_.GD.N0230.N0665.d000407 t)) ∂μ) ≤
      (∫⁻ β : Fin (k + 1) → ℝ,
        ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β w) ∂μ) +
      (∫⁻ β : Fin (k + 1) → ℝ,
        ENNReal.ofReal (_root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028481 s t c) ∂μ) := by
  let r : Fin (k + 1) → ℝ := fun i => c * s i * t i
  have hr : ∀ i, 0 < r i := fun i => mul_pos (mul_pos hc (hs i)) (ht i)
  let μ := Measure.pi fun i => gammaMeasure (s i + 1) (r i)
  letI (i : Fin (k + 1)) :=
    isProbabilityMeasure_gammaMeasure (by have := hs i; linarith : 0 < s i + 1) (hr i)
  have hpos : ∀ᵐ β : Fin (k + 1) → ℝ ∂μ, 0 < ∑ j, β j := by
    filter_upwards [_root_.GD.N0232.N0719.N0910.d010287
      (shape := fun j => s j + 1) (rate := r)
      (fun j => by have := hs j; linarith) hr] with β hβ
    exact Finset.sum_pos (fun j _ => hβ j) Finset.univ_nonempty
  have hD := _root_.GD.N0213.N0513.d008014 μ
    (fun β : Fin (k + 1) → ℝ => ∑ j, β j) (by fun_prop) hL hpos
  have hnonneg : ∀ᵐ β : Fin (k + 1) → ℝ ∂μ,
      0 ≤ _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028481 s t c :=
    Filter.Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (_root_.GD.N0213.N0521.d028483 s t ht hc))
  change (∫⁻ β : Fin (k + 1) → ℝ,
      ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β (_root_.GD.N0230.N0665.d000407 t)) ∂μ) ≤ _
  rw [_root_.GD.N0213.N0521.d028480 s r (_root_.GD.N0230.N0665.d000407 t) hs hr L,
    _root_.GD.N0213.N0521.d028480 s r w hs hr L,
    ← ofReal_integral_eq_lintegral_ofReal (hD.mul_const _) hnonneg, integral_mul_const]
  have h := _root_.GD.N0213.N0507.d023104 s t w hs ht hc hL hw0 hw1
  dsimp only at h
  rw [_root_.GD.N0213.N0521.d028482] at h
  refine (ENNReal.ofReal_le_ofReal (sub_le_iff_le_add.mp h)).trans ?_
  rw [add_comm]
  exact ENNReal.ofReal_add_le

end
end GD.N0213.N0521

#print axioms _root_.GD.N0213.N0521.d028480
#print axioms _root_.GD.N0213.N0521.d028484
