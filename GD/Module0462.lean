import GD.Module0460
import Mathlib.Probability.Independence.Integration




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1744
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem d007163 (a : ι → ℝ) (n : ι → ℕ) (t : ℝ) :
    (∏ i, a i ^ n i * Real.exp (-(t * a i))) =
      (∏ i, a i ^ n i) * Real.exp (-(t * ∑ i, a i)) := by
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]

theorem d007164 (a : ι → ℝ) (i : ι) (m : ℕ) :
    (∏ k, a k ^ (if k = i then m else 0)) = a i ^ m := by
  calc
    _ = a i ^ (if i = i then m else 0) :=
      Finset.prod_eq_single i (fun k _ hk => by simp [hk]) (by simp)
    _ = _ := by simp

theorem d007165 (a : ι → ℝ) (i j : ι) :
    (∏ k, a k ^ ((if k = i then 1 else 0) + (if k = j then 1 else 0))) =
      a i * a j := by
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib, _root_.GD.N0106.N0428.N0770.N1744.d007164, _root_.GD.N0106.N0428.N0770.N1744.d007164]
  simp

theorem d007166 (b : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (∏ k, b k) = b i * b j * ∏ k ∈ (Finset.univ.erase i).erase j, b k := by
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) b
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {A : ι → Ω → ℝ}


theorem d007167 (hA : ∀ i, Measurable (A i))
    (ha : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ A i ω) {t : ℝ} (ht : 0 < t) (n : ι → ℕ) :
    Integrable (fun ω => ∏ i, A i ω ^ n i * Real.exp (-(t * A i ω))) μ := by
  have hm : Measurable (fun ω => ∏ i, A i ω ^ n i * Real.exp (-(t * A i ω))) := by
    fun_prop
  apply (integrable_const (∏ i, ((n i).factorial : ℝ) / t ^ n i)).mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  have hp : ∀ i, 0 ≤ A i ω ^ n i * Real.exp (-(t * A i ω)) :=
    fun i => mul_nonneg (pow_nonneg (hω i) _) (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ => hp i))]
  exact Finset.prod_le_prod (fun i _ => hp i)
    (fun i _ => _root_.GD.N0106.N0428.N0770.N1744.d007145 (hω i) ht (n i))



theorem d007168 (hA : ∀ i, Measurable (A i))
    (ha : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ A i ω) (hI : iIndepFun A μ)
    {t : ℝ} (ht : 0 < t) (n : ι → ℕ) :
    Integrable (fun ω => (∏ i, A i ω ^ n i) * Real.exp (-(t * ∑ i, A i ω))) μ ∧
      (∫ ω, (∏ i, A i ω ^ n i) * Real.exp (-(t * ∑ i, A i ω)) ∂μ) =
        ∏ i, ∫ ω, A i ω ^ n i * Real.exp (-(t * A i ω)) ∂μ := by
  have hi := _root_.GD.N0106.N0428.N0770.N1744.d007167 hA ha ht n
  have he := hI.integral_fun_prod_comp (fun i => (hA i).aemeasurable)
    (f := fun i (x : ℝ) => x ^ n i * Real.exp (-(t * x)))
    (fun i => (by fun_prop : Measurable (fun x : ℝ => x ^ n i * Real.exp (-(t * x)))).aestronglyMeasurable)
  simp_rw [_root_.GD.N0106.N0428.N0770.N1744.d007163] at hi he
  exact ⟨hi, he⟩

theorem d007169 (hA : ∀ i, Measurable (A i))
    (ha : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ A i ω) (hI : iIndepFun A μ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => Real.exp (-(t * ∑ i, A i ω))) μ ∧
      (∫ ω, Real.exp (-(t * ∑ i, A i ω)) ∂μ) =
        ∏ i, ∫ ω, Real.exp (-(t * A i ω)) ∂μ := by
  simpa only [pow_zero, Finset.prod_const_one, one_mul] using
    _root_.GD.N0106.N0428.N0770.N1744.d007168 hA ha hI ht (fun _ => 0)

theorem d007170 (hA : ∀ i, Measurable (A i))
    (ha : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ A i ω) (hI : iIndepFun A μ)
    {t : ℝ} (ht : 0 < t) (i : ι) (m : ℕ) :
    Integrable (fun ω => A i ω ^ m * Real.exp (-(t * ∑ k, A k ω))) μ ∧
      (∫ ω, A i ω ^ m * Real.exp (-(t * ∑ k, A k ω)) ∂μ) =
        (∫ ω, A i ω ^ m * Real.exp (-(t * A i ω)) ∂μ) *
          ∏ k ∈ Finset.univ.erase i, ∫ ω, Real.exp (-(t * A k ω)) ∂μ := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1744.d007168 hA ha hI ht
    (fun k => if k = i then m else 0)
  simp_rw [_root_.GD.N0106.N0428.N0770.N1744.d007164] at hi he
  refine ⟨hi, he.trans ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k => ∫ ω, A k ω ^ (if k = i then m else 0) * Real.exp (-(t * A k ω)) ∂μ)
    (Finset.mem_univ i)]
  simp only [if_pos (rfl : i = i)]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp [(Finset.mem_erase.mp hk).1]

theorem d007171 (hA : ∀ i, Measurable (A i))
    (ha : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ A i ω) (hI : iIndepFun A μ)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    Integrable (fun ω => A i ω * Real.exp (-(t * ∑ k, A k ω))) μ ∧
      (∫ ω, A i ω * Real.exp (-(t * ∑ k, A k ω)) ∂μ) =
        (∫ ω, A i ω * Real.exp (-(t * A i ω)) ∂μ) *
          ∏ k ∈ Finset.univ.erase i, ∫ ω, Real.exp (-(t * A k ω)) ∂μ := by
  simpa only [pow_one] using _root_.GD.N0106.N0428.N0770.N1744.d007170 hA ha hI ht i 1

theorem d007172 (hA : ∀ i, Measurable (A i))
    (ha : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ A i ω) (hI : iIndepFun A μ)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    Integrable (fun ω => A i ω ^ 2 * Real.exp (-(t * ∑ k, A k ω))) μ ∧
      (∫ ω, A i ω ^ 2 * Real.exp (-(t * ∑ k, A k ω)) ∂μ) =
        (∫ ω, A i ω ^ 2 * Real.exp (-(t * A i ω)) ∂μ) *
          ∏ k ∈ Finset.univ.erase i, ∫ ω, Real.exp (-(t * A k ω)) ∂μ :=
  _root_.GD.N0106.N0428.N0770.N1744.d007170 hA ha hI ht i 2

theorem d007173 (hA : ∀ i, Measurable (A i))
    (ha : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ A i ω) (hI : iIndepFun A μ)
    {t : ℝ} (ht : 0 < t) {i j : ι} (hij : i ≠ j) :
    Integrable (fun ω => A i ω * A j ω * Real.exp (-(t * ∑ k, A k ω))) μ ∧
      (∫ ω, A i ω * A j ω * Real.exp (-(t * ∑ k, A k ω)) ∂μ) =
        (∫ ω, A i ω * Real.exp (-(t * A i ω)) ∂μ) *
          (∫ ω, A j ω * Real.exp (-(t * A j ω)) ∂μ) *
            ∏ k ∈ (Finset.univ.erase i).erase j, ∫ ω, Real.exp (-(t * A k ω)) ∂μ := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1744.d007168 hA ha hI ht
    (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0))
  simp_rw [_root_.GD.N0106.N0428.N0770.N1744.d007165] at hi he
  refine ⟨hi, he.trans ?_⟩
  rw [_root_.GD.N0106.N0428.N0770.N1744.d007166 _ hij]
  simp only [if_pos (rfl : i = i), if_pos (rfl : j = j), ite_true, if_neg hij, if_neg hij.symm,
    add_zero, zero_add, pow_one]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  simp [hkj, hki]

end
end GD.N0106.N0428.N0770.N1744

#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007167
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007168
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007169
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007171
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007172
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007173
