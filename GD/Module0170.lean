import Mathlib

set_option warningAsError true
set_option autoImplicit false
set_option linter.unusedSectionVars false










open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0720.N1232

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem d002002
    (a target : ι → ℝ) (h p : ℝ)
    (hnormal : (∑ i, a i * target i) = p * ∑ i, a i) :
    (∑ i, a i * (h - target i) ^ 2) -
      (∑ i, a i * (p - target i) ^ 2) =
        (∑ i, a i) * (h - p) ^ 2 := by
  have hexpand (x : ℝ) :
      (∑ i, a i * (x - target i) ^ 2) =
        (∑ i, a i) * x ^ 2 - 2 * x * (∑ i, a i * target i) +
          ∑ i, a i * target i ^ 2 := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexpand h, hexpand p, hnormal]
  ring

theorem d002003 {x t : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (x - t) ^ 2 ≤ 1 := by
  have hlow : -1 ≤ x - t := by linarith [hx.1, ht.2]
  have hupp : x - t ≤ 1 := by linarith [hx.2, ht.1]
  nlinarith [mul_nonneg (sub_nonneg.mpr hupp) (by linarith : 0 ≤ 1 + (x - t))]

theorem d002004
    (μ : Measure Ω) (density h : Ω → ℝ) (t : ℝ)
    (hd : Integrable density μ) (hd0 : ∀ᵐ z ∂μ, 0 ≤ density z)
    (hh : AEStronglyMeasurable h μ)
    (hb : ∀ᵐ z ∂μ, h z ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z ↦ density z * (h z - t) ^ 2) μ := by
  apply hd.mono' (hd.aestronglyMeasurable.mul
    ((hh.sub aestronglyMeasurable_const).pow 2))
  filter_upwards [hd0, hb] with z hdz hbz
  change ‖density z * (h z - t) ^ 2‖ ≤ density z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdz (sq_nonneg _))]
  exact mul_le_of_le_one_right hdz (_root_.GD.N0232.N0720.N1232.d002003 hbz ht)

theorem d002005
    (μ : Measure Ω) (density h p : Ω → ℝ)
    (hd : Integrable density μ) (hd0 : ∀ᵐ z ∂μ, 0 ≤ density z)
    (hh : AEStronglyMeasurable h μ) (hp : AEStronglyMeasurable p μ)
    (hb : ∀ᵐ z ∂μ, h z ∈ Icc (0 : ℝ) 1)
    (pb : ∀ᵐ z ∂μ, p z ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z ↦ density z * (h z - p z) ^ 2) μ := by
  apply hd.mono' (hd.aestronglyMeasurable.mul ((hh.sub hp).pow 2))
  filter_upwards [hd0, hb, pb] with z hdz hbz pbz
  change ‖density z * (h z - p z) ^ 2‖ ≤ density z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdz (sq_nonneg _))]
  exact mul_le_of_le_one_right hdz (_root_.GD.N0232.N0720.N1232.d002003 hbz pbz)



theorem d002006
    (μ : Measure Ω) (density : ι → Ω → ℝ) (a target : ι → ℝ)
    (h p : Ω → ℝ)
    (hd : ∀ i, Integrable (density i) μ)
    (hd0 : ∀ i, ∀ᵐ z ∂μ, 0 ≤ density i z)
    (hh : AEStronglyMeasurable h μ) (hp : AEStronglyMeasurable p μ)
    (hb : ∀ᵐ z ∂μ, h z ∈ Icc (0 : ℝ) 1)
    (pb : ∀ᵐ z ∂μ, p z ∈ Icc (0 : ℝ) 1)
    (ht : ∀ i, target i ∈ Icc (0 : ℝ) 1)
    (hnormal : ∀ᵐ z ∂μ,
      (∑ i, (a i * density i z) * target i) =
        p z * ∑ i, a i * density i z) :
    (∑ i, a i * ∫ z, density i z * (h z - target i) ^ 2 ∂μ) -
      (∑ i, a i * ∫ z, density i z * (p z - target i) ^ 2 ∂μ) =
        ∫ z, (∑ i, a i * density i z) * (h z - p z) ^ 2 ∂μ := by
  have hiH (i : ι) : Integrable
      (fun z ↦ a i * density i z * (h z - target i) ^ 2) μ := by
    simpa only [mul_assoc] using
      (_root_.GD.N0232.N0720.N1232.d002004 μ (density i) h (target i)
        (hd i) (hd0 i) hh hb (ht i)).const_mul (a i)
  have hiP (i : ι) : Integrable
      (fun z ↦ a i * density i z * (p z - target i) ^ 2) μ := by
    simpa only [mul_assoc] using
      (_root_.GD.N0232.N0720.N1232.d002004 μ (density i) p (target i)
        (hd i) (hd0 i) hp pb (ht i)).const_mul (a i)
  have hH : (∑ i, a i * ∫ z, density i z * (h z - target i) ^ 2 ∂μ) =
      ∫ z, ∑ i, a i * density i z * (h z - target i) ^ 2 ∂μ := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hiH i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all μ fun _ ↦ by ring
  have hP : (∑ i, a i * ∫ z, density i z * (p z - target i) ^ 2 ∂μ) =
      ∫ z, ∑ i, a i * density i z * (p z - target i) ^ 2 ∂μ := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hiP i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all μ fun _ ↦ by ring
  rw [hH, hP, ← integral_sub (integrable_finsetSum Finset.univ (fun i _ ↦ hiH i))
    (integrable_finsetSum Finset.univ (fun i _ ↦ hiP i))]
  apply integral_congr_ae
  filter_upwards [hnormal] with z hz
  exact _root_.GD.N0232.N0720.N1232.d002002 (fun i ↦ a i * density i z) target (h z) (p z) hz



theorem d002007
    (μ : Measure Ω) (density : ι → Ω → ℝ) (a target : ι → ℝ)
    (h p : Ω → ℝ) (i₀ : ι) (ha₀ : a i₀ = 1) (ha : ∀ i, 0 ≤ a i)
    (hd : ∀ i, Integrable (density i) μ)
    (hd0 : ∀ i, ∀ᵐ z ∂μ, 0 ≤ density i z)
    (hh : AEStronglyMeasurable h μ) (hp : AEStronglyMeasurable p μ)
    (hb : ∀ᵐ z ∂μ, h z ∈ Icc (0 : ℝ) 1)
    (pb : ∀ᵐ z ∂μ, p z ∈ Icc (0 : ℝ) 1)
    (ht : ∀ i, target i ∈ Icc (0 : ℝ) 1)
    (hnormal : ∀ᵐ z ∂μ,
      (∑ i, (a i * density i z) * target i) =
        p z * ∑ i, a i * density i z) :
    (∫ z, density i₀ z * (h z - p z) ^ 2 ∂μ) ≤
      (∑ i, a i * ∫ z, density i z * (h z - target i) ^ 2 ∂μ) -
        (∑ i, a i * ∫ z, density i z * (p z - target i) ^ 2 ∂μ) := by
  classical
  rw [_root_.GD.N0232.N0720.N1232.d002006 μ density a target h p hd hd0 hh hp hb pb ht hnormal]
  have hdall : ∀ᵐ z ∂μ, ∀ i, 0 ≤ density i z :=
    (ae_all_iff).mpr hd0
  have hmass : Integrable (fun z ↦ ∑ i, a i * density i z) μ :=
    integrable_finsetSum Finset.univ fun i _ ↦ (hd i).const_mul (a i)
  have hmass0 : ∀ᵐ z ∂μ, 0 ≤ ∑ i, a i * density i z := by
    filter_upwards [hdall] with z hz
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (ha i) (hz i)
  apply integral_mono_ae
    (_root_.GD.N0232.N0720.N1232.d002005 μ (density i₀) h p (hd i₀) (hd0 i₀) hh hp hb pb)
    (_root_.GD.N0232.N0720.N1232.d002005 μ _ h p hmass hmass0 hh hp hb pb)
  filter_upwards [hdall] with z hz
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    density i₀ z = a i₀ * density i₀ z := by rw [ha₀, one_mul]
    _ ≤ ∑ i, a i * density i z :=
      Finset.single_le_sum (fun i _ ↦ mul_nonneg (ha i) (hz i)) (Finset.mem_univ i₀)

end
end GD.N0232.N0720.N1232

#print axioms _root_.GD.N0232.N0720.N1232.d002007
