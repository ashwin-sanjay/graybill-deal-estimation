import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set Function
open scoped BigOperators

namespace GD.N0025
noncomputable section



theorem d005142
    {ι : Type*} [Fintype ι] (a t : ι → ℝ) (q : ℝ)
    (hA : 0 < ∑ i, a i)
    (hdisc : (∑ i, a i * t i) ^ 2 + (∑ i, a i) * q ≤
      (∑ i, a i) * (∑ i, a i * t i ^ 2)) (x : ℝ) :
    q ≤ ∑ i, a i * (x - t i) ^ 2 := by
  have heq : (∑ i, a i * (x - t i) ^ 2) =
      x ^ 2 * (∑ i, a i) - 2 * x * (∑ i, a i * t i) +
        (∑ i, a i * t i ^ 2) := by
    calc
      _ = ∑ i, (x ^ 2 * a i - 2 * x * (a i * t i) + a i * t i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  have hs := sq_nonneg ((∑ i, a i) * x - ∑ i, a i * t i)
  apply (mul_le_mul_iff_right₀ hA).mp
  rw [heq]
  nlinarith


theorem d005143
    {ι : Type*} [Fintype ι] (a n : ι → ℕ) (D N q : ℕ)
    (hD : 0 < D) (hN : 0 < N) (hA : 0 < ∑ i, a i)
    (hdisc : (∑ i, a i * n i) ^ 2 + (∑ i, a i) * q ≤
      (∑ i, a i) * (∑ i, a i * n i ^ 2)) (x : ℝ) :
    (q : ℝ) / ((D : ℝ) * (N : ℝ) ^ 2) ≤
      ∑ i, ((a i : ℝ) / D) * (x - (n i : ℝ) / N) ^ 2 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hAr : (0 : ℝ) < ∑ i, (a i : ℝ) := by exact_mod_cast hA
  have hdr : (∑ i, (a i : ℝ) * n i) ^ 2 + (∑ i, (a i : ℝ)) * q ≤
      (∑ i, (a i : ℝ)) * (∑ i, (a i : ℝ) * (n i : ℝ) ^ 2) := by
    exact_mod_cast hdisc
  have hx := _root_.GD.N0025.d005142
    (fun i => (a i : ℝ)) (fun i => (n i : ℝ)) q hAr hdr ((N : ℝ) * x)
  calc
    _ ≤ (∑ i, (a i : ℝ) * ((N : ℝ) * x - n i) ^ 2) /
        ((D : ℝ) * (N : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hx (mul_nonneg hDr.le (sq_nonneg _))
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [ne_of_gt hDr, ne_of_gt hNr]



theorem d005144
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t d : ι → ℝ) (a : κ → ι → ℝ) (q b : κ → ℝ)
    (hb : ∀ c, 0 ≤ b c)
    (hd : ∀ i, (∑ c, b c * a c i) ≤ d i)
    (hq : ∀ c x, q c ≤ ∑ i, a c i * (x - t i) ^ 2) (x : ℝ) :
    (∑ c, b c * q c) ≤ ∑ i, d i * (x - t i) ^ 2 := by
  calc
    _ ≤ ∑ c, b c * (∑ i, a c i * (x - t i) ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (hq c x) (hb c)
    _ = ∑ i, (∑ c, b c * a c i) * (x - t i) ^ 2 := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hd i) (sq_nonneg _)



theorem d005145
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (μ : Measure Ω) (t : ι → ℝ) (d : ι → Ω → ℝ) (g : Ω → ℝ)
    (a : κ → ι → ℝ) (q : κ → ℝ) (b : κ → Ω → ℝ) (v : κ → ℝ)
    (hb : ∀ c, Integrable (b c) μ)
    (hmoment : ∀ c, ∫ z, b c z ∂μ = v c)
    (hbn : ∀ᵐ z ∂μ, ∀ c, 0 ≤ b c z)
    (hd : ∀ᵐ z ∂μ, ∀ i, (∑ c, b c z * a c i) ≤ d i z)
    (hq : ∀ c x, q c ≤ ∑ i, a c i * (x - t i) ^ 2)
    (hF : Integrable (fun z => ∑ i, d i z * (g z - t i) ^ 2) μ) :
    (∑ c, v c * q c) ≤ ∫ z, ∑ i, d i z * (g z - t i) ^ 2 ∂μ := by
  have hi : Integrable (fun z => ∑ c, b c z * q c) μ :=
    integrable_finsetSum _ (fun c _ => (hb c).mul_const _)
  have heq : (∫ z, ∑ c, b c z * q c ∂μ) = ∑ c, v c * q c := by
    rw [integral_finsetSum _ (fun c _ => (hb c).mul_const _)]
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_mul_const, hmoment]
  rw [← heq]
  apply integral_mono_ae hi hF
  filter_upwards [hbn, hd] with z hbnz hdz
  exact _root_.GD.N0025.d005144 t (fun i => d i z) a q (fun c => b c z)
    hbnz hdz hq (g z)



theorem d005146
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (E : κ → Set Ω) (F : Ω → ℝ) (L : κ → ℝ)
    (hE : ∀ c, MeasurableSet (E c))
    (hdis : Pairwise (Disjoint on E))
    (hF : Integrable F μ) (hn : 0 ≤ᵐ[μ] F)
    (hL : ∀ c, L c ≤ ∫ z in E c, F z ∂μ) :
    (∑ c, L c) ≤ ∫ z, F z ∂μ := by
  calc
    _ ≤ ∑ c, ∫ z in E c, F z ∂μ := Finset.sum_le_sum (fun c _ => hL c)
    _ = ∫ z in ⋃ c, E c, F z ∂μ :=
      (integral_iUnion_fintype hE hdis (fun _ => hF.integrableOn)).symm
    _ ≤ _ := setIntegral_le_integral hF hn

end
end GD.N0025

#print axioms _root_.GD.N0025.d005142
#print axioms _root_.GD.N0025.d005143
#print axioms _root_.GD.N0025.d005144
#print axioms _root_.GD.N0025.d005145
#print axioms _root_.GD.N0025.d005146
