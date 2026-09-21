import GD.Module0203
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic











open Filter MeasureTheory Topology

namespace GD.N0232.N0720

noncomputable section


def d002827
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (evidence current : X → ℝ) : ℝ :=
  ∫ x, current x ^ 2 / evidence x ∂μ



theorem d002828
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (evidence : ℕ → X → ℝ) (current : X → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun x ↦ current x ^ 2 / evidence n x) μ)
    (hfloor : ∀ n, ∀ᵐ x ∂μ, 1 ≤ evidence n x)
    (hgrowth : ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ evidence n x) atTop atTop)
    (hcurrent : Integrable (fun x ↦ current x ^ 2) μ) :
    Tendsto
      (fun n ↦ ∫ x, current x ^ 2 / evidence n x ∂μ)
      atTop (𝓝 0) := by
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ current x ^ 2 / evidence n x) atTop (𝓝 0) := by
    filter_upwards [hgrowth] with x hx
    exact hx.const_div_atTop (current x ^ 2)
  have hdom : ∀ n, ∀ᵐ x ∂μ,
      ‖current x ^ 2 / evidence n x‖ ≤ current x ^ 2 := by
    intro n
    filter_upwards [hfloor n] with x hx
    have he0 : 0 ≤ evidence n x := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) he0)]
    exact div_le_self (sq_nonneg _) hx
  simpa using tendsto_integral_of_dominated_convergence
    (fun x ↦ current x ^ 2) hmeas hcurrent hdom hlim



theorem d002829
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (centralEvidence addedEvidence centralCurrent addedCurrent : X → ℝ)
    (hcentralEvidence : ∀ᵐ x ∂μ, 0 < centralEvidence x)
    (haddedEvidence : ∀ᵐ x ∂μ, 0 ≤ addedEvidence x)
    (hcentralIntegrable : Integrable
      (fun x ↦ centralCurrent x ^ 2 / centralEvidence x) μ)
    (hshieldIntegrable : Integrable
      (fun x ↦ addedCurrent x ^ 2 / centralEvidence x) μ) :
    _root_.GD.N0232.N0720.d002827 μ
        (fun x ↦ centralEvidence x + addedEvidence x)
        (fun x ↦ centralCurrent x + addedCurrent x) ≤
      2 * _root_.GD.N0232.N0720.d002827 μ centralEvidence centralCurrent +
        2 * ∫ x, addedCurrent x ^ 2 / centralEvidence x ∂μ := by
  unfold _root_.GD.N0232.N0720.d002827
  have hupperIntegrable : Integrable
      (fun x ↦ 2 * (centralCurrent x ^ 2 / centralEvidence x) +
        2 * (addedCurrent x ^ 2 / centralEvidence x)) μ :=
    (hcentralIntegrable.const_mul 2).add (hshieldIntegrable.const_mul 2)
  have hnonneg : ∀ᵐ x ∂μ,
      0 ≤ (centralCurrent x + addedCurrent x) ^ 2 /
        (centralEvidence x + addedEvidence x) := by
    filter_upwards [hcentralEvidence, haddedEvidence] with x hcx hax
    exact div_nonneg (sq_nonneg _) (add_nonneg hcx.le hax)
  calc
    (∫ x, (centralCurrent x + addedCurrent x) ^ 2 /
        (centralEvidence x + addedEvidence x) ∂μ) ≤
      ∫ x, 2 * (centralCurrent x ^ 2 / centralEvidence x) +
        2 * (addedCurrent x ^ 2 / centralEvidence x) ∂μ := by
          apply integral_mono_of_nonneg hnonneg hupperIntegrable
          filter_upwards [hcentralEvidence, haddedEvidence] with x hcx hax
          have hsum : 0 < centralEvidence x + addedEvidence x :=
            add_pos_of_pos_of_nonneg hcx hax
          have hsq : (centralCurrent x + addedCurrent x) ^ 2 ≤
              2 * centralCurrent x ^ 2 + 2 * addedCurrent x ^ 2 := by
            nlinarith [sq_nonneg (centralCurrent x - addedCurrent x)]
          calc
            (centralCurrent x + addedCurrent x) ^ 2 /
                (centralEvidence x + addedEvidence x) ≤
              (2 * centralCurrent x ^ 2 + 2 * addedCurrent x ^ 2) /
                (centralEvidence x + addedEvidence x) :=
              div_le_div_of_nonneg_right hsq hsum.le
            _ ≤ (2 * centralCurrent x ^ 2 + 2 * addedCurrent x ^ 2) /
                centralEvidence x := by
              exact div_le_div_of_nonneg_left
                (by positivity) hcx (le_add_of_nonneg_right hax)
            _ = 2 * (centralCurrent x ^ 2 / centralEvidence x) +
                2 * (addedCurrent x ^ 2 / centralEvidence x) := by ring
    _ = 2 * (∫ x, centralCurrent x ^ 2 / centralEvidence x ∂μ) +
        2 * ∫ x, addedCurrent x ^ 2 / centralEvidence x ∂μ := by
      rw [integral_add (hcentralIntegrable.const_mul 2)
        (hshieldIntegrable.const_mul 2), integral_const_mul,
        integral_const_mul]





theorem d002830
    (centralAction : ℕ → ℝ)
    (shield combinedAction : ℕ → ℕ → ℝ)
    (hcentral : Tendsto centralAction atTop (𝓝 0))
    (hshield : ∀ k, Tendsto (shield k) atTop (𝓝 0))
    (hcombinedNonneg : ∀ k n, 0 ≤ combinedAction k n)
    (hcombined : ∀ k n,
      combinedAction k n ≤ 2 * centralAction n + 2 * shield k n) :
    ∃ select : ℕ → ℕ,
      (∀ k, k ≤ select k) ∧
      Tendsto (fun k ↦ combinedAction k (select k)) atTop (𝓝 0) := by
  have hexists : ∀ k : ℕ, ∃ n : ℕ,
      k ≤ n ∧
      |centralAction n| < 1 / ((k : ℝ) + 1) ∧
      |shield k n| < 1 / ((k : ℝ) + 1) := by
    intro k
    have heps : 0 < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hcentral)
      _ heps
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp (hshield k))
      _ heps
    refine ⟨max k (max N₁ N₂), le_max_left _ _, ?_, ?_⟩
    · simpa [Real.dist_eq] using hN₁ _
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · simpa [Real.dist_eq] using hN₂ _
        (le_trans (le_max_right _ _) (le_max_right _ _))
  choose select hselect using hexists
  refine ⟨select, fun k ↦ (hselect k).1, ?_⟩
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k ↦ hcombinedNonneg k (select k)
  · apply Filter.Eventually.of_forall
    intro k
    have hcLe : centralAction (select k) ≤ 1 / ((k : ℝ) + 1) :=
      le_trans (le_abs_self _) (hselect k).2.1.le
    have hsLe : shield k (select k) ≤ 1 / ((k : ℝ) + 1) :=
      le_trans (le_abs_self _) (hselect k).2.2.le
    calc
      combinedAction k (select k) ≤
          2 * centralAction (select k) + 2 * shield k (select k) :=
        hcombined k (select k)
      _ ≤ 2 * (1 / ((k : ℝ) + 1)) +
          2 * (1 / ((k : ℝ) + 1)) := by gcongr
      _ = 4 / ((k : ℝ) + 1) := by ring
  · simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4

end

end GD.N0232.N0720

#print axioms _root_.GD.N0232.N0720.d002828
#print axioms _root_.GD.N0232.N0720.d002829
#print axioms _root_.GD.N0232.N0720.d002830
