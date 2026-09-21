import Mathlib.Analysis.SpecificLimits.Normed






















open Filter Topology

namespace GD
namespace N0232
namespace N0719
namespace N0948

noncomputable section







theorem d001779
    {p b : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b)
    (eventMass eventDeviation candidateRisk : ℕ → ℝ)
    (hmass : ∀ n, p ≤ eventMass n)
    (hdeviation : ∀ n,
      b / ((n + 1 : ℕ) : ℝ) ≤ eventDeviation n)
    (hdeviationNonneg : ∀ n, 0 ≤ eventDeviation n)
    (hrisk : ∀ n,
      eventMass n * eventDeviation n ^ 2 ≤ candidateRisk n) :
    ∀ n, p * b ^ 2 / (((n + 1 : ℕ) : ℝ) ^ 2) ≤
      candidateRisk n := by
  intro n
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdevSq :
      (b / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ eventDeviation n ^ 2 :=
    sq_le_sq₀ (by positivity) (hdeviationNonneg n) |>.2 (hdeviation n)
  have hmassNonneg : 0 ≤ eventMass n := hp.trans (hmass n)
  calc
    p * b ^ 2 / (((n + 1 : ℕ) : ℝ) ^ 2) =
        p * (b / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
          field_simp [hn.ne']
    _ ≤ eventMass n * (b / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (hmass n) (sq_nonneg _)
    _ ≤ eventMass n * eventDeviation n ^ 2 := by
      exact mul_le_mul_of_nonneg_left hdevSq hmassNonneg
    _ ≤ candidateRisk n := hrisk n




theorem d001780
    {theta : ℝ} (htheta : 0 ≤ theta) (hthetaOne : theta < 1) :
    Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ 2 * theta ^ (n + 1))
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun m : ℕ ↦ (m : ℝ) ^ 2 * theta ^ m) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 htheta hthetaOne
  change Tendsto
    ((fun m : ℕ ↦ (m : ℝ) ^ 2 * theta ^ m) ∘ fun n ↦ n + 1)
      atTop (nhds 0)
  exact hbase.comp (tendsto_add_atTop_nat 1)






theorem d001781
    {theta c C : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hc : 0 < c)
    (candidateRisk baselineRisk : ℕ → ℝ)
    (hcandidate : ∀ n,
      c / (((n + 1 : ℕ) : ℝ) ^ 2) ≤ candidateRisk n)
    (hbaseline : ∀ n,
      baselineRisk n ≤ C * theta ^ (n + 1)) :
    ∀ᶠ n in atTop, baselineRisk n < candidateRisk n := by
  have hscaled : Tendsto
      (fun n : ℕ ↦
        C * (((n + 1 : ℕ) : ℝ) ^ 2 * theta ^ (n + 1)))
      atTop (nhds 0) :=
    by simpa using
      (_root_.GD.N0232.N0719.N0948.d001780 htheta hthetaOne).const_mul C
  have hsmall : ∀ᶠ n in atTop,
      C * (((n + 1 : ℕ) : ℝ) ^ 2 * theta ^ (n + 1)) < c :=
    (tendsto_order.1 hscaled).2 c hc
  filter_upwards [hsmall] with n hn
  have hsucc : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hgeom :
      C * theta ^ (n + 1) < c / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    apply (lt_div_iff₀ hsucc).2
    nlinarith
  exact (hbaseline n).trans_lt (hgeom.trans_le (hcandidate n))



theorem d001782
    {theta c C : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hc : 0 < c)
    (candidateRisk baselineRisk : ℕ → ℝ)
    (hcandidate : ∀ n,
      c / (((n + 1 : ℕ) : ℝ) ^ 2) ≤ candidateRisk n)
    (hbaseline : ∀ n,
      baselineRisk n ≤ C * theta ^ (n + 1)) :
    ∃ n, baselineRisk n < candidateRisk n := by
  exact (_root_.GD.N0232.N0719.N0948.d001781 htheta hthetaOne hc
    candidateRisk baselineRisk hcandidate hbaseline).exists



theorem d001783
    {theta c C : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hc : 0 < c)
    (candidateRisk baselineRisk : ℕ → ℝ)
    (hcandidate : ∀ n,
      c / (((n + 1 : ℕ) : ℝ) ^ 2) ≤ candidateRisk n)
    (hbaseline : ∀ n,
      baselineRisk n ≤ C * theta ^ (n + 1)) :
    ¬ ∀ n, candidateRisk n ≤ baselineRisk n := by
  rintro hall
  obtain ⟨n, hn⟩ := _root_.GD.N0232.N0719.N0948.d001782
    htheta hthetaOne hc candidateRisk baselineRisk hcandidate hbaseline
  exact (not_lt_of_ge (hall n)) hn




theorem d001784
    {theta p b C : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hp : 0 < p) (hb : 0 < b)
    (eventMass eventDeviation candidateRisk baselineRisk : ℕ → ℝ)
    (hmass : ∀ n, p ≤ eventMass n)
    (hdeviation : ∀ n,
      b / ((n + 1 : ℕ) : ℝ) ≤ eventDeviation n)
    (hdeviationNonneg : ∀ n, 0 ≤ eventDeviation n)
    (hrisk : ∀ n,
      eventMass n * eventDeviation n ^ 2 ≤ candidateRisk n)
    (hbaseline : ∀ n,
      baselineRisk n ≤ C * theta ^ (n + 1)) :
    ¬ ∀ n, candidateRisk n ≤ baselineRisk n := by
  apply _root_.GD.N0232.N0719.N0948.d001783
    htheta hthetaOne (mul_pos hp (sq_pos_of_pos hb))
      candidateRisk baselineRisk
  · exact _root_.GD.N0232.N0719.N0948.d001779 hp.le hb.le
      eventMass eventDeviation candidateRisk hmass hdeviation
        hdeviationNonneg hrisk
  · exact hbaseline

end

end N0948
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0948.d001781
#print axioms _root_.GD.N0232.N0719.N0948.d001783
#print axioms _root_.GD.N0232.N0719.N0948.d001784
