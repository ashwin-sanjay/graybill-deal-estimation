import GD.Module0157
















open Filter Topology

namespace GD
namespace N0232
namespace N0719
namespace N0949

noncomputable section



theorem d001785
    (degree : ℕ) {theta : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1) :
    Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ degree * theta ^ (n + 1))
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun m : ℕ ↦ (m : ℝ) ^ degree * theta ^ m) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one degree htheta hthetaOne
  change Tendsto
    ((fun m : ℕ ↦ (m : ℝ) ^ degree * theta ^ m) ∘ fun n ↦ n + 1)
      atTop (nhds 0)
  exact hbase.comp (tendsto_add_atTop_nat 1)



theorem d001786
    (degree : ℕ) {theta c C : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hc : 0 < c)
    (candidateRisk baselineRisk : ℕ → ℝ)
    (hcandidate : ∀ n,
      c / (((n + 1 : ℕ) : ℝ) ^ degree) ≤ candidateRisk n)
    (hbaseline : ∀ n,
      baselineRisk n ≤ C * theta ^ (n + 1)) :
    ∀ᶠ n in atTop, baselineRisk n < candidateRisk n := by
  have hscaled : Tendsto
      (fun n : ℕ ↦
        C * (((n + 1 : ℕ) : ℝ) ^ degree * theta ^ (n + 1)))
      atTop (nhds 0) := by
    simpa using
      (_root_.GD.N0232.N0719.N0949.d001785 degree htheta hthetaOne).const_mul C
  have hsmall : ∀ᶠ n in atTop,
      C * (((n + 1 : ℕ) : ℝ) ^ degree * theta ^ (n + 1)) < c :=
    (tendsto_order.1 hscaled).2 c hc
  filter_upwards [hsmall] with n hn
  have hsucc : 0 < (((n + 1 : ℕ) : ℝ) ^ degree) := by positivity
  have hgeom :
      C * theta ^ (n + 1) < c / (((n + 1 : ℕ) : ℝ) ^ degree) := by
    apply (lt_div_iff₀ hsucc).2
    calc
      C * theta ^ (n + 1) * (((n + 1 : ℕ) : ℝ) ^ degree) =
          C * (((n + 1 : ℕ) : ℝ) ^ degree * theta ^ (n + 1)) := by ring
      _ < c := hn
  exact (hbaseline n).trans_lt (hgeom.trans_le (hcandidate n))



theorem d001787
    (degree : ℕ) {theta c C : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hc : 0 < c)
    (candidateRisk baselineRisk : ℕ → ℝ)
    (hcandidate : ∀ n,
      c / (((n + 1 : ℕ) : ℝ) ^ degree) ≤ candidateRisk n)
    (hbaseline : ∀ n,
      baselineRisk n ≤ C * theta ^ (n + 1)) :
    ¬ ∀ n, candidateRisk n ≤ baselineRisk n := by
  intro hall
  have heventually := _root_.GD.N0232.N0719.N0949.d001786 degree
    htheta hthetaOne hc candidateRisk baselineRisk hcandidate hbaseline
  obtain ⟨n, hn⟩ := heventually.exists
  exact (not_lt_of_ge (hall n)) hn



theorem d001788
    (degree : ℕ) {p b : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b)
    (eventMass eventDeviation candidateRisk : ℕ → ℝ)
    (hmass : ∀ n, p ≤ eventMass n)
    (hdeviation : ∀ n,
      b / (((n + 1 : ℕ) : ℝ) ^ degree) ≤ eventDeviation n)
    (hdeviationNonneg : ∀ n, 0 ≤ eventDeviation n)
    (hrisk : ∀ n,
      eventMass n * eventDeviation n ^ 2 ≤ candidateRisk n) :
    ∀ n, p * b ^ 2 / (((n + 1 : ℕ) : ℝ) ^ (2 * degree)) ≤
      candidateRisk n := by
  intro n
  have hn : 0 < (((n + 1 : ℕ) : ℝ) ^ degree) := by positivity
  have hdevSq :
      (b / (((n + 1 : ℕ) : ℝ) ^ degree)) ^ 2 ≤
        eventDeviation n ^ 2 :=
    (sq_le_sq₀ (by positivity) (hdeviationNonneg n)).2 (hdeviation n)
  have hmassNonneg : 0 ≤ eventMass n := hp.trans (hmass n)
  calc
    p * b ^ 2 / (((n + 1 : ℕ) : ℝ) ^ (2 * degree)) =
        p * (b / (((n + 1 : ℕ) : ℝ) ^ degree)) ^ 2 := by
      rw [show 2 * degree = degree * 2 by omega]
      rw [pow_mul]
      field_simp [hn.ne']
    _ ≤ eventMass n *
        (b / (((n + 1 : ℕ) : ℝ) ^ degree)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (hmass n) (sq_nonneg _)
    _ ≤ eventMass n * eventDeviation n ^ 2 := by
      exact mul_le_mul_of_nonneg_left hdevSq hmassNonneg
    _ ≤ candidateRisk n := hrisk n





theorem d001789
    {b L : ℝ} (hb : 0 ≤ b) (hL : 0 < L)
    (denominator deviation : ℕ → ℝ)
    (hdenominatorPos : ∀ n, 0 < denominator n)
    (hdenominatorUpper : ∀ n,
      denominator n ≤ L * ((n + 1 : ℕ) : ℝ))
    (hdeviation : ∀ n,
      b / denominator n ^ 2 ≤ deviation n) :
    ∀ n,
      (b / L ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2) ≤ deviation n := by
  intro n
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hupperPos : 0 < L * ((n + 1 : ℕ) : ℝ) := mul_pos hL hn
  have hsquares : denominator n ^ 2 ≤
      (L * ((n + 1 : ℕ) : ℝ)) ^ 2 :=
    (sq_le_sq₀ (hdenominatorPos n).le hupperPos.le).2
      (hdenominatorUpper n)
  have hfrac : b / (L * ((n + 1 : ℕ) : ℝ)) ^ 2 ≤
      b / denominator n ^ 2 := by
    exact div_le_div_of_nonneg_left hb
      (sq_pos_of_pos (hdenominatorPos n)) hsquares
  calc
    (b / L ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2) =
        b / (L * ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      field_simp [hL.ne', hn.ne']
    _ ≤ b / denominator n ^ 2 := hfrac
    _ ≤ deviation n := hdeviation n




theorem d001790
    {p b L : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) (hL : 0 < L)
    (denominator eventMass eventDeviation candidateRisk : ℕ → ℝ)
    (hdenominatorPos : ∀ n, 0 < denominator n)
    (hdenominatorUpper : ∀ n,
      denominator n ≤ L * ((n + 1 : ℕ) : ℝ))
    (hmass : ∀ n, p ≤ eventMass n)
    (hdeviation : ∀ n,
      b / denominator n ^ 2 ≤ eventDeviation n)
    (hdeviationNonneg : ∀ n, 0 ≤ eventDeviation n)
    (hrisk : ∀ n,
      eventMass n * eventDeviation n ^ 2 ≤ candidateRisk n) :
    ∀ n,
      p * (b / L ^ 2) ^ 2 /
          (((n + 1 : ℕ) : ℝ) ^ 4) ≤ candidateRisk n := by
  apply _root_.GD.N0232.N0719.N0949.d001788 2 hp
      (div_nonneg hb (sq_nonneg L)) eventMass eventDeviation candidateRisk
      hmass
  · exact _root_.GD.N0232.N0719.N0949.d001789 hb hL
      denominator eventDeviation hdenominatorPos hdenominatorUpper hdeviation
  · exact hdeviationNonneg
  · exact hrisk




theorem d001791
    (degree : ℕ) {theta p b C : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hp : 0 < p) (hb : 0 < b)
    (eventMass eventDeviation candidateRisk baselineRisk : ℕ → ℝ)
    (hmass : ∀ n, p ≤ eventMass n)
    (hdeviation : ∀ n,
      b / (((n + 1 : ℕ) : ℝ) ^ degree) ≤ eventDeviation n)
    (hdeviationNonneg : ∀ n, 0 ≤ eventDeviation n)
    (hrisk : ∀ n,
      eventMass n * eventDeviation n ^ 2 ≤ candidateRisk n)
    (hbaseline : ∀ n,
      baselineRisk n ≤ C * theta ^ (n + 1)) :
    ¬ ∀ n, candidateRisk n ≤ baselineRisk n := by
  apply _root_.GD.N0232.N0719.N0949.d001787 (2 * degree)
    htheta hthetaOne (mul_pos hp (sq_pos_of_pos hb))
      candidateRisk baselineRisk
  · exact _root_.GD.N0232.N0719.N0949.d001788 degree hp.le hb.le
      eventMass eventDeviation candidateRisk hmass hdeviation
        hdeviationNonneg hrisk
  · exact hbaseline




theorem d001792
    {theta p b L C : ℝ}
    (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hp : 0 < p) (hb : 0 < b) (hL : 0 < L)
    (denominator eventMass eventDeviation candidateRisk baselineRisk : ℕ → ℝ)
    (hdenominatorPos : ∀ n, 0 < denominator n)
    (hdenominatorUpper : ∀ n,
      denominator n ≤ L * ((n + 1 : ℕ) : ℝ))
    (hmass : ∀ n, p ≤ eventMass n)
    (hdeviation : ∀ n,
      b / denominator n ^ 2 ≤ eventDeviation n)
    (hdeviationNonneg : ∀ n, 0 ≤ eventDeviation n)
    (hrisk : ∀ n,
      eventMass n * eventDeviation n ^ 2 ≤ candidateRisk n)
    (hbaseline : ∀ n,
      baselineRisk n ≤ C * theta ^ (n + 1)) :
    ¬ ∀ n, candidateRisk n ≤ baselineRisk n := by
  apply _root_.GD.N0232.N0719.N0949.d001787 4
    htheta hthetaOne
      (mul_pos hp (sq_pos_of_pos (div_pos hb (sq_pos_of_pos hL))))
      candidateRisk baselineRisk
  · exact _root_.GD.N0232.N0719.N0949.d001790
      hp.le hb.le hL denominator eventMass eventDeviation candidateRisk
      hdenominatorPos hdenominatorUpper hmass hdeviation
      hdeviationNonneg hrisk
  · exact hbaseline

end

end N0949
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0949.d001785
#print axioms _root_.GD.N0232.N0719.N0949.d001786
#print axioms _root_.GD.N0232.N0719.N0949.d001788
#print axioms _root_.GD.N0232.N0719.N0949.d001789
#print axioms _root_.GD.N0232.N0719.N0949.d001790
#print axioms _root_.GD.N0232.N0719.N0949.d001791
#print axioms _root_.GD.N0232.N0719.N0949.d001792
