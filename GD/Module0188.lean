import GD.Module0179
import GD.Module0187
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic














namespace GD.N0232.N0720.N1245

open _root_.GD.N0232.N0720.N1252


theorem d002488 : (50 : ℝ) < Real.exp 4 := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 8)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

theorem d002489 : Real.log 50 < 4 := by
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 50)).2
    _root_.GD.N0232.N0720.N1245.d002488

theorem d002490 {η : ℝ} (hη1 : 1 ≤ η) (hη50 : η ≤ 50) :
    Real.log η ∈ Set.Icc (0 : ℝ) 4 := by
  have hηpos : 0 < η := lt_of_lt_of_le zero_lt_one hη1
  refine ⟨Real.log_nonneg hη1, ?_⟩
  exact ((Real.log_lt_iff_lt_exp hηpos).2
    (hη50.trans_lt _root_.GD.N0232.N0720.N1245.d002488)).le



theorem d002491
    (D J : ℝ → ℝ)
    (hJ : ∀ x ∈ Set.Icc (0 : ℝ) 4, 0 < J x)
    (hrelation : ∀ x : ℝ,
      J x = 11 / (1 + Real.exp x) * D (Real.exp x))
    {η : ℝ} (hη1 : 1 ≤ η) (hη50 : η ≤ 50) :
    0 < D η := by
  have hηpos : 0 < η := lt_of_lt_of_le zero_lt_one hη1
  have hpos := hJ (Real.log η) (_root_.GD.N0232.N0720.N1245.d002490 hη1 hη50)
  rw [hrelation, Real.exp_log hηpos] at hpos
  have hcoefficient : 0 < (11 : ℝ) / (1 + η) := by positivity
  by_contra hnot
  have hD : D η ≤ 0 := le_of_not_gt hnot
  have := mul_nonpos_of_nonneg_of_nonpos hcoefficient.le hD
  linarith



theorem d002492
    (D K : ℝ → ℝ)
    (hK : ∀ e ∈ Set.Icc (0 : ℝ) (1 / 50), 0 < K e)
    (hrelation : ∀ η : ℝ, 0 < η → K (1 / η) = η * D η)
    {η : ℝ} (hηpos : 0 < η) (hη50 : 50 ≤ η) :
    0 < D η := by
  have he0 : (0 : ℝ) ≤ 1 / η := (one_div_pos.mpr hηpos).le
  have he50 : (1 / η : ℝ) ≤ 1 / 50 := by
    rw [div_le_div_iff₀ hηpos (by norm_num : (0 : ℝ) < 50)]
    simpa using hη50
  have hpos := hK (1 / η) ⟨he0, he50⟩
  rw [hrelation η hηpos] at hpos
  have hnonneg : 0 ≤ η := hηpos.le
  by_contra hnot
  have hD : D η ≤ 0 := le_of_not_gt hnot
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hnonneg hD]



theorem d002493
    (D : ℝ → ℝ)
    (hinterior : ∀ η : ℝ, 1 ≤ η → η ≤ 50 → 0 < D η)
    (hwall : ∀ η : ℝ, 0 < η → 50 ≤ η → 0 < D η)
    (hswap : ∀ η : ℝ, 0 < η → D η = η * D (1 / η)) :
    ∀ η : ℝ, 0 < η → 0 < D η := by
  intro η hηpos
  by_cases hη1 : 1 ≤ η
  · by_cases hη50 : η ≤ 50
    · exact hinterior η hη1 hη50
    · exact hwall η hηpos (le_of_lt (lt_of_not_ge hη50))
  · have hηle : η ≤ 1 := le_of_lt (lt_of_not_ge hη1)
    have hrecippos : 0 < (1 / η : ℝ) := one_div_pos.mpr hηpos
    have hrecipone : (1 : ℝ) ≤ 1 / η := by
      rw [le_div_iff₀ hηpos]
      simpa using hηle
    have hrecip : 0 < D (1 / η) := by
      by_cases hrecip50 : (1 / η : ℝ) ≤ 50
      · exact hinterior (1 / η) hrecipone hrecip50
      · exact hwall (1 / η) hrecippos
          (le_of_lt (lt_of_not_ge hrecip50))
    rw [hswap η hηpos]
    exact mul_pos hηpos hrecip





theorem d002494
    (D J K : ℝ → ℝ)
    (hJ : ∀ x ∈ Set.Icc (0 : ℝ) 4, 0 < J x)
    (hJrelation : ∀ x : ℝ,
      J x = 11 / (1 + Real.exp x) * D (Real.exp x))
    (wallEvidence : _root_.GD.N0232.N0720.N1252.d002245 K)
    (hKrelation : ∀ η : ℝ, 0 < η → K (1 / η) = η * D η)
    (hswap : ∀ η : ℝ, 0 < η → D η = η * D (1 / η)) :
    ∀ η : ℝ, 0 < η → 0 < D η := by
  have hinterior : ∀ η : ℝ, 1 ≤ η → η ≤ 50 → 0 < D η := by
    intro η hη1 hη50
    exact _root_.GD.N0232.N0720.N1245.d002491 D J hJ hJrelation hη1 hη50
  have hwallK : ∀ e ∈ Set.Icc (0 : ℝ) (1 / 50), 0 < K e := by
    intro e he
    exact _root_.GD.N0232.N0720.N1252.d002487 K wallEvidence he.1 he.2
  have hwall : ∀ η : ℝ, 0 < η → 50 ≤ η → 0 < D η := by
    intro η hηpos hη50
    exact _root_.GD.N0232.N0720.N1245.d002492 D K hwallK hKrelation hηpos hη50
  exact _root_.GD.N0232.N0720.N1245.d002493 D hinterior hwall hswap

end GD.N0232.N0720.N1245
