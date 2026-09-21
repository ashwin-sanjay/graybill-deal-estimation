import GD.Module0165
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
















open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1051

noncomputable section

set_option linter.unusedSectionVars false





def d001938 (rho p : ℝ) : ℝ :=
  rho + 2 * p - rho * p - p ^ 2

theorem d001939 (rho p : ℝ) :
    _root_.GD.N0232.N0720.N1051.d001938 rho p = p + rho * (1 - p) + p * (1 - p) := by
  unfold _root_.GD.N0232.N0720.N1051.d001938
  ring

theorem d001940
    {rho p : ℝ} (hrho : 0 < rho) (hp : 0 < p) (hp1 : p ≤ 1) :
    0 < _root_.GD.N0232.N0720.N1051.d001938 rho p := by
  rw [_root_.GD.N0232.N0720.N1051.d001939]
  have hnonneg : 0 ≤ rho * (1 - p) + p * (1 - p) := by positivity
  linarith


theorem d001941 (rho q : ℝ) :
    _root_.GD.N0232.N0720.N1051.d001938 rho (1 - q) - _root_.GD.N0232.N0720.N1051.d001938 rho q =
      (1 - rho) * (1 - 2 * q) := by
  unfold _root_.GD.N0232.N0720.N1051.d001938
  ring

theorem d001942
    {rho q : ℝ} (hrho : rho ≤ 1) (hq : q ≤ 1 / 2) :
    _root_.GD.N0232.N0720.N1051.d001938 rho q ≤ _root_.GD.N0232.N0720.N1051.d001938 rho (1 - q) := by
  rw [← sub_nonneg]
  rw [_root_.GD.N0232.N0720.N1051.d001941]
  exact mul_nonneg (sub_nonneg.mpr hrho) (by linarith)


theorem d001943
    {rho p : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (hp0 : 0 < p) (hpHalf : p ≤ 1 / 2) :
    (5 : ℝ) / 6 ≤ _root_.GD.N0232.N0720.N1051.d001938 rho p / (p + rho) ∧
      _root_.GD.N0232.N0720.N1051.d001938 rho p / (p + rho) < 2 := by
  have hden : 0 < p + rho := add_pos hp0 hrho0
  have hlower : 5 * (p + rho) ≤ 6 * _root_.GD.N0232.N0720.N1051.d001938 rho p := by
    by_cases hpSixth : p ≤ 1 / 6
    · have hfirst : 0 ≤ rho * (1 - 6 * p) :=
        mul_nonneg hrho0.le (by linarith)
      have hsecond : 0 ≤ p * (7 - 6 * p) :=
        mul_nonneg hp0.le (by linarith)
      unfold _root_.GD.N0232.N0720.N1051.d001938
      nlinarith
    · have hcoef : 1 - 6 * p ≤ 0 := by linarith
      have hrhoCoef : 1 - 6 * p ≤ rho * (1 - 6 * p) := by
        nlinarith
      have hfactor : 0 ≤ (1 - 2 * p) * (1 + 3 * p) :=
        mul_nonneg (by linarith) (by linarith)
      unfold _root_.GD.N0232.N0720.N1051.d001938
      nlinarith
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith
  · apply (div_lt_iff₀ hden).2
    unfold _root_.GD.N0232.N0720.N1051.d001938
    have hpos : 0 < rho + rho * p + p ^ 2 := by positivity
    nlinarith


theorem d001944 (rho p : ℝ) :
    _root_.GD.N0232.N0720.N1051.d001938 rho p ≤ 1 + rho ^ 2 / 4 := by
  have hsquare : 0 ≤ (p - (1 - rho / 2)) ^ 2 := sq_nonneg _
  unfold _root_.GD.N0232.N0720.N1051.d001938
  nlinarith


theorem d001945
    {rho p : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    _root_.GD.N0232.N0720.N1051.d001938 rho p ≤ (5 : ℝ) / 4 := by
  have hproduct : 0 ≤ rho * (1 - rho) :=
    mul_nonneg hrho0 (sub_nonneg.mpr hrho1)
  have henvelope := _root_.GD.N0232.N0720.N1051.d001944 rho p
  nlinarith





def d001946 (rho p : ℝ) : ℝ :=
  Real.sqrt rho / (_root_.GD.N0232.N0720.N1051.d001938 rho p) ^ ((5 : ℝ) / 2)

theorem d001947 {rho p : ℝ}
    (hA : 0 ≤ _root_.GD.N0232.N0720.N1051.d001938 rho p) : 0 ≤ _root_.GD.N0232.N0720.N1051.d001946 rho p := by
  unfold _root_.GD.N0232.N0720.N1051.d001946
  exact div_nonneg (Real.sqrt_nonneg rho) (Real.rpow_nonneg hA _)



theorem d001948
    {rho q : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (hq0 : 0 < q) (hqHalf : q ≤ 1 / 2) :
    _root_.GD.N0232.N0720.N1051.d001946 rho (1 - q) ≤ _root_.GD.N0232.N0720.N1051.d001946 rho q := by
  have hq1 : q ≤ 1 := hqHalf.trans (by norm_num)
  have hrefPos : 0 < _root_.GD.N0232.N0720.N1051.d001938 rho (1 - q) := by
    apply _root_.GD.N0232.N0720.N1051.d001940 hrho0
    · linarith
    · linarith
  have hqPos : 0 < _root_.GD.N0232.N0720.N1051.d001938 rho q :=
    _root_.GD.N0232.N0720.N1051.d001940 hrho0 hq0 hq1
  have hA := _root_.GD.N0232.N0720.N1051.d001942 hrho1 hqHalf
  have hpow :
      (_root_.GD.N0232.N0720.N1051.d001938 rho q) ^ ((5 : ℝ) / 2) ≤
        (_root_.GD.N0232.N0720.N1051.d001938 rho (1 - q)) ^ ((5 : ℝ) / 2) := by
    exact Real.rpow_le_rpow hqPos.le hA (by norm_num)
  unfold _root_.GD.N0232.N0720.N1051.d001946
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg rho)
    (Real.rpow_pos_of_pos hqPos _) hpow



theorem d001949
    {rho p : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Real.sqrt rho / ((5 : ℝ) / 4) ^ ((5 : ℝ) / 2) ≤
      _root_.GD.N0232.N0720.N1051.d001946 rho p := by
  have hApos : 0 < _root_.GD.N0232.N0720.N1051.d001938 rho p :=
    _root_.GD.N0232.N0720.N1051.d001940 hrho0 hp0 hp1
  have hAle : _root_.GD.N0232.N0720.N1051.d001938 rho p ≤ (5 : ℝ) / 4 :=
    _root_.GD.N0232.N0720.N1051.d001945 hrho0.le hrho1
  have hpow :
      (_root_.GD.N0232.N0720.N1051.d001938 rho p) ^ ((5 : ℝ) / 2) ≤
        ((5 : ℝ) / 4) ^ ((5 : ℝ) / 2) :=
    Real.rpow_le_rpow hApos.le hAle (by norm_num)
  unfold _root_.GD.N0232.N0720.N1051.d001946
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg rho)
    (Real.rpow_pos_of_pos hApos _) hpow

theorem d001950
    {rho q : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (hq0 : 0 < q) (hqHalf : q ≤ 1 / 2) :
    max (_root_.GD.N0232.N0720.N1051.d001946 rho q) (_root_.GD.N0232.N0720.N1051.d001946 rho (1 - q)) =
      _root_.GD.N0232.N0720.N1051.d001946 rho q := by
  exact max_eq_left (_root_.GD.N0232.N0720.N1051.d001948 hrho0 hrho1 hq0 hqHalf)



variable {I : Type*} [Fintype I]


def d001951
    (rho epsilon : I → ℝ) (p : ℝ) : ℝ :=
  ∑ i, epsilon i ^ 2 * _root_.GD.N0232.N0720.N1051.d001946 (rho i) p

theorem d001952
    (rho epsilon : I → ℝ) {q : ℝ}
    (hrho0 : ∀ i, 0 < rho i) (hrho1 : ∀ i, rho i ≤ 1)
    (hq0 : 0 < q) (hqHalf : q ≤ 1 / 2) :
    _root_.GD.N0232.N0720.N1051.d001951 rho epsilon (1 - q) ≤
      _root_.GD.N0232.N0720.N1051.d001951 rho epsilon q := by
  unfold _root_.GD.N0232.N0720.N1051.d001951
  exact Finset.sum_le_sum fun i hi ↦
    mul_le_mul_of_nonneg_left
      (_root_.GD.N0232.N0720.N1051.d001948 (hrho0 i) (hrho1 i) hq0 hqHalf)
      (sq_nonneg (epsilon i))

theorem d001953
    (rho epsilon : I → ℝ) {q : ℝ}
    (hrho0 : ∀ i, 0 < rho i) (hrho1 : ∀ i, rho i ≤ 1)
    (hq0 : 0 < q) (hqHalf : q ≤ 1 / 2) :
    max (_root_.GD.N0232.N0720.N1051.d001951 rho epsilon q)
        (_root_.GD.N0232.N0720.N1051.d001951 rho epsilon (1 - q)) =
      _root_.GD.N0232.N0720.N1051.d001951 rho epsilon q := by
  exact max_eq_left
    (_root_.GD.N0232.N0720.N1051.d001952 rho epsilon hrho0 hrho1 hq0 hqHalf)



theorem d001954
    (rho epsilon : I → ℝ) {M q : ℝ}
    (hrho0 : ∀ i, 0 < rho i) (hrho1 : ∀ i, rho i ≤ 1)
    (hq0 : 0 < q) (hqHalf : q ≤ 1 / 2) :
    (M / 2) *
        (max (_root_.GD.N0232.N0720.N1051.d001951 rho epsilon q)
          (_root_.GD.N0232.N0720.N1051.d001951 rho epsilon (1 - q)) +
        max (_root_.GD.N0232.N0720.N1051.d001951 rho epsilon (1 - q))
          (_root_.GD.N0232.N0720.N1051.d001951 rho epsilon q)) =
      M * _root_.GD.N0232.N0720.N1051.d001951 rho epsilon q := by
  rw [_root_.GD.N0232.N0720.N1051.d001953 rho epsilon hrho0 hrho1 hq0 hqHalf]
  rw [max_eq_right
    (_root_.GD.N0232.N0720.N1051.d001952 rho epsilon hrho0 hrho1 hq0 hqHalf)]
  ring




theorem d001955 (N : ℕ) :
    (∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k) ≤ 2 := by
  exact sum_geometric_two_le N



theorem d001956
    {N : ℕ} (term : ℕ → ℝ) {C M : ℝ}
    (hM : 0 < M)
    (hterm : ∀ k < N, term k ≤ C * ((1 : ℝ) / 2) ^ k / M)
    (hC : 0 ≤ C) :
    (∑ k ∈ Finset.range N, term k) ≤ 2 * C / M := by
  calc
    (∑ k ∈ Finset.range N, term k) ≤
        ∑ k ∈ Finset.range N, C * ((1 : ℝ) / 2) ^ k / M := by
      exact Finset.sum_le_sum fun k hk ↦ hterm k (Finset.mem_range.mp hk)
    _ = (C / M) * ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (C / M) * 2 := by
      exact mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0720.N1051.d001955 N)
        (div_nonneg hC hM.le)
    _ = 2 * C / M := by ring



theorem d001957
    {N K : ℕ} (term : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (hterm : ∀ j < N,
      term (K + j) ≤ C * ((1 : ℝ) / 2) ^ (K + j)) :
    (∑ j ∈ Finset.range N, term (K + j)) ≤
      2 * C * ((1 : ℝ) / 2) ^ K := by
  calc
    (∑ j ∈ Finset.range N, term (K + j)) ≤
        ∑ j ∈ Finset.range N,
          C * ((1 : ℝ) / 2) ^ (K + j) := by
      exact Finset.sum_le_sum fun j hj ↦ hterm j (Finset.mem_range.mp hj)
    _ = (C * ((1 : ℝ) / 2) ^ K) *
        ∑ j ∈ Finset.range N, ((1 : ℝ) / 2) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      ring
    _ ≤ (C * ((1 : ℝ) / 2) ^ K) * 2 := by
      exact mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0720.N1051.d001955 N)
        (mul_nonneg hC (by positivity))
    _ = 2 * C * ((1 : ℝ) / 2) ^ K := by ring


theorem d001958
    {firstTerm Astar baseline cshare M : ℝ}
    (hM : 1 ≤ M) (hAstar : 0 ≤ Astar)
    (hbaseline : 0 < baseline) (hcshare : 0 ≤ cshare)
    (hfirst : firstTerm = Astar / (baseline + cshare * M)) :
    Astar / ((baseline + cshare) * M) ≤ firstTerm := by
  rw [hfirst]
  have hdenSmall : baseline + cshare * M ≤ (baseline + cshare) * M := by
    nlinarith
  by_cases hA : Astar = 0
  · simp [hA]
  have hApos : 0 < Astar := lt_of_le_of_ne hAstar (Ne.symm hA)
  have hsmallPos : 0 < baseline + cshare * M := by
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    exact add_pos_of_pos_of_nonneg hbaseline (mul_nonneg hcshare hMpos.le)
  have hbigPos : 0 < (baseline + cshare) * M := by
    have hsumPos : 0 < baseline + cshare :=
      add_pos_of_pos_of_nonneg hbaseline hcshare
    exact mul_pos hsumPos (lt_of_lt_of_le zero_lt_one hM)
  exact div_le_div_of_nonneg_left hApos.le hsmallPos hdenSmall



theorem d001959
    {N : ℕ} (term : ℕ → ℝ)
    {Astar baseline cshare C M : ℝ}
    (hM : 1 ≤ M) (hAstar : 0 ≤ Astar)
    (hbaseline : 0 < baseline) (hcshare : 0 ≤ cshare)
    (hzero : term 0 = Astar / (baseline + cshare * M))
    (htermNonneg : ∀ k < N, 0 ≤ term k)
    (hterm : ∀ k < N, term k ≤ C * ((1 : ℝ) / 2) ^ k / M)
    (hC : 0 ≤ C) (hN : 0 < N) :
    Astar / ((baseline + cshare) * M) ≤
        (∑ k ∈ Finset.range N, term k) ∧
      (∑ k ∈ Finset.range N, term k) ≤ 2 * C / M := by
  constructor
  · have hfirst := _root_.GD.N0232.N0720.N1051.d001958 hM hAstar
      hbaseline hcshare hzero
    have hmem : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
    calc
      Astar / ((baseline + cshare) * M) ≤ term 0 := hfirst
      _ ≤ ∑ k ∈ Finset.range N, term k :=
        Finset.single_le_sum
          (fun k hk ↦ htermNonneg k (Finset.mem_range.mp hk)) hmem
  · exact _root_.GD.N0232.N0720.N1051.d001956 term
      (lt_of_lt_of_le zero_lt_one hM) hterm hC


def d001960 : ℝ :=
  Real.exp (-(21 : ℝ) / 2) /
    (25 * (2 : ℝ) ^ ((3 : ℝ) / 2) * Real.pi ^ ((5 : ℝ) / 2))

theorem d001961 :
    0 ≤ _root_.GD.N0232.N0720.N1051.d001960 := by
  unfold _root_.GD.N0232.N0720.N1051.d001960
  positivity [Real.pi_pos]




theorem d001962
    {N : ℕ} (term : ℕ → ℝ)
    {Astar cshare M : ℝ}
    (hM : 1 ≤ M) (hAstar : 0 ≤ Astar) (hcshare : 0 ≤ cshare)
    (hzero : term 0 =
      Astar / (2 / Real.sqrt Real.pi + cshare * M))
    (htermNonneg : ∀ k < N, 0 ≤ term k)
    (hterm : ∀ k < N,
      term k ≤ (_root_.GD.N0232.N0720.N1051.d001960 / 2) *
        ((1 : ℝ) / 2) ^ k / M)
    (hN : 0 < N) :
    Astar / ((2 / Real.sqrt Real.pi + cshare) * M) ≤
        (∑ k ∈ Finset.range N, term k) ∧
      (∑ k ∈ Finset.range N, term k) ≤
        _root_.GD.N0232.N0720.N1051.d001960 / M := by
  have hbase : 0 < 2 / Real.sqrt Real.pi := by positivity [Real.pi_pos]
  have hgeneric := _root_.GD.N0232.N0720.N1051.d001959 term
    hM hAstar hbase hcshare hzero htermNonneg hterm
    (div_nonneg _root_.GD.N0232.N0720.N1051.d001961 (by norm_num)) hN
  constructor
  · exact hgeneric.1
  · calc
      (∑ k ∈ Finset.range N, term k) ≤
          2 * (_root_.GD.N0232.N0720.N1051.d001960 / 2) / M := hgeneric.2
      _ = _root_.GD.N0232.N0720.N1051.d001960 / M := by ring

end

end N1051
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1051.d001943
#print axioms _root_.GD.N0232.N0720.N1051.d001945
#print axioms _root_.GD.N0232.N0720.N1051.d001948
#print axioms _root_.GD.N0232.N0720.N1051.d001954
#print axioms _root_.GD.N0232.N0720.N1051.d001955
#print axioms _root_.GD.N0232.N0720.N1051.d001957
#print axioms _root_.GD.N0232.N0720.N1051.d001959
#print axioms _root_.GD.N0232.N0720.N1051.d001962
