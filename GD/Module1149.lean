import GD.Module1148





















open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1211

noncomputable section

open _root_.GD.N0232.N0720.N1121
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1417





theorem d018462
    (evidence base neighbor transported : ℝ) (hEvidence : 0 ≤ evidence) :
    evidence * (transported - base) ^ 2 ≤
      2 * evidence * (neighbor - base) ^ 2 +
        2 * evidence * (transported - neighbor) ^ 2 := by
  have hsquare :
      (transported - base) ^ 2 ≤
        2 * (neighbor - base) ^ 2 +
          2 * (transported - neighbor) ^ 2 := by
    nlinarith [sq_nonneg ((neighbor - base) - (transported - neighbor))]
  have hscaled := mul_le_mul_of_nonneg_left hsquare hEvidence
  nlinarith



theorem d018463
    (evidence base neighbor₀ neighbor₁ transported₀ transported₁ : ℝ)
    (hEvidence : 0 ≤ evidence) :
    evidence * (transported₀ - base) ^ 2 +
        evidence * (transported₁ - base) ^ 2 ≤
      2 * (evidence * (neighbor₀ - base) ^ 2 +
        evidence * (neighbor₁ - base) ^ 2) +
      2 * (evidence * (transported₀ - neighbor₀) ^ 2 +
        evidence * (transported₁ - neighbor₁) ^ 2) := by
  have h₀ := _root_.GD.N0232.N0720.N1211.d018462
    evidence base neighbor₀ transported₀ hEvidence
  have h₁ := _root_.GD.N0232.N0720.N1211.d018462
    evidence base neighbor₁ transported₁ hEvidence
  linarith




theorem d018464
    (evidence neighborEvidence₀ neighborEvidence₁ : ℝ)
    (base neighbor₀ neighbor₁ transported₀ transported₁ : ℝ)
    (conductanceFloor conductance₀ conductance₁ : ℝ)
    (hEvidence : 0 ≤ evidence)
    (hNeighborEvidence₀ : 0 ≤ neighborEvidence₀)
    (hNeighborEvidence₁ : 0 ≤ neighborEvidence₁)
    (hConductanceFloor : 0 < conductanceFloor)
    (hConductance₀ : conductanceFloor ≤ conductance₀)
    (hConductance₁ : conductanceFloor ≤ conductance₁) :
    evidence * (transported₀ - base) ^ 2 +
        evidence * (transported₁ - base) ^ 2 ≤
      (2 / conductanceFloor) *
        (conductance₀ * (evidence + neighborEvidence₀) *
            (neighbor₀ - base) ^ 2 +
          conductance₁ * (evidence + neighborEvidence₁) *
            (neighbor₁ - base) ^ 2) +
      2 * (evidence * (transported₀ - neighbor₀) ^ 2 +
        evidence * (transported₁ - neighbor₁) ^ 2) := by
  have hsplit :=
    _root_.GD.N0232.N0720.N1211.d018463
      evidence base neighbor₀ neighbor₁ transported₀ transported₁ hEvidence
  have hEvidenceScale₀ :
      conductanceFloor * evidence ≤
        conductance₀ * (evidence + neighborEvidence₀) := by
    calc
      conductanceFloor * evidence ≤
          conductanceFloor * (evidence + neighborEvidence₀) := by
            exact mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right hNeighborEvidence₀)
              hConductanceFloor.le
      _ ≤ conductance₀ * (evidence + neighborEvidence₀) := by
            exact mul_le_mul_of_nonneg_right hConductance₀
              (add_nonneg hEvidence hNeighborEvidence₀)
  have hEvidenceScale₁ :
      conductanceFloor * evidence ≤
        conductance₁ * (evidence + neighborEvidence₁) := by
    calc
      conductanceFloor * evidence ≤
          conductanceFloor * (evidence + neighborEvidence₁) := by
            exact mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right hNeighborEvidence₁)
              hConductanceFloor.le
      _ ≤ conductance₁ * (evidence + neighborEvidence₁) := by
            exact mul_le_mul_of_nonneg_right hConductance₁
              (add_nonneg hEvidence hNeighborEvidence₁)
  have hedge₀ :
      evidence * (neighbor₀ - base) ^ 2 ≤
        (conductance₀ * (evidence + neighborEvidence₀) *
          (neighbor₀ - base) ^ 2) / conductanceFloor := by
    apply (le_div_iff₀ hConductanceFloor).2
    have hscaled := mul_le_mul_of_nonneg_right hEvidenceScale₀
      (sq_nonneg (neighbor₀ - base))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hedge₁ :
      evidence * (neighbor₁ - base) ^ 2 ≤
        (conductance₁ * (evidence + neighborEvidence₁) *
          (neighbor₁ - base) ^ 2) / conductanceFloor := by
    apply (le_div_iff₀ hConductanceFloor).2
    have hscaled := mul_le_mul_of_nonneg_right hEvidenceScale₁
      (sq_nonneg (neighbor₁ - base))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hedge :
      2 * (evidence * (neighbor₀ - base) ^ 2 +
        evidence * (neighbor₁ - base) ^ 2) ≤
      (2 / conductanceFloor) *
        (conductance₀ * (evidence + neighborEvidence₀) *
            (neighbor₀ - base) ^ 2 +
          conductance₁ * (evidence + neighborEvidence₁) *
            (neighbor₁ - base) ^ 2) := by
    have hsum := add_le_add hedge₀ hedge₁
    have hscaled := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * (evidence * (neighbor₀ - base) ^ 2 +
          evidence * (neighbor₁ - base) ^ 2) ≤
          2 * ((conductance₀ * (evidence + neighborEvidence₀) *
              (neighbor₀ - base) ^ 2) / conductanceFloor +
            (conductance₁ * (evidence + neighborEvidence₁) *
              (neighbor₁ - base) ^ 2) / conductanceFloor) := hscaled
      _ = (2 / conductanceFloor) *
          (conductance₀ * (evidence + neighborEvidence₀) *
              (neighbor₀ - base) ^ 2 +
            conductance₁ * (evidence + neighborEvidence₁) *
              (neighbor₁ - base) ^ 2) := by ring
  linarith










def d018465 : Prop :=
  ∃ row : _root_.GD.N0232.N0720.N1103.d018289 _root_.GD.N0232.N0720.N1302.d018268,
    ∃ edgeProduction covarianceError : ℕ → ℝ,
      (∀ j, 0 ≤ edgeProduction j) ∧
      (∀ j, 0 ≤ covarianceError j) ∧
      Tendsto edgeProduction atTop (nhds 0) ∧
      Tendsto covarianceError atTop (nhds 0) ∧
      ∀ j,
        _root_.GD.N0232.N0720.N1121.d018305 2 2
            (row.candidate j) ≤
          2 * edgeProduction j + 2 * covarianceError j



theorem d018466
    (h : _root_.GD.N0232.N0720.N1211.d018465) :
    _root_.GD.N0232.N0720.N1417.d018442 := by
  rcases h with
    ⟨row, edgeProduction, covarianceError, hedgeNonneg, hcovNonneg,
      hedgeZero, hcovZero, hcontrol⟩
  refine ⟨row, ?_⟩
  have hupperZero : Tendsto
      (fun j ↦ 2 * edgeProduction j + 2 * covarianceError j)
      atTop (nhds 0) := by
    simpa using (hedgeZero.const_mul 2).add (hcovZero.const_mul 2)
  exact squeeze_zero
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018306
      2 2 (row.candidate j))
    hcontrol hupperZero










theorem d018467 :
    _root_.GD.N0232.N0720.N1211.d018465 ↔
      _root_.GD.N0232.N0720.N1417.d018442 := by
  constructor
  · exact _root_.GD.N0232.N0720.N1211.d018466
  · rintro ⟨row, htaxZero⟩
    refine ⟨row,
      (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 2 2
        (row.candidate j)),
      (fun _ ↦ 0), ?_, ?_, htaxZero, tendsto_const_nhds, ?_⟩
    · intro j
      exact _root_.GD.N0232.N0720.N1121.d018306
        2 2 (row.candidate j)
    · intro j
      exact le_rfl
    · intro j
      have hnonneg := _root_.GD.N0232.N0720.N1121.d018306
        2 2 (row.candidate j)
      nlinarith



theorem d018468
    (h : _root_.GD.N0232.N0720.N1211.d018465) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1417.d018443
    (_root_.GD.N0232.N0720.N1211.d018466 h)

end

end N1211
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1211.d018462
#print axioms _root_.GD.N0232.N0720.N1211.d018463
#print axioms _root_.GD.N0232.N0720.N1211.d018464
#print axioms _root_.GD.N0232.N0720.N1211.d018466
#print axioms _root_.GD.N0232.N0720.N1211.d018467
#print axioms _root_.GD.N0232.N0720.N1211.d018468
