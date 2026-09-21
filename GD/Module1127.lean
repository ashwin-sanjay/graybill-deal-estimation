import GD.Module1126





































open Filter MeasureTheory Topology
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1056

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0691
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1037
open _root_.GD.N0232.N0720.N1031
open _root_.GD.N0232.N0720.N1030
open _root_.GD.N0232.N0720.N1039
open _root_.GD.N0232.N0720.N1108
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1113
open _root_.GD.N0232.N0720.N1148
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false






def d018130 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
    _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) *
    _root_.GD.N0232.N0720.N1039.d016522 g.d009239 g.shift
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) ^ 2


def d018131 (m n : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) : ℝ :=
  ∫ omega, _root_.GD.N0232.N0720.N1056.d018130 g packet weight omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n

theorem d018132 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1056.d018130 g packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1056.d018130
  have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
    _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  exact mul_nonneg (mul_nonneg (_root_.GD.N0232.N0720.N1037.d016513 _ _) (_root_.GD.N0232.N0720.N1039.d016524 hA1 hc).le)
    (sq_nonneg _)


theorem d018133 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1056.d018130 g packet weight omega =
      _root_.GD.N0232.N0720.N1039.d016523 g.d009239 g.shift
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
          _root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) ^ 2 /
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))) := by
  unfold _root_.GD.N0232.N0720.N1056.d018130
  have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
    _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  have hAne : _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≠ 0 := by linarith
  have htne : _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) ≠ 0 :=
    (_root_.GD.N0232.N0720.N1039.d016524 hA1 hc).ne'
  rw [mul_assoc, _root_.GD.N0232.N0720.N1039.d016526 hAne htne]
  have hrec := _root_.GD.N0232.N0720.N1031.d017132 g omega
  have hL : _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega =
      1 / _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) := by
    rw [eq_div_iff hc.ne']
    exact hrec
  rw [hL]
  field_simp




theorem d018134 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
        _root_.GD.N0232.N0720.N1126.d016415 packet weight omega) ^ 2 ≤
      ∑ i, _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 := by
  have h := _root_.GD.N0230.N0617.d000176 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
    (_root_.GD.N0232.N0720.N1126.d016414 packet) hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hμ : _root_.GD.N0230.N0617.d000166 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega =
      _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
        _root_.GD.N0232.N0720.N1126.d016415 packet weight omega := rfl
  rw [hμ] at h
  have hsum : 0 ≤ ∑ i, _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  calc (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
        _root_.GD.N0232.N0720.N1126.d016415 packet weight omega) ^ 2
      = |_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
          _root_.GD.N0232.N0720.N1126.d016415 packet weight omega| ^ 2 := (sq_abs _).symm
    _ = |_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
          _root_.GD.N0232.N0720.N1126.d016415 packet weight omega| *
        |_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
          _root_.GD.N0232.N0720.N1126.d016415 packet weight omega| := sq _
    _ ≤ Real.sqrt (∑ i, _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2) * Real.sqrt (∑ i, _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2) :=
        mul_self_le_mul_self (abs_nonneg _) h
    _ = ∑ i, _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 := Real.mul_self_sqrt hsum


theorem d018135 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1056.d018130 g packet weight omega ≤
      4 * g.d009239 ^ 2 *
          _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
            omega +
        (4 * g.d009239 ^ 2 * (∑ i, _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2) + 2 * g.shift ^ 2) *
          _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega := by
  rw [_root_.GD.N0232.N0720.N1056.d018133 g packet weight hweight omega]
  have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
    _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  have hT1 : 1 ≤ _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) :=
    _root_.GD.N0232.N0720.N1039.d016525 hA1 hc
  have hT : 0 < _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) := by
    linarith
  have hrec := _root_.GD.N0232.N0720.N1031.d017132 g omega
  have hcs := _root_.GD.N0232.N0720.N1030.d018100 packet weight hweight omega
  have hS : 0 ≤ _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
      omega := Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (hweight i) (_root_.GD.N0232.N0720.N1126.d016419 packet i omega)) (sq_nonneg _)
  have hBsq := _root_.GD.N0232.N0720.N1056.d018134 packet weight hweight omega
  set a := g.d009239
  set b := g.shift
  set A := _root_.GD.N0232.N0720.N1126.d016415 packet weight omega with hAdef
  set M := _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega
  set c := _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)
  set S := _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega
  set tw := _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega
  set T := _root_.GD.N0232.N0720.N1039.d016521 A c
  set B2 := ∑ i, _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2
  have hB2 : 0 ≤ B2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _

  have hA0 : 0 < A := by linarith
  have hμ2 : (M / A) ^ 2 ≤ (A - 1) * S := by
    have hA2 : 1 ≤ A ^ 2 := by nlinarith
    calc (M / A) ^ 2 = M ^ 2 / A ^ 2 := by rw [div_pow]
      _ ≤ (A - 1) * S / A ^ 2 := by
          apply div_le_div_of_nonneg_right hcs (by positivity)
      _ ≤ (A - 1) * S := div_le_self (mul_nonneg (by linarith) hS) hA2
  have hμc : (M / A) ^ 2 * c ≤ S * T := by
    have hcA : c * (A - 1) ≤ T := by
      show c * (A - 1) ≤ _root_.GD.N0232.N0720.N1039.d016521 A c
      unfold _root_.GD.N0232.N0720.N1039.d016521
      linarith
    calc (M / A) ^ 2 * c ≤ (A - 1) * S * c := mul_le_mul_of_nonneg_right hμ2 hc.le
      _ = S * (c * (A - 1)) := by ring
      _ ≤ S * T := mul_le_mul_of_nonneg_left hcA hS

  have hN : _root_.GD.N0232.N0720.N1039.d016523 a b (M / A) c ^ 2 ≤
      4 * a ^ 2 * (M / A) ^ 2 * c ^ 2 + 4 * a ^ 2 * (M / A) ^ 2 + 2 * b ^ 2 := by
    unfold _root_.GD.N0232.N0720.N1039.d016523
    have h1 : (a * (M / A) * (c - 1) - b) ^ 2 ≤ 2 * (a * (M / A) * (c - 1)) ^ 2 + 2 * b ^ 2 := by
      nlinarith [sq_nonneg (a * (M / A) * (c - 1) + b)]
    have h2 : (c - 1) ^ 2 ≤ 2 * c ^ 2 + 2 := by nlinarith [sq_nonneg (c + 1)]
    have h3 : 2 * (a * (M / A) * (c - 1)) ^ 2 ≤ 2 * a ^ 2 * (M / A) ^ 2 * (2 * c ^ 2 + 2) := by
      have hx : 2 * (a * (M / A) * (c - 1)) ^ 2 = 2 * a ^ 2 * (M / A) ^ 2 * (c - 1) ^ 2 := by ring
      rw [hx]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [h1, h3]

  rw [div_le_iff₀ (mul_pos hc hT)]
  have e1 : 4 * a ^ 2 * (M / A) ^ 2 * c ^ 2 ≤ 4 * a ^ 2 * (S * T * c) := by
    have := mul_le_mul_of_nonneg_right hμc hc.le
    calc 4 * a ^ 2 * (M / A) ^ 2 * c ^ 2 = 4 * a ^ 2 * ((M / A) ^ 2 * c * c) := by ring
      _ ≤ 4 * a ^ 2 * (S * T * c) := mul_le_mul_of_nonneg_left this (by positivity)
  have e2 : 4 * a ^ 2 * (M / A) ^ 2 ≤ 4 * a ^ 2 * B2 * T := by
    calc 4 * a ^ 2 * (M / A) ^ 2 ≤ 4 * a ^ 2 * B2 :=
          mul_le_mul_of_nonneg_left hBsq (by positivity)
      _ = 4 * a ^ 2 * B2 * 1 := by ring
      _ ≤ 4 * a ^ 2 * B2 * T := mul_le_mul_of_nonneg_left hT1 (by positivity)
  have e3 : 2 * b ^ 2 ≤ 2 * b ^ 2 * T := by
    calc 2 * b ^ 2 = 2 * b ^ 2 * 1 := by ring
      _ ≤ 2 * b ^ 2 * T := mul_le_mul_of_nonneg_left hT1 (by positivity)
  have hR : (4 * a ^ 2 * S + (4 * a ^ 2 * B2 + 2 * b ^ 2) * tw) * (c * T) =
      4 * a ^ 2 * (S * T * c) + 4 * a ^ 2 * B2 * T + 2 * b ^ 2 * T := by
    linear_combination (4 * a ^ 2 * B2 + 2 * b ^ 2) * T * hrec
  rw [hR]
  linarith [hN, e1, e2, e3]

theorem d018136 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    Measurable (fun omega ↦ _root_.GD.N0232.N0720.N1056.d018130 (m := m) (n := n) g packet weight omega) := by
  have hmeasM := _root_.GD.N0232.N0720.N1030.d018106 (m := m) (n := n) packet weight
  have hmeasA := _root_.GD.N0232.N0720.N1030.d018107 (m := m) (n := n) packet weight
  have hmeasc : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) :=
    _root_.GD.N0232.N0720.N1030.d018105 (m := m) (n := n) g
  have hmeasw : Measurable (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹) := _root_.GD.N0232.N0720.N1037.d016515 g⁻¹
  have hmeasc' : Measurable (_root_.GD.N0232.N0720.N1108.d018077 m n g) := _root_.GD.N0232.N0720.N1030.d018105 g
  show Measurable (fun omega ↦ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
    _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega) (_root_.GD.N0232.N0720.N1108.d018077 m n g omega) *
    _root_.GD.N0232.N0720.N1039.d016522 g.d009239 g.shift
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega) (_root_.GD.N0232.N0720.N1108.d018077 m n g omega) ^ 2)
  unfold _root_.GD.N0232.N0720.N1039.d016522
  unfold _root_.GD.N0232.N0720.N1039.d016521
  fun_prop

theorem d018137 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1056.d018130 g packet weight omega) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hbig : Integrable (fun omega ↦ 4 * g.d009239 ^ 2 *
      _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
      (4 * g.d009239 ^ 2 * (∑ i, _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2) + 2 * g.shift ^ 2) *
        _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    ((_root_.GD.N0232.N0720.N1030.d018104 (m := m) (n := n) packet weight).const_mul _).add
      ((_root_.GD.N0232.N0720.N1037.d016516 g⁻¹).const_mul _)
  refine hbig.mono' (_root_.GD.N0232.N0720.N1056.d018136 g packet weight).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1056.d018132 g packet weight hweight omega)]
  exact _root_.GD.N0232.N0720.N1056.d018135 g packet weight hweight omega




theorem d018138 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) (K : ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hK : _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≤ K) :
    _root_.GD.N0232.N0720.N1039.d016523 g.d009239 g.shift
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
          _root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) ^ 2 /
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) +
        _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) ^ 2 *
          (K - 1)) ≤
      _root_.GD.N0232.N0720.N1056.d018130 g packet weight omega := by
  rw [_root_.GD.N0232.N0720.N1056.d018133 g packet weight hweight omega]
  have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
    _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  have hT : 0 < _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) :=
    _root_.GD.N0232.N0720.N1039.d016524 hA1 hc
  apply div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hc hT)
  unfold _root_.GD.N0232.N0720.N1039.d016521
  have := mul_le_mul_of_nonneg_left hK (sq_nonneg
    (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)))
  nlinarith [this]




theorem d018139 (μ c₀ c₁ : ℝ) :
    (4 * (c₀ - 1) ^ 2 + (3 * (c₁ - 1)) ^ 2) *
        (_root_.GD.N0232.N0720.N1039.d016523 2 0 μ c₀ ^ 2 + _root_.GD.N0232.N0720.N1039.d016523 3 1 μ c₁ ^ 2) -
      4 * (c₀ - 1) ^ 2 =
      ((4 * (c₀ - 1) ^ 2 + (3 * (c₁ - 1)) ^ 2) * μ - 3 * (c₁ - 1)) ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1039.d016523
  ring



theorem d018140 (μ c₀ c₁ : ℝ) :
    4 * (c₀ - 1) ^ 2 ≤
      (4 * (c₀ - 1) ^ 2 + (3 * (c₁ - 1)) ^ 2) *
        (_root_.GD.N0232.N0720.N1039.d016523 2 0 μ c₀ ^ 2 + _root_.GD.N0232.N0720.N1039.d016523 3 1 μ c₁ ^ 2) := by
  have h := _root_.GD.N0232.N0720.N1056.d018139 μ c₀ c₁
  nlinarith [sq_nonneg ((4 * (c₀ - 1) ^ 2 + (3 * (c₁ - 1)) ^ 2) * μ - 3 * (c₁ - 1))]




def d018141 (m n : ℕ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1499.d015001 m n
    (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169)
    (_root_.GD.N0232.N0720.N1482.d015130 • omega)


def d018142 (m n : ℕ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1499.d015001 m n
    (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131
      _root_.GD.N0232.N0720.N1080.d014169)
    (_root_.GD.N0232.N0720.N1482.d015131 • omega)

theorem d018143 (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : 0 < _root_.GD.N0232.N0720.N1056.d018141 m n omega :=
  _root_.GD.N0232.N0720.N1499.d015005 m n _ _

theorem d018144 (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : 0 < _root_.GD.N0232.N0720.N1056.d018142 m n omega :=
  _root_.GD.N0232.N0720.N1499.d015005 m n _ _

theorem d018145 : Measurable (_root_.GD.N0232.N0720.N1056.d018141 m n) :=
  _root_.GD.N0232.N0720.N1030.d018105 (m := m) (n := n) _

theorem d018146 : Measurable (_root_.GD.N0232.N0720.N1056.d018142 m n) :=
  _root_.GD.N0232.N0720.N1030.d018105 (m := m) (n := n) _


def d018147 (K c : ℝ) : ℝ := c + c ^ 2 * (K - 1)

theorem d018148 {K c : ℝ} (hK : 1 ≤ K) (hc : 0 < c) : 0 < _root_.GD.N0232.N0720.N1056.d018147 K c := by
  unfold _root_.GD.N0232.N0720.N1056.d018147
  have : 0 ≤ c ^ 2 * (K - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  linarith

theorem d018149 {K c : ℝ} (hK : 1 ≤ K) (hc : 0 < c) : c ≤ _root_.GD.N0232.N0720.N1056.d018147 K c := by
  unfold _root_.GD.N0232.N0720.N1056.d018147
  have : 0 ≤ c ^ 2 * (K - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  linarith


def d018150 (m n : ℕ) (K : ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  4 * (_root_.GD.N0232.N0720.N1056.d018141 m n omega - 1) ^ 2 /
    ((4 * (_root_.GD.N0232.N0720.N1056.d018141 m n omega - 1) ^ 2 + (3 * (_root_.GD.N0232.N0720.N1056.d018142 m n omega - 1)) ^ 2) *
      (_root_.GD.N0232.N0720.N1056.d018147 K (_root_.GD.N0232.N0720.N1056.d018141 m n omega) + _root_.GD.N0232.N0720.N1056.d018147 K (_root_.GD.N0232.N0720.N1056.d018142 m n omega)))

theorem d018151 (K : ℝ) (hK : 1 ≤ K) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1056.d018150 m n K omega := by
  unfold _root_.GD.N0232.N0720.N1056.d018150
  have hD₀ := _root_.GD.N0232.N0720.N1056.d018148 hK (_root_.GD.N0232.N0720.N1056.d018143 (m := m) (n := n) omega)
  have hD₁ := _root_.GD.N0232.N0720.N1056.d018148 hK (_root_.GD.N0232.N0720.N1056.d018144 (m := m) (n := n) omega)
  exact div_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith))


theorem d018152 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (K : ℝ) (hK : 1 ≤ K) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hA : _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≤ K) :
    _root_.GD.N0232.N0720.N1056.d018150 m n K omega ≤
      _root_.GD.N0232.N0720.N1056.d018130 _root_.GD.N0232.N0720.N1482.d015130 packet weight omega +
        _root_.GD.N0232.N0720.N1056.d018130 _root_.GD.N0232.N0720.N1482.d015131 packet weight
          omega := by
  have h0 := _root_.GD.N0232.N0720.N1056.d018138 _root_.GD.N0232.N0720.N1482.d015130
    packet weight hweight K omega hA
  have h1 := _root_.GD.N0232.N0720.N1056.d018138
    _root_.GD.N0232.N0720.N1482.d015131 packet weight hweight K omega hA
  rw [_root_.GD.N0232.N0720.N1148.d018029, _root_.GD.N0232.N0720.N1148.d018027] at h0
  rw [_root_.GD.N0232.N0720.N1148.d018030, _root_.GD.N0232.N0720.N1148.d018028] at h1
  have hc₀ := _root_.GD.N0232.N0720.N1056.d018143 (m := m) (n := n) omega
  have hc₁ := _root_.GD.N0232.N0720.N1056.d018144 (m := m) (n := n) omega
  have hD₀ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₀
  have hD₁ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₁
  have hT0 := _root_.GD.N0232.N0720.N1056.d018132 _root_.GD.N0232.N0720.N1482.d015130 packet weight
    hweight omega
  have hT1 := _root_.GD.N0232.N0720.N1056.d018132 _root_.GD.N0232.N0720.N1482.d015131
    packet weight hweight omega
  set μ := _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
    _root_.GD.N0232.N0720.N1126.d016415 packet weight omega
  set c₀ := _root_.GD.N0232.N0720.N1056.d018141 m n omega with hc₀def
  set c₁ := _root_.GD.N0232.N0720.N1056.d018142 m n omega with hc₁def
  set D₀ := _root_.GD.N0232.N0720.N1056.d018147 K c₀
  set D₁ := _root_.GD.N0232.N0720.N1056.d018147 K c₁
  set N₀ := _root_.GD.N0232.N0720.N1039.d016523 2 0 μ c₀
  set N₁ := _root_.GD.N0232.N0720.N1039.d016523 3 1 μ c₁
  set T₀ := _root_.GD.N0232.N0720.N1056.d018130 _root_.GD.N0232.N0720.N1482.d015130 packet weight omega
  set T₁ := _root_.GD.N0232.N0720.N1056.d018130 _root_.GD.N0232.N0720.N1482.d015131 packet weight
    omega
  have h0' : N₀ ^ 2 / D₀ ≤ T₀ := h0
  have h1' : N₁ ^ 2 / D₁ ≤ T₁ := h1
  have hfloor := _root_.GD.N0232.N0720.N1056.d018140 μ c₀ c₁
  set α := 4 * (c₀ - 1) ^ 2 with hαdef
  set β := 3 * (c₁ - 1) with hβdef
  have hα : 0 ≤ α := by positivity
  have hβ2 : 0 ≤ β ^ 2 := sq_nonneg _

  have hsum : (N₀ ^ 2 + N₁ ^ 2) / (D₀ + D₁) ≤ N₀ ^ 2 / D₀ + N₁ ^ 2 / D₁ := by
    rw [div_add_div _ _ hD₀.ne' hD₁.ne', div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg N₀) (sq_nonneg D₁), mul_nonneg (sq_nonneg N₁) (sq_nonneg D₀),
      mul_nonneg (sq_nonneg N₀) (mul_nonneg hD₀.le hD₁.le),
      mul_nonneg (sq_nonneg N₁) (mul_nonneg hD₀.le hD₁.le)]
  show α / ((α + β ^ 2) * (D₀ + D₁)) ≤ T₀ + T₁
  by_cases hαβ : α + β ^ 2 = 0
  · have hα0 : α = 0 := by linarith
    rw [hα0, zero_div]
    linarith
  · have hαβpos : 0 < α + β ^ 2 := lt_of_le_of_ne (by linarith) (Ne.symm hαβ)
    have hratio : α / (α + β ^ 2) ≤ N₀ ^ 2 + N₁ ^ 2 := by
      rw [div_le_iff₀ hαβpos]
      linarith [hfloor]
    calc α / ((α + β ^ 2) * (D₀ + D₁)) = (α / (α + β ^ 2)) / (D₀ + D₁) := by
          rw [div_div]
      _ ≤ (N₀ ^ 2 + N₁ ^ 2) / (D₀ + D₁) :=
          div_le_div_of_nonneg_right hratio (by linarith)
      _ ≤ N₀ ^ 2 / D₀ + N₁ ^ 2 / D₁ := hsum
      _ ≤ T₀ + T₁ := add_le_add h0' h1'






theorem d018153 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (K : ℝ) (hK : 1 ≤ K)
    (hmass : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≤ K) :
    (∫ omega, _root_.GD.N0232.N0720.N1056.d018150 m n K omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130 packet
          weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          packet weight := by
  unfold _root_.GD.N0232.N0720.N1056.d018131
  have h0 := _root_.GD.N0232.N0720.N1056.d018137 (m := m) (n := n)
    _root_.GD.N0232.N0720.N1482.d015130 packet weight hweight
  have h1 := _root_.GD.N0232.N0720.N1056.d018137 (m := m) (n := n)
    _root_.GD.N0232.N0720.N1482.d015131 packet weight hweight
  rw [← integral_add h0 h1]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun omega ↦ _root_.GD.N0232.N0720.N1056.d018151 K hK omega
  · exact h0.add h1
  · filter_upwards [hmass] with omega hω
    exact _root_.GD.N0232.N0720.N1056.d018152 packet weight hweight K hK omega hω



theorem d018154 (K : ℝ) : Measurable (_root_.GD.N0232.N0720.N1056.d018150 m n K) := by
  have h₀ := _root_.GD.N0232.N0720.N1056.d018145 (m := m) (n := n)
  have h₁ := _root_.GD.N0232.N0720.N1056.d018146 (m := m) (n := n)
  unfold _root_.GD.N0232.N0720.N1056.d018150 _root_.GD.N0232.N0720.N1056.d018147
  fun_prop


theorem d018155 (K : ℝ) (hK : 1 ≤ K) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1056.d018150 m n K omega ≤
      _root_.GD.N0232.N0720.N1037.d016512 m n _root_.GD.N0232.N0720.N1482.d015130⁻¹ omega := by
  have hc₀ := _root_.GD.N0232.N0720.N1056.d018143 (m := m) (n := n) omega
  have hc₁ := _root_.GD.N0232.N0720.N1056.d018144 (m := m) (n := n) omega
  have hD₀ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₀
  have hD₁ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₁
  have hcD := _root_.GD.N0232.N0720.N1056.d018149 hK hc₀
  have hrec := _root_.GD.N0232.N0720.N1031.d017132
    _root_.GD.N0232.N0720.N1482.d015130 omega
  have hL : _root_.GD.N0232.N0720.N1037.d016512 m n _root_.GD.N0232.N0720.N1482.d015130⁻¹ omega =
      1 / _root_.GD.N0232.N0720.N1056.d018141 m n omega := by
    rw [eq_div_iff hc₀.ne']
    exact hrec
  rw [hL]
  unfold _root_.GD.N0232.N0720.N1056.d018150
  set c₀ := _root_.GD.N0232.N0720.N1056.d018141 m n omega
  set c₁ := _root_.GD.N0232.N0720.N1056.d018142 m n omega
  set D₀ := _root_.GD.N0232.N0720.N1056.d018147 K c₀
  set D₁ := _root_.GD.N0232.N0720.N1056.d018147 K c₁
  set α := 4 * (c₀ - 1) ^ 2
  set β := 3 * (c₁ - 1)
  have hα : 0 ≤ α := by positivity
  have hβ2 : 0 ≤ β ^ 2 := sq_nonneg _
  by_cases hαβ : α + β ^ 2 = 0
  · have hα0 : α = 0 := by linarith
    rw [hα0, zero_div]
    positivity
  · have hαβpos : 0 < α + β ^ 2 := lt_of_le_of_ne (by linarith) (Ne.symm hαβ)
    rw [div_le_div_iff₀ (mul_pos hαβpos (by linarith)) hc₀]
    have h1 : α * c₀ ≤ (α + β ^ 2) * c₀ := mul_le_mul_of_nonneg_right (by linarith) hc₀.le
    have h2 : (α + β ^ 2) * c₀ ≤ (α + β ^ 2) * (D₀ + D₁) :=
      mul_le_mul_of_nonneg_left (by linarith) hαβpos.le
    linarith

theorem d018156 (K : ℝ) (hK : 1 ≤ K) :
    Integrable (_root_.GD.N0232.N0720.N1056.d018150 m n K) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  refine (_root_.GD.N0232.N0720.N1037.d016516 (m := m) (n := n)
    _root_.GD.N0232.N0720.N1482.d015130⁻¹).mono'
    (_root_.GD.N0232.N0720.N1056.d018154 K).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1056.d018151 K hK omega)]
  exact _root_.GD.N0232.N0720.N1056.d018155 K hK omega



theorem d018157 (K : ℝ) (hK : 1 ≤ K)
    (hpos : 0 < _root_.GD.N0232.N0720.N1080.d014172 m n {omega | _root_.GD.N0232.N0720.N1056.d018141 m n omega ≠ 1}) :
    0 < ∫ omega, _root_.GD.N0232.N0720.N1056.d018150 m n K omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun omega ↦ _root_.GD.N0232.N0720.N1056.d018151 K hK omega)
    (_root_.GD.N0232.N0720.N1056.d018156 K hK)]
  refine lt_of_lt_of_le hpos (measure_mono ?_)
  intro omega hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [Function.mem_support]
  have hc₀ := _root_.GD.N0232.N0720.N1056.d018143 (m := m) (n := n) omega
  have hc₁ := _root_.GD.N0232.N0720.N1056.d018144 (m := m) (n := n) omega
  have hD₀ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₀
  have hD₁ := _root_.GD.N0232.N0720.N1056.d018148 hK hc₁
  have hα : 0 < 4 * (_root_.GD.N0232.N0720.N1056.d018141 m n omega - 1) ^ 2 := by
    have : _root_.GD.N0232.N0720.N1056.d018141 m n omega - 1 ≠ 0 := sub_ne_zero.mpr hω
    positivity
  unfold _root_.GD.N0232.N0720.N1056.d018150
  apply div_ne_zero hα.ne'
  apply mul_ne_zero
  · have : 0 ≤ (3 * (_root_.GD.N0232.N0720.N1056.d018142 m n omega - 1)) ^ 2 := sq_nonneg _
    linarith
  · linarith








theorem d018158 (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (ha : g.d009239 ≠ 1) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (hs : s.value ≠ 0) :
    0 < _root_.GD.N0232.N0720.N1080.d014172 m n {omega |
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) ≠ 1} := by
  by_contra hcon
  push Not at hcon
  have hzero : _root_.GD.N0232.N0720.N1080.d014172 m n {omega |
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) ≠ 1} = 0 :=
    nonpos_iff_eq_zero.mp hcon
  have hae : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) = 1 := by
    rw [ae_iff]
    exact hzero
  have htw : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega = 1 := by
    filter_upwards [hae] with omega h
    have hrec := _root_.GD.N0232.N0720.N1031.d017132 g omega
    rw [h, mul_one] at hrec
    exact hrec
  have hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) s.value ≠ ⊤ := s.finiteRisk _
  have hloc := _root_.GD.N0232.N0720.N1108.d018085 g hg
  have hr := _root_.GD.N0232.N0720.N1126.d016430 (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
    s.value hfin
  rw [hloc] at hr
  simp only [sub_zero] at hr
  have hr' : (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) s.value).toReal =
      ‖s.value‖ ^ 2 := by
    rw [hr, _root_.GD.N0230.N0691.d001213 (_root_.GD.N0232.N0720.N1080.d014172 m n) s.value]
    apply integral_congr_ae
    filter_upwards [htw] with omega h
    show _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (s.value omega) ^ 2 = (s.value omega) ^ 2
    rw [h, one_mul]
  have hchar := s.riskCharacter g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
  rw [_root_.GD.N0232.N0720.N1215.d014279, _root_.GD.N0232.N0720.N1080.d014190] at hchar
  have hreal := congrArg ENNReal.toReal hchar
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _), hr'] at hreal
  simp only [zero_sub, norm_neg] at hreal
  have ha2 : g.d009239 ^ 2 ≠ 1 := by
    intro h
    have h' : (g.d009239 - 1) * (g.d009239 + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact ha (by linarith)
    · linarith [g.d009240]
  have hnorm : ‖s.value‖ ^ 2 = 0 := by
    have hz : (1 - g.d009239 ^ 2) * ‖s.value‖ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (by linarith : g.d009239 ^ 2 = 1) ha2
    · exact h
  exact hs (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hnorm))

theorem d018159 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (hs : s.value ≠ 0) :
    0 < _root_.GD.N0232.N0720.N1080.d014172 m n {omega | _root_.GD.N0232.N0720.N1056.d018141 m n omega ≠ 1} :=
  _root_.GD.N0232.N0720.N1056.d018158 _root_.GD.N0232.N0720.N1482.d015130
    _root_.GD.N0232.N0720.N1148.d018027 (by rw [_root_.GD.N0232.N0720.N1148.d018029]; norm_num) s hs







theorem d018160 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (hs : s.value ≠ 0)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (K : ℝ) (hK : 1 ≤ K)
    (hmass : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≤ K) :
    0 < (∫ omega, _root_.GD.N0232.N0720.N1056.d018150 m n K omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ∧
      (∫ omega, _root_.GD.N0232.N0720.N1056.d018150 m n K omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130 packet
            weight +
          _root_.GD.N0232.N0720.N1056.d018131 m n
            _root_.GD.N0232.N0720.N1482.d015131 packet weight :=
  ⟨_root_.GD.N0232.N0720.N1056.d018157 K hK (_root_.GD.N0232.N0720.N1056.d018159 s hs),
    _root_.GD.N0232.N0720.N1056.d018153 packet weight hweight K hK hmass⟩


theorem d018161 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs : s.value ≠ 0) (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (K : ℝ) (hK : 1 ≤ K)
    (hmass : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega ≤ K) :
    ¬ Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130
          (candidate j).packet (candidate j).weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          (candidate j).packet (candidate j).weight) atTop (𝓝 0) := by
  intro h
  have hκ := _root_.GD.N0232.N0720.N1056.d018157 K hK (_root_.GD.N0232.N0720.N1056.d018159 s hs)
  have hev := (tendsto_order.1 h).2 _ hκ
  obtain ⟨j, hj⟩ := hev.exists
  have hall := _root_.GD.N0232.N0720.N1056.d018153 (candidate j).packet (candidate j).weight
    (candidate j).weight_nonneg K hK (hmass j)
  linarith

end

end N1056
end N0720
end N0232
end GD
