import GD.Module0689


















open MeasureTheory

namespace GD.N0232.N0719.N0936

noncomputable section

set_option maxHeartbeats 20000

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1018
open _root_.GD.N0232.N0719.N1015
open _root_.GD.N0237.N0746

variable {k : ℕ} {sizes : Fin k → ℕ}


def d010092 (Γ ε : ℝ) : ℝ :=
  -2 * ε + Γ * ε ^ 2


def d010093 (Γ : ℝ) : ℝ :=
  1 / Γ



def d010094 (C B ε : ℝ) : ℝ :=
  2 * ε * C + ε ^ 2 * B



def d010095 (C B : ℝ) : ℝ :=
  -C / B


theorem d010096
    {Γ : ℝ} (hΓ : Γ ≠ 0) (ε : ℝ) :
    _root_.GD.N0232.N0719.N0936.d010092 Γ ε =
      Γ * (ε - _root_.GD.N0232.N0719.N0936.d010093 Γ) ^ 2 - _root_.GD.N0232.N0719.N0936.d010093 Γ := by
  unfold _root_.GD.N0232.N0719.N0936.d010092 _root_.GD.N0232.N0719.N0936.d010093
  field_simp
  ring


theorem d010097
    {Γ : ℝ} (hΓ : Γ ≠ 0) :
    _root_.GD.N0232.N0719.N0936.d010092 Γ (_root_.GD.N0232.N0719.N0936.d010093 Γ) = -_root_.GD.N0232.N0719.N0936.d010093 Γ := by
  rw [_root_.GD.N0232.N0719.N0936.d010096 hΓ]
  ring


theorem d010098
    {Γ : ℝ} (hΓ : 0 < Γ) (ε : ℝ) :
    _root_.GD.N0232.N0719.N0936.d010092 Γ (_root_.GD.N0232.N0719.N0936.d010093 Γ) ≤
      _root_.GD.N0232.N0719.N0936.d010092 Γ ε := by
  calc
    _root_.GD.N0232.N0719.N0936.d010092 Γ (_root_.GD.N0232.N0719.N0936.d010093 Γ) =
        -_root_.GD.N0232.N0719.N0936.d010093 Γ :=
      _root_.GD.N0232.N0719.N0936.d010097 (ne_of_gt hΓ)
    _ ≤ Γ * (ε - _root_.GD.N0232.N0719.N0936.d010093 Γ) ^ 2 - _root_.GD.N0232.N0719.N0936.d010093 Γ := by
      simpa using sub_le_sub_right
        (mul_nonneg (le_of_lt hΓ) (sq_nonneg (ε - _root_.GD.N0232.N0719.N0936.d010093 Γ)))
        (_root_.GD.N0232.N0719.N0936.d010093 Γ)
    _ = _root_.GD.N0232.N0719.N0936.d010092 Γ ε :=
      (_root_.GD.N0232.N0719.N0936.d010096 (ne_of_gt hΓ) ε).symm


theorem d010099
    {Γ : ℝ} (hΓ : 0 < Γ) (ε : ℝ) :
    _root_.GD.N0232.N0719.N0936.d010092 Γ ε =
        _root_.GD.N0232.N0719.N0936.d010092 Γ (_root_.GD.N0232.N0719.N0936.d010093 Γ) ↔
      ε = _root_.GD.N0232.N0719.N0936.d010093 Γ := by
  rw [_root_.GD.N0232.N0719.N0936.d010096 (ne_of_gt hΓ),
    _root_.GD.N0232.N0719.N0936.d010097 (ne_of_gt hΓ)]
  constructor
  · intro h
    have hmul : Γ * (ε - _root_.GD.N0232.N0719.N0936.d010093 Γ) ^ 2 = 0 := by
      linarith
    have hz : (ε - _root_.GD.N0232.N0719.N0936.d010093 Γ) ^ 2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hΓ)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    rw [h]
    ring


theorem d010100 {Γ : ℝ} (hΓ : 0 < Γ) :
    0 < _root_.GD.N0232.N0719.N0936.d010093 Γ := by
  exact one_div_pos.mpr hΓ



theorem d010101
    {C B : ℝ} (hB : B ≠ 0) (ε : ℝ) :
    _root_.GD.N0232.N0719.N0936.d010094 C B ε =
      B * (ε - _root_.GD.N0232.N0719.N0936.d010095 C B) ^ 2 - C ^ 2 / B := by
  unfold _root_.GD.N0232.N0719.N0936.d010094 _root_.GD.N0232.N0719.N0936.d010095
  field_simp [hB]
  ring



theorem d010102
    {C B : ℝ} (hB : 0 < B) (ε : ℝ) :
    _root_.GD.N0232.N0719.N0936.d010094 C B (_root_.GD.N0232.N0719.N0936.d010095 C B) ≤
      _root_.GD.N0232.N0719.N0936.d010094 C B ε := by
  rw [_root_.GD.N0232.N0719.N0936.d010101 (ne_of_gt hB),
    _root_.GD.N0232.N0719.N0936.d010101 (ne_of_gt hB)]
  have hnonneg : 0 ≤ B * (ε - _root_.GD.N0232.N0719.N0936.d010095 C B) ^ 2 :=
    mul_nonneg (le_of_lt hB) (sq_nonneg _)
  simpa using sub_le_sub_right hnonneg (C ^ 2 / B)


theorem d010103
    {C B : ℝ} (hB : B ≠ 0) :
    _root_.GD.N0232.N0719.N0936.d010094 C B (_root_.GD.N0232.N0719.N0936.d010095 C B) = -C ^ 2 / B := by
  rw [_root_.GD.N0232.N0719.N0936.d010101 hB]
  ring









theorem d010104
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    0 < cert.gamma := by
  have henergy_nonneg :
      0 ≤ _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle := by
    unfold _root_.GD.N0232.N0719.N1015.d010081
    exact integral_nonneg fun _ ↦ sq_nonneg _
  by_contra hnot
  have hgamma_zero : cert.gamma = 0 :=
    le_antisymm (le_of_not_gt hnot) cert.gamma_nonneg
  have henergy_le_zero :
      _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle ≤ 0 := by
    simpa [hgamma_zero] using cert.energy_le θ
  have henergy_zero :
      _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle = 0 :=
    le_antisymm henergy_le_zero henergy_nonneg
  have hsq_ae :
      (fun ω ↦ (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2) =ᵐ[law θ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (fun ω ↦ sq_nonneg (_root_.GD.N0232.N0719.N1015.d010079 triangle ω))
      (cert.correction_sq_integrable θ)).mp
    simpa [_root_.GD.N0232.N0719.N1015.d010081] using henergy_zero
  have hcorrection_ae :
      _root_.GD.N0232.N0719.N1015.d010079 triangle =ᵐ[law θ] 0 := by
    filter_upwards [hsq_ae] with ω hω
    simp only [Pi.zero_apply] at hω ⊢
    exact sq_eq_zero_iff.mp hω
  have hproduct_ae :
      (fun ω ↦
        _root_.GD.N0232.N0719.N1015.d010078 (target θ) ω *
          _root_.GD.N0232.N0719.N1015.d010079 triangle ω) =ᵐ[law θ]
        0 := by
    filter_upwards [hcorrection_ae] with ω hω
    simp [hω]
  have hcross_zero :
      _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle = 0 := by
    unfold _root_.GD.N0232.N0719.N1015.d010080
    rw [integral_congr_ae hproduct_ae]
    simp
  linarith [cert.cross_negative θ]




theorem d010105
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    0 < _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle := by
  have hnonneg :
      0 ≤ _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle := by
    unfold _root_.GD.N0232.N0719.N1015.d010081
    exact integral_nonneg fun _ ↦ sq_nonneg _
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have henergy_zero :
      _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle = 0 :=
    hzero.symm
  have hsq_ae :
      (fun ω ↦ (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2) =ᵐ[law θ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (fun ω ↦ sq_nonneg (_root_.GD.N0232.N0719.N1015.d010079 triangle ω))
      (cert.correction_sq_integrable θ)).mp
    simpa [_root_.GD.N0232.N0719.N1015.d010081] using henergy_zero
  have hcorrection_ae :
      _root_.GD.N0232.N0719.N1015.d010079 triangle =ᵐ[law θ] 0 := by
    filter_upwards [hsq_ae] with ω hω
    simp only [Pi.zero_apply] at hω ⊢
    exact sq_eq_zero_iff.mp hω
  have hcross_zero :
      _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle = 0 := by
    unfold _root_.GD.N0232.N0719.N1015.d010080
    apply integral_eq_zero_of_ae
    filter_upwards [hcorrection_ae] with ω hω
    simp [hω]
  linarith [cert.cross_negative θ]




theorem d010106
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    _root_.GD.N0232.N0719.N0936.d010093 cert.gamma ≤
      _root_.GD.N0232.N0719.N0936.d010095
        (_root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle)
        (_root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle) := by
  let C := _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle
  let B := _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle
  have hΓ : 0 < cert.gamma := _root_.GD.N0232.N0719.N0936.d010104 cert θ
  have hB : 0 < B := _root_.GD.N0232.N0719.N0936.d010105 cert θ
  have hcap : B ≤ cert.gamma * (-C) := cert.energy_le θ
  dsimp [_root_.GD.N0232.N0719.N0936.d010093, _root_.GD.N0232.N0719.N0936.d010095, C, B]
  rw [div_le_div_iff₀ hΓ hB]
  nlinarith



theorem d010107
    {Θ : Type*} [Nonempty Θ]
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle) :
    0 < cert.gamma := by
  exact _root_.GD.N0232.N0719.N0936.d010104 cert
    (Classical.choice (inferInstance : Nonempty Θ))






theorem d010108
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    2 * _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
        _root_.GD.N0232.N0719.N0936.d010093 cert.gamma ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle ≤
      _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
        _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
  have hΓ : 0 < cert.gamma := _root_.GD.N0232.N0719.N0936.d010104 cert θ
  let ε := _root_.GD.N0232.N0719.N0936.d010093 cert.gamma
  let C := _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle
  let B := _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle
  have hcap : B ≤ cert.gamma * (-C) := cert.energy_le θ
  have hεnonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hscaled : ε ^ 2 * B ≤ ε ^ 2 * (cert.gamma * (-C)) :=
    mul_le_mul_of_nonneg_left hcap hεnonneg
  calc
    2 * _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
        _root_.GD.N0232.N0719.N0936.d010093 cert.gamma ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle =
        2 * ε * C + ε ^ 2 * B := by rfl
    _ ≤ 2 * ε * C + ε ^ 2 * (cert.gamma * (-C)) :=
      by linarith
    _ = ε * C := by
      dsimp [ε, _root_.GD.N0232.N0719.N0936.d010093]
      field_simp [ne_of_gt hΓ]
      ring
    _ = _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by rfl


theorem d010109
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    2 * _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
        _root_.GD.N0232.N0719.N0936.d010093 cert.gamma ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle < 0 := by
  have hΓ : 0 < cert.gamma := _root_.GD.N0232.N0719.N0936.d010104 cert θ
  have hle :=
    _root_.GD.N0232.N0719.N0936.d010108 cert θ
  have hstep : 0 < _root_.GD.N0232.N0719.N0936.d010093 cert.gamma := _root_.GD.N0232.N0719.N0936.d010100 hΓ
  have hcross :
      _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle < 0 :=
    cert.cross_negative θ
  exact hle.trans_lt (mul_neg_of_pos_of_neg hstep hcross)




theorem d010110
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    2 * _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
        _root_.GD.N0232.N0719.N0936.d010093 cert.gamma ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle <
      2 * _root_.GD.N0232.N0719.N1015.d010083 cert *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
        _root_.GD.N0232.N0719.N1015.d010083 cert ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle := by
  let Γ := cert.gamma
  let C := _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle
  let B := _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle
  let εstar := _root_.GD.N0232.N0719.N0936.d010093 Γ
  let εsafe := _root_.GD.N0232.N0719.N1015.d010083 cert
  have hΓ : 0 < Γ := _root_.GD.N0232.N0719.N0936.d010104 cert θ
  have hC : C < 0 := cert.cross_negative θ
  have hcap : B ≤ Γ * (-C) := cert.energy_le θ
  have hstar : 0 < εstar := _root_.GD.N0232.N0719.N0936.d010100 hΓ
  have hsafe : 0 < εsafe := _root_.GD.N0232.N0719.N1015.d010084 cert
  have hsafelt : εsafe < εstar := by
    dsimp [εsafe, εstar, _root_.GD.N0232.N0719.N1015.d010083, _root_.GD.N0232.N0719.N0936.d010093, Γ]
    have hden : 0 < 1 + cert.gamma := by linarith
    exact (div_lt_div_iff₀ hden hΓ).2 (by nlinarith)
  have hsum_nonneg : 0 ≤ εstar + εsafe := by positivity
  have hscaled :
      (εstar + εsafe) * B ≤
        (εstar + εsafe) * (Γ * (-C)) :=
    mul_le_mul_of_nonneg_left hcap hsum_nonneg
  have hcoefficient : (εstar + εsafe) * Γ < 2 := by
    have hstarGamma : εstar * Γ = 1 := by
      dsimp [εstar, _root_.GD.N0232.N0719.N0936.d010093]
      exact div_mul_cancel₀ 1 (ne_of_gt hΓ)
    have hsafeGamma : εsafe * Γ < 1 := by
      simpa [εsafe, Γ] using _root_.GD.N0232.N0719.N1015.d010086 cert
    calc
      (εstar + εsafe) * Γ =
          εstar * Γ + εsafe * Γ := by ring
      _ = 1 + εsafe * Γ := by rw [hstarGamma]
      _ < 2 := by linarith
  have hscaled_strict :
      (εstar + εsafe) * B < 2 * (-C) := by
    calc
      (εstar + εsafe) * B ≤
          (εstar + εsafe) * (Γ * (-C)) := hscaled
      _ = ((εstar + εsafe) * Γ) * (-C) := by ring
      _ < 2 * (-C) :=
        mul_lt_mul_of_pos_right hcoefficient (neg_pos.mpr hC)
  have hbracket : 2 * C + (εstar + εsafe) * B < 0 := by
    linarith
  have hproduct :
      (εstar - εsafe) *
          (2 * C + (εstar + εsafe) * B) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hsafelt) hbracket
  dsimp [εstar, εsafe, C, B, Γ] at hproduct ⊢
  nlinarith


theorem d010111
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle (_root_.GD.N0232.N0719.N0936.d010093 cert.gamma) ω -
          target θ) ^ 2 ∂law θ) -
        ∫ ω,
          (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - target θ) ^ 2 ∂law θ ≤
      _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
        _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
  let ε := _root_.GD.N0232.N0719.N0936.d010093 cert.gamma
  let r : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ :=
    _root_.GD.N0232.N0719.N1015.d010078 (target θ)
  let h : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := -_root_.GD.N0232.N0719.N1015.d010079 triangle
  have hr : Integrable (fun ω ↦ (r ω) ^ 2) (law θ) :=
    cert.residual_sq_integrable θ
  have hh : Integrable (fun ω ↦ (h ω) ^ 2) (law θ) := by
    simpa [h] using cert.correction_sq_integrable θ
  have hrh : Integrable (fun ω ↦ r ω * h ω) (law θ) := by
    simpa [r, h, mul_neg] using (cert.cross_integrable θ).neg
  have hid := _root_.GD.N0237.N0746.d004286 (law θ) ε r h hr hh hrh
  have hgain :
      _root_.GD.N0237.N0746.d004280 (law θ) r h =
        -_root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
    unfold _root_.GD.N0237.N0746.d004280 _root_.GD.N0232.N0719.N1015.d010080 r h _root_.GD.N0232.N0719.N1015.d010078
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Pi.neg_apply]
    ring
  have henergy :
      _root_.GD.N0237.N0746.d004281
          (law θ) h =
        _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle := by
    unfold _root_.GD.N0237.N0746.d004281
      _root_.GD.N0232.N0719.N1015.d010081 h
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Pi.neg_apply]
    ring
  rw [hgain, henergy] at hid
  have hbound := _root_.GD.N0232.N0719.N0936.d010108 cert θ
  have hdiff :
      (∫ ω, (r ω - ε * h ω) ^ 2 ∂law θ) -
          ∫ ω, (r ω) ^ 2 ∂law θ ≤
        _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
    rw [hid]
    simpa [ε, add_comm] using hbound
  simpa only [r, h, _root_.GD.N0232.N0719.N1015.d010078, ε,
    _root_.GD.N0232.N0719.N1015.d010089, Pi.neg_apply] using hdiff



theorem d010112
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle (_root_.GD.N0232.N0719.N0936.d010093 cert.gamma) ω -
          target θ) ^ 2 ∂law θ) <
      ∫ ω,
        (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - target θ) ^ 2 ∂law θ := by
  have hbound :=
    _root_.GD.N0232.N0719.N0936.d010111 cert θ
  have hΓ : 0 < cert.gamma := _root_.GD.N0232.N0719.N0936.d010104 cert θ
  have hright :
      _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle < 0 :=
    mul_neg_of_pos_of_neg (_root_.GD.N0232.N0719.N0936.d010100 hΓ) (cert.cross_negative θ)
  linarith



theorem d010113
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle (_root_.GD.N0232.N0719.N0936.d010093 cert.gamma) ω -
          target θ) ^ 2 ∂law θ) <
      ∫ ω,
        (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle (_root_.GD.N0232.N0719.N1015.d010083 cert) ω -
          target θ) ^ 2 ∂law θ := by
  let r : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ :=
    _root_.GD.N0232.N0719.N1015.d010078 (target θ)
  let h : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := -_root_.GD.N0232.N0719.N1015.d010079 triangle
  have hr : Integrable (fun ω ↦ (r ω) ^ 2) (law θ) :=
    cert.residual_sq_integrable θ
  have hh : Integrable (fun ω ↦ (h ω) ^ 2) (law θ) := by
    simpa [h] using cert.correction_sq_integrable θ
  have hrh : Integrable (fun ω ↦ r ω * h ω) (law θ) := by
    simpa [r, h, mul_neg] using (cert.cross_integrable θ).neg
  have hgain :
      _root_.GD.N0237.N0746.d004280 (law θ) r h =
        -_root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
    unfold _root_.GD.N0237.N0746.d004280 _root_.GD.N0232.N0719.N1015.d010080 r h _root_.GD.N0232.N0719.N1015.d010078
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Pi.neg_apply]
    ring
  have henergy :
      _root_.GD.N0237.N0746.d004281
          (law θ) h =
        _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle := by
    unfold _root_.GD.N0237.N0746.d004281
      _root_.GD.N0232.N0719.N1015.d010081 h
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Pi.neg_apply]
    ring
  have hopt := _root_.GD.N0237.N0746.d004286
    (law θ) (_root_.GD.N0232.N0719.N0936.d010093 cert.gamma) r h hr hh hrh
  have hsafe := _root_.GD.N0237.N0746.d004286
    (law θ) (_root_.GD.N0232.N0719.N1015.d010083 cert) r h hr hh hrh
  rw [hgain, henergy] at hopt hsafe
  have hincrement :=
    _root_.GD.N0232.N0719.N0936.d010110 cert θ
  have hopt' :
      (∫ ω,
          (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle (_root_.GD.N0232.N0719.N0936.d010093 cert.gamma) ω -
            target θ) ^ 2 ∂law θ) -
          ∫ ω, (r ω) ^ 2 ∂law θ =
        2 * _root_.GD.N0232.N0719.N0936.d010093 cert.gamma *
            _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
          _root_.GD.N0232.N0719.N0936.d010093 cert.gamma ^ 2 *
            _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle := by
    simp only [_root_.GD.N0232.N0719.N1015.d010089]
    change
      (∫ ω,
          (r ω - _root_.GD.N0232.N0719.N0936.d010093 cert.gamma * h ω) ^ 2 ∂law θ) -
          ∫ ω, (r ω) ^ 2 ∂law θ = _
    rw [hopt]
    ring
  have hsafe' :
      (∫ ω,
          (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle (_root_.GD.N0232.N0719.N1015.d010083 cert) ω -
            target θ) ^ 2 ∂law θ) -
          ∫ ω, (r ω) ^ 2 ∂law θ =
        2 * _root_.GD.N0232.N0719.N1015.d010083 cert *
            _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
          _root_.GD.N0232.N0719.N1015.d010083 cert ^ 2 *
            _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle := by
    simp only [_root_.GD.N0232.N0719.N1015.d010089]
    change
      (∫ ω,
          (r ω - _root_.GD.N0232.N0719.N1015.d010083 cert * h ω) ^ 2 ∂law θ) -
          ∫ ω, (r ω) ^ 2 ∂law θ = _
    rw [hsafe]
    ring
  linarith

end

end GD.N0232.N0719.N0936
