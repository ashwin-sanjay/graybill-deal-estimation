import GD.Module0687
import GD.Module0290



















open MeasureTheory

namespace GD.N0232.N0719.N1015

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1018
open _root_.GD.N0237.N0746

variable {k : ℕ} {sizes : Fin k → ℕ}


def d010078
    (target : ℝ) :
    _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ :=
  fun ω ↦ _root_.GD.N0232.N0719.N0900.d009111 k sizes ω - target


def d010079
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ :=
  fun ω ↦ _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)



def d010080
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes))
    (target : ℝ) (triangle : Fin 3 ↪ Fin k) : ℝ :=
  ∫ ω, _root_.GD.N0232.N0719.N1015.d010078 target ω * _root_.GD.N0232.N0719.N1015.d010079 triangle ω ∂μ


def d010081
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes))
    (triangle : Fin 3 ↪ Fin k) : ℝ :=
  ∫ ω, (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2 ∂μ









structure d010082
    (Θ : Type*)
    (law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes))
    (target : Θ → ℝ)
    (triangle : Fin 3 ↪ Fin k) where
  gamma : ℝ
  gamma_nonneg : 0 ≤ gamma
  residual_sq_integrable :
    ∀ θ,
      Integrable (fun ω ↦ (_root_.GD.N0232.N0719.N1015.d010078 (target θ) ω) ^ 2) (law θ)
  correction_sq_integrable :
    ∀ θ,
      Integrable (fun ω ↦ (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2) (law θ)
  cross_integrable :
    ∀ θ,
      Integrable
        (fun ω ↦
          _root_.GD.N0232.N0719.N1015.d010078 (target θ) ω * _root_.GD.N0232.N0719.N1015.d010079 triangle ω)
        (law θ)
  cross_negative :
    ∀ θ, _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle < 0
  energy_le :
    ∀ θ,
      _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle ≤
        gamma * (-_root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle)


def d010083
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle) : ℝ :=
  1 / (1 + cert.gamma)

theorem d010084
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle) :
    0 < _root_.GD.N0232.N0719.N1015.d010083 cert := by
  unfold _root_.GD.N0232.N0719.N1015.d010083
  exact one_div_pos.mpr (by linarith [cert.gamma_nonneg])

theorem d010085
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle) :
    _root_.GD.N0232.N0719.N1015.d010083 cert * cert.gamma < 2 := by
  have hden : 0 < 1 + cert.gamma := by
    linarith [cert.gamma_nonneg]
  have hfrac : cert.gamma / (1 + cert.gamma) < 1 :=
    (div_lt_one hden).2 (by linarith)
  calc
    _root_.GD.N0232.N0719.N1015.d010083 cert * cert.gamma =
        cert.gamma / (1 + cert.gamma) := by
      unfold _root_.GD.N0232.N0719.N1015.d010083
      ring
    _ < 1 := hfrac
    _ < 2 := by norm_num






theorem d010086
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle) :
    _root_.GD.N0232.N0719.N1015.d010083 cert * cert.gamma < 1 := by
  have hden : 0 < 1 + cert.gamma := by
    linarith [cert.gamma_nonneg]
  have hfrac : cert.gamma / (1 + cert.gamma) < 1 :=
    (div_lt_one hden).2 (by linarith)
  calc
    _root_.GD.N0232.N0719.N1015.d010083 cert * cert.gamma =
        cert.gamma / (1 + cert.gamma) := by
      unfold _root_.GD.N0232.N0719.N1015.d010083
      ring
    _ < 1 := hfrac



theorem d010087
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    2 * _root_.GD.N0232.N0719.N1015.d010083 cert *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
        _root_.GD.N0232.N0719.N1015.d010083 cert ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle < 0 := by
  let ε := _root_.GD.N0232.N0719.N1015.d010083 cert
  let C := _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle
  let B := _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle
  have hC : C < 0 := cert.cross_negative θ
  have hB : 0 ≤ B := by
    unfold B _root_.GD.N0232.N0719.N1015.d010081
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hcap : B ≤ cert.gamma * (-C) := cert.energy_le θ
  have hε : 0 < ε := _root_.GD.N0232.N0719.N1015.d010084 cert
  have hstep : ε * cert.gamma < 2 :=
    _root_.GD.N0232.N0719.N1015.d010085 cert
  have hscaled :
      ε ^ 2 * B ≤ ε ^ 2 * (cert.gamma * (-C)) :=
    mul_le_mul_of_nonneg_left hcap (sq_nonneg ε)
  have hmain :
      2 * ε * C + ε ^ 2 * B ≤
        ε * (-C) * (ε * cert.gamma - 2) := by
    nlinarith
  have hleft : 0 < ε * (-C) :=
    mul_pos hε (neg_pos.mpr hC)
  have hright : ε * cert.gamma - 2 < 0 :=
    sub_neg.mpr hstep
  have hneg :
      ε * (-C) * (ε * cert.gamma - 2) < 0 :=
    mul_neg_of_pos_of_neg hleft hright
  dsimp [ε, C, B] at hmain hneg ⊢
  exact lt_of_le_of_lt hmain hneg









theorem d010088
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    2 * _root_.GD.N0232.N0719.N1015.d010083 cert *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
        _root_.GD.N0232.N0719.N1015.d010083 cert ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle <
      _root_.GD.N0232.N0719.N1015.d010083 cert *
        _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
  let ε := _root_.GD.N0232.N0719.N1015.d010083 cert
  let C := _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle
  let B := _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle
  have hC : C < 0 := cert.cross_negative θ
  have hcap : B ≤ cert.gamma * (-C) := cert.energy_le θ
  have hε : 0 < ε := _root_.GD.N0232.N0719.N1015.d010084 cert
  have hstep : ε * cert.gamma < 1 :=
    _root_.GD.N0232.N0719.N1015.d010086 cert
  have hscaled :
      ε ^ 2 * B ≤ ε ^ 2 * (cert.gamma * (-C)) :=
    mul_le_mul_of_nonneg_left hcap (sq_nonneg ε)
  have hmain :
      2 * ε * C + ε ^ 2 * B ≤
        ε * (-C) * (ε * cert.gamma - 2) := by
    nlinarith
  have hleft : 0 < ε * (-C) :=
    mul_pos hε (neg_pos.mpr hC)
  have hfactor : ε * cert.gamma - 2 < -1 := by
    linarith
  calc
    2 * _root_.GD.N0232.N0719.N1015.d010083 cert *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle +
        _root_.GD.N0232.N0719.N1015.d010083 cert ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law θ) triangle =
        2 * ε * C + ε ^ 2 * B := by rfl
    _ ≤ ε * (-C) * (ε * cert.gamma - 2) := hmain
    _ < ε * (-C) * (-1) :=
      mul_lt_mul_of_pos_left hfactor hleft
    _ = _root_.GD.N0232.N0719.N1015.d010083 cert *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
      dsimp [ε, C]
      ring




theorem d010089
    (triangle : Fin 3 ↪ Fin k) (ε target : ℝ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N1018.d010023 k sizes triangle ε ω - target =
      _root_.GD.N0232.N0719.N1015.d010078 target ω - ε * (-_root_.GD.N0232.N0719.N1015.d010079 triangle ω) := by
  unfold _root_.GD.N0232.N0719.N1018.d010023 _root_.GD.N0232.N0719.N1018.d010022 _root_.GD.N0232.N0719.N1015.d010078 _root_.GD.N0232.N0719.N1015.d010079 _root_.GD.N0232.N0719.N0900.d009111
  ring







theorem d010090
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle)
    (θ : Θ) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle (_root_.GD.N0232.N0719.N1015.d010083 cert) ω -
          target θ) ^ 2 ∂law θ) -
        ∫ ω,
          (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - target θ) ^ 2 ∂law θ <
      _root_.GD.N0232.N0719.N1015.d010083 cert *
        _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
  let ε := _root_.GD.N0232.N0719.N1015.d010083 cert
  let r : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := _root_.GD.N0232.N0719.N1015.d010078 (target θ)
  let h : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := -_root_.GD.N0232.N0719.N1015.d010079 triangle
  have hr : Integrable (fun ω ↦ (r ω) ^ 2) (law θ) :=
    cert.residual_sq_integrable θ
  have hh : Integrable (fun ω ↦ (h ω) ^ 2) (law θ) := by
    simpa [h] using cert.correction_sq_integrable θ
  have hrh : Integrable (fun ω ↦ r ω * h ω) (law θ) := by
    have hcross := cert.cross_integrable θ
    simpa [r, h, mul_neg] using hcross.neg
  have hid :=
    _root_.GD.N0237.N0746.d004286 (law θ) ε r h hr hh hrh
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
  have hmargin :=
    _root_.GD.N0232.N0719.N1015.d010088 cert θ
  have hdiff :
      (∫ ω, (r ω - ε * h ω) ^ 2 ∂law θ) -
          ∫ ω, (r ω) ^ 2 ∂law θ <
        _root_.GD.N0232.N0719.N1015.d010083 cert *
          _root_.GD.N0232.N0719.N1015.d010080 (law θ) (target θ) triangle := by
    rw [hid]
    simpa [ε, add_comm] using hmargin
  simpa only [r, h, _root_.GD.N0232.N0719.N1015.d010078, ε, _root_.GD.N0232.N0719.N1015.d010089, Pi.neg_apply] using hdiff







theorem d010091
    {Θ : Type*}
    {law : Θ → Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Θ → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Θ law target triangle) :
    ∀ θ,
      (∫ ω,
          (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle (_root_.GD.N0232.N0719.N1015.d010083 cert) ω -
            target θ) ^ 2 ∂law θ) <
        ∫ ω,
          (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - target θ) ^ 2 ∂law θ := by
  intro θ
  let ε := _root_.GD.N0232.N0719.N1015.d010083 cert
  let r : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := _root_.GD.N0232.N0719.N1015.d010078 (target θ)
  let h : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := -_root_.GD.N0232.N0719.N1015.d010079 triangle
  have hr :
      Integrable (fun ω ↦ (r ω) ^ 2) (law θ) :=
    cert.residual_sq_integrable θ
  have hh :
      Integrable (fun ω ↦ (h ω) ^ 2) (law θ) := by
    simpa [h] using cert.correction_sq_integrable θ
  have hrh :
      Integrable (fun ω ↦ r ω * h ω) (law θ) := by
    have hcross := cert.cross_integrable θ
    simpa [r, h, mul_neg] using hcross.neg
  have hid :=
    _root_.GD.N0237.N0746.d004286
      (law θ) ε r h hr hh hrh
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
    unfold
      _root_.GD.N0237.N0746.d004281
      _root_.GD.N0232.N0719.N1015.d010081 h
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Pi.neg_apply]
    ring
  rw [hgain, henergy] at hid
  have hneg := _root_.GD.N0232.N0719.N1015.d010087 cert θ
  have hdiff :
      (∫ ω, (r ω - ε * h ω) ^ 2 ∂law θ) -
          ∫ ω, (r ω) ^ 2 ∂law θ < 0 := by
    rw [hid]
    simpa [ε, add_comm] using hneg
  have hlt :
      (∫ ω, (r ω - ε * h ω) ^ 2 ∂law θ) <
        ∫ ω, (r ω) ^ 2 ∂law θ := by
    linarith
  simpa only [r, h, _root_.GD.N0232.N0719.N1015.d010078, ε, _root_.GD.N0232.N0719.N1015.d010089, Pi.neg_apply] using hlt

end

end GD.N0232.N0719.N1015
