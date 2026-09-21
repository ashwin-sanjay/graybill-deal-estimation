import GD.Module0750






























open MeasureTheory
open scoped BigOperators

namespace GD.N0232.N0719.N0944

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1015
open _root_.GD.N0232.N0719.N0852
open _root_.GD.N0232.N0719.N0874
open _root_.GD.N0232.N0719.N0851
open _root_.GD.N0232.N0719.N0943
open _root_.GD.N0232.N0719.N1005
open _root_.GD.N0237.N0746



def d011270
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) (alpha : ℝ) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  fun ω =>
    _root_.GD.N0232.N0719.N0900.d009111 k sizes ω +
      alpha * _root_.GD.N0232.N0719.N0943.d011242 hk sizes ω

@[fun_prop]
theorem d011271
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) (alpha : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0944.d011270 hk sizes alpha) := by
  unfold _root_.GD.N0232.N0719.N0944.d011270
  fun_prop

@[simp]
theorem d011272
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) :
    _root_.GD.N0232.N0719.N0944.d011270 hk sizes 0 = _root_.GD.N0232.N0719.N0900.d009111 k sizes := by
  funext ω
  unfold _root_.GD.N0232.N0719.N0944.d011270
  ring

@[simp]
theorem d011273
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) :
    _root_.GD.N0232.N0719.N0944.d011270 hk sizes 1 =
      _root_.GD.N0232.N0719.N0943.d011243 hk sizes := by
  funext ω
  unfold _root_.GD.N0232.N0719.N0944.d011270 _root_.GD.N0232.N0719.N0943.d011243
  ring





theorem d011274
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) (alpha : ℝ)
    (τ : Equiv.Perm (Fin k)) (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0944.d011270 hk (sizes ∘ τ) alpha
        (_root_.GD.N0232.N0719.N0851.d010783 sizes τ ω) =
      _root_.GD.N0232.N0719.N0944.d011270 hk sizes alpha ω := by
  unfold _root_.GD.N0232.N0719.N0944.d011270
  rw [_root_.GD.N0232.N0719.N0851.d010787,
    _root_.GD.N0232.N0719.N0943.d011251]



theorem d011275
    {k : ℕ} (hk : 3 ≤ k)
    {sizes : Fin k → ℕ} (hsizes : ∀ i, 0 < sizes i)
    (alpha location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0944.d011270 hk sizes alpha
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      location + scale * _root_.GD.N0232.N0719.N0944.d011270 hk sizes alpha ω := by
  unfold _root_.GD.N0232.N0719.N0944.d011270
  rw [_root_.GD.N0232.N0719.N0900.d009146 (by omega) hsizes location hscale,
    _root_.GD.N0232.N0719.N0943.d011254
      hk hsizes location hscale]
  ring




theorem d011276
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location alpha : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0944.d011270 hk sizes alpha ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) -
      ∫ ω, (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales =
      2 * alpha *
          _root_.GD.N0232.N0719.N0874.d010193 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
            (_root_.GD.N0232.N0719.N1015.d010078 location)
            (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
            (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) +
        alpha ^ 2 *
          _root_.GD.N0232.N0719.N0874.d010194 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
            (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
            (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes location scales
  let r : _root_.GD.N0232.N0719.d009173 k sizes → ℝ := _root_.GD.N0232.N0719.N1015.d010078 location
  let u := _root_.GD.N0232.N0719.N0943.d011242 hk sizes
  let h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ := -u
  have hr : Integrable (fun ω => (r ω) ^ 2) μ := by
    exact (_root_.GD.N0232.N0719.N0910.d010294
      sizes (by omega) hsizes location scales).integrable_sq
  have hu : Integrable (fun ω => (u ω) ^ 2) μ := by
    exact _root_.GD.N0232.N0719.N0943.d011264
      hk sizes hsizes location scales hscales
  have hh : Integrable (fun ω => (h ω) ^ 2) μ := by
    simpa [h] using hu
  have hru : Integrable (fun ω => r ω * u ω) μ := by
    exact _root_.GD.N0232.N0719.N0943.d011265
      hk sizes hsizes location scales hscales
  have hrh : Integrable (fun ω => r ω * h ω) μ := by
    simpa [h, mul_neg] using hru.neg
  have hid := _root_.GD.N0237.N0746.d004286 μ alpha r h hr hh hrh
  have hgain : _root_.GD.N0237.N0746.d004280 μ r h =
      -_root_.GD.N0232.N0719.N0874.d010193 μ r
        (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
        (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) := by
    unfold _root_.GD.N0237.N0746.d004280 _root_.GD.N0232.N0719.N0874.d010193 h u
      _root_.GD.N0232.N0719.N0943.d011242
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Pi.neg_apply]
    ring
  have henergy :
      _root_.GD.N0237.N0746.d004281 μ h =
      _root_.GD.N0232.N0719.N0874.d010194 μ
        (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
        (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) := by
    unfold _root_.GD.N0237.N0746.d004281
      _root_.GD.N0232.N0719.N0874.d010194 h u _root_.GD.N0232.N0719.N0943.d011242
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Pi.neg_apply]
    ring
  rw [hgain, henergy] at hid
  have herror :
      (fun ω =>
        _root_.GD.N0232.N0719.N0944.d011270 hk sizes alpha ω - location) =
        (fun ω => r ω - alpha * h ω) := by
    funext ω
    unfold _root_.GD.N0232.N0719.N0944.d011270 r h u
      _root_.GD.N0232.N0719.N1015.d010078 _root_.GD.N0232.N0719.N0900.d009111
    simp only [Pi.neg_apply]
    ring
  change
    (∫ ω,
        ((fun ω =>
          _root_.GD.N0232.N0719.N0944.d011270 hk sizes alpha ω - location) ω) ^ 2
          ∂μ) -
      ∫ ω, (r ω) ^ 2 ∂μ = _
  rw [herror]
  change (∫ ω, (r ω - alpha * h ω) ^ 2 ∂μ) -
      ∫ ω, (r ω) ^ 2 ∂μ = _
  rw [hid]
  ring



theorem d011277
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha2 : alpha < 2)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0944.d011270 hk sizes alpha ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) <
      ∫ ω, (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes location scales
  let C := _root_.GD.N0232.N0719.N0874.d010193 μ (_root_.GD.N0232.N0719.N1015.d010078 location)
    (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
    (_root_.GD.N0232.N0719.N0943.d011241 hk sizes)
  let B := _root_.GD.N0232.N0719.N0874.d010194 μ
    (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
    (_root_.GD.N0232.N0719.N0943.d011241 hk sizes)
  have hexact := _root_.GD.N0232.N0719.N0944.d011276
    hk sizes hsizes location alpha scales hscales
  have hcap :=
    _root_.GD.N0232.N0719.N0943.d011263
      hk sizes hsizes location scales hscales
  have hC : C < 0 := hcap.1
  have hbound : 2 * alpha * C + alpha ^ 2 * B ≤
      alpha * (2 - alpha) * C := by
    exact _root_.GD.N0232.N0719.N0943.d011267
      hk sizes hsizes location alpha scales hscales
  have hfactor : 0 < alpha * (2 - alpha) :=
    _root_.GD.N0232.N0719.N1005.d010122 halpha0 halpha2
  have hnegative : alpha * (2 - alpha) * C < 0 :=
    mul_neg_of_pos_of_neg hfactor hC
  linarith





theorem d011278 (alpha : ℝ) :
    0 < alpha * (2 - alpha) ↔ 0 < alpha ∧ alpha < 2 := by
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨halpha0, halpha2⟩
    exact _root_.GD.N0232.N0719.N1005.d010122 halpha0 halpha2



theorem d011279 (alpha : ℝ) :
    alpha * (2 - alpha) ≤ (1 : ℝ) * (2 - 1) := by
  rw [show (2 : ℝ) - 1 = 1 by norm_num, one_mul]
  exact _root_.GD.N0232.N0719.N1005.d010120 alpha


theorem d011280 (alpha : ℝ) :
    alpha * (2 - alpha) = (1 : ℝ) * (2 - 1) ↔ alpha = 1 := by
  rw [show (2 : ℝ) - 1 = 1 by norm_num, one_mul]
  exact _root_.GD.N0232.N0719.N1005.d010121 alpha



theorem d011281 (alpha : ℝ) :
    (∀ beta : ℝ,
        beta * (2 - beta) ≤ alpha * (2 - alpha)) ↔ alpha = 1 := by
  constructor
  · intro hmax
    have hone := hmax 1
    have hle := _root_.GD.N0232.N0719.N1005.d010120 alpha
    have heq : alpha * (2 - alpha) = 1 := by
      norm_num at hone
      linarith
    exact (_root_.GD.N0232.N0719.N1005.d010121 alpha).mp heq
  · rintro rfl
    intro beta
    rw [show (2 : ℝ) - 1 = 1 by norm_num, one_mul]
    exact _root_.GD.N0232.N0719.N1005.d010120 beta

end

end GD.N0232.N0719.N0944
