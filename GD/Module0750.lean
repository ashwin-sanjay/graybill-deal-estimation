import GD.Module0722
import GD.Module0691


































open MeasureTheory
open scoped BigOperators

namespace GD.N0232.N0719.N0943

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1015
open _root_.GD.N0232.N0719.N1018
open _root_.GD.N0232.N0719.N0852
open _root_.GD.N0232.N0719.N0874
open _root_.GD.N0232.N0719.N0851
open _root_.GD.N0232.N0719.N1005
open _root_.GD.N0237.N0746
open _root_.GD.N0232.N0719.N1024



section AbstractFiniteNormalization

variable {ι Ω : Type*} [MeasurableSpace Ω]



def d011231
    (gamma : ι → ℝ) (correction : ι → Ω → ℝ) : ι → Ω → ℝ :=
  fun i ω => (gamma i)⁻¹ * correction i ω

@[fun_prop]
theorem d011232
    (gamma : ι → ℝ) (correction : ι → Ω → ℝ)
    (hmeasurable : ∀ i, Measurable (correction i)) :
    ∀ i, Measurable (_root_.GD.N0232.N0719.N0943.d011231 gamma correction i) := by
  intro i
  unfold _root_.GD.N0232.N0719.N0943.d011231
  fun_prop

theorem d011233
    (μ : Measure Ω) (residual : Ω → ℝ)
    (gamma : ι → ℝ) (correction : ι → Ω → ℝ) (i : ι) :
    _root_.GD.N0232.N0719.N0874.d010191 μ residual (_root_.GD.N0232.N0719.N0943.d011231 gamma correction) i =
      (gamma i)⁻¹ * _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i := by
  unfold _root_.GD.N0232.N0719.N0874.d010191 _root_.GD.N0232.N0719.N0943.d011231
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring

theorem d011234
    (μ : Measure Ω)
    (gamma : ι → ℝ) (correction : ι → Ω → ℝ) (i : ι) :
    _root_.GD.N0232.N0719.N0874.d010192 μ (_root_.GD.N0232.N0719.N0943.d011231 gamma correction) i =
      (gamma i)⁻¹ ^ 2 * _root_.GD.N0232.N0719.N0874.d010192 μ correction i := by
  unfold _root_.GD.N0232.N0719.N0874.d010192 _root_.GD.N0232.N0719.N0943.d011231
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring



theorem d011235
    (μ : Measure Ω) (residual : Ω → ℝ)
    (gamma : ι → ℝ) (correction : ι → Ω → ℝ)
    (hintegrable : ∀ i,
      Integrable (fun ω => residual ω * correction i ω) μ) :
    ∀ i, Integrable
      (fun ω => residual ω *
        _root_.GD.N0232.N0719.N0943.d011231 gamma correction i ω) μ := by
  intro i
  have h := (hintegrable i).const_mul (gamma i)⁻¹
  simpa [_root_.GD.N0232.N0719.N0943.d011231, mul_assoc, mul_left_comm, mul_comm]
    using h



theorem d011236
    (μ : Measure Ω)
    (gamma : ι → ℝ) (correction : ι → Ω → ℝ)
    (hintegrable : ∀ i,
      Integrable (fun ω => (correction i ω) ^ 2) μ) :
    ∀ i, Integrable
      (fun ω =>
        (_root_.GD.N0232.N0719.N0943.d011231 gamma correction i ω) ^ 2) μ := by
  intro i
  have h := (hintegrable i).const_mul ((gamma i)⁻¹ ^ 2)
  simpa [_root_.GD.N0232.N0719.N0943.d011231, mul_pow] using h

variable [Fintype ι] [Nonempty ι]






theorem d011237
    (μ : Measure Ω) (residual : Ω → ℝ)
    (weight gamma : ι → ℝ) (correction : ι → Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1)
    (hgamma : ∀ i, 0 < gamma i)
    (hmeasurable : ∀ i, Measurable (correction i))
    (hcross_integrable : ∀ i,
      Integrable (fun ω => residual ω * correction i ω) μ)
    (henergy_integrable : ∀ i,
      Integrable (fun ω => (correction i ω) ^ 2) μ)
    (hcross_negative : ∀ i,
      _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i < 0)
    (hcapacity : ∀ i,
      _root_.GD.N0232.N0719.N0874.d010192 μ correction i ≤
        gamma i * (-_root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) :
    _root_.GD.N0232.N0719.N0874.d010193 μ residual weight
        (_root_.GD.N0232.N0719.N0943.d011231 gamma correction) < 0 ∧
      _root_.GD.N0232.N0719.N0874.d010194 μ weight
          (_root_.GD.N0232.N0719.N0943.d011231 gamma correction) ≤
        -_root_.GD.N0232.N0719.N0874.d010193 μ residual weight
          (_root_.GD.N0232.N0719.N0943.d011231 gamma correction) := by
  have h := _root_.GD.N0232.N0719.N0874.d010203 μ residual weight
    (_root_.GD.N0232.N0719.N0943.d011231 gamma correction) 1 (by norm_num)
    hweight hsum
    (_root_.GD.N0232.N0719.N0943.d011232 gamma correction hmeasurable)
    (_root_.GD.N0232.N0719.N0943.d011235
      μ residual gamma correction hcross_integrable)
    (_root_.GD.N0232.N0719.N0943.d011236
      μ gamma correction henergy_integrable)
    (fun i => by
      rw [_root_.GD.N0232.N0719.N0943.d011233]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr (hgamma i))
        (hcross_negative i))
    (fun i => by
      rw [_root_.GD.N0232.N0719.N0943.d011233,
        _root_.GD.N0232.N0719.N0943.d011234]
      have hscaled : (gamma i)⁻¹ ^ 2 * _root_.GD.N0232.N0719.N0874.d010192 μ correction i ≤
          (gamma i)⁻¹ ^ 2 *
            (gamma i * (-_root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) :=
        mul_le_mul_of_nonneg_left (hcapacity i) (sq_nonneg (gamma i)⁻¹)
      have hunit :
          (gamma i)⁻¹ ^ 2 *
              (gamma i * (-_root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) =
            -((gamma i)⁻¹ * _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i) := by
        field_simp [ne_of_gt (hgamma i)]
      simpa only [one_mul] using hscaled.trans_eq hunit)
  simpa only [one_mul] using h

end AbstractFiniteNormalization


def d011238 (k : ℕ) : ℝ :=
  ((Fintype.card (Equiv.Perm (Fin k)) : ℕ) : ℝ)⁻¹

theorem d011239 (k : ℕ) :
    0 < _root_.GD.N0232.N0719.N0943.d011238 k := by
  letI : Nonempty (Equiv.Perm (Fin k)) := ⟨Equiv.refl (Fin k)⟩
  unfold _root_.GD.N0232.N0719.N0943.d011238
  positivity

theorem d011240 (k : ℕ) :
    ∑ _σ : Equiv.Perm (Fin k), _root_.GD.N0232.N0719.N0943.d011238 k = 1 := by
  letI : Nonempty (Equiv.Perm (Fin k)) := ⟨Equiv.refl (Fin k)⟩
  have hcard : (Fintype.card (Equiv.Perm (Fin k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (∑ _σ : Equiv.Perm (Fin k), _root_.GD.N0232.N0719.N0943.d011238 k) =
        (Fintype.card (Equiv.Perm (Fin k)) : ℝ) *
          _root_.GD.N0232.N0719.N0943.d011238 k := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1 := by
      unfold _root_.GD.N0232.N0719.N0943.d011238
      exact mul_inv_cancel₀ hcard



def d011241
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (σ : Equiv.Perm (Fin k)) : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  fun ω =>
    (_root_.GD.N0232.N0719.N0851.d010792 hk sizes σ)⁻¹ *
      _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk)) ω


def d011242
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0874.d010190
    (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
    (_root_.GD.N0232.N0719.N0943.d011241 hk sizes)


def d011243
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  fun ω =>
    _root_.GD.N0232.N0719.N0900.d009111 k sizes ω +
      _root_.GD.N0232.N0719.N0943.d011242 hk sizes ω

@[fun_prop]
theorem d011244
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (σ : Equiv.Perm (Fin k)) :
    Measurable (_root_.GD.N0232.N0719.N0943.d011241 hk sizes σ) := by
  unfold _root_.GD.N0232.N0719.N0943.d011241 _root_.GD.N0232.N0719.N1015.d010079
  fun_prop

@[fun_prop]
theorem d011245
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0943.d011242 hk sizes) := by
  apply _root_.GD.N0232.N0719.N0874.d010197
  exact _root_.GD.N0232.N0719.N0943.d011244 hk sizes

@[fun_prop]
theorem d011246
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0943.d011243 hk sizes) := by
  unfold _root_.GD.N0232.N0719.N0943.d011243
  fun_prop





def d011247 {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin k) ≃ Equiv.Perm (Fin k) where
  toFun σ := σ.trans τ
  invFun σ := σ.trans τ.symm
  left_inv σ := by
    ext i
    simp
  right_inv σ := by
    ext i
    simp

@[simp]
theorem d011248 {k : ℕ} (τ σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.N0943.d011247 τ σ = σ.trans τ :=
  rfl



theorem d011249
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (τ σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.N0851.d010792 hk (sizes ∘ τ) σ =
      _root_.GD.N0232.N0719.N0851.d010792 hk sizes (σ.trans τ) := by
  rfl



theorem d011250
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (τ σ : Equiv.Perm (Fin k)) (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0943.d011241 hk (sizes ∘ τ) σ
        (_root_.GD.N0232.N0719.N0851.d010783 sizes τ ω) =
      _root_.GD.N0232.N0719.N0943.d011241 hk sizes (σ.trans τ) ω := by
  unfold _root_.GD.N0232.N0719.N0943.d011241
  rw [_root_.GD.N0232.N0719.N0943.d011249,
    _root_.GD.N0232.N0719.N0851.d010788]
  congr 2



theorem d011251
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (τ : Equiv.Perm (Fin k)) (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0943.d011242 hk (sizes ∘ τ)
        (_root_.GD.N0232.N0719.N0851.d010783 sizes τ ω) =
      _root_.GD.N0232.N0719.N0943.d011242 hk sizes ω := by
  unfold _root_.GD.N0232.N0719.N0943.d011242 _root_.GD.N0232.N0719.N0874.d010190
  simp_rw [_root_.GD.N0232.N0719.N0943.d011250]
  simpa only [_root_.GD.N0232.N0719.N0943.d011248] using
    (Equiv.sum_comp (_root_.GD.N0232.N0719.N0943.d011247 τ)
      (fun σ : Equiv.Perm (Fin k) =>
        _root_.GD.N0232.N0719.N0943.d011238 k *
          _root_.GD.N0232.N0719.N0943.d011241 hk sizes σ ω))


theorem d011252
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (τ : Equiv.Perm (Fin k)) (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0943.d011243 hk (sizes ∘ τ)
        (_root_.GD.N0232.N0719.N0851.d010783 sizes τ ω) =
      _root_.GD.N0232.N0719.N0943.d011243 hk sizes ω := by
  unfold _root_.GD.N0232.N0719.N0943.d011243
  rw [_root_.GD.N0232.N0719.N0851.d010787,
    _root_.GD.N0232.N0719.N0943.d011251]



theorem d011253
    {k : ℕ} (hk : 3 ≤ k)
    {sizes : Fin k → ℕ} (hsizes : ∀ i, 0 < sizes i)
    (σ : Equiv.Perm (Fin k))
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0943.d011241 hk sizes σ
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      scale * _root_.GD.N0232.N0719.N0943.d011241 hk sizes σ ω := by
  unfold _root_.GD.N0232.N0719.N0943.d011241 _root_.GD.N0232.N0719.N1015.d010079
  rw [_root_.GD.N0232.N0719.N0900.d009139 hsizes location scale,
    _root_.GD.N0232.N0719.N1018.d010057 (by omega) _ location hscale]
  ring



theorem d011254
    {k : ℕ} (hk : 3 ≤ k)
    {sizes : Fin k → ℕ} (hsizes : ∀ i, 0 < sizes i)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0943.d011242 hk sizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      scale * _root_.GD.N0232.N0719.N0943.d011242 hk sizes ω := by
  unfold _root_.GD.N0232.N0719.N0943.d011242 _root_.GD.N0232.N0719.N0874.d010190
  simp_rw [_root_.GD.N0232.N0719.N0943.d011253 hk hsizes _ location hscale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring



theorem d011255
    {k : ℕ} (hk : 3 ≤ k)
    {sizes : Fin k → ℕ} (hsizes : ∀ i, 0 < sizes i)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0943.d011243 hk sizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      location + scale * _root_.GD.N0232.N0719.N0943.d011243 hk sizes ω := by
  unfold _root_.GD.N0232.N0719.N0943.d011243
  rw [_root_.GD.N0232.N0719.N0900.d009146 (by omega) hsizes location hscale,
    _root_.GD.N0232.N0719.N0943.d011254
      hk hsizes location hscale]
  ring





theorem d011256
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0
        (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk)) < 0 ∧
      _root_.GD.N0232.N0719.N1015.d010081 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales)
          (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk)) ≤
        _root_.GD.N0232.N0719.N0851.d010792 hk sizes σ *
          (-_root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0
            (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk))) := by
  have hprojective :=
    _root_.GD.N0232.N0719.N0912.d010782
      hk (sizes ∘ σ) (fun i => hsizes (σ i))
      (scales ∘ σ) (fun i => hscales (σ i))
  have hcrossTransport :=
    _root_.GD.N0232.N0719.N0851.d010790 sizes σ 0 scales (_root_.GD.N0232.N0719.N1024.d010710 hk)
  have henergyTransport :=
    _root_.GD.N0232.N0719.N0851.d010791 sizes σ scales (_root_.GD.N0232.N0719.N1024.d010710 hk)
  constructor
  · rw [hcrossTransport]
    simpa [_root_.GD.N0232.N0719.N1024.d010712,
      _root_.GD.N0232.N0719.N1024.d010711] using hprojective.1
  · rw [henergyTransport, hcrossTransport]
    simpa [_root_.GD.N0232.N0719.N1024.d010713,
      _root_.GD.N0232.N0719.N1024.d010712, _root_.GD.N0232.N0719.N1024.d010711,
      _root_.GD.N0232.N0719.N0851.d010792] using hprojective.2


theorem d011257
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (μ : Measure (_root_.GD.N0232.N0719.d009173 k sizes)) (target : ℝ)
    (σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.N0874.d010191 μ (_root_.GD.N0232.N0719.N1015.d010078 target)
        (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) σ =
      (_root_.GD.N0232.N0719.N0851.d010792 hk sizes σ)⁻¹ *
        _root_.GD.N0232.N0719.N1015.d010080 μ target
          (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk)) := by
  unfold _root_.GD.N0232.N0719.N0874.d010191 _root_.GD.N0232.N0719.N0943.d011241 _root_.GD.N0232.N0719.N1015.d010080
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring


theorem d011258
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (μ : Measure (_root_.GD.N0232.N0719.d009173 k sizes))
    (σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.N0874.d010192 μ (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) σ =
      (_root_.GD.N0232.N0719.N0851.d010792 hk sizes σ)⁻¹ ^ 2 *
        _root_.GD.N0232.N0719.N1015.d010081 μ
          (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk)) := by
  unfold _root_.GD.N0232.N0719.N0874.d010192 _root_.GD.N0232.N0719.N0943.d011241
    _root_.GD.N0232.N0719.N1015.d010081
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring



theorem d011259
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.N0874.d010191 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) (_root_.GD.N0232.N0719.N1015.d010078 0)
        (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) σ < 0 ∧
      _root_.GD.N0232.N0719.N0874.d010192 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales)
          (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) σ ≤
        -_root_.GD.N0232.N0719.N0874.d010191 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) (_root_.GD.N0232.N0719.N1015.d010078 0)
          (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) σ := by
  let gamma := _root_.GD.N0232.N0719.N0851.d010792 hk sizes σ
  let C := _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0
    (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk))
  let B := _root_.GD.N0232.N0719.N1015.d010081 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales)
    (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk))
  have hgamma : 0 < gamma :=
    _root_.GD.N0232.N0719.N0851.d010794 hk sizes hsizes σ
  have hbranch := _root_.GD.N0232.N0719.N0943.d011256
    hk sizes hsizes scales hscales σ
  have hC : C < 0 := hbranch.1
  have hB : B ≤ gamma * (-C) := hbranch.2
  rw [_root_.GD.N0232.N0719.N0943.d011257,
    _root_.GD.N0232.N0719.N0943.d011258]
  change gamma⁻¹ * C < 0 ∧ gamma⁻¹ ^ 2 * B ≤ -(gamma⁻¹ * C)
  refine ⟨mul_neg_of_pos_of_neg (inv_pos.mpr hgamma) hC, ?_⟩
  have hscaled : gamma⁻¹ ^ 2 * B ≤
      gamma⁻¹ ^ 2 * (gamma * (-C)) :=
    mul_le_mul_of_nonneg_left hB (sq_nonneg gamma⁻¹)
  calc
    gamma⁻¹ ^ 2 * B ≤ gamma⁻¹ ^ 2 * (gamma * (-C)) := hscaled
    _ = -(gamma⁻¹ * C) := by
      field_simp [ne_of_gt hgamma]



theorem d011260
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (σ : Equiv.Perm (Fin k)) :
    Integrable
      (fun ω => _root_.GD.N0232.N0719.N1015.d010078 location ω *
        _root_.GD.N0232.N0719.N0943.d011241 hk sizes σ ω)
      (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  have h := _root_.GD.N0232.N0719.N0910.d010296
    sizes (by omega) hsizes location scales hscales
      (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk))
  have hscaled := h.const_mul (_root_.GD.N0232.N0719.N0851.d010792 hk sizes σ)⁻¹
  simpa [_root_.GD.N0232.N0719.N0943.d011241, mul_assoc, mul_left_comm, mul_comm]
    using hscaled



theorem d011261
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (σ : Equiv.Perm (Fin k)) :
    Integrable
      (fun ω => (_root_.GD.N0232.N0719.N0943.d011241 hk sizes σ ω) ^ 2)
      (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  have h := (_root_.GD.N0232.N0719.N0910.d010295
    sizes (by omega) hsizes location scales hscales
      (_root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk))).integrable_sq
  have hscaled := h.const_mul
    ((_root_.GD.N0232.N0719.N0851.d010792 hk sizes σ)⁻¹ ^ 2)
  simpa [_root_.GD.N0232.N0719.N0943.d011241, mul_pow] using hscaled



theorem d011262
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.N0874.d010191 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
        (_root_.GD.N0232.N0719.N1015.d010078 location) (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) σ < 0 ∧
      _root_.GD.N0232.N0719.N0874.d010192 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) σ ≤
        -_root_.GD.N0232.N0719.N0874.d010191 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          (_root_.GD.N0232.N0719.N1015.d010078 location) (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) σ := by
  have hzero :=
    _root_.GD.N0232.N0719.N0943.d011259
      hk sizes hsizes scales hscales σ
  rw [_root_.GD.N0232.N0719.N0943.d011257,
    _root_.GD.N0232.N0719.N0943.d011258] at hzero ⊢
  rw [_root_.GD.N0232.N0719.N0851.d010800 sizes hk hsizes location scales,
    _root_.GD.N0232.N0719.N0851.d010801 sizes hk hsizes location scales]
  exact hzero





theorem d011263
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N0874.d010193 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
        (_root_.GD.N0232.N0719.N1015.d010078 location)
        (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
        (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) < 0 ∧
      _root_.GD.N0232.N0719.N0874.d010194 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
          (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) ≤
        -_root_.GD.N0232.N0719.N0874.d010193 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          (_root_.GD.N0232.N0719.N1015.d010078 location)
          (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
          (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) := by
  have h := _root_.GD.N0232.N0719.N0874.d010203
    (_root_.GD.N0232.N0719.d009176 k sizes location scales)
    (_root_.GD.N0232.N0719.N1015.d010078 location)
    (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
    (_root_.GD.N0232.N0719.N0943.d011241 hk sizes)
    1 (by norm_num)
    (fun _ => (_root_.GD.N0232.N0719.N0943.d011239 k).le)
    (_root_.GD.N0232.N0719.N0943.d011240 k)
    (_root_.GD.N0232.N0719.N0943.d011244 hk sizes)
    (_root_.GD.N0232.N0719.N0943.d011260
      hk sizes hsizes location scales hscales)
    (_root_.GD.N0232.N0719.N0943.d011261
      hk sizes hsizes location scales hscales)
    (fun σ =>
      (_root_.GD.N0232.N0719.N0943.d011262
        hk sizes hsizes location scales hscales σ).1)
    (fun σ => by
      simpa using
        (_root_.GD.N0232.N0719.N0943.d011262
          hk sizes hsizes location scales hscales σ).2)
  simpa using h


theorem d011264
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    Integrable
      (fun ω =>
        (_root_.GD.N0232.N0719.N0943.d011242 hk sizes ω) ^ 2)
      (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  exact _root_.GD.N0232.N0719.N0874.d010198
    (_root_.GD.N0232.N0719.d009176 k sizes location scales)
    (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
    (_root_.GD.N0232.N0719.N0943.d011241 hk sizes)
    (fun _ => (_root_.GD.N0232.N0719.N0943.d011239 k).le)
    (_root_.GD.N0232.N0719.N0943.d011240 k)
    (_root_.GD.N0232.N0719.N0943.d011244 hk sizes)
    (_root_.GD.N0232.N0719.N0943.d011261
      hk sizes hsizes location scales hscales)


theorem d011265
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    Integrable
      (fun ω => _root_.GD.N0232.N0719.N1015.d010078 location ω *
        _root_.GD.N0232.N0719.N0943.d011242 hk sizes ω)
      (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  exact _root_.GD.N0232.N0719.N0874.d010199
    (_root_.GD.N0232.N0719.d009176 k sizes location scales)
    (_root_.GD.N0232.N0719.N1015.d010078 location)
    (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
    (_root_.GD.N0232.N0719.N0943.d011241 hk sizes)
    (_root_.GD.N0232.N0719.N0943.d011260
      hk sizes hsizes location scales hscales)


theorem d011266
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0943.d011243 hk sizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) -
      ∫ ω, (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales =
      2 * _root_.GD.N0232.N0719.N0874.d010193 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          (_root_.GD.N0232.N0719.N1015.d010078 location)
          (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
          (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) +
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
  have hid := _root_.GD.N0237.N0746.d004286 μ 1 r h hr hh hrh
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
      (fun ω => _root_.GD.N0232.N0719.N0943.d011243 hk sizes ω - location) =
        (fun ω => r ω - 1 * h ω) := by
    funext ω
    unfold _root_.GD.N0232.N0719.N0943.d011243 r h u
      _root_.GD.N0232.N0719.N1015.d010078
    simp only [Pi.neg_apply]
    ring
  change
    (∫ ω,
        ((fun ω =>
          _root_.GD.N0232.N0719.N0943.d011243 hk sizes ω - location) ω) ^ 2
          ∂μ) -
      ∫ ω, (r ω) ^ 2 ∂μ = _
  rw [herror]
  change (∫ ω, (r ω - 1 * h ω) ^ 2 ∂μ) -
      ∫ ω, (r ω) ^ 2 ∂μ = _
  rw [hid]
  ring






theorem d011267
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location alpha : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    2 * alpha *
          _root_.GD.N0232.N0719.N0874.d010193 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
            (_root_.GD.N0232.N0719.N1015.d010078 location)
            (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
            (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) +
        alpha ^ 2 *
          _root_.GD.N0232.N0719.N0874.d010194 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
            (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
            (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) ≤
      alpha * (2 - alpha) *
        _root_.GD.N0232.N0719.N0874.d010193 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          (_root_.GD.N0232.N0719.N1015.d010078 location)
          (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
          (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) := by
  have hcap :=
    _root_.GD.N0232.N0719.N0943.d011263
      hk sizes hsizes location scales hscales
  have h := _root_.GD.N0232.N0719.N1005.d010116
    (gamma := (1 : ℝ))
    (C := _root_.GD.N0232.N0719.N0874.d010193 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
      (_root_.GD.N0232.N0719.N1015.d010078 location)
      (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
      (_root_.GD.N0232.N0719.N0943.d011241 hk sizes))
    (B := _root_.GD.N0232.N0719.N0874.d010194 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
      (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
      (_root_.GD.N0232.N0719.N0943.d011241 hk sizes))
    (alpha := alpha) (by norm_num) (by simpa using hcap.2)
  simpa using h



theorem d011268
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0943.d011243 hk sizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) -
      ∫ ω, (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales ≤
      _root_.GD.N0232.N0719.N0874.d010193 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
        (_root_.GD.N0232.N0719.N1015.d010078 location)
        (fun _σ : Equiv.Perm (Fin k) => _root_.GD.N0232.N0719.N0943.d011238 k)
        (_root_.GD.N0232.N0719.N0943.d011241 hk sizes) := by
  rw [_root_.GD.N0232.N0719.N0943.d011266
    hk sizes hsizes location scales hscales]
  have h := _root_.GD.N0232.N0719.N0943.d011267
    hk sizes hsizes location 1 scales hscales
  norm_num at h
  simpa using h




theorem d011269
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0943.d011243 hk sizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) <
      ∫ ω, (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales := by
  have hcap :=
    _root_.GD.N0232.N0719.N0943.d011263
      hk sizes hsizes location scales hscales
  have hbound :=
    _root_.GD.N0232.N0719.N0943.d011268
      hk sizes hsizes location scales hscales
  linarith

end

end GD.N0232.N0719.N0943
