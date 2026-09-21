import GD.Module0723
import GD.Module0690















open MeasureTheory

namespace GD.N0232.N0719.N0911

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1015
open _root_.GD.N0232.N0719.N1018
open _root_.GD.N0232.N0719.N1024
open _root_.GD.N0232.N0719.N0936


noncomputable def d011139
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    _root_.GD.N0232.N0719.N1015.d010082
      Unit
      (fun _ ↦ _root_.GD.N0232.N0719.N1024.d010711 k sizes location scale)
      (fun _ ↦ location)
      (_root_.GD.N0232.N0719.N1024.d010710 hk) where
  gamma := _root_.GD.N0232.N0719.N1024.d010720 k sizes hk
  gamma_nonneg := _root_.GD.N0232.N0719.N1024.d010721 k sizes hk
  residual_sq_integrable := fun _ ↦
    _root_.GD.N0232.N0719.N1024.d010735
      k sizes hk hsizes location scale hscale
  correction_sq_integrable := fun _ ↦
    _root_.GD.N0232.N0719.N1024.d010736
      k sizes hk hsizes location scale hscale
  cross_integrable := fun _ ↦
    _root_.GD.N0232.N0719.N1024.d010737
      k sizes hk hsizes location scale hscale
  cross_negative := fun _ ↦ by
    rw [_root_.GD.N0232.N0719.N1024.d010715
      k sizes hk hsizes location scale]
    exact _root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes scale hscale
  energy_le := fun _ ↦ by
    rw [_root_.GD.N0232.N0719.N1024.d010717
      k sizes hk hsizes location scale,
      _root_.GD.N0232.N0719.N1024.d010715
        k sizes hk hsizes location scale]
    exact _root_.GD.N0232.N0719.N1024.d010726
      k sizes hk (_root_.GD.N0232.N0719.N1024.d010806 hk sizes hsizes)
      scale hscale (_root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes scale hscale)



theorem d011140
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    0 < _root_.GD.N0232.N0719.N1024.d010713 k sizes hk scale := by
  let cert := _root_.GD.N0232.N0719.N0911.d011139
    k sizes hk hsizes location scale hscale
  have henergy := _root_.GD.N0232.N0719.N0936.d010105 cert ()
  rw [_root_.GD.N0232.N0719.N1024.d010717
    k sizes hk hsizes location scale] at henergy
  exact henergy


theorem d011141
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (scale : Fin k → ℝ) (hscale : ∀ i, 0 < scale i) :
    0 < _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scale := by
  unfold _root_.GD.N0232.N0719.N1024.d010718
  exact div_pos
    (_root_.GD.N0232.N0719.N0911.d011140 k sizes hk hsizes 0 scale hscale)
    (neg_pos.mpr (_root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes scale hscale))


theorem d011142
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    0 < _root_.GD.N0232.N0719.N1024.d010720 k sizes hk := by
  let scale : Fin k → ℝ := fun _ ↦ 1
  let cert := _root_.GD.N0232.N0719.N0911.d011139
    k sizes hk hsizes 0 scale (fun _ ↦ zero_lt_one)
  exact _root_.GD.N0232.N0719.N0936.d010104 cert ()




theorem d011143
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N1024.d010720 k sizes hk = sSup (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk) := by
  unfold _root_.GD.N0232.N0719.N1024.d010720
  apply max_eq_right
  let scale : Fin k → ℝ := fun _ ↦ 1
  have hscale : ∀ i, 0 < scale i := fun _ ↦ zero_lt_one
  have hmem :
      _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scale ∈ _root_.GD.N0232.N0719.N1024.d010719 k sizes hk :=
    ⟨scale, hscale, rfl⟩
  have hratio_nonneg : 0 ≤ _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scale :=
    _root_.GD.N0232.N0719.N1024.d010724
      k sizes hk scale
      (_root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes scale hscale)
  exact hratio_nonneg.trans
    (le_csSup (_root_.GD.N0232.N0719.N1024.d010806 hk sizes hsizes) hmem)





theorem d011144
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    IsLUB (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk) (_root_.GD.N0232.N0719.N1024.d010720 k sizes hk) := by
  rw [_root_.GD.N0232.N0719.N0911.d011143 k sizes hk hsizes]
  exact isLUB_csSup
    (_root_.GD.N0232.N0719.N1024.d010722 k sizes hk)
    (_root_.GD.N0232.N0719.N1024.d010806 hk sizes hsizes)


noncomputable def d011145
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) : ℝ :=
  _root_.GD.N0232.N0719.N0936.d010093 (_root_.GD.N0232.N0719.N1024.d010720 k sizes hk)

theorem d011146
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    0 < _root_.GD.N0232.N0719.N0911.d011145 k sizes hk :=
  _root_.GD.N0232.N0719.N0936.d010100 (_root_.GD.N0232.N0719.N0911.d011142 k sizes hk hsizes)


noncomputable def d011147
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (_hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N1018.d010023 k sizes (_root_.GD.N0232.N0719.N1024.d010710 hk)
    (_root_.GD.N0232.N0719.N0911.d011145 k sizes hk)

theorem d011148
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    Measurable (_root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes) := by
  unfold _root_.GD.N0232.N0719.N0911.d011147
  exact _root_.GD.N0232.N0719.N1018.d010046
    k sizes (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N0911.d011145 k sizes hk)


theorem d011149
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      location + scale * _root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes ω := by
  unfold _root_.GD.N0232.N0719.N0911.d011147
  exact _root_.GD.N0232.N0719.N1018.d010059
    (by omega)
    (fun i ↦ lt_of_lt_of_le (by decide : 0 < 2) (hsizes i))
    (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N0911.d011145 k sizes hk)
    location hscale ω



theorem d011150
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    MemLp
      (fun ω ↦
        _root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes ω - location)
      2 (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) := by
  unfold _root_.GD.N0232.N0719.N0911.d011147 _root_.GD.N0232.N0719.N1024.d010711
  exact
    _root_.GD.N0232.N0719.N0910.d010297
      sizes (by omega) hsizes location scale hscale
      (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N0911.d011145 k sizes hk)


theorem d011151
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) -
        ∫ ω,
          (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
            ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale ≤
      _root_.GD.N0232.N0719.N0911.d011145 k sizes hk * _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale := by
  let cert := _root_.GD.N0232.N0719.N0911.d011139
    k sizes hk hsizes location scale hscale
  have hbound :=
    _root_.GD.N0232.N0719.N0936.d010111 cert ()
  rw [_root_.GD.N0232.N0719.N1024.d010715
    k sizes hk hsizes location scale] at hbound
  simpa [_root_.GD.N0232.N0719.N0911.d011147, _root_.GD.N0232.N0719.N0911.d011145,
    _root_.GD.N0232.N0719.N0911.d011139, cert] using hbound



theorem d011152
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) <
      ∫ ω,
        (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale := by
  have hbound := _root_.GD.N0232.N0719.N0911.d011151
    k sizes hk hsizes location scale hscale
  have hstep : 0 < _root_.GD.N0232.N0719.N0911.d011145 k sizes hk :=
    _root_.GD.N0232.N0719.N0911.d011146 k sizes hk hsizes
  have hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale < 0 :=
    _root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes scale hscale
  have hright :
      _root_.GD.N0232.N0719.N0911.d011145 k sizes hk * _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale < 0 :=
    mul_neg_of_pos_of_neg hstep hcross
  linarith



theorem d011153
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0911.d011147 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) <
      ∫ ω,
        (_root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale := by
  let cert := _root_.GD.N0232.N0719.N0911.d011139
    k sizes hk hsizes location scale hscale
  have hrisk := _root_.GD.N0232.N0719.N0936.d010113 cert ()
  simpa [_root_.GD.N0232.N0719.N0911.d011147, _root_.GD.N0232.N0719.N1024.d010731, _root_.GD.N0232.N0719.N0911.d011145,
    _root_.GD.N0232.N0719.N1015.d010083,
    _root_.GD.N0232.N0719.N1024.d010727, _root_.GD.N0232.N0719.N0911.d011139,
    cert] using hrisk

end

end GD.N0232.N0719.N0911
