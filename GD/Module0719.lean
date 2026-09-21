import GD.Module0637
import GD.Module0689
import GD.Module0697
import GD.Module0699
























open MeasureTheory Set

namespace GD.N0232.N0719.N1024

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1018
open _root_.GD.N0232.N0719.N1015


def d010710 {k : ℕ} (hk : 3 ≤ k) : Fin 3 ↪ Fin k :=
  Fin.castLEEmb hk



def d010711
    (k : ℕ) (sizes : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ) :
    Measure (_root_.GD.N0232.N0719.d009173 k sizes) :=
  _root_.GD.N0232.N0719.d009176 k sizes location scale




def d010712
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (scale : Fin k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1015.d010080
    (_root_.GD.N0232.N0719.N1024.d010711 k sizes 0 scale) 0 (_root_.GD.N0232.N0719.N1024.d010710 hk)


def d010713
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (scale : Fin k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1015.d010081
    (_root_.GD.N0232.N0719.N1024.d010711 k sizes 0 scale) (_root_.GD.N0232.N0719.N1024.d010710 hk)



theorem d010714
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N1015.d010078 location
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes location 1 ω) *
        _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk)
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes location 1 ω) =
      _root_.GD.N0232.N0719.N1015.d010078 0 ω *
        _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk) ω := by
  have hk0 : 0 < k := by omega
  have hsizes0 : ∀ i, 0 < sizes i := fun i =>
    lt_of_lt_of_le (by decide : 0 < 2) (hsizes i)
  have hbase :=
    _root_.GD.N0232.N0719.N0900.d009146
      hk0 hsizes0 location (scale := 1) one_ne_zero ω
  have hsummary :=
    _root_.GD.N0232.N0719.N0900.d009139
      hsizes0 location 1 ω
  have hcorrection :=
    _root_.GD.N0232.N0719.N1018.d010057
      hk0 (_root_.GD.N0232.N0719.N1024.d010710 hk) location
      (scale := 1) one_ne_zero (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)
  unfold _root_.GD.N0232.N0719.N1015.d010078
    _root_.GD.N0232.N0719.N1015.d010079
  rw [hbase, hsummary, hcorrection]
  ring




theorem d010715
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N1015.d010080
        (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale)
        location (_root_.GD.N0232.N0719.N1024.d010710 hk) =
      _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale := by
  have hmap :=
    _root_.GD.N0232.N0719.d009178
      k sizes location scale
  unfold _root_.GD.N0232.N0719.N1024.d010712 _root_.GD.N0232.N0719.N1024.d010711 _root_.GD.N0232.N0719.N1015.d010080
    _root_.GD.N0232.N0719.N1015.d010078 _root_.GD.N0232.N0719.N1015.d010079
  rw [← hmap]
  rw [integral_map_of_stronglyMeasurable
    (μ := _root_.GD.N0232.N0719.d009176 k sizes 0 scale)
    (φ := _root_.GD.N0232.N0719.N0900.d009095 k sizes location 1)
    (f := fun ω =>
      (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) *
        _root_.GD.N0232.N0719.N1018.d010021 (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω))
    (_root_.GD.N0232.N0719.N0900.d009112 k sizes location 1)
    (((_root_.GD.N0232.N0719.N0900.d009122 k sizes).sub measurable_const).mul
      ((_root_.GD.N0232.N0719.N1018.d010044 (_root_.GD.N0232.N0719.N1024.d010710 hk)).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with ω
  exact _root_.GD.N0232.N0719.N1024.d010714
    k sizes hk hsizes location scale ω


theorem d010716
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk)
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes location 1 ω) ^ 2 =
      _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk) ω ^ 2 := by
  have hk0 : 0 < k := by omega
  have hsizes0 : ∀ i, 0 < sizes i := fun i =>
    lt_of_lt_of_le (by decide : 0 < 2) (hsizes i)
  have hsummary :=
    _root_.GD.N0232.N0719.N0900.d009139
      hsizes0 location 1 ω
  have hcorrection :=
    _root_.GD.N0232.N0719.N1018.d010057
      hk0 (_root_.GD.N0232.N0719.N1024.d010710 hk) location
      (scale := 1) one_ne_zero (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)
  unfold _root_.GD.N0232.N0719.N1015.d010079
  rw [hsummary, hcorrection]
  ring


theorem d010717
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N1015.d010081
        (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale)
        (_root_.GD.N0232.N0719.N1024.d010710 hk) =
      _root_.GD.N0232.N0719.N1024.d010713 k sizes hk scale := by
  have hmap :=
    _root_.GD.N0232.N0719.d009178
      k sizes location scale
  unfold _root_.GD.N0232.N0719.N1024.d010713 _root_.GD.N0232.N0719.N1024.d010711 _root_.GD.N0232.N0719.N1015.d010081
    _root_.GD.N0232.N0719.N1015.d010079
  rw [← hmap]
  rw [integral_map_of_stronglyMeasurable
    (μ := _root_.GD.N0232.N0719.d009176 k sizes 0 scale)
    (φ := _root_.GD.N0232.N0719.N0900.d009095 k sizes location 1)
    (f := fun ω =>
      _root_.GD.N0232.N0719.N1018.d010021 (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) ^ 2)
    (_root_.GD.N0232.N0719.N0900.d009112 k sizes location 1)
    ((((_root_.GD.N0232.N0719.N1018.d010044 (_root_.GD.N0232.N0719.N1024.d010710 hk)).comp
      (_root_.GD.N0232.N0719.N0900.d009115 k sizes))).pow_const 2).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with ω
  exact _root_.GD.N0232.N0719.N1024.d010716
    k sizes hk hsizes location scale ω





def d010718
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (scale : Fin k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1024.d010713 k sizes hk scale /
    (-_root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale)


def d010719
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) : Set ℝ :=
  {x | ∃ scale : Fin k → ℝ,
    (∀ i, 0 < scale i) ∧
      x = _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scale}







noncomputable def d010720
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) : ℝ :=
  max 0 (sSup (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk))

theorem d010721
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) :
    0 ≤ _root_.GD.N0232.N0719.N1024.d010720 k sizes hk := by
  exact le_max_left _ _



theorem d010722
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) :
    (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk).Nonempty := by
  refine ⟨_root_.GD.N0232.N0719.N1024.d010718 k sizes hk (fun _ => 1), ?_⟩
  exact ⟨(fun _ : Fin k => (1 : ℝ)), (fun _ => zero_lt_one), rfl⟩



theorem d010723
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (scale : Fin k → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N1024.d010713 k sizes hk scale := by
  unfold _root_.GD.N0232.N0719.N1024.d010713 _root_.GD.N0232.N0719.N1015.d010081
  exact integral_nonneg fun _ => sq_nonneg _



theorem d010724
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (scale : Fin k → ℝ)
    (hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale < 0) :
    0 ≤ _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scale := by
  unfold _root_.GD.N0232.N0719.N1024.d010718
  exact div_nonneg
    (_root_.GD.N0232.N0719.N1024.d010723 k sizes hk scale)
    (neg_nonneg.mpr hcross.le)



theorem d010725
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hbounded : BddAbove (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk))
    (scale : Fin k → ℝ) (hscale : ∀ i, 0 < scale i) :
    _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scale ≤
      _root_.GD.N0232.N0719.N1024.d010720 k sizes hk := by
  have hmem :
      _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scale ∈
        _root_.GD.N0232.N0719.N1024.d010719 k sizes hk :=
    ⟨scale, hscale, rfl⟩
  exact
    (le_csSup hbounded hmem).trans
      (le_max_right 0 (sSup (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk)))



theorem d010726
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hbounded : BddAbove (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk))
    (scale : Fin k → ℝ) (hscale : ∀ i, 0 < scale i)
    (hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale < 0) :
    _root_.GD.N0232.N0719.N1024.d010713 k sizes hk scale ≤
      _root_.GD.N0232.N0719.N1024.d010720 k sizes hk *
        (-_root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale) := by
  have hratio :=
    _root_.GD.N0232.N0719.N1024.d010725
      k sizes hk hbounded scale hscale
  have hden :
      0 < -_root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale :=
    neg_pos.mpr hcross
  calc
    _root_.GD.N0232.N0719.N1024.d010713 k sizes hk scale =
        _root_.GD.N0232.N0719.N1024.d010718 k sizes hk scale *
          (-_root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale) := by
      unfold _root_.GD.N0232.N0719.N1024.d010718
      exact (div_mul_cancel₀ _ hden.ne').symm
    _ ≤ _root_.GD.N0232.N0719.N1024.d010720 k sizes hk *
          (-_root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale) :=
      mul_le_mul_of_nonneg_right hratio hden.le


noncomputable def d010727
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) : ℝ :=
  1 / (1 + _root_.GD.N0232.N0719.N1024.d010720 k sizes hk)

theorem d010728
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) :
    0 < _root_.GD.N0232.N0719.N1024.d010727 k sizes hk := by
  unfold _root_.GD.N0232.N0719.N1024.d010727
  exact one_div_pos.mpr
    (by linarith [_root_.GD.N0232.N0719.N1024.d010721 k sizes hk])



theorem d010729
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) :
    _root_.GD.N0232.N0719.N1024.d010727 k sizes hk *
        _root_.GD.N0232.N0719.N1024.d010720 k sizes hk < 2 := by
  have hΓ := _root_.GD.N0232.N0719.N1024.d010721 k sizes hk
  have hden : 0 < 1 + _root_.GD.N0232.N0719.N1024.d010720 k sizes hk := by
    linarith
  have hfrac :
      _root_.GD.N0232.N0719.N1024.d010720 k sizes hk /
          (1 + _root_.GD.N0232.N0719.N1024.d010720 k sizes hk) < 1 :=
    (div_lt_one hden).2 (by linarith)
  calc
    _root_.GD.N0232.N0719.N1024.d010727 k sizes hk * _root_.GD.N0232.N0719.N1024.d010720 k sizes hk =
        _root_.GD.N0232.N0719.N1024.d010720 k sizes hk /
          (1 + _root_.GD.N0232.N0719.N1024.d010720 k sizes hk) := by
      unfold _root_.GD.N0232.N0719.N1024.d010727
      ring
    _ < 1 := hfrac
    _ < 2 := by norm_num




theorem d010730
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k)
    (hbounded : BddAbove (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk))
    (scale : Fin k → ℝ) (hscale : ∀ i, 0 < scale i)
    (hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale < 0) :
    2 * _root_.GD.N0232.N0719.N1024.d010727 k sizes hk *
          _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale +
        _root_.GD.N0232.N0719.N1024.d010727 k sizes hk ^ 2 *
          _root_.GD.N0232.N0719.N1024.d010713 k sizes hk scale < 0 := by
  let ε := _root_.GD.N0232.N0719.N1024.d010727 k sizes hk
  let Γ := _root_.GD.N0232.N0719.N1024.d010720 k sizes hk
  let C := _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale
  let B := _root_.GD.N0232.N0719.N1024.d010713 k sizes hk scale
  have hε : 0 < ε := _root_.GD.N0232.N0719.N1024.d010728 k sizes hk
  have hC : C < 0 := hcross
  have hcap : B ≤ Γ * (-C) := by
    exact _root_.GD.N0232.N0719.N1024.d010726
      k sizes hk hbounded scale hscale hcross
  have hstep : ε * Γ < 2 := by
    exact _root_.GD.N0232.N0719.N1024.d010729 k sizes hk
  have hscaled :
      ε ^ 2 * B ≤ ε ^ 2 * (Γ * (-C)) :=
    mul_le_mul_of_nonneg_left hcap (sq_nonneg ε)
  have hmain :
      2 * ε * C + ε ^ 2 * B ≤
        ε * (-C) * (ε * Γ - 2) := by
    nlinarith
  have hleft : 0 < ε * (-C) :=
    mul_pos hε (neg_pos.mpr hC)
  have hright : ε * Γ - 2 < 0 :=
    sub_neg.mpr hstep
  have hneg : ε * (-C) * (ε * Γ - 2) < 0 :=
    mul_neg_of_pos_of_neg hleft hright
  dsimp [ε, Γ, C, B] at hmain hneg ⊢
  exact lt_of_le_of_lt hmain hneg


noncomputable def d010731
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (_hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N1018.d010023 k sizes (_root_.GD.N0232.N0719.N1024.d010710 hk)
    (_root_.GD.N0232.N0719.N1024.d010727 k sizes hk)

theorem d010732
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    Measurable (_root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes) := by
  unfold _root_.GD.N0232.N0719.N1024.d010731
  exact _root_.GD.N0232.N0719.N1018.d010046
    k sizes (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N1024.d010727 k sizes hk)



theorem d010733
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (_hscale : ∀ i, 0 < scale i) :
    MemLp
      (fun ω =>
        _root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location)
      2 (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) := by
  exact
    _root_.GD.N0232.N0719.N0910.d010294
      sizes (by omega) hsizes location scale



theorem d010734
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    MemLp
      (fun ω =>
        _root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes ω - location)
      2 (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) := by
  unfold _root_.GD.N0232.N0719.N1024.d010731 _root_.GD.N0232.N0719.N1024.d010711
  exact
    _root_.GD.N0232.N0719.N0910.d010297
      sizes (by omega) hsizes location scale hscale
      (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N1024.d010727 k sizes hk)



theorem d010735
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    Integrable
      (fun ω => _root_.GD.N0232.N0719.N1015.d010078 location ω ^ 2)
      (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) :=
  (_root_.GD.N0232.N0719.N1024.d010733
    k sizes hk hsizes location scale hscale).integrable_sq



theorem d010736
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    Integrable
      (fun ω =>
        _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk) ω ^ 2)
      (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) := by
  exact
    (_root_.GD.N0232.N0719.N0910.d010295
      sizes (by omega) hsizes location scale hscale
      (_root_.GD.N0232.N0719.N1024.d010710 hk)).integrable_sq


theorem d010737
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    Integrable
      (fun ω =>
        _root_.GD.N0232.N0719.N1015.d010078 location ω *
          _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk) ω)
      (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) := by
  exact
    _root_.GD.N0232.N0719.N0910.d010296
      sizes (by omega) hsizes location scale hscale
      (_root_.GD.N0232.N0719.N1024.d010710 hk)



theorem d010738
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      location + scale * _root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes ω := by
  unfold _root_.GD.N0232.N0719.N1024.d010731
  exact _root_.GD.N0232.N0719.N1018.d010059
    (by omega)
    (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hsizes i))
    (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N1024.d010727 k sizes hk)
    location hscale ω








theorem d010739
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i)
    (hbounded : BddAbove (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk))
    (hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale < 0)
    (hresidual :
      Integrable
        (fun ω => (_root_.GD.N0232.N0719.N1015.d010078 location ω) ^ 2)
        (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale))
    (hcorrection :
      Integrable
        (fun ω => (_root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk) ω) ^ 2)
        (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale))
    (hproduct :
      Integrable
        (fun ω =>
          _root_.GD.N0232.N0719.N1015.d010078 location ω * _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk) ω)
        (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale)) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) -
        ∫ ω,
          (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
            ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale <
      _root_.GD.N0232.N0719.N1024.d010727 k sizes hk * _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale := by
  let law₁ : Unit → Measure (_root_.GD.N0232.N0719.d009173 k sizes) :=
    fun _ => _root_.GD.N0232.N0719.N1024.d010711 k sizes location scale
  let target₁ : Unit → ℝ := fun _ => location
  let cert :
      _root_.GD.N0232.N0719.N1015.d010082 Unit law₁ target₁ (_root_.GD.N0232.N0719.N1024.d010710 hk) :=
    { gamma := _root_.GD.N0232.N0719.N1024.d010720 k sizes hk
      gamma_nonneg := _root_.GD.N0232.N0719.N1024.d010721 k sizes hk
      residual_sq_integrable := fun _ => hresidual
      correction_sq_integrable := fun _ => hcorrection
      cross_integrable := fun _ => hproduct
      cross_negative := fun _ => by
        rw [_root_.GD.N0232.N0719.N1024.d010715
          k sizes hk hsizes location scale]
        exact hcross
      energy_le := fun _ => by
        rw [_root_.GD.N0232.N0719.N1024.d010717
          k sizes hk hsizes location scale,
          _root_.GD.N0232.N0719.N1024.d010715
            k sizes hk hsizes location scale]
        exact _root_.GD.N0232.N0719.N1024.d010726
          k sizes hk hbounded scale hscale hcross }
  have hmargin :=
    _root_.GD.N0232.N0719.N1015.d010090 cert ()
  dsimp [law₁, target₁] at hmargin
  rw [_root_.GD.N0232.N0719.N1024.d010715
    k sizes hk hsizes location scale] at hmargin
  simpa [_root_.GD.N0232.N0719.N1024.d010731, law₁, target₁, cert,
    _root_.GD.N0232.N0719.N1015.d010083, _root_.GD.N0232.N0719.N1024.d010727,
    _root_.GD.N0232.N0719.N1024.d010711] using hmargin











theorem d010740
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i)
    (hbounded : BddAbove (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk))
    (hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale < 0)
    (hresidual :
      Integrable
        (fun ω =>
          (_root_.GD.N0232.N0719.N1015.d010078 location ω) ^ 2)
        (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale))
    (hcorrection :
      Integrable
        (fun ω =>
          (_root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk) ω) ^ 2)
        (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale))
    (hproduct :
      Integrable
        (fun ω =>
          _root_.GD.N0232.N0719.N1015.d010078 location ω *
            _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N1024.d010710 hk) ω)
        (_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale)) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) <
      ∫ ω,
        (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale := by
  let law₁ : Unit → Measure (_root_.GD.N0232.N0719.d009173 k sizes) :=
    fun _ => _root_.GD.N0232.N0719.N1024.d010711 k sizes location scale
  let target₁ : Unit → ℝ := fun _ => location
  let cert :
      _root_.GD.N0232.N0719.N1015.d010082 Unit law₁ target₁ (_root_.GD.N0232.N0719.N1024.d010710 hk) :=
    { gamma := _root_.GD.N0232.N0719.N1024.d010720 k sizes hk
      gamma_nonneg := _root_.GD.N0232.N0719.N1024.d010721 k sizes hk
      residual_sq_integrable := fun _ => hresidual
      correction_sq_integrable := fun _ => hcorrection
      cross_integrable := fun _ => hproduct
      cross_negative := fun _ => by
        rw [_root_.GD.N0232.N0719.N1024.d010715
          k sizes hk hsizes location scale]
        exact hcross
      energy_le := fun _ => by
        rw [_root_.GD.N0232.N0719.N1024.d010717
          k sizes hk hsizes location scale,
          _root_.GD.N0232.N0719.N1024.d010715
            k sizes hk hsizes location scale]
        exact _root_.GD.N0232.N0719.N1024.d010726
          k sizes hk hbounded scale hscale hcross }
  have hstrict :=
    _root_.GD.N0232.N0719.N1015.d010091 cert ()
  simpa [_root_.GD.N0232.N0719.N1024.d010731, law₁, target₁, cert,
    _root_.GD.N0232.N0719.N1015.d010083, _root_.GD.N0232.N0719.N1024.d010727,
    _root_.GD.N0232.N0719.N1024.d010711] using hstrict










theorem d010741
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i)
    (hbounded : BddAbove (_root_.GD.N0232.N0719.N1024.d010719 k sizes hk))
    (hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk scale < 0) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N1024.d010731 k sizes hk hsizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale) <
      ∫ ω,
        (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.N1024.d010711 k sizes location scale := by
  exact
    _root_.GD.N0232.N0719.N1024.d010740
      k sizes hk hsizes location scale hscale
      hbounded hcross
      (_root_.GD.N0232.N0719.N1024.d010735
        k sizes hk hsizes location scale hscale)
      (_root_.GD.N0232.N0719.N1024.d010736
        k sizes hk hsizes location scale hscale)
      (_root_.GD.N0232.N0719.N1024.d010737
        k sizes hk hsizes location scale hscale)

end

end GD.N0232.N0719.N1024
