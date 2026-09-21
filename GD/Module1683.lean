import GD.Module1682
import GD.Module1490







set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0403
noncomputable section

open _root_.GD.N0213.N0508
open _root_.GD.N0213.N0509
open _root_.GD.N0213.N0522
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0351 _root_.GD.N0101.N0415 _root_.GD.N0101.N0398
open _root_.GD.N0230.N0665
open _root_.GD.N0232.N0719.N0954

variable {k : ℕ}

def d028435 (l u : ℝ) : Set (Fin k → ℝ) := Icc (fun _ => l) (fun _ => u)

def d028436 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ) :
    Measure (Fin k → ℝ) :=
  (_root_.GD.N0213.N0508.d028429 a).withDensity (fun β => ENNReal.ofReal (h β ^ 2))

theorem d028437 (a : Fin k → ℝ) : _root_.GD.N0213.N0508.d028429 a ≤ volume := by
  have hprior : _root_.GD.N0213.N0522.d008020 (fun _ : Fin k => 1) ≤ volume := by
    calc
      _ ≤ volume.withDensity 1 := by
        apply withDensity_mono
        filter_upwards with β
        have hw : _root_.GD.N0213.N0522.d008019 (fun _ : Fin k => 1) β ≤ 1 := by
          unfold _root_.GD.N0213.N0522.d008019
          split_ifs <;> simp
        simpa only [Pi.one_apply, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hw
      _ = _ := withDensity_one
  calc
    _ ≤ (_root_.GD.N0213.N0522.d008020 (fun _ : Fin k => 1)).withDensity 1 := by
      apply withDensity_mono
      filter_upwards [_root_.GD.N0213.N0522.d008026 (fun _ : Fin k => 1)] with β hβ
      have hp := _root_.GD.N0213.N0509.d023112 a β hβ
      have hs : _root_.GD.N0213.N0509.d023108 a β ^ 2 ≤ 1 := by nlinarith [hp.1, hp.2]
      simpa only [Pi.one_apply, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs
    _ = _root_.GD.N0213.N0522.d008020 (fun _ : Fin k => 1) := withDensity_one
    _ ≤ volume := hprior



theorem d028438 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {l u : ℝ} (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0) :
    _root_.GD.N0101.N0403.d028436 a h ≤ volume.restrict (_root_.GD.N0101.N0403.d028435 l u) := by
  have hbox : MeasurableSet (_root_.GD.N0101.N0403.d028435 (k := k) l u) := measurableSet_Icc
  calc
    _ ≤ (_root_.GD.N0213.N0508.d028429 a).withDensity ((_root_.GD.N0101.N0403.d028435 l u).indicator 1) := by
      apply withDensity_mono
      filter_upwards with β
      by_cases hβ : β ∈ _root_.GD.N0101.N0403.d028435 l u
      · rw [indicator_of_mem hβ]
        have hs : h β ^ 2 ≤ 1 := by nlinarith [(hh β).1, (hh β).2]
        simpa only [Pi.one_apply, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs
      · simp only [hsupp β hβ, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
          indicator_of_notMem hβ, le_refl]
    _ = (_root_.GD.N0213.N0508.d028429 a).restrict (_root_.GD.N0101.N0403.d028435 l u) := withDensity_indicator_one hbox
    _ ≤ volume.restrict (_root_.GD.N0101.N0403.d028435 l u) := Measure.restrict_mono_measure (_root_.GD.N0101.N0403.d028437 a) _

theorem d028439 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {l u : ℝ} (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0) :
    _root_.GD.N0101.N0403.d028436 a h univ ≤ ENNReal.ofReal (u - l) ^ k := by
  have hb := (_root_.GD.N0101.N0403.d028438 a h hh hsupp) univ
  simpa only [Measure.restrict_apply_univ, _root_.GD.N0101.N0403.d028435, Real.volume_Icc_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hb

theorem d028440 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {l u : ℝ} (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0) :
    _root_.GD.N0101.N0403.d028436 a h univ ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (_root_.GD.N0101.N0403.d028439 a h hh hsupp)

theorem d028441 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {l u : ℝ} (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0) :
    ∀ᵐ β ∂_root_.GD.N0101.N0403.d028436 a h, β ∈ _root_.GD.N0101.N0403.d028435 l u :=
  (_root_.GD.N0101.N0403.d028438 a h hh hsupp).absolutelyContinuous.ae_le
    (ae_restrict_mem measurableSet_Icc)

theorem d028442 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ) :
    ∀ᵐ β ∂_root_.GD.N0101.N0403.d028436 a h, β ∈ _root_.GD.N0101.N0357.d023158 := by
  apply (withDensity_absolutelyContinuous (_root_.GD.N0213.N0508.d028429 a) _).ae_le
  exact (withDensity_absolutelyContinuous (_root_.GD.N0213.N0522.d008020 (fun _ : Fin k => 1)) _).ae_le
    (_root_.GD.N0213.N0522.d008026 (fun _ : Fin k => 1))

theorem d028443 {l u : ℝ} (hl : 0 < l) {β : Fin k → ℝ}
    (hβ : β ∈ _root_.GD.N0101.N0403.d028435 l u) : (∑ i, (β i)⁻¹) ≤ (k : ℝ) / l := by
  calc
    _ ≤ ∑ _i : Fin k, l⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      exact inv_anti₀ hl (hβ.1 i)
    _ = _ := by simp [div_eq_mul_inv]

theorem d028444 [NeZero k] (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {l u : ℝ} (hl : 0 < l) {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0403.d028435 l u) :
    _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β ≤ ENNReal.ofReal ((k : ℝ) / l) :=
  (_root_.GD.N0101.N0415.d023233 a ha (fun i => hl.trans_le (hβ.1 i))).trans
    (ENNReal.ofReal_le_ofReal (_root_.GD.N0101.N0403.d028443 hl hβ))

theorem d028445 [NeZero k] (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (h : (Fin k → ℝ) → ℝ) {l u : ℝ} (hl : 0 < l)
    (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0) :
    (∫⁻ β, _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β ∂_root_.GD.N0101.N0403.d028436 a h) ≤
      ENNReal.ofReal ((k : ℝ) / l) * _root_.GD.N0101.N0403.d028436 a h univ := by
  calc
    _ ≤ ∫⁻ _β, ENNReal.ofReal ((k : ℝ) / l) ∂_root_.GD.N0101.N0403.d028436 a h := by
      apply lintegral_mono_ae
      filter_upwards [_root_.GD.N0101.N0403.d028441 a h hh hsupp] with β hβ
      exact _root_.GD.N0101.N0403.d028444 a ha hl hβ
    _ = _ := lintegral_const _

theorem d028446 [NeZero k] (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (h : (Fin k → ℝ) → ℝ) {l u : ℝ} (hl : 0 < l)
    (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0) :
    (∫⁻ β, _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β ∂_root_.GD.N0101.N0403.d028436 a h) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0101.N0403.d028440 a h hh hsupp))
    (_root_.GD.N0101.N0403.d028445 a ha h hl hh hsupp)

theorem d028447 [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (h : (Fin k → ℝ) → ℝ) {l u : ℝ} (hl : 0 < l)
    (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0) :
    Integrable (fun β => (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β).toReal) (_root_.GD.N0101.N0403.d028436 a h) := by
  apply (integrable_toReal_iff
    (_root_.GD.N0101.N0415.d023237 a ha _ (_root_.GD.N0101.N0403.d028442 a h))
    ((_root_.GD.N0101.N0403.d028442 a h).mono fun _ hβ => _root_.GD.N0101.N0415.d023234 a ha hβ)).mpr
  exact _root_.GD.N0101.N0403.d028446 a ha h hl hh hsupp

theorem d028448 [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (h : (Fin k → ℝ) → ℝ) {l u : ℝ} (hl : 0 < l)
    (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0) :
    Integrable (_root_.GD.N0101.N0415.d023239 a) (_root_.GD.N0101.N0403.d028436 a h) :=
  (_root_.GD.N0101.N0403.d028447 a ha h hl hh hsupp).congr
    (_root_.GD.N0101.N0415.d023242 a _ (_root_.GD.N0101.N0403.d028442 a h)).symm



theorem d028449 [NeZero k] (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (h : (Fin k → ℝ) → ℝ) {l u : ℝ} (hl : 0 < l)
    (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0)
    (p : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t) :
    Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal)
      (_root_.GD.N0101.N0403.d028436 (_root_.GD.N0232.N0719.N0954.d009355 sizes) h) := by
  apply (_root_.GD.N0101.N0403.d028447 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N0954.d009358 hn)
    h hl hh hsupp).congr
  filter_upwards [_root_.GD.N0101.N0403.d028442 (_root_.GD.N0232.N0719.N0954.d009355 sizes) h] with β hβ
  rw [_root_.GD.N0101.N0398.d023336 sizes hn p hp hpunit hβ,
    _root_.GD.N0101.N0349.d023344
      (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N0954.d009358 hn) p hporacle hβ]

theorem d028450 [NeZero k] (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (h : (Fin k → ℝ) → ℝ) {l u : ℝ} (hl : 0 < l)
    (hh : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (hsupp : ∀ β ∉ _root_.GD.N0101.N0403.d028435 l u, h β = 0)
    (p : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t) :
    (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn p β ∂_root_.GD.N0101.N0403.d028436 (_root_.GD.N0232.N0719.N0954.d009355 sizes) h) ≠ ⊤ := by
  have heq : _root_.GD.N0101.N0398.d023335 sizes hn p =ᵐ[_root_.GD.N0101.N0403.d028436 (_root_.GD.N0232.N0719.N0954.d009355 sizes) h]
      _root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) _root_.GD.N0230.N0665.d000407 := by
    filter_upwards [_root_.GD.N0101.N0403.d028442 (_root_.GD.N0232.N0719.N0954.d009355 sizes) h] with β hβ
    rw [_root_.GD.N0101.N0398.d023336 sizes hn p hp hpunit hβ,
      _root_.GD.N0101.N0349.d023344
        (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N0954.d009358 hn) p hporacle hβ]
  rw [lintegral_congr_ae heq]
  exact _root_.GD.N0101.N0403.d028446 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N0954.d009358 hn) h hl hh hsupp

end
end GD.N0101.N0403

#print axioms _root_.GD.N0101.N0403.d028437
#print axioms _root_.GD.N0101.N0403.d028440
#print axioms _root_.GD.N0101.N0403.d028445
#print axioms _root_.GD.N0101.N0403.d028448
#print axioms _root_.GD.N0101.N0403.d028449
#print axioms _root_.GD.N0101.N0403.d028450
