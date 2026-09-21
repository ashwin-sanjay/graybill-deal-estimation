import GD.Module1479
import GD.Module0540
import GD.Module1489

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0349
noncomputable section

open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0230.N0665
open _root_.GD.N0225.N0539
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0351 _root_.GD.N0101.N0415
open _root_.GD.N0101.N0416 _root_.GD.N0101.N0360 _root_.GD.N0101.N0398

variable {k : ℕ} [NeZero k]



theorem d023341 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    {L : ℝ} (hL : 0 < L) :
    Integrable (_root_.GD.N0101.N0415.d023239 a) (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) := by
  apply _root_.GD.N0101.N0360.d008071 _ hsum
    (_root_.GD.N0101.N0415.d023239 a) (_root_.GD.N0101.N0415.d023243 a ha)
    (fun β _ => _root_.GD.N0101.N0415.d023240 a β)
    (fun _ hc β _ => _root_.GD.N0101.N0415.d023244 a ha hc β)
    (_root_.GD.N0101.N0416.d023247 a ρ ha hρ hα hsum) hL

theorem d023342 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => (_root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β).toReal)
      (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) :=
  (_root_.GD.N0101.N0349.d023341 a ρ ha hρ hα hsum hL).congr
    (_root_.GD.N0101.N0415.d023242 a _ (_root_.GD.N0101.N0351.d023194 _ L))

theorem d023343 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    {L : ℝ} (hL : 0 < L) :
    (∫⁻ β, _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * a i) L) ≠ ⊤ := by
  apply (integrable_toReal_iff
    (_root_.GD.N0101.N0415.d023237 a ha _ (_root_.GD.N0101.N0351.d023194 _ L))
    ((_root_.GD.N0101.N0351.d023194 _ L).mono fun _ hβ => _root_.GD.N0101.N0415.d023234 a ha hβ)).mp
  exact _root_.GD.N0101.N0349.d023342 a ρ ha hρ hα hsum hL

omit [NeZero k] in
theorem d023344 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (p : (Fin k → ℝ) → Fin k → ℝ)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t)
    {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0101.N0351.d023188 a p β = _root_.GD.N0101.N0351.d023188 a _root_.GD.N0230.N0665.d000407 β := by
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0101.N0415.d023228 a ha hβ] with t ht
  rw [hporacle t ht]



theorem d023345 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (p : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t)
    {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal)
      (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L) := by
  apply (_root_.GD.N0101.N0349.d023342
    (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ (_root_.GD.N0232.N0719.N0954.d009358 hn) hρ hα hsum hL).congr
  filter_upwards [_root_.GD.N0101.N0351.d023194 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L] with β hβ
  rw [_root_.GD.N0101.N0398.d023336 sizes hn p hp hpunit hβ,
    _root_.GD.N0101.N0349.d023344 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N0954.d009358 hn) p hporacle hβ]

end
end GD.N0101.N0349

#print axioms _root_.GD.N0101.N0349.d023341
#print axioms _root_.GD.N0101.N0349.d023342
#print axioms _root_.GD.N0101.N0349.d023343
#print axioms _root_.GD.N0101.N0349.d023345
