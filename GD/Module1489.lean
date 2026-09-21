import GD.Module1488
import GD.Module1474







set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0398
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0072 _root_.GD.N0101.N0357 _root_.GD.N0101.N0399 _root_.GD.N0101.N0351
open _root_.GD.N0225.N0539

variable {k : ℕ}

def d023335 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (β : Fin k → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0232.N0719.N0859.d010840 k sizes
    (_root_.GD.N0101.N0399.d023328 sizes (fun i => by have := hn i; omega) β)
    (_root_.GD.N0072.d023291 sizes w)

theorem d023336 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) {β : Fin k → ℝ} (hβ : β ∈ _root_.GD.N0101.N0357.d023158) :
    _root_.GD.N0101.N0398.d023335 sizes hn w β = _root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) w β :=
  _root_.GD.N0101.N0399.d023333 sizes hn hβ w hw hunit

theorem d023337 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (α : Fin k → ℝ) (L : ℝ) :
    _root_.GD.N0101.N0398.d023335 sizes hn w =ᵐ[_root_.GD.N0225.N0539.d008058 α L] _root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) w := by
  filter_upwards [_root_.GD.N0101.N0351.d023194 α L] with β hβ
  exact _root_.GD.N0101.N0398.d023336 sizes hn w hw hunit hβ



theorem d023338 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ L : ℝ) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) :
    (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn w β
      ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L) =
      ∫⁻ t, _root_.GD.N0101.N0351.d023189 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L w t
        ∂_root_.GD.N0101.N0351.d023191 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ := by
  rw [lintegral_congr_ae (_root_.GD.N0101.N0398.d023337 sizes hn w hw hunit _ L)]
  exact _root_.GD.N0101.N0351.d023200 _ ρ L (_root_.GD.N0232.N0719.N0954.d009358 hn) hρ w hw



theorem d023339
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (α : Fin k → ℝ) (L : ℝ)
    (p : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1)
    (hpfinite : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) ≠ ⊤)
    (hbase : Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal) (_root_.GD.N0225.N0539.d008058 α L)) :
    (∫⁻ β, _root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) p β ∂_root_.GD.N0225.N0539.d008058 α L) ≠ ⊤ := by
  have hae := _root_.GD.N0101.N0398.d023337 sizes hn p hp hpunit α L
  have htop : ∀ᵐ β ∂_root_.GD.N0225.N0539.d008058 α L, _root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) p β ≠ ⊤ := by
    filter_upwards [hae] with β hβ
    rw [← hβ]
    exact hpfinite _
  apply (integrable_toReal_iff
    (_root_.GD.N0101.N0351.d023198 _ α (_root_.GD.N0232.N0719.N0954.d009358 hn) L p hp) htop).mp
  exact hbase.congr (hae.mono fun _ h => congrArg ENNReal.toReal h)



theorem d023340
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ L : ℝ) (hρ : ρ < 1)
    (p w : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hpfinite : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) ≠ ⊤)
    (hbase : Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal)
      (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L))
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) :
    Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal -
      (_root_.GD.N0101.N0398.d023335 sizes hn w β).toReal)
        (_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L) ∧
      Integrable (fun t => _root_.GD.N0101.N0351.d023190 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L p t -
        _root_.GD.N0101.N0351.d023190 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L w t) (_root_.GD.N0101.N0351.d023191 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ) ∧
      (∫ β, (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal - (_root_.GD.N0101.N0398.d023335 sizes hn w β).toReal
        ∂_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L) =
      ∫ t, _root_.GD.N0101.N0351.d023190 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L p t - _root_.GD.N0101.N0351.d023190 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L w t
        ∂_root_.GD.N0101.N0351.d023191 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ := by
  have hfinite := _root_.GD.N0101.N0398.d023339
    sizes hn _ L p hp hpunit hpfinite hbase
  have hdom : ∀ β ∈ _root_.GD.N0101.N0357.d023158,
      _root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) w β ≤ _root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) p β := by
    intro β hβ
    rw [← _root_.GD.N0101.N0398.d023336 sizes hn w hw hwunit hβ,
      ← _root_.GD.N0101.N0398.d023336 sizes hn p hp hpunit hβ]
    exact hweak _
  obtain ⟨hgi, hpi, heq⟩ := _root_.GD.N0101.N0351.d023206 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ L
    (_root_.GD.N0232.N0719.N0954.d009358 hn) hρ p w hp hw hfinite hdom
  have hae : (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal -
      (_root_.GD.N0101.N0398.d023335 sizes hn w β).toReal) =ᵐ[_root_.GD.N0225.N0539.d008058 (fun i => 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) L]
      fun β => (_root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) p β).toReal -
        (_root_.GD.N0101.N0351.d023188 (_root_.GD.N0232.N0719.N0954.d009355 sizes) w β).toReal := by
    filter_upwards [_root_.GD.N0101.N0398.d023337 sizes hn p hp hpunit _ L,
      _root_.GD.N0101.N0398.d023337 sizes hn w hw hwunit _ L] with β hpβ hwβ
    rw [hpβ, hwβ]
  exact ⟨hgi.congr hae.symm, hpi, (integral_congr_ae hae).trans heq⟩

end
end GD.N0101.N0398

#print axioms _root_.GD.N0101.N0398.d023338
#print axioms _root_.GD.N0101.N0398.d023339
#print axioms _root_.GD.N0101.N0398.d023340
