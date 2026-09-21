import GD.Module1470
import GD.Module1651

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0101.N0397
noncomputable section

open _root_.GD.N0213
open _root_.GD.N0213.N0509 _root_.GD.N0213.N0510 _root_.GD.N0213.N0526

abbrev d028118 : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.finTwoArrow


theorem d028119 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (T : X → Y) (hT : MeasurePreserving T μ ν)
    (D : Y → ℝ≥0∞) (hD : Measurable D) :
    (μ.withDensity (fun x => D (T x))).map T = ν.withDensity D := by
  ext E hE
  rw [Measure.map_apply hT.measurable hE,
    withDensity_apply _ (hT.measurable hE), withDensity_apply _ hE,
    ← lintegral_indicator (hT.measurable hE), ← lintegral_indicator hE]
  calc
    (∫⁻ x, (T ⁻¹' E).indicator (fun x => D (T x)) x ∂μ) =
        ∫⁻ x, E.indicator D (T x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : T x ∈ E <;> simp [hx]
    _ = _ := hT.lintegral_comp (hD.indicator hE)

theorem d028120 (a r₁ r₂ : ℝ) :
    (_root_.GD.N0213.N0510.d023122 (fun _ : Fin 2 => a) ![r₁, r₂]).map _root_.GD.N0101.N0397.d028118 =
      _root_.GD.N0213.N0526.d028107 (a + 1) r₁ r₂ := by
  exact (measurePreserving_piFinTwo
    (fun i : Fin 2 => gammaMeasure (a + 1) (![r₁, r₂] i))).map_eq

def d028121 (a r₁ r₂ p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + p ^ a)⁻¹) ^ 2 /
    _root_.GD.N0213.N0510.d023124 (fun _ : Fin 2 => a) ![r₁, r₂])

@[fun_prop] theorem d028122 (a r₁ r₂ : ℝ) :
    Measurable (_root_.GD.N0101.N0397.d028121 a r₁ r₂) := by
  unfold _root_.GD.N0101.N0397.d028121
  fun_prop

theorem d028123 (a : ℝ) (β : Fin 2 → ℝ) (hβ : ∀ i, 0 ≤ β i) :
    _root_.GD.N0213.N0509.d023108 (fun _ : Fin 2 => a) β = (1 + (β 0 * β 1) ^ a)⁻¹ := by
  simp only [_root_.GD.N0213.N0509.d023108, _root_.GD.N0213.N0509.d023107, Fin.prod_univ_two,
    Real.mul_rpow (hβ 0) (hβ 1)]



theorem d028124 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    (_root_.GD.N0213.N0510.d023126 (fun _ : Fin 2 => a) ![r₁, r₂]).map _root_.GD.N0101.N0397.d028118 =
      _root_.GD.N0213.N0526.d028111 (a + 1) r₁ r₂ (_root_.GD.N0101.N0397.d028121 a r₁ r₂) := by
  have hr : ∀ i : Fin 2, 0 < (![r₁, r₂] i) := Fin.forall_fin_two.mpr ⟨h₁, h₂⟩
  have hpos := _root_.GD.N0232.N0719.N0910.d010287
    (shape := fun _ : Fin 2 => a + 1) (rate := ![r₁, r₂])
    (fun _ => by linarith) hr
  have hd : _root_.GD.N0213.N0510.d023125 (fun _ : Fin 2 => a) ![r₁, r₂] =ᵐ[
      _root_.GD.N0213.N0510.d023122 (fun _ : Fin 2 => a) ![r₁, r₂]]
      (fun β => _root_.GD.N0101.N0397.d028121 a r₁ r₂ ((_root_.GD.N0101.N0397.d028118 β).1 * (_root_.GD.N0101.N0397.d028118 β).2)) := by
    filter_upwards [hpos] with β hβ
    change ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 (fun _ : Fin 2 => a) β ^ 2 / _) = _
    rw [_root_.GD.N0101.N0397.d028123 a β (fun i => (hβ i).le)]
    rfl
  unfold _root_.GD.N0213.N0510.d023126
  rw [withDensity_congr_ae hd]
  exact _root_.GD.N0101.N0397.d028119 _ _ _root_.GD.N0101.N0397.d028118
    ⟨_root_.GD.N0101.N0397.d028118.measurable, _root_.GD.N0101.N0397.d028120 a r₁ r₂⟩
    (fun z : ℝ × ℝ => _root_.GD.N0101.N0397.d028121 a r₁ r₂ (z.1 * z.2)) (by fun_prop)

def d028125 (a r₁ r₂ : ℝ) : Measure (ℝ × ℝ) :=
  (_root_.GD.N0213.N0510.d023126 (fun _ : Fin 2 => a) ![r₁, r₂]).map _root_.GD.N0101.N0397.d028118

theorem d028126 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    MeasurePreserving (_root_.GD.N0213.N0526.d028101 r₁ r₂) (_root_.GD.N0101.N0397.d028125 a r₁ r₂)
      (_root_.GD.N0101.N0397.d028125 a r₁ r₂) := by
  unfold _root_.GD.N0101.N0397.d028125
  rw [_root_.GD.N0101.N0397.d028124 ha h₁ h₂]
  exact _root_.GD.N0213.N0526.d028113 (by linarith) h₁ h₂
    (_root_.GD.N0101.N0397.d028121 a r₁ r₂) (_root_.GD.N0101.N0397.d028122 a r₁ r₂)




theorem d028127 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    ((_root_.GD.N0101.N0397.d028125 a r₁ r₂).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal z.1⁻¹)).map (_root_.GD.N0213.N0526.d028101 r₁ r₂) =
      ENNReal.ofReal (r₁ / r₂) • (_root_.GD.N0101.N0397.d028125 a r₁ r₂).withDensity
        (fun z : ℝ × ℝ => ENNReal.ofReal z.2⁻¹) := by
  have hinv := _root_.GD.N0213.N0526.d028103 h₁.ne' h₂.ne'
  have heq : (fun z : ℝ × ℝ => ENNReal.ofReal z.1⁻¹) =
      fun z => ENNReal.ofReal ((_root_.GD.N0213.N0526.d028101 r₁ r₂ (_root_.GD.N0213.N0526.d028101 r₁ r₂ z)).1⁻¹) := by
    funext z
    rw [hinv]
  rw [heq, _root_.GD.N0101.N0397.d028119 _ _ _ (_root_.GD.N0101.N0397.d028126 ha h₁ h₂)
    (fun z : ℝ × ℝ => ENNReal.ofReal ((_root_.GD.N0213.N0526.d028101 r₁ r₂ z).1⁻¹)) (by fun_prop)]
  simp_rw [_root_.GD.N0213.N0526.d028115, ENNReal.ofReal_mul (div_pos h₁ h₂).le]
  exact withDensity_smul _ (by fun_prop)

end
end GD.N0101.N0397

#print axioms _root_.GD.N0101.N0397.d028119
#print axioms _root_.GD.N0101.N0397.d028120
#print axioms _root_.GD.N0101.N0397.d028124
#print axioms _root_.GD.N0101.N0397.d028126
#print axioms _root_.GD.N0101.N0397.d028127
