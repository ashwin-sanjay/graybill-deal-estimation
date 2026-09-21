import GD.Module1423
import GD.Module1412

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GD.N0099
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1220

variable {Ω : Type*} [MeasurableSpace Ω]


theorem d022753 (m n : ℕ)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n × Ω → ℝ) (hd : Measurable d)
    (B : ℝ) (hb : ∀ x, |d x| ≤ B) :
    _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤
      (∫ x, d x ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014172 m n).prod ν) +
        ∑ θ ∈ F, w θ * ∫ x, (d x - θ.location) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod ν := by
  letI (θ : _root_.GD.N0232.N0720.N1080.d014168) : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by unfold _root_.GD.N0232.N0720.N1080.d014171; infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by unfold _root_.GD.N0232.N0720.N1080.d014172; infer_instance
  have hint (θ : _root_.GD.N0232.N0720.N1080.d014168) : Integrable (fun x => (d x - θ.location) ^ 2) ((_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod ν) :=
    (_root_.GD.N0099.d022750 _ d hd B hb θ.location).integrable_sq
  have hint0 : Integrable (fun x => d x ^ 2) ((_root_.GD.N0232.N0720.N1080.d014172 m n).prod ν) := by
    simpa only [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169, sub_zero] using hint _root_.GD.N0232.N0720.N1080.d014169
  have hp (y : Ω) := _root_.GD.N0099.d022751 m n F w hw
    (fun x => d (x, y)) (hd.comp measurable_prodMk_right) B (fun x => hb (x, y))
  have hi := hint0.integral_prod_right.add (integrable_finsetSum F fun θ _ =>
    (hint θ).integral_prod_right.const_mul (w θ))
  have hh := integral_mono (integrable_const (_root_.GD.N0232.N0720.N1220.d017301 m n F w)) hi hp
  rw [integral_const, probReal_univ, one_smul] at hh
  simp only [Pi.add_apply] at hh
  rw [integral_add hint0.integral_prod_right
    (integrable_finsetSum F fun θ _ => (hint θ).integral_prod_right.const_mul (w θ)),
    integral_finsetSum F (fun θ _ => (hint θ).integral_prod_right.const_mul (w θ))] at hh
  simp_rw [integral_const_mul] at hh
  rw [← integral_prod_symm _ hint0] at hh
  simp_rw [← integral_prod_symm _ (hint _)] at hh
  exact hh


theorem d022754 (m n : ℕ)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (η : _root_.GD.N0232.N0720.N1080.d014168 → Measure Ω) [∀ θ, IsProbabilityMeasure (η θ)]
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n × Ω → ℝ) (hd : Measurable d)
    (B : ℝ) (hb : ∀ x, |d x| ≤ B) (A : ℝ) (hA : 0 ≤ A)
    (cap : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hdom : ∀ θ, θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F → ν ≤ ENNReal.ofReal A • η θ)
    (hcap : ∀ θ, θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F →
      (∫ x, (d x - θ.location) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ)) ≤ cap θ) :
    _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ A * (cap _root_.GD.N0232.N0720.N1080.d014169 + ∑ θ ∈ F, w θ * cap θ) := by
  letI (θ : _root_.GD.N0232.N0720.N1080.d014168) : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n θ) := by unfold _root_.GD.N0232.N0720.N1080.d014171; infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by unfold _root_.GD.N0232.N0720.N1080.d014172; infer_instance
  have hbound (θ : _root_.GD.N0232.N0720.N1080.d014168) (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
      (∫ x, (d x - θ.location) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod ν) ≤ A * cap θ := by
    have hμ : (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod ν ≤ ENNReal.ofReal A • (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ) := by
      simpa only [one_mul] using _root_.GD.N0099.d022648 (_root_.GD.N0232.N0720.N1080.d014171 m n θ) (_root_.GD.N0232.N0720.N1080.d014171 m n θ) ν (η θ)
        1 (ENNReal.ofReal A) ENNReal.ofReal_ne_top (by simp) (hdom θ hθ)
    have hint := (_root_.GD.N0099.d022750 ((_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ)) d hd B hb θ.location).integrable_sq
    have hh := integral_mono_measure hμ
      (ae_of_all _ fun _ => sq_nonneg _) (hint.smul_measure ENNReal.ofReal_ne_top)
    rw [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hcap θ hθ) hA)
  have href : (∫ x, d x ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014172 m n).prod ν) ≤ A * cap _root_.GD.N0232.N0720.N1080.d014169 := by
    simpa only [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169, sub_zero] using hbound _root_.GD.N0232.N0720.N1080.d014169 (Or.inl rfl)
  apply (_root_.GD.N0099.d022753 m n F w hw ν d hd B hb).trans
  calc
    _ ≤ A * cap _root_.GD.N0232.N0720.N1080.d014169 + ∑ θ ∈ F, w θ * (A * cap θ) :=
      add_le_add href (Finset.sum_le_sum fun θ hθ =>
        mul_le_mul_of_nonneg_left (hbound θ (Or.inr hθ)) (hw θ hθ))
    _ = _ := by simp only [mul_add, Finset.mul_sum, mul_left_comm]

end
end GD.N0099

#print axioms _root_.GD.N0099.d022753
#print axioms _root_.GD.N0099.d022754
