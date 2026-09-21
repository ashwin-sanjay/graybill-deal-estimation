import GD.Module1478
import GD.Module1680

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0101.N0414
noncomputable section

open _root_.GD.N0213.N0516
open _root_.GD.N0232.N0719.N0954

variable {k : ℕ}


def d028417 (a : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (a i) (a i)

def d028418 (β t : Fin k → ℝ) : Fin k → ℝ := fun i => β i * t i

def d028419 (β u : Fin k → ℝ) : Fin k → ℝ := fun i => u i / β i

@[fun_prop] theorem d028420 (β : Fin k → ℝ) :
    Measurable (_root_.GD.N0101.N0414.d028418 β) := by unfold _root_.GD.N0101.N0414.d028418; fun_prop

@[fun_prop] theorem d028421 (β : Fin k → ℝ) :
    Measurable (_root_.GD.N0101.N0414.d028419 β) := by unfold _root_.GD.N0101.N0414.d028419; fun_prop

def d028422 (β : Fin k → ℝ) (hβ : ∀ i, β i ≠ 0) :
    (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) where
  toFun := _root_.GD.N0101.N0414.d028418 β
  invFun := _root_.GD.N0101.N0414.d028419 β
  left_inv t := by
    funext i
    exact mul_div_cancel_left₀ (t i) (hβ i)
  right_inv u := by
    funext i
    exact mul_div_cancel₀ (u i) (hβ i)
  measurable_toFun := _root_.GD.N0101.N0414.d028420 β
  measurable_invFun := _root_.GD.N0101.N0414.d028421 β

theorem d028423 (a β : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hβ : ∀ i, 0 < β i) :
    MeasurePreserving (_root_.GD.N0101.N0414.d028418 β) (_root_.GD.N0213.N0516.d028411 a β) (_root_.GD.N0101.N0414.d028417 a) := by
  letI (i : Fin k) := isProbabilityMeasure_gammaMeasure (ha i) (ha i)
  apply measurePreserving_pi (fun i => gammaMeasure (a i) (a i * β i))
    (fun i => gammaMeasure (a i) (a i))
  intro i
  refine ⟨measurable_const.mul measurable_id, ?_⟩
  simpa only [mul_div_cancel_right₀ _ (hβ i).ne'] using
    _root_.GD.N0232.N0719.N0954.d009354 (ha i) (mul_pos (ha i) (hβ i)) (hβ i)

theorem d028424 (a β : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hβ : ∀ i, 0 < β i) :
    MeasurePreserving (_root_.GD.N0101.N0414.d028419 β) (_root_.GD.N0101.N0414.d028417 a) (_root_.GD.N0213.N0516.d028411 a β) :=
  MeasurePreserving.symm (_root_.GD.N0101.N0414.d028422 β (fun i => (hβ i).ne'))
    (_root_.GD.N0101.N0414.d028423 a β ha hβ)

theorem d028425 (a β : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hβ : ∀ i, 0 < β i) :
    (_root_.GD.N0213.N0516.d028411 a β).map (_root_.GD.N0101.N0414.d028418 β) = _root_.GD.N0101.N0414.d028417 a :=
  (_root_.GD.N0101.N0414.d028423 a β ha hβ).map_eq



theorem d028426 (a β : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hβ : ∀ i, 0 < β i) (F : (Fin k → ℝ) → ℝ≥0∞) :
    (∫⁻ t, F t ∂_root_.GD.N0213.N0516.d028411 a β) =
      ∫⁻ u, F (_root_.GD.N0101.N0414.d028419 β u) ∂_root_.GD.N0101.N0414.d028417 a :=
  ((_root_.GD.N0101.N0414.d028424 a β ha hβ).lintegral_comp_emb
    (_root_.GD.N0101.N0414.d028422 β (fun i => (hβ i).ne')).symm.measurableEmbedding F).symm

theorem d028427 (a β : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hβ : ∀ i, 0 < β i) (F : (Fin k → ℝ) → ℝ) :
    (∫ t, F t ∂_root_.GD.N0213.N0516.d028411 a β) =
      ∫ u, F (_root_.GD.N0101.N0414.d028419 β u) ∂_root_.GD.N0101.N0414.d028417 a :=
  ((_root_.GD.N0101.N0414.d028424 a β ha hβ).integral_comp
    (_root_.GD.N0101.N0414.d028422 β (fun i => (hβ i).ne')).symm.measurableEmbedding F).symm

theorem d028428 (a β : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hβ : ∀ i, 0 < β i) (F : (Fin k → ℝ) → ℝ) :
    Integrable F (_root_.GD.N0213.N0516.d028411 a β) ↔
      Integrable (fun u => F (_root_.GD.N0101.N0414.d028419 β u)) (_root_.GD.N0101.N0414.d028417 a) :=
  ((_root_.GD.N0101.N0414.d028424 a β ha hβ).integrable_comp_emb
    (_root_.GD.N0101.N0414.d028422 β (fun i => (hβ i).ne')).symm.measurableEmbedding).symm

end
end GD.N0101.N0414

#print axioms _root_.GD.N0101.N0414.d028423
#print axioms _root_.GD.N0101.N0414.d028424
#print axioms _root_.GD.N0101.N0414.d028425
#print axioms _root_.GD.N0101.N0414.d028426
#print axioms _root_.GD.N0101.N0414.d028427
#print axioms _root_.GD.N0101.N0414.d028428
