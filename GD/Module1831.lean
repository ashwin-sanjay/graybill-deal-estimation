import GD.Module1830
import GD.Module1081

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0034.N0289

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1220
open _root_.GD.N0046.N0305

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030220 (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  (min (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))
    (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))).toReal

theorem d030221 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    0 ≤ _root_.GD.N0034.N0289.d030220 m n hm hn θ := ENNReal.toReal_nonneg

theorem d030222 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    ENNReal.ofReal (_root_.GD.N0034.N0289.d030220 m n hm hn θ) =
      min (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))
        (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) := by
  apply ENNReal.ofReal_toReal
  apply ne_top_of_le_ne_top _ (min_le_right _ _)
  rw [_root_.GD.N0232.N0720.N1080.d014184]
  exact ENNReal.ofReal_ne_top

theorem d030223 (p : _root_.GD.N0046.N0305.d030201 m n) :
    (∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (_root_.GD.N0034.N0289.d030220 m n hm hn θ)) ↔
      p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
  simp only [_root_.GD.N0034.N0289.d030222, le_min_iff, _root_.GD.N0046.N0305.d030202, Set.mem_setOf_eq]

def d030224 : Prop :=
  ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
    _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ _root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 +
      ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 m n hm hn θ

theorem d030225 :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔ _root_.GD.N0034.N0289.d030224 m n hm hn := by
  have h := _root_.GD.N0232.N0720.N1220.d017305 m n hm hn
    (_root_.GD.N0034.N0289.d030220 m n hm hn) (_root_.GD.N0034.N0289.d030221 m n hm hn)
  simpa only [_root_.GD.N0034.N0289.d030223, _root_.GD.N0034.N0289.d030224, Set.Nonempty] using h

theorem d030226 :
    _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ ↔
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) ∧
        _root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 +
          ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 m n hm hn θ < _root_.GD.N0232.N0720.N1220.d017301 m n F w := by
  rw [← Set.not_nonempty_iff_eq_empty, _root_.GD.N0034.N0289.d030225]
  simp only [_root_.GD.N0034.N0289.d030224, not_forall, exists_prop, not_le]

end
end GD.N0034.N0289

#print axioms _root_.GD.N0034.N0289.d030222
#print axioms _root_.GD.N0034.N0289.d030225
#print axioms _root_.GD.N0034.N0289.d030226
