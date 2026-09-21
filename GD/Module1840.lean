import GD.Module1831
import GD.Module1839

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0034.N0297

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1220
open _root_.GD.N0230.N0718
open _root_.GD.N0046.N0305 _root_.GD.N0046.N0303
open _root_.GD.N0034.N0289

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030293
    {p q : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hpq : p ≠ q)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0230.N0718.d001528 p q) < ENNReal.ofReal (_root_.GD.N0034.N0289.d030220 m n hm hn θ) := by
  exact _root_.GD.N0046.N0303.d030188
    (_root_.GD.N0232.N0720.N1080.d014173 m n θ)
    (_root_.GD.N0046.N0305.d030203 m n θ) θ.location ENNReal.ofReal_ne_top
    ((_root_.GD.N0034.N0289.d030223 m n hm hn p).mpr hp θ)
    ((_root_.GD.N0034.N0289.d030223 m n hm hn q).mpr hq θ) hpq

theorem d030294
    {p q : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hpq : p ≠ q) :
    0 < _root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 - ‖_root_.GD.N0230.N0718.d001528 p q‖ ^ 2 := by
  have h := _root_.GD.N0034.N0297.d030293 m n hm hn hp hq hpq _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190] at h
  simp only [zero_sub, norm_neg] at h
  exact sub_pos.mpr ((ENNReal.ofReal_lt_ofReal_iff').mp h).1

theorem d030295
    {p q : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    _root_.GD.N0232.N0720.N1220.d017301 m n F w +
      (_root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 - ‖_root_.GD.N0230.N0718.d001528 p q‖ ^ 2) ≤
        _root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 +
          ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 m n hm hn θ := by
  have hz := _root_.GD.N0046.N0305.d030209 m n hp hq
  have hbound := _root_.GD.N0232.N0720.N1220.d017302 m n F w hw (_root_.GD.N0230.N0718.d001528 p q)
    (_root_.GD.N0046.N0305.d030204 m n hz)
  have hsum : (∑ θ ∈ F, w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0230.N0718.d001528 p q)).toReal) ≤
      ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 m n hm hn θ := by
    apply Finset.sum_le_sum
    intro θ hθ
    apply mul_le_mul_of_nonneg_left _ (hw θ hθ)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((_root_.GD.N0034.N0289.d030223 m n hm hn (_root_.GD.N0230.N0718.d001528 p q)).mpr hz θ)).trans_eq
      (ENNReal.toReal_ofReal (_root_.GD.N0034.N0289.d030221 m n hm hn θ))
  linarith

theorem d030296
    {p q : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hpq : p ≠ q) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0720.N1220.d017301 m n F w + ε ≤
          _root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 +
            ∑ θ ∈ F, w θ * _root_.GD.N0034.N0289.d030220 m n hm hn θ := by
  exact ⟨_root_.GD.N0034.N0289.d030220 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 - ‖_root_.GD.N0230.N0718.d001528 p q‖ ^ 2,
    _root_.GD.N0034.N0297.d030294 m n hm hn hp hq hpq,
    _root_.GD.N0034.N0297.d030295 m n hm hn hp hq⟩

end
end GD.N0034.N0297

#print axioms _root_.GD.N0034.N0297.d030293
#print axioms _root_.GD.N0034.N0297.d030294
#print axioms _root_.GD.N0034.N0297.d030295
#print axioms _root_.GD.N0034.N0297.d030296
