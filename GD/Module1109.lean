import GD.Module1104
import GD.Module0148
import Mathlib.Tactic



















open MeasureTheory
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1478

noncomputable section

open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0671
open _root_.GD.N0230.N0718

variable (m n : ℕ)

private theorem d017816 (x : ENNReal) :
    ENNReal.ofReal (1 / 2 : ℝ) * x +
        ENNReal.ofReal (1 / 2 : ℝ) * x = x := by
  rw [← add_mul]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

private theorem d017817
    {x y : ENNReal} (hx : x ≠ ⊤) (hxy : x + y = x) : y = 0 := by
  have hyLe : y ≤ x := by
    calc
      y ≤ x + y := le_add_left le_rfl
      _ = x := hxy
  have hy : y ≠ ⊤ := ne_top_of_le_ne_top hx hyLe
  have hreal := congrArg ENNReal.toReal hxy
  rw [ENNReal.toReal_add hx hy] at hreal
  have hyReal : y.toReal = 0 := by linarith
  exact ((ENNReal.toReal_eq_zero_iff y).1 hyReal).resolve_right hy





theorem d017818
    {p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hpq : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014182 m n theta q) :
    _root_.GD.N0232.N0720.N1036.d014669 m n p ↔
      _root_.GD.N0232.N0720.N1036.d014669 m n q := by
  constructor
  · intro hp e he theta
    have hep : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e p := by
      intro eta
      simpa [hpq eta] using he eta
    exact (hp e hep theta).trans (hpq theta)
  · intro hq e he theta
    have heq : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e q := by
      intro eta
      simpa [hpq eta] using he eta
    exact (hq e heq theta).trans (hpq theta).symm



theorem d017819
    {p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : _root_.GD.N0232.N0720.N1036.d014669 m n p)
    (hqp : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) q p) :
    _root_.GD.N0232.N0720.N1036.d014669 m n q := by
  exact (_root_.GD.N0232.N0720.N1478.d017818 m n
    (p := q) (q := p) (hp q hqp)).2 hp






theorem d017820
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : _root_.GD.N0232.N0720.N1036.d014669 m n p) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p := by
  intro q hqp
  have hprofile : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta q = _root_.GD.N0232.N0720.N1080.d014182 m n theta p :=
    hp q hqp
  have hmidpoint :
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0230.N0718.d001528 q p) p := by
    intro theta
    have htax := _root_.GD.N0230.N0670.d001647
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
      theta.location q p
    change _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0718.d001528 q p) +
        _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0
          (_root_.GD.N0230.N0670.d001646 q p) =
      ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n theta q +
        ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p at htax
    calc
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0718.d001528 q p) ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0718.d001528 q p) +
            _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0
              (_root_.GD.N0230.N0670.d001646 q p) := le_add_right le_rfl
      _ = ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n theta q +
            ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p := htax
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
        rw [hprofile theta]
        exact _root_.GD.N0232.N0720.N1478.d017816 (_root_.GD.N0232.N0720.N1080.d014182 m n theta p)
  have hmidProfile :
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0230.N0718.d001528 q p) =
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p :=
    hp (_root_.GD.N0230.N0718.d001528 q p) hmidpoint _root_.GD.N0232.N0720.N1080.d014169
  have htaxRef := _root_.GD.N0230.N0670.d001647
    (_root_.GD.N0232.N0720.N1080.d014173 m n _root_.GD.N0232.N0720.N1080.d014169)
    _root_.GD.N0232.N0720.N1080.d014169.location q p
  change _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0230.N0718.d001528 q p) +
        _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n)
          (_root_.GD.N0232.N0720.N1080.d014171 m n _root_.GD.N0232.N0720.N1080.d014169) 0 (_root_.GD.N0230.N0670.d001646 q p) =
      ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q +
        ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p at htaxRef
  have hpFinite : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014190]
    exact ENNReal.ofReal_ne_top
  have htaxZero : _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n)
      (_root_.GD.N0232.N0720.N1080.d014171 m n _root_.GD.N0232.N0720.N1080.d014169) 0 (_root_.GD.N0230.N0670.d001646 q p) = 0 := by
    rw [hmidProfile, hprofile _root_.GD.N0232.N0720.N1080.d014169] at htaxRef
    rw [_root_.GD.N0232.N0720.N1478.d017816] at htaxRef
    exact _root_.GD.N0232.N0720.N1478.d017817 hpFinite htaxRef
  apply _root_.GD.N0230.N0671.d001650
    (_root_.GD.N0232.N0720.N1080.d014173 m n _root_.GD.N0232.N0720.N1080.d014169)
      (by
        simpa [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
          (Measure.AbsolutelyContinuous.rfl :
            _root_.GD.N0232.N0720.N1080.d014172 m n ≪ _root_.GD.N0232.N0720.N1080.d014172 m n))
    htaxZero



theorem d017821
    {p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : _root_.GD.N0232.N0720.N1036.d014669 m n p)
    (hqp : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) q p) :
    q = p :=
  _root_.GD.N0232.N0720.N1478.d017820 m n hp q hqp



theorem d017822
    {p s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : _root_.GD.N0232.N0720.N1036.d014669 m n p)
    (hsp : s ≠ p) {t : ℝ} (ht : t ≠ 0) :
    ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (p + t • (s - p)) p := by
  intro hdom
  have heq : p + t • (s - p) = p :=
    _root_.GD.N0232.N0720.N1478.d017821 m n hp hdom
  have hsmul : t • (s - p) = 0 := by
    apply add_left_cancel (a := p)
    simpa using heq
  have hsub : s - p = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left ht
  exact hsp (sub_eq_zero.mp hsub)



theorem d017823
    {p q base : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hpq : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014182 m n theta q) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p base ↔
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) q base := by
  constructor <;> intro h theta
  · simpa [hpq theta] using h theta
  · simpa [hpq theta] using h theta

end

end N1478
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1478.d017820
#print axioms _root_.GD.N0232.N0720.N1478.d017822
