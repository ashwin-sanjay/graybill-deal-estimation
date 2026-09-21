import GD.Module1269

set_option autoImplicit false
set_option warningAsError true









open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0719.N0991

open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1330
  (d020031 d020030 d020032)
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0990

noncomputable section

variable {k d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
variable (hn : ∀ i, 0 < sizes i)
variable {I : Type*} [Fintype I]

def d020528 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ) (i : I) : ℝ :=
  w i * _root_.GD.N0232.N0719.N0990.d020524 sizes hdim (q i)

def d020529 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ) : ℝ :=
  ∑ i, _root_.GD.N0232.N0719.N0991.d020528 sizes hdim q w i

omit [Fintype I] in
include hn in
theorem d020530 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : I) : 0 ≤ _root_.GD.N0232.N0719.N0991.d020528 sizes hdim q w i :=
  mul_nonneg (hw i) (_root_.GD.N0232.N0719.N0990.d020525 sizes hdim hn _).le

include hn in
theorem d020531 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) : 0 < _root_.GD.N0232.N0719.N0991.d020529 sizes hdim q w := by
  obtain ⟨j, hj⟩ := hp
  exact Finset.sum_pos' (fun i _ => _root_.GD.N0232.N0719.N0991.d020530 sizes hdim hn q w hw i)
    ⟨j, Finset.mem_univ j, mul_pos hj (_root_.GD.N0232.N0719.N0990.d020525 sizes hdim hn _)⟩

def d020532 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ) (i : I) : ℝ :=
  _root_.GD.N0232.N0719.N0991.d020528 sizes hdim q w i / _root_.GD.N0232.N0719.N0991.d020529 sizes hdim q w

include hn in
theorem d020533 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (i : I) :
    0 ≤ _root_.GD.N0232.N0719.N0991.d020532 sizes hdim q w i :=
  div_nonneg (_root_.GD.N0232.N0719.N0991.d020530 sizes hdim hn q w hw i)
    (_root_.GD.N0232.N0719.N0991.d020531 sizes hdim hn q w hw hp).le

include hn in
theorem d020534 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) :
    ∑ i, _root_.GD.N0232.N0719.N0991.d020532 sizes hdim q w i = 1 := by
  simp only [_root_.GD.N0232.N0719.N0991.d020532, ← Finset.sum_div]
  exact div_self (_root_.GD.N0232.N0719.N0991.d020531 sizes hdim hn q w hw hp).ne'


def d020535 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) : ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k) :=
  ⟨∑ i, ENNReal.ofReal (_root_.GD.N0232.N0719.N0991.d020532 sizes hdim q w i) •
      Measure.dirac (_root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn (q i)), by
    refine ⟨?_⟩
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => _root_.GD.N0232.N0719.N0991.d020533 sizes hdim hn q w hw hp i),
      _root_.GD.N0232.N0719.N0991.d020534 sizes hdim hn q w hw hp, ENNReal.ofReal_one]⟩

theorem d020536 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (f : _root_.GD.N0232.N0719.N0990.d020496 k → ℝ) :
    (∫ p, f p ∂(_root_.GD.N0232.N0719.N0991.d020535 sizes hdim hn q w hw hp : Measure (_root_.GD.N0232.N0719.N0990.d020496 k))) =
      ∑ i, _root_.GD.N0232.N0719.N0991.d020532 sizes hdim q w i * f (_root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn (q i)) := by
  change (∫ p, f p ∂(∑ i, ENNReal.ofReal (_root_.GD.N0232.N0719.N0991.d020532 sizes hdim q w i) •
    Measure.dirac (_root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn (q i)))) = _
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0719.N0991.d020533 sizes hdim hn q w hw hp i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d020537 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (f : _root_.GD.N0232.N0719.N0990.d020496 k → ℝ) :
    (∫ p, f p ∂(_root_.GD.N0232.N0719.N0991.d020535 sizes hdim hn q w hw hp : Measure (_root_.GD.N0232.N0719.N0990.d020496 k))) =
      (_root_.GD.N0232.N0719.N0991.d020529 sizes hdim q w)⁻¹ *
        ∑ i, _root_.GD.N0232.N0719.N0991.d020528 sizes hdim q w i * f (_root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn (q i)) := by
  rw [_root_.GD.N0232.N0719.N0991.d020536, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold _root_.GD.N0232.N0719.N0991.d020532
  ring

omit hn in
def d020538 (ν : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) (x : _root_.GD.N0232.N0720.N1341.d004414 d) : ℝ :=
  (∫ p, _root_.GD.N0232.N0719.N0990.d020511 (d := d) p (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) ∂ν) /
    (∫ p, _root_.GD.N0232.N0719.N0990.d020510 (d := d) p (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) ∂ν)


theorem d020539 (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0719.N0991.d020538 sizes hdim
      (_root_.GD.N0232.N0719.N0991.d020535 sizes hdim hn q w hw hp : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x =
      _root_.GD.N0232.N0720.N1330.d020032 (fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) w x := by
  have hK : _root_.GD.N0232.N0720.N1330.d020030 (fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) w x =
      ∑ i, _root_.GD.N0232.N0719.N0991.d020528 sizes hdim q w i *
        _root_.GD.N0232.N0719.N0990.d020510 (d := d) (_root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn (q i))
          (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) := by
    unfold _root_.GD.N0232.N0720.N1330.d020030
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, _root_.GD.N0232.N0719.N0990.d020526 sizes hdim hn]
    unfold _root_.GD.N0232.N0719.N0991.d020528
    ring
  have hL : _root_.GD.N0232.N0720.N1330.d020031 (fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) w x =
      ∑ i, _root_.GD.N0232.N0719.N0991.d020528 sizes hdim q w i *
        _root_.GD.N0232.N0719.N0990.d020511 (d := d) (_root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn (q i))
          (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) := by
    unfold _root_.GD.N0232.N0720.N1330.d020031
    apply Finset.sum_congr rfl
    intro i _
    change w i * _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) * (q i).1 *
      _root_.GD.N0232.N0720.N1377.d002852 (d + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) x)
        (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) x) = _
    calc
      _ = w i * (_root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) * (q i).1 *
        _root_.GD.N0232.N0720.N1377.d002852 (d + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) x)
          (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q i)) x)) := by ring
      _ = _ := by
        rw [_root_.GD.N0232.N0719.N0990.d020527 sizes hdim hn]
        unfold _root_.GD.N0232.N0719.N0991.d020528
        ring
  unfold _root_.GD.N0232.N0719.N0991.d020538 _root_.GD.N0232.N0720.N1330.d020032
  rw [_root_.GD.N0232.N0719.N0991.d020537, _root_.GD.N0232.N0719.N0991.d020537, hK, hL]
  exact mul_div_mul_left _ _
    (inv_ne_zero (_root_.GD.N0232.N0719.N0991.d020531 sizes hdim hn q w hw hp).ne')

end
end GD.N0232.N0719.N0991

#print axioms _root_.GD.N0232.N0719.N0991.d020539
