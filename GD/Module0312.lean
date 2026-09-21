import GD.Module0311
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure











open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1373

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1372
open _root_.GD.N0232.N0720.N1371 _root_.GD.N0232.N0720.N1376

noncomputable section

abbrev d004628 := Icc (0 : ℝ) 1
abbrev d004629 := ℝ × _root_.GD.N0232.N0720.N1373.d004628

def d004630 (q : _root_.GD.N0232.N0720.N1372.d004518) : _root_.GD.N0232.N0720.N1373.d004629 :=
  (_root_.GD.N0232.N0720.N1371.d004614 q, ⟨q.2.1, q.2.2.1.le, q.2.2.2.le⟩)

def d004631 (p : _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  _root_.GD.N0232.N0720.N1376.d002894 p.1 p.2.1 (x 0) (x 2) (x 1 ^ 2 / 2) (x 3 ^ 2 / 2)

def d004632 (p : _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  _root_.GD.N0232.N0720.N1376.d002895 p.1 p.2.1 (x 0) (x 2) (x 1 ^ 2 / 2) (x 3 ^ 2 / 2)

variable {I : Type*} [Fintype I]

def d004633 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (i : I) : ℝ :=
  w i * _root_.GD.N0232.N0720.N1371.d004615 (q i)

def d004634 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) : ℝ := ∑ i, _root_.GD.N0232.N0720.N1373.d004633 q w i

theorem d004635 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : I) : 0 ≤ _root_.GD.N0232.N0720.N1373.d004633 q w i :=
  mul_nonneg (hw i) (_root_.GD.N0232.N0720.N1371.d004618 _).le

theorem d004636 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) : 0 < _root_.GD.N0232.N0720.N1373.d004634 q w := by
  obtain ⟨j, hj⟩ := hp
  exact Finset.sum_pos' (fun i _ ↦ _root_.GD.N0232.N0720.N1373.d004635 q w hw i)
    ⟨j, Finset.mem_univ j, mul_pos hj (_root_.GD.N0232.N0720.N1371.d004618 _)⟩

def d004637 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (i : I) : ℝ :=
  _root_.GD.N0232.N0720.N1373.d004633 q w i / _root_.GD.N0232.N0720.N1373.d004634 q w

theorem d004638 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (i : I) :
    0 ≤ _root_.GD.N0232.N0720.N1373.d004637 q w i :=
  div_nonneg (_root_.GD.N0232.N0720.N1373.d004635 q w hw i) (_root_.GD.N0232.N0720.N1373.d004636 q w hw hp).le

theorem d004639 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) : ∑ i, _root_.GD.N0232.N0720.N1373.d004637 q w i = 1 := by
  simp only [_root_.GD.N0232.N0720.N1373.d004637, ← Finset.sum_div]
  exact div_self (_root_.GD.N0232.N0720.N1373.d004636 q w hw hp).ne'



def d004640 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) : ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629 :=
  ⟨∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1373.d004637 q w i) • Measure.dirac (_root_.GD.N0232.N0720.N1373.d004630 (q i)), by
    refine ⟨?_⟩
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ _root_.GD.N0232.N0720.N1373.d004638 q w hw hp i),
      _root_.GD.N0232.N0720.N1373.d004639 q w hw hp, ENNReal.ofReal_one]⟩

theorem d004641 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (f : _root_.GD.N0232.N0720.N1373.d004629 → ℝ) :
    (∫ p, f p ∂(_root_.GD.N0232.N0720.N1373.d004640 q w hw hp : Measure _root_.GD.N0232.N0720.N1373.d004629)) =
      ∑ i, _root_.GD.N0232.N0720.N1373.d004637 q w i * f (_root_.GD.N0232.N0720.N1373.d004630 (q i)) := by
  change (∫ p, f p ∂(∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1373.d004637 q w i) •
    Measure.dirac (_root_.GD.N0232.N0720.N1373.d004630 (q i)))) = _
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1373.d004638 q w hw hp i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d004642 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (f : _root_.GD.N0232.N0720.N1373.d004629 → ℝ) :
    (∫ p, f p ∂(_root_.GD.N0232.N0720.N1373.d004640 q w hw hp : Measure _root_.GD.N0232.N0720.N1373.d004629)) =
      (_root_.GD.N0232.N0720.N1373.d004634 q w)⁻¹ * ∑ i, _root_.GD.N0232.N0720.N1373.d004633 q w i * f (_root_.GD.N0232.N0720.N1373.d004630 (q i)) := by
  rw [_root_.GD.N0232.N0720.N1373.d004641, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold _root_.GD.N0232.N0720.N1373.d004637
  ring

def d004643 (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  ∫ p, _root_.GD.N0232.N0720.N1373.d004631 p x ∂ν

def d004644 (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  ∫ p, _root_.GD.N0232.N0720.N1373.d004632 p x ∂ν

def d004645 (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  _root_.GD.N0232.N0720.N1373.d004644 ν x / _root_.GD.N0232.N0720.N1373.d004643 ν x

def d004646 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  (∑ i, _root_.GD.N0232.N0720.N1373.d004633 q w i * _root_.GD.N0232.N0720.N1373.d004632 (_root_.GD.N0232.N0720.N1373.d004630 (q i)) x) /
    (∑ i, _root_.GD.N0232.N0720.N1373.d004633 q w i * _root_.GD.N0232.N0720.N1373.d004631 (_root_.GD.N0232.N0720.N1373.d004630 (q i)) x)

theorem d004647 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1373.d004645 (_root_.GD.N0232.N0720.N1373.d004640 q w hw hp : Measure _root_.GD.N0232.N0720.N1373.d004629) x =
      _root_.GD.N0232.N0720.N1373.d004646 q w x := by
  unfold _root_.GD.N0232.N0720.N1373.d004645 _root_.GD.N0232.N0720.N1373.d004644 _root_.GD.N0232.N0720.N1373.d004643
  rw [_root_.GD.N0232.N0720.N1373.d004642, _root_.GD.N0232.N0720.N1373.d004642]
  exact mul_div_mul_left _ _ (inv_ne_zero (_root_.GD.N0232.N0720.N1373.d004636 q w hw hp).ne')

theorem d004648 (p : _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1393.d004492)
    {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0232.N0720.N1373.d004631 p (c • x) = (c ^ 6)⁻¹ * _root_.GD.N0232.N0720.N1373.d004631 p x := by
  simp only [_root_.GD.N0232.N0720.N1373.d004631, PiLp.smul_apply, smul_eq_mul, mul_pow]
  rw [show c ^ 2 * x 1 ^ 2 / 2 = c ^ 2 * (x 1 ^ 2 / 2) by ring,
    show c ^ 2 * x 3 ^ 2 / 2 = c ^ 2 * (x 3 ^ 2 / 2) by ring]
  exact _root_.GD.N0232.N0720.N1376.d002904 _ _ _ _ _ _ hc

theorem d004649 (p : _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1393.d004492)
    {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0232.N0720.N1373.d004632 p (c • x) = (c ^ 5)⁻¹ * _root_.GD.N0232.N0720.N1373.d004632 p x := by
  simp only [_root_.GD.N0232.N0720.N1373.d004632, PiLp.smul_apply, smul_eq_mul, mul_pow]
  rw [show c ^ 2 * x 1 ^ 2 / 2 = c ^ 2 * (x 1 ^ 2 / 2) by ring,
    show c ^ 2 * x 3 ^ 2 / 2 = c ^ 2 * (x 3 ^ 2 / 2) by ring]
  exact _root_.GD.N0232.N0720.N1376.d002905 _ _ _ _ _ _ hc

theorem d004650 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) :
    _root_.GD.N0238.N0753.d004397
      (_root_.GD.N0232.N0720.N1373.d004646 q w) := by
  intro c hc x
  have h5 : (c ^ 5)⁻¹ = (c ^ 6)⁻¹ * c := by
    field_simp [hc.ne'] <;> ring
  have hL : (∑ i, _root_.GD.N0232.N0720.N1373.d004633 q w i * _root_.GD.N0232.N0720.N1373.d004632 (_root_.GD.N0232.N0720.N1373.d004630 (q i)) (c • x)) =
      (c ^ 5)⁻¹ * ∑ i, _root_.GD.N0232.N0720.N1373.d004633 q w i * _root_.GD.N0232.N0720.N1373.d004632 (_root_.GD.N0232.N0720.N1373.d004630 (q i)) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.GD.N0232.N0720.N1373.d004649 _ _ hc]
    ring
  have hK : (∑ i, _root_.GD.N0232.N0720.N1373.d004633 q w i * _root_.GD.N0232.N0720.N1373.d004631 (_root_.GD.N0232.N0720.N1373.d004630 (q i)) (c • x)) =
      (c ^ 6)⁻¹ * ∑ i, _root_.GD.N0232.N0720.N1373.d004633 q w i * _root_.GD.N0232.N0720.N1373.d004631 (_root_.GD.N0232.N0720.N1373.d004630 (q i)) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.GD.N0232.N0720.N1373.d004648 _ _ hc]
    ring
  unfold _root_.GD.N0232.N0720.N1373.d004646
  rw [hL, hK, h5, mul_assoc,
    mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero 6 hc.ne'))]
  simp only [smul_eq_mul, mul_div_assoc]

end

end GD.N0232.N0720.N1373

#print axioms _root_.GD.N0232.N0720.N1373.d004639
#print axioms _root_.GD.N0232.N0720.N1373.d004647
#print axioms _root_.GD.N0232.N0720.N1373.d004650
