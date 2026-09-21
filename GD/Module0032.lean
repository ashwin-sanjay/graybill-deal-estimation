import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

















open MeasureTheory
open scoped BigOperators

namespace GD
namespace N0230
namespace N0657

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]


def d000365 (mu : Measure Omega) (target : Omega -> Real) : Real :=
  ∫ omega, target omega ∂mu


def d000366 (mu : Measure Omega) (weight : Omega -> Real) : Real :=
  ∫ omega, weight omega ∂mu


def d000367
    (mu : Measure Omega) (target weight : Omega -> Real) : Real :=
  (∫ omega, target omega * weight omega ∂mu) /
    _root_.GD.N0230.N0657.d000366 mu weight


def d000368
    (mu : Measure Omega) (target weight : Omega -> Real) : Real :=
  ∫ omega,
      (target omega - _root_.GD.N0230.N0657.d000365 mu target) * weight omega ∂mu


theorem d000369
    (mu : Measure Omega) (target weight : Omega -> Real)
    (hweighted : Integrable (fun omega => target omega * weight omega) mu)
    (hweight : Integrable weight mu) :
    _root_.GD.N0230.N0657.d000368 mu target weight =
      (∫ omega, target omega * weight omega ∂mu) -
        _root_.GD.N0230.N0657.d000365 mu target * _root_.GD.N0230.N0657.d000366 mu weight := by
  unfold _root_.GD.N0230.N0657.d000368 _root_.GD.N0230.N0657.d000365 _root_.GD.N0230.N0657.d000366
  have hconst : Integrable
      (fun omega => (∫ x, target x ∂mu) * weight omega) mu :=
    hweight.const_mul _
  rw [show (fun omega =>
      (target omega - (∫ x, target x ∂mu)) * weight omega) =
        (fun omega => target omega * weight omega -
          (∫ x, target x ∂mu) * weight omega) by
      funext omega
      ring]
  rw [integral_sub hweighted hconst, integral_const_mul]


theorem d000370
    (mu : Measure Omega) (target weight : Omega -> Real)
    (hweighted : Integrable (fun omega => target omega * weight omega) mu)
    (hweight : Integrable weight mu)
    (hmass : _root_.GD.N0230.N0657.d000366 mu weight ≠ 0) :
    _root_.GD.N0230.N0657.d000367 mu target weight - _root_.GD.N0230.N0657.d000365 mu target =
      _root_.GD.N0230.N0657.d000368 mu target weight / _root_.GD.N0230.N0657.d000366 mu weight := by
  rw [_root_.GD.N0230.N0657.d000369 mu target weight hweighted hweight]
  unfold _root_.GD.N0230.N0657.d000367
  field_simp [hmass]



theorem d000371
    (mu : Measure Omega) (target weight : Omega -> Real)
    (hweighted : Integrable (fun omega => target omega * weight omega) mu)
    (hweight : Integrable weight mu)
    (hmass : _root_.GD.N0230.N0657.d000366 mu weight ≠ 0) :
    _root_.GD.N0230.N0657.d000366 mu weight *
        (_root_.GD.N0230.N0657.d000367 mu target weight -
          _root_.GD.N0230.N0657.d000365 mu target) ^ 2 =
      _root_.GD.N0230.N0657.d000368 mu target weight ^ 2 / _root_.GD.N0230.N0657.d000366 mu weight := by
  rw [_root_.GD.N0230.N0657.d000370 mu target weight hweighted hweight hmass]
  field_simp [hmass]



variable {I : Type*} [Fintype I]


def d000372 (w f : I -> Real) : Real :=
  ∑ i, w i * f i


def d000373 (w f g : I -> Real) : Real :=
  _root_.GD.N0230.N0657.d000372 w (fun i => f i * g i) - _root_.GD.N0230.N0657.d000372 w f * _root_.GD.N0230.N0657.d000372 w g


theorem d000374
    (w f g : I -> Real) :
    _root_.GD.N0230.N0657.d000373 w f g =
      ∑ i, w i * (f i - _root_.GD.N0230.N0657.d000372 w f) * g i := by
  classical
  unfold _root_.GD.N0230.N0657.d000373 _root_.GD.N0230.N0657.d000372
  have hmul :
      (∑ i, w i * f i) * (∑ i, w i * g i) =
        ∑ i, w i * (∑ j, w j * f j) * g i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring


theorem d000375
    (w f g : I -> Real) (hsum : ∑ i, w i = 1) :
    _root_.GD.N0230.N0657.d000373 w f g =
      (1 / 2 : Real) *
        ∑ i, ∑ j,
          w i * w j * (f i - f j) * (g i - g j) := by
  classical
  unfold _root_.GD.N0230.N0657.d000373 _root_.GD.N0230.N0657.d000372
  have hexpand :
      (∑ i, ∑ j, w i * w j * (f i - f j) * (g i - g j)) =
        (∑ i, ∑ j, w i * w j * (f i * g i)) -
        (∑ i, ∑ j, w i * w j * (f j * g i)) -
        (∑ i, ∑ j, w i * w j * (f i * g j)) +
        (∑ i, ∑ j, w i * w j * (f j * g j)) := by
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have h1 :
      (∑ i, ∑ j, w i * w j * (f i * g i)) =
        ∑ i, w i * (f i * g i) := by
    calc
      (∑ i, ∑ j, w i * w j * (f i * g i)) =
          ∑ i, (∑ j, w j) * (w i * (f i * g i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ i, w i * (f i * g i) := by simp [hsum]
  have h2 :
      (∑ i, ∑ j, w i * w j * (f i * g j)) =
        (∑ i, w i * f i) * (∑ j, w j * g j) := by
    calc
      (∑ i, ∑ j, w i * w j * (f i * g j)) =
          ∑ i, (w i * f i) * (∑ j, w j * g j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ i, w i * f i) * (∑ j, w j * g j) := by
        rw [Finset.sum_mul]
  have h3 :
      (∑ i, ∑ j, w i * w j * (f j * g i)) =
        (∑ i, w i * f i) * (∑ j, w j * g j) := by
    calc
      (∑ i, ∑ j, w i * w j * (f j * g i)) =
          ∑ i, (∑ j, w j * f j) * (w i * g i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ i, w i * f i) * (∑ j, w j * g j) := by
        rw [Finset.mul_sum]
  have h4 :
      (∑ i, ∑ j, w i * w j * (f j * g j)) =
        ∑ i, w i * (f i * g i) := by
    calc
      (∑ i, ∑ j, w i * w j * (f j * g j)) =
          ∑ j, (∑ i, w i) * (w j * (f j * g j)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ i, w i * (f i * g i) := by simp [hsum]
  rw [hexpand, h1, h2, h3, h4]
  ring


theorem d000376
    (w f : I -> Real) (c : Real) (hsum : ∑ i, w i = 1) :
    _root_.GD.N0230.N0657.d000373 w f (fun _ => c) = 0 := by
  rw [_root_.GD.N0230.N0657.d000375 w f (fun _ => c) hsum]
  simp



theorem d000377
    (w f : I -> Real) (hsum : ∑ i, w i = 1) :
    _root_.GD.N0230.N0657.d000373 w f f =
      (1 / 2 : Real) *
        ∑ i, ∑ j, w i * w j * (f i - f j) ^ 2 := by
  rw [_root_.GD.N0230.N0657.d000375 w f f hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem d000378
    (w f : I -> Real) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    0 ≤ _root_.GD.N0230.N0657.d000373 w f f := by
  rw [_root_.GD.N0230.N0657.d000377 w f hsum]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (hw i) (hw j)) (sq_nonneg _)



theorem d000379
    [Nonempty I] (w f : I -> Real)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    _root_.GD.N0230.N0657.d000373 w f f = 0 ↔
      ∀ i j, f i = f j := by
  classical
  constructor
  · intro hzero i j
    have hpair :
        (∑ a, ∑ b, w a * w b * (f a - f b) ^ 2) = 0 := by
      have hhalf := _root_.GD.N0230.N0657.d000377 w f hsum
      rw [hzero] at hhalf
      linarith
    have houter_nonneg : ∀ a ∈ (Finset.univ : Finset I),
        0 ≤ ∑ b, w a * w b * (f a - f b) ^ 2 := by
      intro a _
      apply Finset.sum_nonneg
      intro b _
      exact mul_nonneg (mul_nonneg (le_of_lt (hw a)) (le_of_lt (hw b)))
        (sq_nonneg _)
    have hrow : (∑ b, w i * w b * (f i - f b) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg houter_nonneg).1 hpair i
        (Finset.mem_univ i)
    have hinner_nonneg : ∀ b ∈ (Finset.univ : Finset I),
        0 ≤ w i * w b * (f i - f b) ^ 2 := by
      intro b _
      exact mul_nonneg (mul_nonneg (le_of_lt (hw i)) (le_of_lt (hw b)))
        (sq_nonneg _)
    have hij : w i * w j * (f i - f j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hinner_nonneg).1 hrow j
        (Finset.mem_univ j)
    have hsquare : (f i - f j) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hij with hwij | hsquare
      · exfalso
        rcases mul_eq_zero.mp hwij with hwi | hwj
        · exact (ne_of_gt (hw i)) hwi
        · exact (ne_of_gt (hw j)) hwj
      · exact hsquare
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro hconst
    obtain i0 := Classical.choice (inferInstance : Nonempty I)
    have hf : f = fun _ => f i0 := by
      funext i
      exact hconst i i0
    rw [hf]
    exact _root_.GD.N0230.N0657.d000376 w (fun _ => f i0) (f i0) hsum




theorem d000380
    [Nonempty I] (w g : I -> Real)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    (∀ f, _root_.GD.N0230.N0657.d000373 w f g = 0) ↔
      ∀ i j, g i = g j := by
  classical
  constructor
  · intro h i j
    let f : I -> Real := fun a => if a = i then 1 / w i else 0
    have hf := h f
    unfold _root_.GD.N0230.N0657.d000373 _root_.GD.N0230.N0657.d000372 at hf
    have hwi : w i ≠ 0 := (hw i).ne'
    simp [f, hwi] at hf
    have hmean : (∑ a, w a * g a) = g i := by linarith
    let f' : I -> Real := fun a => if a = j then 1 / w j else 0
    have hf' := h f'
    have hwj : w j ≠ 0 := (hw j).ne'
    unfold _root_.GD.N0230.N0657.d000373 _root_.GD.N0230.N0657.d000372 at hf'
    simp [f', hwj] at hf'
    linarith
  · intro h f
    obtain i0 := Classical.choice (inferInstance : Nonempty I)
    have hg : g = fun _ => g i0 := by
      funext i
      exact h i i0
    rw [hg]
    exact _root_.GD.N0230.N0657.d000376 w f (g i0) hsum

end

end N0657
end N0230
end GD

#print axioms _root_.GD.N0230.N0657.d000370
#print axioms _root_.GD.N0230.N0657.d000371
#print axioms _root_.GD.N0230.N0657.d000375
#print axioms _root_.GD.N0230.N0657.d000380
