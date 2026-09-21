import GD.Module0168
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

set_option warningAsError true
set_option autoImplicit false














namespace GD.N0232.N0720.N1230

noncomputable section

open MeasureTheory
open scoped LineDeriv SchwartzMap

variable {D : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]



def d001992 : List D → 𝓢(D, ℝ) → 𝓢(D, ℝ)
  | [], f => f
  | v :: vs, f => ∂_{v} (d001992 vs f)


def d001993 : List D → 𝓢(D, ℝ) → 𝓢(D, ℝ)
  | [], f => f
  | v :: vs, f => d001993 vs (∂_{v} f)



def d001994 (f g : 𝓢(D, ℝ)) : 𝓢(D, ℝ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f g

@[simp]
theorem d001995 (f g : 𝓢(D, ℝ)) (x : D) :
    _root_.GD.N0232.N0720.N1230.d001994 f g x = f x * g x := rfl

section AdjointIntegral

variable [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ D]
variable {mu : Measure D} [mu.IsAddHaarMeasure]


theorem d001996
    (test error : 𝓢(D, ℝ)) (dirs : List D) :
    (∫ x, test x * _root_.GD.N0232.N0720.N1230.d001992 dirs error x ∂mu) =
      (-1 : ℝ) ^ dirs.length *
        ∫ x, error x * _root_.GD.N0232.N0720.N1230.d001993 dirs test x ∂mu := by
  induction dirs generalizing test with
  | nil => simp [_root_.GD.N0232.N0720.N1230.d001992, _root_.GD.N0232.N0720.N1230.d001993, mul_comm]
  | cons v vs ih =>
      rw [_root_.GD.N0232.N0720.N1230.d001992]
      rw [SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
        test (_root_.GD.N0232.N0720.N1230.d001992 vs error) v]
      rw [ih (∂_{v} test)]
      simp only [List.length_cons, _root_.GD.N0232.N0720.N1230.d001993, pow_succ]
      ring


def d001997
    {J : Type*} [Fintype J]
    (directions : J → List D) (coefficient : J → 𝓢(D, ℝ))
    (error : 𝓢(D, ℝ)) : 𝓢(D, ℝ) :=
  ∑ j, _root_.GD.N0232.N0720.N1230.d001994 (coefficient j) (_root_.GD.N0232.N0720.N1230.d001992 (directions j) error)


def d001998
    {J : Type*} [Fintype J]
    (directions : J → List D) (coefficient : J → 𝓢(D, ℝ))
    (test : 𝓢(D, ℝ)) : 𝓢(D, ℝ) :=
  ∑ j, ((-1 : ℝ) ^ (directions j).length) •
    _root_.GD.N0232.N0720.N1230.d001993 (directions j) (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j))

omit [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ D] in
@[simp]
theorem d001999
    {J : Type*} [Fintype J]
    (directions : J → List D) (coefficient : J → 𝓢(D, ℝ))
    (error : 𝓢(D, ℝ)) (x : D) :
    _root_.GD.N0232.N0720.N1230.d001997 directions coefficient error x =
      ∑ j, coefficient j x * _root_.GD.N0232.N0720.N1230.d001992 (directions j) error x := by
  simp [_root_.GD.N0232.N0720.N1230.d001997]

omit [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ D] in
@[simp]
theorem d002000
    {J : Type*} [Fintype J]
    (directions : J → List D) (coefficient : J → 𝓢(D, ℝ))
    (test : 𝓢(D, ℝ)) (x : D) :
    _root_.GD.N0232.N0720.N1230.d001998 directions coefficient test x =
      ∑ j, (-1 : ℝ) ^ (directions j).length *
        _root_.GD.N0232.N0720.N1230.d001993 (directions j) (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j)) x := by
  simp [_root_.GD.N0232.N0720.N1230.d001998]




theorem d002001
    {J : Type*} [Fintype J]
    (directions : J → List D) (coefficient : J → 𝓢(D, ℝ))
    (test error : 𝓢(D, ℝ)) :
    (∫ x, test x * _root_.GD.N0232.N0720.N1230.d001997 directions coefficient error x ∂mu) =
      ∫ x, error x * _root_.GD.N0232.N0720.N1230.d001998 directions coefficient test x ∂mu := by
  classical
  let leftTerm : J → D → ℝ := fun j x ↦
    test x * (coefficient j x * _root_.GD.N0232.N0720.N1230.d001992 (directions j) error x)
  let rightTerm : J → D → ℝ := fun j x ↦
    error x * (((-1 : ℝ) ^ (directions j).length) *
      _root_.GD.N0232.N0720.N1230.d001993 (directions j) (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j)) x)
  have hLeftIntegrable : ∀ j, Integrable (leftTerm j) mu := by
    intro j
    have h : Integrable
        (_root_.GD.N0232.N0720.N1230.d001994 (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j))
          (_root_.GD.N0232.N0720.N1230.d001992 (directions j) error) : D → ℝ) mu :=
      (_root_.GD.N0232.N0720.N1230.d001994 (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j))
        (_root_.GD.N0232.N0720.N1230.d001992 (directions j) error)).integrable
    refine h.congr ?_
    filter_upwards with x
    simp only [leftTerm, _root_.GD.N0232.N0720.N1230.d001995]
    ring
  have hRightIntegrable : ∀ j, Integrable (rightTerm j) mu := by
    intro j
    have h : Integrable
        (_root_.GD.N0232.N0720.N1230.d001994 error
          (((-1 : ℝ) ^ (directions j).length) •
            _root_.GD.N0232.N0720.N1230.d001993 (directions j)
              (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j))) : D → ℝ) mu :=
      (_root_.GD.N0232.N0720.N1230.d001994 error
        (((-1 : ℝ) ^ (directions j).length) •
          _root_.GD.N0232.N0720.N1230.d001993 (directions j) (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j)))).integrable
    refine h.congr ?_
    filter_upwards with x
    change error x * (((-1 : ℝ) ^ (directions j).length) *
      _root_.GD.N0232.N0720.N1230.d001993 (directions j) (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j)) x) =
        rightTerm j x
    rfl
  calc
    (∫ x, test x * _root_.GD.N0232.N0720.N1230.d001997 directions coefficient error x ∂mu) =
        ∫ x, ∑ j, leftTerm j x ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [_root_.GD.N0232.N0720.N1230.d001999, leftTerm, Finset.mul_sum]
    _ = ∑ j, ∫ x, leftTerm j x ∂mu :=
      integral_finsetSum Finset.univ (fun j _ ↦ hLeftIntegrable j)
    _ = ∑ j, ∫ x, rightTerm j x ∂mu := by
      apply Finset.sum_congr rfl
      intro j _
      have hAdj := _root_.GD.N0232.N0720.N1230.d001996
        (mu := mu) (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j)) error (directions j)
      calc
        (∫ x, leftTerm j x ∂mu) =
            ∫ x, _root_.GD.N0232.N0720.N1230.d001994 test (coefficient j) x *
              _root_.GD.N0232.N0720.N1230.d001992 (directions j) error x ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [leftTerm, _root_.GD.N0232.N0720.N1230.d001995]
          ring
        _ = (-1 : ℝ) ^ (directions j).length *
            ∫ x, error x * _root_.GD.N0232.N0720.N1230.d001993 (directions j)
              (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j)) x ∂mu := hAdj
        _ = ∫ x, rightTerm j x ∂mu := by
          rw [← integral_const_mul
            ((-1 : ℝ) ^ (directions j).length)
            (fun x ↦ error x * _root_.GD.N0232.N0720.N1230.d001993 (directions j)
              (_root_.GD.N0232.N0720.N1230.d001994 test (coefficient j)) x)]
          apply integral_congr_ae
          filter_upwards with x
          simp only [rightTerm]
          ring
    _ = ∫ x, ∑ j, rightTerm j x ∂mu :=
      (integral_finsetSum Finset.univ (fun j _ ↦ hRightIntegrable j)).symm
    _ = ∫ x, error x * _root_.GD.N0232.N0720.N1230.d001998 directions coefficient test x ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [_root_.GD.N0232.N0720.N1230.d002000, rightTerm, Finset.mul_sum]

end AdjointIntegral

end

end GD.N0232.N0720.N1230

#print axioms _root_.GD.N0232.N0720.N1230.d001996
#print axioms _root_.GD.N0232.N0720.N1230.d002001
