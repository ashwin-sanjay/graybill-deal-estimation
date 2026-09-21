import Mathlib


















open MeasureTheory
open Set

namespace GD
namespace N0232
namespace N0720
namespace N1422

noncomputable section





def d002977 (leftDegrees rightDegrees observationFraction parameter : ℝ) : ℝ :=
  leftDegrees * (1 - observationFraction) / (1 - parameter) +
    rightDegrees * observationFraction / parameter


def d002978 (leftDegrees rightDegrees : ℝ) : ℝ :=
  rightDegrees / (leftDegrees + rightDegrees)



theorem d002979
    {leftDegrees rightDegrees observationFraction parameter : ℝ}
    (hparameterZero : parameter ≠ 0)
    (hparameterOne : parameter ≠ 1)
    (htotal : leftDegrees + rightDegrees ≠ 0) :
    _root_.GD.N0232.N0720.N1422.d002977 leftDegrees rightDegrees observationFraction parameter -
        (leftDegrees + rightDegrees) =
      (leftDegrees + rightDegrees) *
          (parameter - observationFraction) *
          (parameter - _root_.GD.N0232.N0720.N1422.d002978 leftDegrees rightDegrees) /
        (parameter * (1 - parameter)) := by
  unfold _root_.GD.N0232.N0720.N1422.d002977 _root_.GD.N0232.N0720.N1422.d002978
  field_simp [hparameterZero, hparameterOne, htotal]
  ring


theorem d002980
    {leftDegrees rightDegrees observationFraction : ℝ}
    (hobservationZero : observationFraction ≠ 0)
    (hobservationOne : observationFraction ≠ 1) :
    _root_.GD.N0232.N0720.N1422.d002977 leftDegrees rightDegrees observationFraction
        observationFraction = leftDegrees + rightDegrees := by
  unfold _root_.GD.N0232.N0720.N1422.d002977
  field_simp [hobservationZero, hobservationOne]


theorem d002981
    {leftDegrees rightDegrees : ℝ}
    (hleft : 0 < leftDegrees) (hright : 0 < rightDegrees) :
    _root_.GD.N0232.N0720.N1422.d002978 leftDegrees rightDegrees ∈ Ioo (0 : ℝ) 1 := by
  unfold _root_.GD.N0232.N0720.N1422.d002978
  constructor
  · positivity
  · rw [div_lt_one (add_pos hleft hright)]
    linarith


theorem d002982
    {leftDegrees rightDegrees observationFraction : ℝ}
    (hleft : 0 < leftDegrees) (hright : 0 < rightDegrees) :
    _root_.GD.N0232.N0720.N1422.d002977 leftDegrees rightDegrees observationFraction
        (_root_.GD.N0232.N0720.N1422.d002978 leftDegrees rightDegrees) =
      leftDegrees + rightDegrees := by
  have hcritical := _root_.GD.N0232.N0720.N1422.d002981 hleft hright
  have hfactor := _root_.GD.N0232.N0720.N1422.d002979
    (observationFraction := observationFraction)
    (parameter := _root_.GD.N0232.N0720.N1422.d002978 leftDegrees rightDegrees)
    hcritical.1.ne' hcritical.2.ne
    (add_pos hleft hright).ne'
  rw [sub_self, mul_zero, zero_div] at hfactor
  linarith




theorem d002983
    {leftDegrees rightDegrees observationFraction parameter : ℝ}
    (hleft : 0 < leftDegrees) (hright : 0 < rightDegrees)
    (hparameterZero : 0 < parameter) (hparameterOne : parameter < 1)
    (hlower : observationFraction < parameter)
    (hupper : parameter < _root_.GD.N0232.N0720.N1422.d002978 leftDegrees rightDegrees) :
    _root_.GD.N0232.N0720.N1422.d002977 leftDegrees rightDegrees observationFraction parameter <
      leftDegrees + rightDegrees := by
  rw [← sub_neg]
  rw [_root_.GD.N0232.N0720.N1422.d002979 hparameterZero.ne'
    hparameterOne.ne (add_pos hleft hright).ne']
  have hdenominator : 0 < parameter * (1 - parameter) := by positivity
  have hfirst : 0 < parameter - observationFraction := sub_pos.mpr hlower
  have hsecond : parameter - _root_.GD.N0232.N0720.N1422.d002978 leftDegrees rightDegrees < 0 :=
    sub_neg.mpr hupper
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg
    (mul_pos (add_pos hleft hright) hfirst) hsecond) hdenominator


theorem d002984
    {leftDegrees rightDegrees observationFraction parameter : ℝ}
    (hleft : 0 < leftDegrees) (hright : 0 < rightDegrees)
    (hparameterZero : 0 < parameter) (hparameterOne : parameter < 1)
    (hlower : _root_.GD.N0232.N0720.N1422.d002978 leftDegrees rightDegrees < parameter)
    (hupper : parameter < observationFraction) :
    _root_.GD.N0232.N0720.N1422.d002977 leftDegrees rightDegrees observationFraction parameter <
      leftDegrees + rightDegrees := by
  rw [← sub_neg]
  rw [_root_.GD.N0232.N0720.N1422.d002979 hparameterZero.ne'
    hparameterOne.ne (add_pos hleft hright).ne']
  have hdenominator : 0 < parameter * (1 - parameter) := by positivity
  have hfirst : parameter - observationFraction < 0 := sub_neg.mpr hupper
  have hsecond : 0 < parameter - _root_.GD.N0232.N0720.N1422.d002978 leftDegrees rightDegrees :=
    sub_pos.mpr hlower
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (add_pos hleft hright) hfirst) hsecond)
    hdenominator





def d002985
    (leftShape rightShape totalShape leftDegrees rightDegrees
      observationFraction disagreement : ℝ)
    (parameter : ℝ) : ℝ :=
  parameter ^ (-rightShape) * (1 - parameter) ^ (-leftShape) *
    (disagreement +
      _root_.GD.N0232.N0720.N1422.d002977 leftDegrees rightDegrees observationFraction parameter) ^
        (-totalShape)


def d002986 (prior : Measure ℝ) (likelihood : ℝ → ℝ) : ℝ :=
  ∫ parameter, likelihood parameter ∂prior


def d002987
    (prior : Measure ℝ) (likelihood : ℝ → ℝ) : ℝ :=
  ∫ parameter, parameter * likelihood parameter ∂prior


def d002988 (prior : Measure ℝ) (likelihood : ℝ → ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1422.d002987 prior likelihood / _root_.GD.N0232.N0720.N1422.d002986 prior likelihood


def d002989
    (prior : Measure ℝ) (likelihood : ℝ → ℝ) (action : ℝ) : ℝ :=
  ∫ parameter, (parameter - action) * likelihood parameter ∂prior


theorem d002990
    (prior : Measure ℝ) (likelihood : ℝ → ℝ) (action : ℝ)
    (hlikelihood : Integrable likelihood prior)
    (hmoment : Integrable (fun parameter ↦ parameter * likelihood parameter) prior) :
    _root_.GD.N0232.N0720.N1422.d002989 prior likelihood action =
      _root_.GD.N0232.N0720.N1422.d002987 prior likelihood -
        action * _root_.GD.N0232.N0720.N1422.d002986 prior likelihood := by
  unfold _root_.GD.N0232.N0720.N1422.d002989 _root_.GD.N0232.N0720.N1422.d002987 _root_.GD.N0232.N0720.N1422.d002986
  have hscaled :
      Integrable (fun parameter ↦ action * likelihood parameter) prior :=
    hlikelihood.const_mul action
  have hpoint :
      (fun parameter ↦ (parameter - action) * likelihood parameter) =
        fun parameter ↦ parameter * likelihood parameter -
          action * likelihood parameter := by
    funext parameter
    ring
  rw [hpoint, integral_sub hmoment hscaled, integral_const_mul]



theorem d002991
    (prior : Measure ℝ) (likelihood : ℝ → ℝ) (action : ℝ)
    (hlikelihood : Integrable likelihood prior)
    (hmoment : Integrable (fun parameter ↦ parameter * likelihood parameter) prior)
    (hmass : _root_.GD.N0232.N0720.N1422.d002986 prior likelihood ≠ 0) :
    _root_.GD.N0232.N0720.N1422.d002988 prior likelihood = action ↔
      _root_.GD.N0232.N0720.N1422.d002989 prior likelihood action = 0 := by
  rw [_root_.GD.N0232.N0720.N1422.d002990 prior likelihood action hlikelihood hmoment]
  unfold _root_.GD.N0232.N0720.N1422.d002988
  constructor
  · intro h
    have hmul :
        _root_.GD.N0232.N0720.N1422.d002987 prior likelihood =
          action * _root_.GD.N0232.N0720.N1422.d002986 prior likelihood := by
      exact (div_eq_iff hmass).mp h
    linarith
  · intro h
    apply (div_eq_iff hmass).2
    linarith




def d002992
    {Observation : Type*}
    (prior : Measure ℝ)
    (likelihood : Observation → ℝ → ℝ)
    (action : Observation → ℝ) : Prop :=
  prior (Ioo (0 : ℝ) 1)ᶜ = 0 ∧
    ∀ observation,
      Integrable (likelihood observation) prior ∧
      Integrable
        (fun parameter ↦ parameter * likelihood observation parameter) prior ∧
      _root_.GD.N0232.N0720.N1422.d002986 prior (likelihood observation) ≠ 0 ∧
      _root_.GD.N0232.N0720.N1422.d002989 prior (likelihood observation)
        (action observation) = 0




theorem d002993
    {Observation : Type*}
    (prior : Measure ℝ)
    (likelihood : Observation → ℝ → ℝ)
    (action : Observation → ℝ)
    (hsupport : _root_.GD.N0232.N0720.N1422.d002992 prior likelihood action) :
    ∀ observation,
      _root_.GD.N0232.N0720.N1422.d002988 prior (likelihood observation) = action observation := by
  intro observation
  rcases hsupport.2 observation with
    ⟨hlikelihood, hmoment, hmass, hnormal⟩
  exact (_root_.GD.N0232.N0720.N1422.d002991
    prior (likelihood observation) (action observation)
    hlikelihood hmoment hmass).2 hnormal




def d002994
    (prior : Measure ℝ)
    (leftShape rightShape totalShape leftDegrees rightDegrees : ℝ) : Prop :=
  _root_.GD.N0232.N0720.N1422.d002992 prior
    (fun observation : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1422.d002985 leftShape rightShape totalShape
        leftDegrees rightDegrees observation.1 observation.2)
    (fun observation : ℝ × ℝ ↦ observation.1)



theorem d002995
    (prior : Measure ℝ)
    (leftShape rightShape totalShape leftDegrees rightDegrees : ℝ)
    (hsupport : _root_.GD.N0232.N0720.N1422.d002994 prior leftShape rightShape totalShape
      leftDegrees rightDegrees) :
    ∀ observation : ℝ × ℝ,
      _root_.GD.N0232.N0720.N1422.d002988 prior
          (_root_.GD.N0232.N0720.N1422.d002985 leftShape rightShape totalShape
            leftDegrees rightDegrees observation.1 observation.2) =
        observation.1 := by
  exact _root_.GD.N0232.N0720.N1422.d002993 prior _ _ hsupport

end

end N1422
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1422.d002979
#print axioms _root_.GD.N0232.N0720.N1422.d002982
#print axioms _root_.GD.N0232.N0720.N1422.d002990
#print axioms _root_.GD.N0232.N0720.N1422.d002991
#print axioms _root_.GD.N0232.N0720.N1422.d002993
