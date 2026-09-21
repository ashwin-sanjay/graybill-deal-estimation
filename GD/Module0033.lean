import GD.Module0019
import GD.Module0032




























open scoped BigOperators

namespace GD
namespace N0230
namespace N0619

noncomputable section

set_option linter.unusedSectionVars false

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0657

variable {Omega iota : Type*} [MeasurableSpace Omega]
variable [Fintype iota] [DecidableEq iota]



def d000381 (weight : iota -> Real) : Option iota -> Real
  | none => 1
  | some i => weight i


def d000382
    (likelihood : iota -> Omega -> Real) (omega : Omega) :
    Option iota -> Real
  | none => 1
  | some i => likelihood i omega


def d000383 (center : iota -> Real) : Option iota -> Real
  | none => 0
  | some i => center i


def d000384
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (omega : Omega) (s : Option iota) : Real :=
  _root_.GD.N0230.N0619.d000381 weight s * _root_.GD.N0230.N0619.d000382 likelihood omega s /
    _root_.GD.N0230.N0617.d000163 weight likelihood omega


def d000385
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real) (omega : Omega) : Real :=
  ∑ s : Option iota,
    _root_.GD.N0230.N0619.d000384 weight likelihood omega s * _root_.GD.N0230.N0619.d000383 center s


def d000386
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real) (omega : Omega) : Real :=
  ∑ s : Option iota,
    _root_.GD.N0230.N0619.d000384 weight likelihood omega s *
      (_root_.GD.N0230.N0619.d000383 center s -
        _root_.GD.N0230.N0617.d000166 weight likelihood center omega) ^ 2


def d000387
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real) (omega : Omega) : Real :=
  ∑ s : Option iota,
    ∑ t : Option iota,
      _root_.GD.N0230.N0619.d000384 weight likelihood omega s *
        _root_.GD.N0230.N0619.d000384 weight likelihood omega t *
          (_root_.GD.N0230.N0619.d000383 center s - _root_.GD.N0230.N0619.d000383 center t) ^ 2


def d000388
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real) (omega : Omega) (decision : Real) : Real :=
  ∑ truth : Option iota,
    _root_.GD.N0230.N0619.d000384 weight likelihood omega truth *
      (decision - _root_.GD.N0230.N0619.d000383 center truth) ^ 2



def d000389
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real) (omega : Omega) (decision : Real) : Real :=
  (_root_.GD.N0230.N0617.d000163 weight likelihood omega * decision -
      _root_.GD.N0230.N0617.d000164 weight likelihood center omega) ^ 2 /
    _root_.GD.N0230.N0617.d000163 weight likelihood omega



def d000390
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (omega : Omega) (observable : Option iota -> Option iota -> Real) : Real :=
  ∑ truth : Option iota,
    ∑ replica : Option iota,
      _root_.GD.N0230.N0619.d000384 weight likelihood omega truth *
        _root_.GD.N0230.N0619.d000384 weight likelihood omega replica *
          observable truth replica


theorem d000391
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (omega : Omega) :
    (∑ s : Option iota,
      _root_.GD.N0230.N0619.d000381 weight s * _root_.GD.N0230.N0619.d000382 likelihood omega s) =
      _root_.GD.N0230.N0617.d000163 weight likelihood omega := by
  rw [Fintype.sum_option]
  simp [_root_.GD.N0230.N0619.d000381, _root_.GD.N0230.N0619.d000382, _root_.GD.N0230.N0617.d000163]



theorem d000392
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (omega : Omega)
    (hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0) :
    (∑ s : Option iota,
      _root_.GD.N0230.N0619.d000384 weight likelihood omega s) = 1 := by
  unfold _root_.GD.N0230.N0619.d000384
  rw [<- Finset.sum_div, _root_.GD.N0230.N0619.d000391]
  exact div_self hmass



theorem d000393
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (hweight : forall i, 0 <= weight i)
    (hlikelihood : forall i omega, 0 <= likelihood i omega)
    (omega : Omega) (s : Option iota) :
    0 <= _root_.GD.N0230.N0619.d000384 weight likelihood omega s := by
  have hmass : 0 <= _root_.GD.N0230.N0617.d000163 weight likelihood omega :=
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).le
  cases s with
  | none =>
      simpa [_root_.GD.N0230.N0619.d000384, _root_.GD.N0230.N0619.d000381, _root_.GD.N0230.N0619.d000382] using
        (div_nonneg (by norm_num : (0 : Real) <= 1) hmass)
  | some i =>
      simpa [_root_.GD.N0230.N0619.d000384, _root_.GD.N0230.N0619.d000381, _root_.GD.N0230.N0619.d000382] using
        (div_nonneg (mul_nonneg (hweight i) (hlikelihood i omega)) hmass)



theorem d000394
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real) (omega : Omega) :
    _root_.GD.N0230.N0619.d000385 weight likelihood center omega =
      _root_.GD.N0230.N0617.d000166 weight likelihood center omega := by
  unfold _root_.GD.N0230.N0619.d000385 _root_.GD.N0230.N0619.d000384
  rw [Fintype.sum_option]
  simp only [_root_.GD.N0230.N0619.d000381, _root_.GD.N0230.N0619.d000382, _root_.GD.N0230.N0619.d000383, mul_zero,
    zero_add]
  unfold _root_.GD.N0230.N0617.d000166 _root_.GD.N0230.N0617.d000164
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring



theorem d000395
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real) (omega : Omega) (decision : Real)
    (hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0) :
    _root_.GD.N0230.N0619.d000389 weight likelihood center omega decision =
      _root_.GD.N0230.N0617.d000163 weight likelihood omega *
        (decision - _root_.GD.N0230.N0617.d000166 weight likelihood center omega) ^ 2 := by
  unfold _root_.GD.N0230.N0619.d000389 _root_.GD.N0230.N0617.d000166
  field_simp [hmass]




theorem d000396
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (omega : Omega) (observable : Option iota -> Option iota -> Real) :
    _root_.GD.N0230.N0619.d000390 weight likelihood omega observable =
      _root_.GD.N0230.N0619.d000390 weight likelihood omega
        (fun truth replica => observable replica truth) := by
  unfold _root_.GD.N0230.N0619.d000390
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro truth htruth
  apply Finset.sum_congr rfl
  intro replica hreplica
  ring



private theorem d000397
    {state : Type*} [Fintype state]
    (probability coordinate : state -> Real) (mean : Real)
    (hprobability : (∑ s, probability s) = 1)
    (hmean : (∑ s, probability s * coordinate s) = mean) :
    (∑ s, probability s * (coordinate s - mean) ^ 2) =
      _root_.GD.N0230.N0657.d000373 probability coordinate coordinate := by
  have hexpand :
      (∑ s, probability s * (coordinate s - mean) ^ 2) =
        (∑ s, probability s * coordinate s ^ 2) -
          2 * mean * (∑ s, probability s * coordinate s) +
            mean ^ 2 * (∑ s, probability s) := by
    calc
      (∑ s, probability s * (coordinate s - mean) ^ 2) =
          ∑ s, (
            probability s * coordinate s ^ 2 -
              2 * mean * (probability s * coordinate s) +
                mean ^ 2 * probability s) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = (∑ s, probability s * coordinate s ^ 2) -
          (∑ s, 2 * mean * (probability s * coordinate s)) +
            (∑ s, mean ^ 2 * probability s) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ s, probability s * coordinate s ^ 2) -
          2 * mean * (∑ s, probability s * coordinate s) +
            mean ^ 2 * (∑ s, probability s) := by
        rw [Finset.mul_sum, Finset.mul_sum]
  rw [hexpand, hprobability, hmean]
  unfold _root_.GD.N0230.N0657.d000373 _root_.GD.N0230.N0657.d000372
  have hsquare :
      (∑ s, probability s * coordinate s ^ 2) =
        ∑ s, probability s * (coordinate s * coordinate s) := by
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [hsquare]
  rw [hmean]
  ring


theorem d000398
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real)
    (hweight : forall i, 0 <= weight i)
    (hlikelihood : forall i omega, 0 <= likelihood i omega)
    (omega : Omega) :
    _root_.GD.N0230.N0619.d000386 weight likelihood center omega =
      _root_.GD.N0230.N0657.d000373
        (_root_.GD.N0230.N0619.d000384 weight likelihood omega)
        (_root_.GD.N0230.N0619.d000383 center) (_root_.GD.N0230.N0619.d000383 center) := by
  unfold _root_.GD.N0230.N0619.d000386
  apply _root_.GD.N0230.N0619.d000397
  . exact _root_.GD.N0230.N0619.d000392 weight likelihood omega
      (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
  . exact _root_.GD.N0230.N0619.d000394
      weight likelihood center omega



theorem d000399
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real)
    (hweight : forall i, 0 <= weight i)
    (hlikelihood : forall i omega, 0 <= likelihood i omega)
    (omega : Omega) :
    _root_.GD.N0230.N0619.d000386 weight likelihood center omega =
      (1 / 2 : Real) *
        _root_.GD.N0230.N0619.d000387 weight likelihood center omega := by
  rw [_root_.GD.N0230.N0619.d000398
    weight likelihood center hweight hlikelihood omega]
  rw [_root_.GD.N0230.N0657.d000377
    (_root_.GD.N0230.N0619.d000384 weight likelihood omega)
    (_root_.GD.N0230.N0619.d000383 center)
    (_root_.GD.N0230.N0619.d000392 weight likelihood omega
      (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne')]
  rfl



private theorem d000400
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real)
    (hweight : forall i, 0 <= weight i)
    (hlikelihood : forall i omega, 0 <= likelihood i omega)
    (omega : Omega) :
    _root_.GD.N0230.N0617.d000163 weight likelihood omega *
        _root_.GD.N0230.N0619.d000386 weight likelihood center omega =
      _root_.GD.N0230.N0617.d000166 weight likelihood center omega ^ 2 +
        ∑ i, weight i * likelihood i omega *
          (_root_.GD.N0230.N0617.d000166 weight likelihood center omega - center i) ^ 2 := by
  have hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
  unfold _root_.GD.N0230.N0619.d000386 _root_.GD.N0230.N0619.d000384
  rw [Fintype.sum_option]
  simp only [_root_.GD.N0230.N0619.d000381, _root_.GD.N0230.N0619.d000382, _root_.GD.N0230.N0619.d000383,
    zero_sub, neg_sq]
  have hphysical :
      (∑ i,
        weight i * likelihood i omega /
            _root_.GD.N0230.N0617.d000163 weight likelihood omega *
          (center i - _root_.GD.N0230.N0617.d000166 weight likelihood center omega) ^ 2) =
        (∑ i,
          weight i * likelihood i omega *
            (center i - _root_.GD.N0230.N0617.d000166 weight likelihood center omega) ^ 2) /
          _root_.GD.N0230.N0617.d000163 weight likelihood omega := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hphysical]
  field_simp [hmass]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring



theorem d000401
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real)
    (hweight : forall i, 0 <= weight i)
    (hlikelihood : forall i omega, 0 <= likelihood i omega)
    (omega : Omega) :
    _root_.GD.N0230.N0617.d000165 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000167 weight likelihood center omega =
      _root_.GD.N0230.N0617.d000163 weight likelihood omega *
        _root_.GD.N0230.N0619.d000386 weight likelihood center omega := by
  have hsquare := _root_.GD.N0230.N0617.d000171
    weight likelihood center hweight hlikelihood
      (_root_.GD.N0230.N0617.d000166 weight likelihood center omega) omega
  have hmmse := _root_.GD.N0230.N0619.d000400
    weight likelihood center hweight hlikelihood omega
  rw [hmmse]
  simpa [sub_self] using hsquare.symm



private theorem d000402
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real)
    (hweight : forall i, 0 <= weight i)
    (hlikelihood : forall i omega, 0 <= likelihood i omega)
    (omega : Omega) (decision : Real) :
    _root_.GD.N0230.N0617.d000163 weight likelihood omega *
        _root_.GD.N0230.N0619.d000388 weight likelihood center omega decision =
      decision ^ 2 +
        ∑ i, weight i * likelihood i omega *
          (decision - center i) ^ 2 := by
  have hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
  unfold _root_.GD.N0230.N0619.d000388 _root_.GD.N0230.N0619.d000384
  rw [Fintype.sum_option]
  simp only [_root_.GD.N0230.N0619.d000381, _root_.GD.N0230.N0619.d000382, _root_.GD.N0230.N0619.d000383, sub_zero]
  have hphysical :
      (∑ i,
        weight i * likelihood i omega /
            _root_.GD.N0230.N0617.d000163 weight likelihood omega *
          (decision - center i) ^ 2) =
        (∑ i,
          weight i * likelihood i omega * (decision - center i) ^ 2) /
          _root_.GD.N0230.N0617.d000163 weight likelihood omega := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hphysical]
  field_simp [hmass]




theorem d000403
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real)
    (hweight : forall i, 0 <= weight i)
    (hlikelihood : forall i omega, 0 <= likelihood i omega)
    (omega : Omega) (decision : Real) :
    _root_.GD.N0230.N0619.d000388 weight likelihood center omega decision =
      (decision - _root_.GD.N0230.N0617.d000166 weight likelihood center omega) ^ 2 +
        _root_.GD.N0230.N0619.d000386 weight likelihood center omega := by
  have hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
  have hloss := _root_.GD.N0230.N0619.d000402
    weight likelihood center hweight hlikelihood omega decision
  have hsquare := _root_.GD.N0230.N0617.d000171
    weight likelihood center hweight hlikelihood decision omega
  have hmmse := _root_.GD.N0230.N0619.d000401
    weight likelihood center hweight hlikelihood omega
  apply mul_left_cancel₀ hmass
  calc
    _root_.GD.N0230.N0617.d000163 weight likelihood omega *
        _root_.GD.N0230.N0619.d000388 weight likelihood center omega decision =
      decision ^ 2 +
        ∑ i, weight i * likelihood i omega *
          (decision - center i) ^ 2 := hloss
    _ = _root_.GD.N0230.N0617.d000163 weight likelihood omega *
          (decision - _root_.GD.N0230.N0617.d000166 weight likelihood center omega) ^ 2 +
        (_root_.GD.N0230.N0617.d000165 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000167 weight likelihood center omega) := by
      simpa only [add_sub_assoc] using hsquare
    _ = _root_.GD.N0230.N0617.d000163 weight likelihood omega *
          ((decision - _root_.GD.N0230.N0617.d000166 weight likelihood center omega) ^ 2 +
            _root_.GD.N0230.N0619.d000386 weight likelihood center omega) := by
      rw [hmmse]
      ring



theorem d000404
    (weight : iota -> Real) (likelihood : iota -> Omega -> Real)
    (center : iota -> Real)
    (hweight : forall i, 0 <= weight i)
    (hlikelihood : forall i omega, 0 <= likelihood i omega)
    (omega : Omega) :
    _root_.GD.N0230.N0617.d000165 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000167 weight likelihood center omega =
      _root_.GD.N0230.N0617.d000163 weight likelihood omega * (1 / 2 : Real) *
        _root_.GD.N0230.N0619.d000387 weight likelihood center omega := by
  rw [_root_.GD.N0230.N0619.d000401
    weight likelihood center hweight hlikelihood omega]
  rw [_root_.GD.N0230.N0619.d000399
    weight likelihood center hweight hlikelihood omega]
  ring

end

end N0619
end N0230
end GD

#print axioms _root_.GD.N0230.N0619.d000394
#print axioms _root_.GD.N0230.N0619.d000396
#print axioms _root_.GD.N0230.N0619.d000399
#print axioms _root_.GD.N0230.N0619.d000395
#print axioms _root_.GD.N0230.N0619.d000403
#print axioms _root_.GD.N0230.N0619.d000404
