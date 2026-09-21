import GD.Module0022
import GD.Module1034





















open Filter
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1162

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0629
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false


def d016619 (t : ℝ) (weight : ι → ℝ) : ι → ℝ :=
  fun i ↦ t * weight i


def d016620
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  ∑ i, weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega



def d016621
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  ∑ i, weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega * _root_.GD.N0232.N0720.N1126.d016414 packet i


theorem d016622
    (t : ℝ) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1162.d016620 packet (_root_.GD.N0232.N0720.N1162.d016619 t weight) omega =
      t * _root_.GD.N0232.N0720.N1162.d016620 packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1162.d016620 _root_.GD.N0232.N0720.N1162.d016619
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring


theorem d016623
    (t : ℝ) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1162.d016621 packet (_root_.GD.N0232.N0720.N1162.d016619 t weight) omega =
      t * _root_.GD.N0232.N0720.N1162.d016621 packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1162.d016621 _root_.GD.N0232.N0720.N1162.d016619
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring


theorem d016624
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016415 packet weight omega =
      1 + _root_.GD.N0232.N0720.N1162.d016620 packet weight omega := by
  rfl



theorem d016625
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
        omega = _root_.GD.N0232.N0720.N1162.d016621 packet weight omega := by
  rfl



theorem d016626
    (t : ℝ) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016416 packet (_root_.GD.N0232.N0720.N1162.d016619 t weight) omega =
      _root_.GD.N0230.N0629.d000227 t
        (_root_.GD.N0232.N0720.N1162.d016620 packet weight omega)
        (_root_.GD.N0232.N0720.N1162.d016621 packet weight omega) := by
  unfold _root_.GD.N0232.N0720.N1126.d016416
  change
    _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1162.d016619 t weight)
          (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega /
        _root_.GD.N0232.N0720.N1126.d016415 packet (_root_.GD.N0232.N0720.N1162.d016619 t weight) omega = _
  rw [_root_.GD.N0232.N0720.N1162.d016624,
    _root_.GD.N0232.N0720.N1162.d016625,
    _root_.GD.N0232.N0720.N1162.d016622, _root_.GD.N0232.N0720.N1162.d016623]
  rfl



theorem d016627
    (g : _root_.GD.N0232.N0719.N0946.d009229) (t : ℝ)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016416
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
        (_root_.GD.N0232.N0720.N1162.d016619 t weight) (g • omega) =
      _root_.GD.N0230.N0629.d000233 t
        (_root_.GD.N0232.N0720.N1162.d016620 packet weight omega)
        (_root_.GD.N0232.N0720.N1162.d016621 packet weight omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
        g.shift g.d009239 := by
  unfold _root_.GD.N0232.N0720.N1126.d016416
  change
    _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1162.d016619 t weight)
          (_root_.GD.N0232.N0720.N1126.d016413 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
          (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))) (g • omega) /
        _root_.GD.N0232.N0720.N1126.d016415 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
          (_root_.GD.N0232.N0720.N1162.d016619 t weight) (g • omega) = _
  rw [_root_.GD.N0232.N0720.N1124.d016508,
    _root_.GD.N0232.N0720.N1124.d016509]
  rw [_root_.GD.N0232.N0720.N1162.d016624,
    _root_.GD.N0232.N0720.N1162.d016625,
    _root_.GD.N0232.N0720.N1162.d016622, _root_.GD.N0232.N0720.N1162.d016623]
  unfold _root_.GD.N0230.N0629.d000233
  ring_nf


theorem d016628
    (g : _root_.GD.N0232.N0719.N0946.d009229) (t : ℝ)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (ht : 0 ≤ t)
    (hS : 0 < _root_.GD.N0232.N0720.N1162.d016620 packet weight omega) :
    _root_.GD.N0232.N0720.N1126.d016416
          (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
          (_root_.GD.N0232.N0720.N1162.d016619 t weight) (g • omega) -
        g • _root_.GD.N0232.N0720.N1126.d016416 packet
          (_root_.GD.N0232.N0720.N1162.d016619 t weight) omega =
      _root_.GD.N0230.N0629.d000235 t
        (_root_.GD.N0232.N0720.N1162.d016620 packet weight omega)
        (_root_.GD.N0232.N0720.N1162.d016621 packet weight omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
        g.shift g.d009239 := by
  rw [_root_.GD.N0232.N0720.N1162.d016627,
    _root_.GD.N0232.N0720.N1162.d016626]
  change _root_.GD.N0230.N0629.d000233 _ _ _ _ _ _ -
      _root_.GD.N0230.N0629.d000234 _ _ _ _ _ = _
  apply _root_.GD.N0230.N0629.d000236
  · exact (_root_.GD.N0230.N0629.d000229 ht hS).ne'
  · have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n
        (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
      _root_.GD.N0232.N0720.N1499.d015005 m n _ _
    have : 0 < 1 +
        _root_.GD.N0232.N0720.N1499.d015001 m n
          (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
          t * _root_.GD.N0232.N0720.N1162.d016620 packet weight omega := by
      positivity
    exact this.ne'




theorem d016629
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hS : 0 < _root_.GD.N0232.N0720.N1162.d016620 packet weight omega) :
    Tendsto
      (fun t : ℝ ↦
        _root_.GD.N0232.N0720.N1126.d016416
              (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
              (_root_.GD.N0232.N0720.N1162.d016619 t weight) (g • omega) -
          g • _root_.GD.N0232.N0720.N1126.d016416 packet
              (_root_.GD.N0232.N0720.N1162.d016619 t weight) omega)
      atTop (nhds 0) := by
  have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n
      (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  apply (_root_.GD.N0230.N0629.d000238 hS hc).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (_root_.GD.N0232.N0720.N1162.d016628
    g t packet weight omega ht hS).symm

end

end N1162
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1162.d016626
#print axioms _root_.GD.N0232.N0720.N1162.d016627
#print axioms _root_.GD.N0232.N0720.N1162.d016628
#print axioms _root_.GD.N0232.N0720.N1162.d016629
