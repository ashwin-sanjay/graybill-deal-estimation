import GD.Module1010
import Mathlib.Tactic












open Filter MeasureTheory

namespace GD.N0232.N0720.N1405

noncomputable section

open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1282
open _root_.GD.N0232.N0720.N1397
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0657

noncomputable local instance d016079 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016080 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩




structure d016081
    (N : ℝ) (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ) (phase : ℝ) : Prop where
  finitePrior : IsFiniteMeasure prior
  phase_sq : phase ^ 2 = 1
  evidence_eq :
    _root_.GD.N0232.N0720.N1276.d016063 prior =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1282.d014826 N
  current_eq :
    _root_.GD.N0232.N0720.N1276.d016066 prior candidate =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      fun x ↦ phase * _root_.GD.N0232.N0720.N1282.d014827 N x



theorem d016082
    {N : ℝ} {prior : Measure _root_.GD.N0232.N0720.N1080.d014168}
    {candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ} {phase : ℝ}
    (hreal : _root_.GD.N0232.N0720.N1405.d016081 N prior candidate phase) :
    _root_.GD.N0232.N0720.N1276.d016067 prior candidate =
      _root_.GD.N0232.N0720.N1282.d014828 N := by
  unfold _root_.GD.N0232.N0720.N1276.d016067 _root_.GD.N0232.N0720.N1282.d014828
  apply integral_congr_ae
  filter_upwards [hreal.evidence_eq, hreal.current_eq] with x hE hJ
  rw [hE, hJ, mul_pow, hreal.phase_sq, one_mul]



theorem d016083
    {N : ℝ} (hN : 3 ≤ N)
    {prior : Measure _root_.GD.N0232.N0720.N1080.d014168}
    {candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ} {phase : ℝ}
    (hreal : _root_.GD.N0232.N0720.N1405.d016081 N prior candidate phase) :
    _root_.GD.N0232.N0720.N1276.d016067 prior candidate ≤
      48 / N ^ 9 := by
  rw [_root_.GD.N0232.N0720.N1405.d016082
    hreal]
  exact _root_.GD.N0232.N0720.N1282.d014838 hN


theorem d016084
    {N : ℝ} {prior : Measure _root_.GD.N0232.N0720.N1080.d014168}
    {candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ}
    (hreal : _root_.GD.N0232.N0720.N1276.d016069 N prior candidate) :
    _root_.GD.N0232.N0720.N1405.d016081 N prior candidate 1 where
  finitePrior := hreal.finitePrior
  phase_sq := by norm_num
  evidence_eq := hreal.evidence_eq
  current_eq := by
    filter_upwards [hreal.current_eq] with x hx
    simpa using hx



theorem d016085
    {N : ℝ} {prior : Measure _root_.GD.N0232.N0720.N1080.d014168}
    {candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ}
    (hfinite : IsFiniteMeasure prior)
    (hE : _root_.GD.N0232.N0720.N1276.d016063 prior =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1282.d014826 N)
    (hJ : _root_.GD.N0232.N0720.N1276.d016066 prior candidate =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      fun x ↦ -_root_.GD.N0232.N0720.N1282.d014827 N x) :
    _root_.GD.N0232.N0720.N1405.d016081 N prior candidate (-1) where
  finitePrior := hfinite
  phase_sq := by norm_num
  evidence_eq := hE
  current_eq := by
    filter_upwards [hJ] with x hx
    simpa using hx



def d016086 (x : _root_.GD.N0232.N0720.N1276.d016060) : ℝ :=
  (_root_.GD.N0232.N0720.N1397.d014815 x).1






theorem d016087
    {N : ℝ} {prior : Measure _root_.GD.N0232.N0720.N1080.d014168}
    (hfinite : IsFiniteMeasure prior)
    (hE : _root_.GD.N0232.N0720.N1276.d016063 prior =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1282.d014826 N)
    (hM : _root_.GD.N0232.N0720.N1276.d016064 prior =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      fun x ↦ _root_.GD.N0232.N0720.N1405.d016086 x * _root_.GD.N0232.N0720.N1282.d014826 N x -
        _root_.GD.N0232.N0720.N1282.d014827 N x)
    (hint : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) prior ∧
      Integrable
        (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta x)
        prior) :
    _root_.GD.N0232.N0720.N1405.d016081 N prior
      _root_.GD.N0232.N0720.N1405.d016086 (-1) := by
  apply _root_.GD.N0232.N0720.N1405.d016085 hfinite hE
  filter_upwards [hE, hM, hint] with x hxE hxM hxint
  rw [_root_.GD.N0232.N0720.N1276.d016072 prior
      _root_.GD.N0232.N0720.N1405.d016086 x hxint.1 hxint.2,
    hxM, hxE]
  ring





theorem d016088
    {N : ℝ} (hN : 3 ≤ N)
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    {phase : ℝ}
    (hreal : _root_.GD.N0232.N0720.N1405.d016081 N prior candidate phase)
    (hcandidateJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 candidate).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hposteriorJoint : Integrable
      (_root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
        (_root_.GD.N0232.N0720.N1276.d016065 prior)).uncurry
      (prior.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
        (_root_.GD.N0232.N0720.N1276.d016065 prior))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta x) prior ∧
      Integrable
        (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta x)
        prior ∧
      Integrable
        (fun theta ↦
          _root_.GD.N0232.N0720.N1276.d016061 theta ^ 2 * _root_.GD.N0232.N0720.N1276.d016062 theta x)
        prior ∧
      _root_.GD.N0232.N0720.N1276.d016063 prior x ≠ 0) :
    _root_.GD.N0232.N0720.N1276.d016068 prior candidate ≤ 48 / N ^ 9 := by
  letI : IsFiniteMeasure prior := hreal.finitePrior
  letI : SigmaFinite prior := inferInstance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  letI : SFinite (_root_.GD.N0232.N0720.N1080.d014172 2 2) := inferInstance
  have hpointwise : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 x
          (candidate x) =
        _root_.GD.N0230.N0589.d000087 prior _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061 x
            (_root_.GD.N0232.N0720.N1276.d016065 prior x) +
          _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
            (_root_.GD.N0232.N0720.N1276.d016065 prior) x := by
    filter_upwards [hmoments] with x hx
    exact _root_.GD.N0232.N0720.N1276.d016075 prior candidate x
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  have hdeficit : _root_.GD.N0232.N0720.N1276.d016068 prior candidate =
      ∫ x, _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
        (_root_.GD.N0232.N0720.N1276.d016065 prior) x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
    unfold _root_.GD.N0232.N0720.N1276.d016068
    exact _root_.GD.N0230.N0589.d000093
      prior (_root_.GD.N0232.N0720.N1080.d014172 2 2) _root_.GD.N0232.N0720.N1276.d016062 _root_.GD.N0232.N0720.N1276.d016061
      candidate (_root_.GD.N0232.N0720.N1276.d016065 prior)
      hcandidateJoint hposteriorJoint htax hpointwise
  rw [hdeficit]
  have hperspective :
      (∫ x, _root_.GD.N0230.N0589.d000089 prior _root_.GD.N0232.N0720.N1276.d016062 candidate
          (_root_.GD.N0232.N0720.N1276.d016065 prior) x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        _root_.GD.N0232.N0720.N1276.d016067 prior candidate := by
    unfold _root_.GD.N0232.N0720.N1276.d016067
    apply integral_congr_ae
    filter_upwards [hmoments] with x hx
    exact _root_.GD.N0232.N0720.N1276.d016074
      prior candidate x hx.1 hx.2.1 hx.2.2.2
  rw [hperspective]
  exact _root_.GD.N0232.N0720.N1405.d016083 hN hreal

end

end GD.N0232.N0720.N1405

#print axioms _root_.GD.N0232.N0720.N1405.d016082
#print axioms _root_.GD.N0232.N0720.N1405.d016085
#print axioms _root_.GD.N0232.N0720.N1405.d016087
#print axioms _root_.GD.N0232.N0720.N1405.d016088

