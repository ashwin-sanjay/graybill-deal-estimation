import GD.Module1496

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0084

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0981
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0896

noncomputable section

variable {k : ℕ} [NeZero k] (sizes : Fin k → ℕ)

omit [NeZero k] in
@[fun_prop] theorem d023428 (i : Fin k) : Measurable (fun z => _root_.GD.N0084.d023416 sizes z i) :=
  (_root_.GD.N0232.N0719.N0981.d020649 sizes i).measurable.comp (_root_.GD.N0232.N0719.N0981.d020645 sizes).symm.measurable

omit [NeZero k] in
@[fun_prop] theorem d023429
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : Measurable W) : Measurable (_root_.GD.N0084.d023417 sizes W) := by
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp hW).mul (_root_.GD.N0084.d023428 sizes i)


def d023430 (z : _root_.GD.N0084.d023414 sizes) : _root_.GD.N0084.d023414 sizes := fun i j => z i j - _root_.GD.N0084.d023416 sizes z i

omit [NeZero k] in
@[fun_prop] theorem d023431 : Measurable (_root_.GD.N0084.d023430 sizes) := by
  unfold _root_.GD.N0084.d023430
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).sub (_root_.GD.N0084.d023428 sizes i)

omit [NeZero k] in
theorem d023432 (hn : ∀ i, 0 < sizes i)
    (c : Fin k → ℝ) (z : _root_.GD.N0084.d023414 sizes) :
    _root_.GD.N0084.d023430 sizes (_root_.GD.N0084.d023415 sizes c z) = _root_.GD.N0084.d023430 sizes z := by
  funext i j
  simp only [_root_.GD.N0084.d023430, _root_.GD.N0084.d023422 sizes hn, _root_.GD.N0084.d023415]
  ring

omit [NeZero k] in
theorem d023433 (hn : ∀ i, 0 < sizes i)
    (w : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) : _root_.GD.N0084.d023418 sizes (w ∘ _root_.GD.N0084.d023430 sizes) := by
  intro c z
  simp only [Function.comp_apply, _root_.GD.N0084.d023432 sizes hn]



def d023434 (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (z : _root_.GD.N0084.d023414 sizes) : Fin k → ℝ :=
  if ∀ i, 0 ≤ W z i then W z else fun _ => 1 / (k : ℝ)

omit [NeZero k] in
@[fun_prop] theorem d023435
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : Measurable W) : Measurable (_root_.GD.N0084.d023434 sizes W) := by
  apply Measurable.ite
  · simpa only [setOf_forall, Function.comp_apply] using MeasurableSet.iInter (fun i =>
      measurableSet_le measurable_const ((measurable_pi_apply i).comp hW))
  · exact hW
  · exact measurable_const

omit [NeZero k] in
theorem d023436 (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (z : _root_.GD.N0084.d023414 sizes) (i : Fin k) :
    0 ≤ _root_.GD.N0084.d023434 sizes W z i := by
  unfold _root_.GD.N0084.d023434
  split
  · exact ‹∀ i, 0 ≤ W z i› i
  · positivity

theorem d023437 (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ)
    (hunit : ∀ z, ∑ i, W z i = 1) (z : _root_.GD.N0084.d023414 sizes) :
    ∑ i, _root_.GD.N0084.d023434 sizes W z i = 1 := by
  unfold _root_.GD.N0084.d023434
  split
  · exact hunit z
  · simp [NeZero.ne k]

omit [NeZero k] in
theorem d023438 (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ)
    (hW : _root_.GD.N0084.d023418 sizes W) : _root_.GD.N0084.d023418 sizes (_root_.GD.N0084.d023434 sizes W) := by
  intro c z
  simp only [_root_.GD.N0084.d023434, hW c z]



theorem d023439 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hWm : Measurable W) (hW : _root_.GD.N0084.d023418 sizes W)
    (hunit : ∀ z, ∑ i, W z i = 1)
    (hf : _root_.GD.N0084.d023417 sizes W ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes (_root_.GD.N0084.d023417 sizes W)) :
    Measurable (_root_.GD.N0084.d023434 sizes W) ∧
      _root_.GD.N0084.d023418 sizes (_root_.GD.N0084.d023434 sizes W) ∧
      (∀ z i, 0 ≤ _root_.GD.N0084.d023434 sizes W z i) ∧
      (∀ z, ∑ i, _root_.GD.N0084.d023434 sizes W z i = 1) ∧
      _root_.GD.N0084.d023417 sizes (_root_.GD.N0084.d023434 sizes W) ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes (_root_.GD.N0084.d023417 sizes (_root_.GD.N0084.d023434 sizes W)) ∧
      (∀ θ, _root_.GD.N0084.d023417 sizes (_root_.GD.N0084.d023434 sizes W) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0084.d023417 sizes W) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0084.d023417 sizes (_root_.GD.N0084.d023434 sizes W)) =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0084.d023417 sizes W)) := by
  have hae (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
      _root_.GD.N0084.d023417 sizes (_root_.GD.N0084.d023434 sizes W) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0084.d023417 sizes W := by
    filter_upwards [_root_.GD.N0084.d023427 sizes hn W hW hunit hf ht θ]
      with z hz
    simp only [_root_.GD.N0084.d023417, _root_.GD.N0084.d023434, if_pos hz]
  have hrisk (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0084.d023417 sizes (_root_.GD.N0084.d023434 sizes W)) =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0084.d023417 sizes W) :=
    _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hae θ)
  refine ⟨_root_.GD.N0084.d023435 sizes W hWm, _root_.GD.N0084.d023438 sizes W hW,
    _root_.GD.N0084.d023436 sizes W, _root_.GD.N0084.d023437 sizes W hunit,
    ⟨_root_.GD.N0084.d023429 sizes _ (_root_.GD.N0084.d023435 sizes W hWm),
      fun θ => by rw [hrisk]; exact hf.2 θ⟩, ?_, hae, hrisk⟩
  intro e hem he θ
  exact (ht e hem (fun θ => by simpa only [hrisk θ] using he θ) θ).trans (hae θ).symm

end
end GD.N0084

#print axioms _root_.GD.N0084.d023433
#print axioms _root_.GD.N0084.d023438
#print axioms _root_.GD.N0084.d023439
