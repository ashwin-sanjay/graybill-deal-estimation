import GD.Module1496
import GD.Module1452

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0084

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0981
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0156.N0444

noncomputable section

variable {k : ℕ} [NeZero k] (sizes : Fin k → ℕ)

omit [NeZero k] in
theorem d023546 (θ η : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ ≪ _root_.GD.N0232.N0719.N0859.d010812 k sizes η :=
  (_root_.GD.N0084.d023419 sizes θ).trans (_root_.GD.N0084.d023420 sizes η)

omit [NeZero k] in
theorem d023547
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ {z | ∃ i, W z i < 0}) :
    ¬ ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, ∀ i, 0 ≤ W z i := by
  intro h
  have hzero : _root_.GD.N0232.N0719.N0859.d010812 k sizes θ {z | ∃ i, W z i < 0} = 0 := by
    simpa only [ae_iff, not_forall, not_le] using h
  exact hneg.ne' hzero




theorem d023548 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : _root_.GD.N0084.d023418 sizes W)
    (hunit : ∀ z, ∑ i, W z i = 1)
    (hf : _root_.GD.N0084.d023417 sizes W ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k) (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, W z i < 0}) :
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes (_root_.GD.N0084.d023417 sizes W)) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0084.d023417 sizes W) := by
  have hnot := _root_.GD.N0084.d023547 sizes W θ₀ hneg
  intro θ
  apply (_root_.GD.N0084.N0337.d023004 sizes hn
    (_root_.GD.N0084.d023417 sizes W) hf.1 (_root_.GD.N0084.d023424 sizes hn W hW hunit) θ (hf.2 θ)).mpr
  intro heq
  have hi : ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, _root_.GD.N0156.N0444.d020667 sizes (_root_.GD.N0084.d023417 sizes W) z := by
    filter_upwards [heq] with z hz
    have h := _root_.GD.N0232.N0719.N0981.d020662 sizes (_root_.GD.N0084.d023417 sizes W) z
    rwa [hz] at h
  exact hnot ((_root_.GD.N0084.d023546 sizes θ₀ θ).ae_le
    (_root_.GD.N0084.d023426 sizes hn W hW θ hi))




theorem d023549 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : _root_.GD.N0084.d023418 sizes W)
    (hunit : ∀ z, ∑ i, W z i = 1)
    (hf : _root_.GD.N0084.d023417 sizes W ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k) (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, W z i < 0}) :
    _root_.GD.N0232.N0719.N0981.d020660 sizes (_root_.GD.N0084.d023417 sizes W) ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes (_root_.GD.N0084.d023417 sizes W)) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0084.d023417 sizes W)) := by
  have hs := _root_.GD.N0084.d023548 sizes hn W hW hunit hf θ₀ hneg
  refine ⟨⟨_root_.GD.N0232.N0719.N0981.d020661 sizes hf.1, fun θ => ?_⟩, hs⟩
  exact ne_top_of_le_ne_top (hf.2 θ) (hs θ).le

end
end GD.N0084

#print axioms _root_.GD.N0084.d023546
#print axioms _root_.GD.N0084.d023548
#print axioms _root_.GD.N0084.d023549
