import GD.Module0964
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GD.N0097

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0946
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0594
open _root_.GD.N0232.N0719.N1022
open _root_.GD.N0232.N0720.N1482

noncomputable section

variable {k : ℕ} (sizes : Fin k → ℕ)

def d028164 (t : ℝ) (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0842.d010911 k sizes t 1 f

@[simp] theorem d028165 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0097.d028164 sizes 0 f = f := _root_.GD.N0232.N0719.N0842.d010914 k sizes f

theorem d028166 (s t : ℝ)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0097.d028164 sizes (s + t) f = _root_.GD.N0097.d028164 sizes s (_root_.GD.N0097.d028164 sizes t f) := by
  simpa only [_root_.GD.N0097.d028164, one_mul, mul_one] using
    (_root_.GD.N0232.N0719.N0842.d010916 k sizes s 1 t 1 one_ne_zero one_ne_zero f).symm

theorem d028167 (t : ℝ)
    {f g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hfg : f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] g) :
    _root_.GD.N0097.d028164 sizes t f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0097.d028164 sizes t g := by
  simpa [_root_.GD.N0097.d028164, _root_.GD.N0232.N0720.N1482.d015128, _root_.GD.N0232.N0719.N0946.d009229.d009239] using
    _root_.GD.N0232.N0719.N0896.d011120 k sizes (_root_.GD.N0232.N0720.N1482.d015128 t) hfg



def d028168 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : AddSubgroup ℝ where
  carrier := {t | _root_.GD.N0097.d028164 sizes t f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] f}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht
    change _root_.GD.N0097.d028164 sizes (s + t) f =ᵐ[_] f
    rw [_root_.GD.N0097.d028166]
    exact (_root_.GD.N0097.d028167 sizes s ht).trans hs
  neg_mem' := by
    intro t ht
    have h := _root_.GD.N0097.d028167 sizes (-t) ht
    rw [← _root_.GD.N0097.d028166, neg_add_cancel, _root_.GD.N0097.d028165] at h
    exact h.symm

theorem d028169 : Continuous _root_.GD.N0232.N0720.N1482.d015128 := by
  refine continuous_induced_rng.2 ?_
  change Continuous (fun t : ℝ => ((0 : ℝ), t))
  fun_prop

local instance d028170 : IsProbabilityMeasure
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813 _root_.GD.N0232.N0719.d009182
  infer_instance




theorem d028171
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p)
    (a b : ℝ) (hab : Irrational (a / b))
    (ha : _root_.GD.N0097.d028164 sizes a (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] _root_.GD.N0232.N0719.N0896.d011088 k sizes p)
    (hb : _root_.GD.N0097.d028164 sizes b (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] _root_.GD.N0232.N0719.N0896.d011088 k sizes p) :
    ∀ t : ℝ, _root_.GD.N0097.d028164 sizes t (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
  let H := AddSubgroup.closure ({a, b} : Set ℝ)
  have hH : Dense (H : Set ℝ) := dense_addSubgroupClosure_pair_iff.mpr hab
  have hle : H ≤ _root_.GD.N0097.d028168 sizes (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) := by
    apply (AddSubgroup.closure_le (_root_.GD.N0097.d028168 sizes (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))).2
    intro t ht
    rcases ht with (rfl | rfl)
    · exact ha
    · exact hb
  apply _root_.GD.N0230.N0594.d000115
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (fun t : H => (t : ℝ)) (Dense.denseRange_val hH)
    (fun t => _root_.GD.N0097.d028164 sizes t (_root_.GD.N0232.N0719.N0896.d011088 k sizes p))
    (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (_root_.GD.N0232.N0719.N0896.d011089 k sizes p).aestronglyMeasurable
    (fun t => hle t.2)
  intro seq t hseq
  have hpa := _root_.GD.N0232.N0719.N1022.d015183 k sizes p hp
    (fun j => _root_.GD.N0232.N0720.N1482.d015128 (seq j).1) (_root_.GD.N0232.N0720.N1482.d015128 t)
    (_root_.GD.N0097.d028169.tendsto t |>.comp hseq)
  simpa only [_root_.GD.N0097.d028164, _root_.GD.N0232.N0720.N1482.d015128, _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_zero] using hpa


theorem d028172
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p)
    (h1 : _root_.GD.N0097.d028164 sizes 1 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] _root_.GD.N0232.N0719.N0896.d011088 k sizes p)
    (h2 : _root_.GD.N0097.d028164 sizes (Real.sqrt 2) (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] _root_.GD.N0232.N0719.N0896.d011088 k sizes p) :
    ∀ t : ℝ, _root_.GD.N0097.d028164 sizes t (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] _root_.GD.N0232.N0719.N0896.d011088 k sizes p := by
  exact _root_.GD.N0097.d028171 sizes p hp (Real.sqrt 2) 1
    (by simpa using irrational_sqrt_two) h2 h1

end
end GD.N0097

#print axioms _root_.GD.N0097.d028168
#print axioms _root_.GD.N0097.d028171
#print axioms _root_.GD.N0097.d028172
