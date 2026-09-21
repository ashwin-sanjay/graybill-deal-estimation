import GD.Module1659

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GD.N0226

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0946
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0594
open _root_.GD.N0232.N0719.N1022
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0962 _root_.GD.N0097

noncomputable section

variable {k : ℕ} (sizes : Fin k → ℕ)

def d028194 (t : ℝ)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0842.d010911 k sizes 0 (Real.exp t) f

@[simp] theorem d028195
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0226.d028194 sizes 0 f = f := by
  simp [_root_.GD.N0226.d028194]

theorem d028196 (s t : ℝ)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0226.d028194 sizes (s + t) f =
      _root_.GD.N0226.d028194 sizes s (_root_.GD.N0226.d028194 sizes t f) := by
  simpa only [_root_.GD.N0226.d028194, Real.exp_add, mul_zero, zero_add] using
    (_root_.GD.N0232.N0719.N0842.d010916 k sizes 0 (Real.exp s) 0 (Real.exp t)
      (Real.exp_ne_zero s) (Real.exp_ne_zero t) f).symm

theorem d028197 (t : ℝ)
    {f g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hfg : f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] g) :
    _root_.GD.N0226.d028194 sizes t f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0226.d028194 sizes t g := by
  exact _root_.GD.N0232.N0719.N0896.d011120 k sizes (⟨0, t⟩ : _root_.GD.N0232.N0719.N0946.d009229) hfg


def d028198 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    AddSubgroup ℝ where
  carrier := {t | _root_.GD.N0226.d028194 sizes t f =ᵐ[
    _root_.GD.N0232.N0719.N0859.d010813 k sizes] f}
  zero_mem' := by simp
  add_mem' := by
    intro s t hs ht
    change _root_.GD.N0226.d028194 sizes (s + t) f =ᵐ[_] f
    rw [_root_.GD.N0226.d028196]
    exact (_root_.GD.N0226.d028197 sizes s ht).trans hs
  neg_mem' := by
    intro t ht
    have h := _root_.GD.N0226.d028197 sizes (-t) ht
    rw [← _root_.GD.N0226.d028196, neg_add_cancel, _root_.GD.N0226.d028195] at h
    exact h.symm

theorem d028199 :
    Continuous (fun t : ℝ => (⟨0, t⟩ : _root_.GD.N0232.N0719.N0946.d009229)) := by
  refine continuous_induced_rng.2 ?_
  change Continuous (fun t : ℝ => (t, (0 : ℝ)))
  fun_prop

local instance d028200 : IsProbabilityMeasure
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813 _root_.GD.N0232.N0719.d009182
  infer_instance



theorem d028201
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (seq : ℕ → ℝ) (t : ℝ) (hseq : Tendsto seq atTop (𝓝 t)) :
    TendstoInMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (fun j => _root_.GD.N0226.d028194 sizes (seq j) f) atTop
      (_root_.GD.N0226.d028194 sizes t f) := by
  let p := _root_.GD.N0232.N0719.N0970.d012312 k sizes f hf
  have hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p := by
    intro θ
    rw [_root_.GD.N0232.N0719.N0970.d012313]
    exact hf.2 θ
  have hdf : _root_.GD.N0232.N0719.N0896.d011088 k sizes p =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] f := by
    apply (_root_.GD.N0232.N0719.N0896.d011090 k sizes p).trans
    exact (_root_.GD.N0232.N0719.N0896.d011095 k sizes f hf.1
      (hf.2 (_root_.GD.N0232.N0719.N0859.d010810 k))).coeFn_toLp
  have h := _root_.GD.N0232.N0719.N1022.d015183 k sizes p hp
    (fun j => ⟨0, seq j⟩) ⟨0, t⟩
    (_root_.GD.N0226.d028199.tendsto t |>.comp hseq)
  change TendstoInMeasure _
    (fun j => _root_.GD.N0226.d028194 sizes (seq j) (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)) atTop
    (_root_.GD.N0226.d028194 sizes t (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)) at h
  exact h.congr' (Filter.Eventually.of_forall fun j => _root_.GD.N0226.d028197 sizes (seq j) hdf)
    (_root_.GD.N0226.d028197 sizes t hdf)


theorem d028202
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    IsClosed (_root_.GD.N0226.d028198 sizes f : Set ℝ) := by
  apply IsSeqClosed.isClosed
  intro seq t hmem hseq
  have horbit := _root_.GD.N0226.d028201 sizes f hf seq t hseq
  have hconst : TendstoInMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (fun _ : ℕ => f) atTop f := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => hf.1.aestronglyMeasurable)
    exact ae_of_all _ fun _ => tendsto_const_nhds
  have hfixed : TendstoInMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (fun j => _root_.GD.N0226.d028194 sizes (seq j) f) atTop f :=
    hconst.congr' (Filter.Eventually.of_forall fun j =>
      (show _root_.GD.N0226.d028194 sizes (seq j) f =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010813 k sizes] f from hmem j).symm)
      Filter.EventuallyEq.rfl
  exact tendstoInMeasure_ae_unique horbit hfixed



theorem d028203
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hd : Dense (_root_.GD.N0226.d028198 sizes f : Set ℝ)) :
    ∀ t : ℝ, _root_.GD.N0226.d028194 sizes t f =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] f := by
  have heq : (_root_.GD.N0226.d028198 sizes f : Set ℝ) = Set.univ :=
    (_root_.GD.N0226.d028202 sizes f hf).closure_eq ▸ hd.closure_eq
  intro t
  have : t ∈ (_root_.GD.N0226.d028198 sizes f : Set ℝ) := by rw [heq]; trivial
  exact this

end
end GD.N0226

#print axioms _root_.GD.N0226.d028198
#print axioms _root_.GD.N0226.d028201
#print axioms _root_.GD.N0226.d028202
#print axioms _root_.GD.N0226.d028203
