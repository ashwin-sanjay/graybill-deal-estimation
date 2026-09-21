import GD.Module1512

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0084.N0338

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0981 _root_.GD.N0232.N0719.N0980
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0156.N0444

noncomputable section

variable {k : ℕ} [NeZero k] (sizes : Fin k → ℕ)

omit [NeZero k] in
theorem d028795 (hn : ∀ i, 0 < sizes i) (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) (i : Fin k) :
    |_root_.GD.N0232.N0719.N0981.d020646 sizes x i| ≤ ‖x‖ := by
  have hpos : 0 < (sizes i : ℝ) := Nat.cast_pos.mpr (hn i)
  rw [_root_.GD.N0232.N0719.N0981.d020646, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc
    |∑ j, x ⟨i, j⟩| ≤ ∑ j, |x ⟨i, j⟩| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin (sizes i), ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_le_pi_norm x ⟨i, j⟩
    _ = ‖x‖ * (sizes i : ℝ) := by simp [mul_comm]



theorem d028796 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.d023414 sizes → ℝ) (z : _root_.GD.N0084.d023414 sizes) :
    |_root_.GD.N0232.N0719.N0981.d020660 sizes f z| ≤ ‖(_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z‖ := by
  have hm := fun i => abs_le.mp (_root_.GD.N0084.N0338.d028795 sizes hn ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) i)
  have hl : -‖(_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z‖ ≤ _root_.GD.N0232.N0719.N0981.d020647 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) := by
    exact Finset.le_inf' _ _ (fun i _ => (hm i).1)
  have hu : _root_.GD.N0232.N0719.N0981.d020648 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) ≤ ‖(_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z‖ := by
    exact Finset.sup'_le _ _ (fun i _ => (hm i).2)
  have hc := _root_.GD.N0232.N0719.N0981.d020662 sizes f z
  exact abs_le.mpr ⟨hl.trans hc.1, hc.2.trans hu⟩



theorem d028797 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.d023414 sizes → ℝ) (hf : Measurable f) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp (_root_.GD.N0232.N0719.N0981.d020660 sizes f) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  let v : Fin k → ℝ≥0 := fun i => _root_.GD.N0232.N0719.N0932.d009193 (θ.scale i)
  have hL : _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = Measure.pi (fun i => Measure.pi
      (fun _ : Fin (sizes i) => gaussianReal θ.location (v i))) := _root_.GD.N0156.N0444.d020668 sizes θ
  have hmap : MeasurePreserving (_root_.GD.N0232.N0719.N0981.d020645 sizes)
      (_root_.GD.N0232.N0719.N0980.d009697 θ.location (_root_.GD.N0232.N0719.N0981.d020658 sizes v)) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    rw [hL]
    simpa only [_root_.GD.N0232.N0719.N0981.d020645, MeasurableEquiv.symm_symm, _root_.GD.N0232.N0719.N0980.d009697, _root_.GD.N0232.N0719.N0981.d020658] using
      (_root_.GD.N0232.N0719.N0997.d019803
        (fun (i : Fin k) (_ : Fin (sizes i)) => gaussianReal θ.location (v i))).symm
  have h2v := (_root_.GD.N0232.N0719.N0885.d009316
    θ.location (_root_.GD.N0232.N0719.N0981.d020658 sizes v)).memLp_two
  have h2norm : MemLp (fun z : _root_.GD.N0084.d023414 sizes => ‖(_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z‖) 2
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    rw [← hmap.map_eq]
    apply (_root_.GD.N0232.N0719.N0981.d020645 sizes).memLp_map_measure_iff.mpr
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using h2v.norm
  apply h2norm.mono' (_root_.GD.N0232.N0719.N0981.d020661 sizes hf).aestronglyMeasurable
  exact ae_of_all _ (fun z => _root_.GD.N0084.N0338.d028796 sizes hn f z)

theorem d028798 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.d023414 sizes → ℝ) (hf : Measurable f) :
    _root_.GD.N0232.N0719.N0981.d020660 sizes f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
  refine ⟨_root_.GD.N0232.N0719.N0981.d020661 sizes hf, fun θ => ?_⟩
  rw [_root_.GD.N0156.N0444.d020671 sizes _ θ (_root_.GD.N0084.N0338.d028797 sizes hn f hf θ)]
  exact ENNReal.ofReal_ne_top



theorem d028799 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.d023414 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  by_cases hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f = ⊤
  · rw [hfinite]
    exact le_top
  · exact _root_.GD.N0084.N0337.d023002 sizes hn f hf he θ hfinite



theorem d028800 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.d023414 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ↔
      _root_.GD.N0232.N0719.N0981.d020660 sizes f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  constructor
  · intro heq
    have hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≠ ⊤ := by
      rw [← heq]
      exact (_root_.GD.N0084.N0338.d028798 sizes hn f hf).2 θ
    exact (_root_.GD.N0084.N0337.d023003 sizes hn f hf he θ hfinite).mp heq
  · exact fun hae => _root_.GD.N0232.N0719.N0896.d011094 k sizes θ hae

theorem d028801 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.d023414 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ↔
      ¬ _root_.GD.N0232.N0719.N0981.d020660 sizes f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  rw [lt_iff_le_and_ne]
  simp only [_root_.GD.N0084.N0338.d028799 sizes hn f hf he θ, true_and]
  exact not_congr (_root_.GD.N0084.N0338.d028800 sizes hn f hf he θ)



theorem d028802 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.d023414 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
  have hae := ht (_root_.GD.N0232.N0719.N0981.d020660 sizes f) (_root_.GD.N0232.N0719.N0981.d020661 sizes hf)
    (_root_.GD.N0084.N0338.d028799 sizes hn f hf he)
  refine ⟨hf, fun θ => ?_⟩
  rw [← _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hae θ)]
  exact (_root_.GD.N0084.N0338.d028798 sizes hn f hf).2 θ

theorem d028803 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.d023414 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, _root_.GD.N0156.N0444.d020667 sizes f z := by
  have hae := ht (_root_.GD.N0232.N0719.N0981.d020660 sizes f) (_root_.GD.N0232.N0719.N0981.d020661 sizes hf)
    (_root_.GD.N0084.N0338.d028799 sizes hn f hf he) θ
  filter_upwards [hae] with z hz
  have hi := _root_.GD.N0232.N0719.N0981.d020662 sizes f z
  rwa [hz] at hi



theorem d028804 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : _root_.GD.N0084.d023418 sizes W)
    (hunit : ∀ z, ∑ i, W z i = 1)
    (hf : Measurable (_root_.GD.N0084.d023417 sizes W))
    (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k) (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, W z i < 0}) :
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes (_root_.GD.N0084.d023417 sizes W)) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0084.d023417 sizes W) := by
  have hnot := _root_.GD.N0084.d023547 sizes W θ₀ hneg
  intro θ
  apply (_root_.GD.N0084.N0338.d028801 sizes hn (_root_.GD.N0084.d023417 sizes W) hf
    (_root_.GD.N0084.d023424 sizes hn W hW hunit) θ).mpr
  intro heq
  have hi : ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, _root_.GD.N0156.N0444.d020667 sizes (_root_.GD.N0084.d023417 sizes W) z := by
    filter_upwards [heq] with z hz
    have h := _root_.GD.N0232.N0719.N0981.d020662 sizes (_root_.GD.N0084.d023417 sizes W) z
    rwa [hz] at h
  exact hnot ((_root_.GD.N0084.d023546 sizes θ₀ θ).ae_le
    (_root_.GD.N0084.d023426 sizes hn W hW θ hi))

theorem d028805 (hn : ∀ i, 0 < sizes i)
    (W : _root_.GD.N0084.d023414 sizes → Fin k → ℝ) (hW : _root_.GD.N0084.d023418 sizes W)
    (hunit : ∀ z, ∑ i, W z i = 1)
    (hf : Measurable (_root_.GD.N0084.d023417 sizes W))
    (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k) (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, W z i < 0}) :
    _root_.GD.N0232.N0719.N0981.d020660 sizes (_root_.GD.N0084.d023417 sizes W) ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes (_root_.GD.N0084.d023417 sizes W)) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0084.d023417 sizes W)) :=
  ⟨_root_.GD.N0084.N0338.d028798 sizes hn _ hf,
    _root_.GD.N0084.N0338.d028804 sizes hn W hW hunit hf θ₀ hneg⟩

end
end GD.N0084.N0338

#print axioms _root_.GD.N0084.N0338.d028796
#print axioms _root_.GD.N0084.N0338.d028797
#print axioms _root_.GD.N0084.N0338.d028798
#print axioms _root_.GD.N0084.N0338.d028799
#print axioms _root_.GD.N0084.N0338.d028800
#print axioms _root_.GD.N0084.N0338.d028801
#print axioms _root_.GD.N0084.N0338.d028802
#print axioms _root_.GD.N0084.N0338.d028803
#print axioms _root_.GD.N0084.N0338.d028804
#print axioms _root_.GD.N0084.N0338.d028805
