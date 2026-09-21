import GD.Module1280

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0084.N0337

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0981 _root_.GD.N0232.N0719.N0980
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0156.N0444
open _root_.GD.N0156.N0443

noncomputable section

variable {k : ℕ} [NeZero k] (sizes : Fin k → ℕ)

abbrev d022997 := _root_.GD.N0232.N0719.N0859.d010811 k sizes


def d022998 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ) : ℝ :=
  ∫ z, (f z - _root_.GD.N0232.N0719.N0981.d020660 sizes f z) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ

theorem d022999 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ) :
    0 ≤ _root_.GD.N0084.N0337.d022998 sizes θ f := integral_nonneg (fun z => sq_nonneg (f z - _root_.GD.N0232.N0719.N0981.d020660 sizes f z))


theorem d023000 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (h2 : MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) :
    MemLp (_root_.GD.N0232.N0719.N0981.d020660 sizes f) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) ∧
      (∫ z, (_root_.GD.N0232.N0719.N0981.d020660 sizes f z - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) +
        _root_.GD.N0084.N0337.d022998 sizes θ f ≤ ∫ z, (f z - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ := by
  let v : Fin k → ℝ≥0 := fun i => _root_.GD.N0232.N0719.N0932.d009193 (θ.scale i)
  have hv : ∀ i, 0 < v i := fun i =>
    pos_iff_ne_zero.mpr (_root_.GD.N0232.N0719.N0932.d009196 (θ.scale_pos i).ne')
  have hL : _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = Measure.pi (fun i => Measure.pi
      (fun _ : Fin (sizes i) => gaussianReal θ.location (v i))) := _root_.GD.N0156.N0444.d020668 sizes θ
  have h2g := h2
  rw [hL] at h2g
  have hc := _root_.GD.N0232.N0719.N0981.d020663 sizes hn θ.location v hv f hf he h2g
  have hc2 : MemLp (_root_.GD.N0232.N0719.N0981.d020660 sizes f) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    rw [hL]
    exact hc.1
  refine ⟨hc2, ?_⟩
  letI : Nonempty (_root_.GD.N0232.N0719.N0981.d020643 sizes) := ⟨⟨0, ⟨0, hn 0⟩⟩⟩
  have hmap : MeasurePreserving (_root_.GD.N0232.N0719.N0981.d020645 sizes)
      (_root_.GD.N0232.N0719.N0980.d009697 θ.location (_root_.GD.N0232.N0719.N0981.d020658 sizes v)) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    rw [hL]
    simpa only [_root_.GD.N0232.N0719.N0981.d020645, MeasurableEquiv.symm_symm, _root_.GD.N0232.N0719.N0980.d009697, _root_.GD.N0232.N0719.N0981.d020658] using
      (_root_.GD.N0232.N0719.N0997.d019803
        (fun (i : Fin k) (_ : Fin (sizes i)) => gaussianReal θ.location (v i))).symm
  have h2v : MemLp (f ∘ _root_.GD.N0232.N0719.N0981.d020645 sizes) 2 (_root_.GD.N0232.N0719.N0980.d009697 θ.location (_root_.GD.N0232.N0719.N0981.d020658 sizes v)) := by
    apply (_root_.GD.N0232.N0719.N0981.d020645 sizes).memLp_map_measure_iff.mp
    rw [hmap.map_eq]
    exact h2
  have hgap := _root_.GD.N0156.N0443.d020665 θ.location (_root_.GD.N0232.N0719.N0981.d020658 sizes v) (fun j => hv j.1)
    (_root_.GD.N0232.N0719.N0981.d020647 sizes) (_root_.GD.N0232.N0719.N0981.d020648 sizes) (f ∘ _root_.GD.N0232.N0719.N0981.d020645 sizes)
    (_root_.GD.N0232.N0719.N0981.d020650 sizes).measurable (_root_.GD.N0232.N0719.N0981.d020651 sizes).measurable
    (hf.comp (_root_.GD.N0232.N0719.N0981.d020645 sizes).measurable) (_root_.GD.N0232.N0719.N0981.d020656 sizes hn) (_root_.GD.N0232.N0719.N0981.d020657 sizes hn)
    (fun c x => he c (_root_.GD.N0232.N0719.N0981.d020645 sizes x))
    (fun x => (_root_.GD.N0232.N0719.N0981.d020659 sizes hn v hv x).1)
    (fun x => (_root_.GD.N0232.N0719.N0981.d020659 sizes hn v hv x).2) h2v
  have hleft := hmap.integral_comp' (fun z => (_root_.GD.N0232.N0719.N0981.d020660 sizes f z - θ.location) ^ 2)
  have hdist := hmap.integral_comp' (fun z => (f z - _root_.GD.N0232.N0719.N0981.d020660 sizes f z) ^ 2)
  have hright := hmap.integral_comp' (fun z => (f z - θ.location) ^ 2)
  unfold _root_.GD.N0084.N0337.d022998
  rw [← hleft, ← hdist, ← hright]
  simpa only [_root_.GD.N0232.N0719.N0981.d020660, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hgap

theorem d023001 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ)
    (h2 : MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ))
    (hc2 : MemLp (_root_.GD.N0232.N0719.N0981.d020660 sizes f) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) :
    _root_.GD.N0084.N0337.d022998 sizes θ f = 0 ↔ _root_.GD.N0232.N0719.N0981.d020660 sizes f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  have hi : Integrable (fun z => (f z - _root_.GD.N0232.N0719.N0981.d020660 sizes f z) ^ 2) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    simpa only [Pi.sub_apply] using (h2.sub hc2).integrable_sq
  have hzero := integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (f z - _root_.GD.N0232.N0719.N0981.d020660 sizes f z)) hi
  constructor
  · intro hz
    have hae := hzero.mp hz
    filter_upwards [hae] with z hz
    have hsq : (f z - _root_.GD.N0232.N0719.N0981.d020660 sizes f z) ^ 2 = 0 := hz
    nlinarith
  · intro hae
    apply hzero.mpr
    filter_upwards [hae] with z hz
    simp [hz]


theorem d023002 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≠ ⊤) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  have h2 := _root_.GD.N0156.N0444.d020670 sizes f hf θ hfinite
  obtain ⟨hc2, hgap⟩ := _root_.GD.N0084.N0337.d023000 sizes hn f hf he θ h2
  have hnonneg := _root_.GD.N0084.N0337.d022999 sizes θ f
  rw [_root_.GD.N0156.N0444.d020671 sizes _ θ hc2, _root_.GD.N0156.N0444.d020671 sizes f θ h2]
  apply ENNReal.ofReal_le_ofReal
  linarith



theorem d023003 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≠ ⊤) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ↔
      _root_.GD.N0232.N0719.N0981.d020660 sizes f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  have h2 := _root_.GD.N0156.N0444.d020670 sizes f hf θ hfinite
  obtain ⟨hc2, hgap⟩ := _root_.GD.N0084.N0337.d023000 sizes hn f hf he θ h2
  constructor
  · intro heq
    rw [_root_.GD.N0156.N0444.d020671 sizes _ θ hc2, _root_.GD.N0156.N0444.d020671 sizes f θ h2] at heq
    have hcnn : 0 ≤ (∫ z, (_root_.GD.N0232.N0719.N0981.d020660 sizes f z - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) :=
      integral_nonneg (fun z => sq_nonneg (_root_.GD.N0232.N0719.N0981.d020660 sizes f z - θ.location))
    have hfnn : 0 ≤ (∫ z, (f z - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) :=
      integral_nonneg (fun z => sq_nonneg (f z - θ.location))
    have hreal := (ENNReal.ofReal_eq_ofReal_iff hcnn hfnn).mp heq
    have hzero : _root_.GD.N0084.N0337.d022998 sizes θ f = 0 := by
      rw [hreal] at hgap
      have hn := _root_.GD.N0084.N0337.d022999 sizes θ f
      linarith
    exact (_root_.GD.N0084.N0337.d023001 sizes θ f h2 hc2).mp hzero
  · exact fun hae => _root_.GD.N0232.N0719.N0896.d011094 k sizes θ hae

theorem d023004 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≠ ⊤) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ↔
      ¬ _root_.GD.N0232.N0719.N0981.d020660 sizes f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  have hle := _root_.GD.N0084.N0337.d023002 sizes hn f hf he θ hfinite
  rw [lt_iff_le_and_ne]
  simp only [hle, true_and]
  exact not_congr (_root_.GD.N0084.N0337.d023003 sizes hn f hf he θ hfinite)

theorem d023005 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≠ ⊤) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ↔
      0 < _root_.GD.N0084.N0337.d022998 sizes θ f := by
  have h2 := _root_.GD.N0156.N0444.d020670 sizes f hf θ hfinite
  have hc2 := (_root_.GD.N0084.N0337.d023000 sizes hn f hf he θ h2).1
  rw [_root_.GD.N0084.N0337.d023004 sizes hn f hf he θ hfinite]
  have hz := _root_.GD.N0084.N0337.d023001 sizes θ f h2 hc2
  constructor
  · intro hnot
    exact lt_of_le_of_ne (_root_.GD.N0084.N0337.d022999 sizes θ f) (fun h => hnot (hz.mp h.symm))
  · intro hpos hae
    exact (ne_of_gt hpos) (hz.mpr hae)



theorem d023006 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0084.N0337.d022997 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≠ ⊤) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ↔
      0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ {z | _root_.GD.N0232.N0719.N0981.d020660 sizes f z ≠ f z} := by
  rw [_root_.GD.N0084.N0337.d023004 sizes hn f hf he θ hfinite]
  simp only [Filter.EventuallyEq, ae_iff, pos_iff_ne_zero]

end
end GD.N0084.N0337

#print axioms _root_.GD.N0084.N0337.d023000
#print axioms _root_.GD.N0084.N0337.d023001
#print axioms _root_.GD.N0084.N0337.d023002
#print axioms _root_.GD.N0084.N0337.d023003
#print axioms _root_.GD.N0084.N0337.d023004
#print axioms _root_.GD.N0084.N0337.d023005
#print axioms _root_.GD.N0084.N0337.d023006
