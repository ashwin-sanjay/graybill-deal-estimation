import GD.Module1012























open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1495

noncomputable section

open _root_.GD.N0232.N0720.N1493

attribute [local instance] Measure.Subtype.measureSpace

private abbrev d016115 :=
  _root_.GD.N0232.N0719.N0857.d009377 2

private abbrev d016116 :=
  {q : _root_.GD.N0232.N0720.N1495.d016115 //
    q ∈ _root_.GD.N0232.N0719.N0955.d009607 2}

private def d016117 : _root_.GD.N0232.N0720.N1495.d016115 ≃ᵐ ℝ :=
  MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℝ)



private theorem d016118 :
    _root_.GD.N0232.N0720.N1495.d016117 ⁻¹' Set.Ioo (0 : ℝ) 1 =
      _root_.GD.N0232.N0719.N0955.d009607 2 := by
  ext q
  simp [_root_.GD.N0232.N0720.N1495.d016117,
    _root_.GD.N0232.N0719.N0955.d009607]



private theorem d016119
    (q : _root_.GD.N0232.N0720.N1495.d016116) :
    ((_root_.GD.N0232.N0720.N1493.d016102 q : Set.Ioo (0 : ℝ) 1) : ℝ) =
      _root_.GD.N0232.N0720.N1495.d016117 q.1 := by
  change
    _root_.GD.N0232.N0719.N0853.d009567
        (by norm_num : 0 < 2) q.1 0 = q.1 default
  rw [show (0 : Fin 2) =
      _root_.GD.N0232.N0719.N0954.d009344 2
        (by norm_num) (Sum.inl default) by rfl]
  rw [_root_.GD.N0232.N0719.N0853.d009568]



theorem d016120 :
    _root_.GD.N0232.N0720.N1493.d016104 =
      (volume : Measure (Set.Ioo (0 : ℝ) 1)) := by
  let e : _root_.GD.N0232.N0720.N1495.d016115 ≃ᵐ ℝ := _root_.GD.N0232.N0720.N1495.d016117
  let S : Set _root_.GD.N0232.N0720.N1495.d016115 :=
    _root_.GD.N0232.N0719.N0955.d009607 2
  let T : Set ℝ := Set.Ioo (0 : ℝ) 1
  have hS : MeasurableSet S :=
    _root_.GD.N0232.N0719.N0955.d009608 2
  have hT : MeasurableSet T := measurableSet_Ioo
  have hpreimage : e ⁻¹' T = S := by
    simpa [e, S, T] using _root_.GD.N0232.N0720.N1495.d016118
  have hmp : MeasurePreserving e (volume : Measure _root_.GD.N0232.N0720.N1495.d016115)
      (volume : Measure ℝ) := by
    simpa [e, _root_.GD.N0232.N0720.N1495.d016117] using
      (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℝ))
  have hfraction :
      (fun q : _root_.GD.N0232.N0720.N1495.d016116 ↦
          ((_root_.GD.N0232.N0720.N1493.d016102 q : Set.Ioo (0 : ℝ) 1) : ℝ)) =
        e ∘ ((↑) : _root_.GD.N0232.N0720.N1495.d016116 → _root_.GD.N0232.N0720.N1495.d016115) := by
    funext q
    simpa [e, Function.comp_def] using _root_.GD.N0232.N0720.N1495.d016119 q
  apply (MeasurableEmbedding.subtype_coe hT).map_injective
  calc
    (_root_.GD.N0232.N0720.N1493.d016104.map
        ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)) =
        (volume : Measure _root_.GD.N0232.N0720.N1495.d016116).map
          (fun q ↦ ((_root_.GD.N0232.N0720.N1493.d016102 q : Set.Ioo (0 : ℝ) 1) : ℝ)) := by
      rw [_root_.GD.N0232.N0720.N1493.d016104, Measure.map_map
        measurable_subtype_coe _root_.GD.N0232.N0720.N1493.d016103.measurable]
      rfl
    _ = (volume : Measure _root_.GD.N0232.N0720.N1495.d016116).map
          (e ∘ ((↑) : _root_.GD.N0232.N0720.N1495.d016116 → _root_.GD.N0232.N0720.N1495.d016115)) := by
      rw [hfraction]
    _ = ((volume : Measure _root_.GD.N0232.N0720.N1495.d016116).map
          ((↑) : _root_.GD.N0232.N0720.N1495.d016116 → _root_.GD.N0232.N0720.N1495.d016115)).map e := by
      rw [Measure.map_map e.measurable measurable_subtype_coe]
    _ = ((volume : Measure _root_.GD.N0232.N0720.N1495.d016115).restrict S).map e := by
      rw [MeasurableSet.map_coe_volume hS]
    _ = ((volume : Measure _root_.GD.N0232.N0720.N1495.d016115).map e).restrict T := by
      rw [e.restrict_map, hpreimage]
    _ = (volume : Measure ℝ).restrict T := by
      rw [hmp.map_eq]
    _ = (volume : Measure (Set.Ioo (0 : ℝ) 1)).map
          ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ) := by
      exact (MeasurableSet.map_coe_volume hT).symm

end

end N1495
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1495.d016120
