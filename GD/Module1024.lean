import GD.Module1012
import Mathlib.MeasureTheory.Measure.OpenPos















open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1496

noncomputable section

open _root_.GD.N0232.N0720.N1493

attribute [local instance] Measure.Subtype.measureSpace

private abbrev d016281 :=
  {q : _root_.GD.N0232.N0719.N0857.d009377 2 //
    q ∈ _root_.GD.N0232.N0719.N0955.d009607 2}


def d016282 (z : Set.Ioo (0 : ℝ) 1) : _root_.GD.N0232.N0720.N1496.d016281 :=
  ⟨fun _ ↦ (z : ℝ), by
    constructor
    · intro j
      exact z.property.1
    · simpa using sub_pos.mpr z.property.2⟩

@[simp]
theorem d016283
    (z : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1493.d016102 (_root_.GD.N0232.N0720.N1496.d016282 z) = z := by
  apply Subtype.ext
  change
    _root_.GD.N0232.N0719.N0853.d009567
        (by norm_num : 0 < 2) (_root_.GD.N0232.N0720.N1496.d016282 z).1 0 = (z : ℝ)
  rw [show (0 : Fin 2) =
      _root_.GD.N0232.N0719.N0954.d009344 2
        (by norm_num) (Sum.inl 0) by rfl]
  rw [_root_.GD.N0232.N0719.N0853.d009568]
  rfl

theorem d016284 :
    Function.Surjective _root_.GD.N0232.N0720.N1493.d016102 := by
  intro z
  exact ⟨_root_.GD.N0232.N0720.N1496.d016282 z,
    _root_.GD.N0232.N0720.N1496.d016283 z⟩

private noncomputable instance d016285 :
    (volume : Measure _root_.GD.N0232.N0720.N1496.d016281).IsOpenPosMeasure := by
  exact Measure.IsOpenPosMeasure.comap
    (volume : Measure
      (_root_.GD.N0232.N0719.N0857.d009377 2))
    (_root_.GD.N0232.N0719.N0929.d009635 2).isOpenEmbedding_subtypeVal



noncomputable instance d016286 :
    _root_.GD.N0232.N0720.N1493.d016104.IsOpenPosMeasure := by
  unfold _root_.GD.N0232.N0720.N1493.d016104
  exact _root_.GD.N0232.N0720.N1493.d016103.isOpenPosMeasure_map
    _root_.GD.N0232.N0720.N1496.d016284

end

end N1496
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1496.d016284
#print axioms _root_.GD.N0232.N0720.N1496.d016286
