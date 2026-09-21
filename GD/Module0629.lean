import GD.Module0621
import GD.Module0624
import GD.Module0287

















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0232.N0719

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0232.N0720



abbrev d009172 (k : ℕ) (sampleSize : Fin k → ℕ) :=
  ∀ i, _root_.GD.N0137.d008894 (sampleSize i)


abbrev d009173 (k : ℕ) (sampleSize : Fin k → ℕ) :=
  _root_.GD.N0232.N0719.d009172 k sampleSize




def d009174
    (n : ℕ) (location scale : ℝ) :
    Measure (_root_.GD.N0137.d008894 n) :=
  (_root_.GD.N0137.d008895 n).map (_root_.GD.N0107.d009018 n location scale)


abbrev d009175 := _root_.GD.N0232.N0719.d009174

noncomputable instance
    (n : ℕ) (location scale : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.d009174 n location scale) := by
  unfold _root_.GD.N0232.N0719.d009174
  exact Measure.isProbabilityMeasure_map
    (_root_.GD.N0107.d009020 n location scale).aemeasurable



def d009176
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ) :
    Measure (_root_.GD.N0232.N0719.d009172 k sampleSize) :=
  Measure.pi
    (fun i => _root_.GD.N0232.N0719.d009174 (sampleSize i) location (scale i))

noncomputable instance
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ) :
    IsProbabilityMeasure
      (_root_.GD.N0232.N0719.d009176 k sampleSize location scale) := by
  unfold _root_.GD.N0232.N0719.d009176
  infer_instance



theorem d009177
    (n : ℕ) (location scale : ℝ) :
    (_root_.GD.N0232.N0719.d009174 n 0 scale).map
        (_root_.GD.N0107.d009018 n location 1) =
      _root_.GD.N0232.N0719.d009174 n location scale := by
  unfold _root_.GD.N0232.N0719.d009174
  rw [Measure.map_map
    (_root_.GD.N0107.d009020 n location 1)
    (_root_.GD.N0107.d009020 n 0 scale)]
  congr 1
  funext z i
  simp [Function.comp_apply, _root_.GD.N0107.d009018]










theorem d009178
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.d009176 k sampleSize 0 scale).map
        (_root_.GD.N0232.N0719.N0900.d009095
          k sampleSize location 1) =
      _root_.GD.N0232.N0719.d009176 k sampleSize location scale := by
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N0900.d009095
  rw [Measure.pi_map_pi]
  · congr 1
    funext i
    exact _root_.GD.N0232.N0719.d009177
      (sampleSize i) location (scale i)
  · intro i
    exact (_root_.GD.N0107.d009020 (sampleSize i) location 1).aemeasurable



theorem d009179
    (n : ℕ)
    (location scale location' scale' : ℝ)
    (hscale : scale ≠ 0) (hscale' : scale' ≠ 0) :
    _root_.GD.N0232.N0719.d009174 n location scale ≪
      _root_.GD.N0232.N0719.d009174 n location' scale' :=
  (_root_.GD.N0232.N0720.d009059
      n location scale hscale).trans
    (_root_.GD.N0232.N0720.d009060
      n location' scale' hscale')


theorem d009180
    (n : ℕ)
    (location scale location' scale' : ℝ)
    (hscale : scale ≠ 0) (hscale' : scale' ≠ 0) :
    _root_.GD.N0232.N0719.d009175 n location scale ≪ _root_.GD.N0232.N0719.d009175 n location' scale' :=
  _root_.GD.N0232.N0719.d009179
    n location scale location' scale' hscale hscale'



theorem d009181
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location location' : ℝ)
    (scale scale' : Fin k → ℝ)
    (hscale : ∀ i, scale i ≠ 0)
    (hscale' : ∀ i, scale' i ≠ 0) :
    _root_.GD.N0232.N0719.d009176 k sampleSize location scale ≪
      _root_.GD.N0232.N0719.d009176 k sampleSize location' scale' := by
  unfold _root_.GD.N0232.N0719.d009176
  apply _root_.GD.N0235.d004256
  intro i
  exact _root_.GD.N0232.N0719.d009179
    (sampleSize i) location (scale i) location' (scale' i)
    (hscale i) (hscale' i)



def d009182
    (k : ℕ) (sampleSize : Fin k → ℕ) :
    Measure (_root_.GD.N0232.N0719.d009172 k sampleSize) :=
  _root_.GD.N0232.N0719.d009176 k sampleSize 0 (fun _ => 1)

noncomputable instance
    (k : ℕ) (sampleSize : Fin k → ℕ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.d009182 k sampleSize) := by
  unfold _root_.GD.N0232.N0719.d009182
  infer_instance



theorem d009183
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    (_root_.GD.N0232.N0719.d009176 k sampleSize location scale ≪
        _root_.GD.N0232.N0719.d009182 k sampleSize) ∧
      (_root_.GD.N0232.N0719.d009182 k sampleSize ≪
        _root_.GD.N0232.N0719.d009176 k sampleSize location scale) := by
  constructor
  · exact _root_.GD.N0232.N0719.d009181
      k sampleSize location 0 scale (fun _ => 1)
      (fun i => (hscale i).ne') (fun _ => one_ne_zero)
  · exact _root_.GD.N0232.N0719.d009181
      k sampleSize 0 location (fun _ => 1) scale
      (fun _ => one_ne_zero) (fun i => (hscale i).ne')



theorem d009184
    (k : ℕ) (sampleSize : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, 0 < scale i)
    {f g : _root_.GD.N0232.N0719.d009172 k sampleSize → ℝ} :
    f =ᵐ[_root_.GD.N0232.N0719.d009176 k sampleSize location scale] g ↔
      f =ᵐ[_root_.GD.N0232.N0719.d009182 k sampleSize] g := by
  rcases
      _root_.GD.N0232.N0719.d009183
        k sampleSize location scale hscale with
    ⟨hparameter, hreference⟩
  exact
    ⟨fun hfg => hreference.ae_eq hfg,
      fun hfg => hparameter.ae_eq hfg⟩

end

end GD.N0232.N0719
