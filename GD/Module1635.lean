import GD.Module1518

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0074

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0845

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d027952 (b a : ℝ) (ha : 0 < a) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 b a) a⁻¹ (inv_pos.mpr ha) θ)) := by
  refine ⟨_root_.GD.N0232.N0719.N0842.d010908 k sizes b a, ?_⟩
  exact _root_.GD.N0232.N0719.d009188 k sizes (_root_.GD.N0232.N0719.N0842.d010906 b a) a⁻¹ θ.location θ.scale

theorem d027953 (b a : ℝ) (ha : 0 < a)
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp (_root_.GD.N0232.N0719.N0842.d010911 k sizes b a f) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by unfold _root_.GD.N0232.N0719.N0859.d010812; infer_instance
  exact (memLp_const b).add (((hf _).comp_measurePreserving
    (_root_.GD.N0074.d027952 k sizes b a ha θ)).const_mul a)

theorem d027954 (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) :
    MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := hf (_root_.GD.N0232.N0719.N0859.d010810 k)

def d027955 (b a : ℝ) (ha : 0 < a)
    (d : _root_.GD.N0074.d023612 k sizes) : _root_.GD.N0074.d023612 k sizes := by
  let f := _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (d.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
  have hf := _root_.GD.N0074.d027953 k sizes b a ha _ d.property
  let hf₀ := _root_.GD.N0074.d027954 k sizes f hf
  refine ⟨hf₀.toLp f, fun θ => ?_⟩
  exact (memLp_congr_ae ((_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le
    hf₀.coeFn_toLp)).mpr (hf θ)

theorem d027956 (b a : ℝ) (ha : 0 < a) (d : _root_.GD.N0074.d023612 k sizes)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ((_root_.GD.N0074.d027955 k sizes b a ha d).val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
      _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (d.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) :=
  (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le
    (_root_.GD.N0074.d027954 k sizes _ (_root_.GD.N0074.d027953 k sizes b a ha _ d.property)).coeFn_toLp

theorem d027957 (b a : ℝ) (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  (_root_.GD.N0074.d027952 k sizes b a ha (_root_.GD.N0232.N0719.N0859.d010810 k)).quasiMeasurePreserving.mono_right
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes _)

end
end GD.N0074

#print axioms _root_.GD.N0074.d027953
#print axioms _root_.GD.N0074.d027956
#print axioms _root_.GD.N0074.d027957
