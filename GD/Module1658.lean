import GD.Module1657
import GD.Module0809

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

namespace GD.N0097

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0962

noncomputable section

variable {k : ℕ} (sizes : Fin k → ℕ)

def d028173 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : Prop :=
  ∀ t : ℝ, ∀ z, f (fun i j => t + z i j) = t + f z

def d028174 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (t : ℝ) : Prop :=
  (fun z => f (fun i j => t + z i j)) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
    fun z => t + f z

theorem d028175 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (t : ℝ) :
    _root_.GD.N0097.d028164 sizes t f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] f ↔
      _root_.GD.N0097.d028174 sizes f t := by
  constructor
  · intro h
    have hpull := (_root_.GD.N0232.N0719.N0896.d011119 k sizes t 1 zero_lt_one).ae_eq h
    filter_upwards [hpull] with z hz
    change _root_.GD.N0097.d028164 sizes t f (_root_.GD.N0232.N0719.N0900.d009095 k sizes t 1 z) =
      f (_root_.GD.N0232.N0719.N0900.d009095 k sizes t 1 z) at hz
    rw [_root_.GD.N0097.d028164, _root_.GD.N0232.N0719.N0842.d010913 k sizes t 1 one_ne_zero f z] at hz
    have hobs : _root_.GD.N0232.N0719.N0900.d009095 k sizes t 1 z =
        (fun i j => t + z i j) := by
      ext i j
      change t + 1 * z i j = t + z i j
      ring
    rw [hobs] at hz
    simpa only [one_mul] using hz.symm
  · intro h
    have hpull := (_root_.GD.N0232.N0719.N0896.d011119 k sizes (-t) 1 zero_lt_one).ae_eq h
    filter_upwards [hpull] with z hz
    simpa [_root_.GD.N0097.d028164, _root_.GD.N0232.N0719.N0842.d010911, _root_.GD.N0232.N0719.N0842.d010907, _root_.GD.N0232.N0719.N0842.d010906,
      _root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018, Function.comp_def, add_assoc]
      using hz.symm

private abbrev d028176 := Multiplicative ℝ

local instance d028177 : MeasurableSpace _root_.GD.N0097.d028176 :=
  inferInstanceAs (MeasurableSpace ℝ)

local instance d028178 : MeasurableInv _root_.GD.N0097.d028176 where
  measurable_inv := by
    change Measurable (fun t : ℝ => -t)
    fun_prop

local instance d028179 : MulAction _root_.GD.N0097.d028176 ℝ where
  smul t y := t.toAdd + y
  one_smul y := zero_add y
  mul_smul s t y := add_assoc s.toAdd t.toAdd y

local instance d028180 : MulAction _root_.GD.N0097.d028176
    (_root_.GD.N0232.N0719.N0859.d010811 k sizes) where
  smul t z := fun i j => t.toAdd + z i j
  one_smul z := by ext i j; exact zero_add _
  mul_smul s t z := by ext i j; exact add_assoc _ _ _

local instance d028181 : MeasurableSMul₂ _root_.GD.N0097.d028176 ℝ where
  measurable_smul := by
    change Measurable (fun z : ℝ × ℝ => z.1 + z.2)
    fun_prop

local instance d028182 : MeasurableSMul₂ _root_.GD.N0097.d028176
    (_root_.GD.N0232.N0719.N0859.d010811 k sizes) where
  measurable_smul := by
    change Measurable (fun z : ℝ × _root_.GD.N0232.N0719.N0859.d010811 k sizes =>
      fun i j => z.1 + z.2 i j)
    fun_prop

private def d028183 : Measure _root_.GD.N0097.d028176 := gaussianReal 0 1

local instance d028184 : IsProbabilityMeasure _root_.GD.N0097.d028183 := by
  change IsProbabilityMeasure (gaussianReal 0 1)
  infer_instance

private theorem d028185 (h : _root_.GD.N0097.d028176) :
    Measure.QuasiMeasurePreserving (fun g : _root_.GD.N0097.d028176 => g * h)
      _root_.GD.N0097.d028183 _root_.GD.N0097.d028183 := by
  change Measure.QuasiMeasurePreserving (fun g : ℝ => g + h.toAdd)
    (gaussianReal 0 1) (gaussianReal 0 1)
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_add_const, zero_add]
  exact (gaussianReal_absolutelyContinuous h.toAdd one_ne_zero).trans
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero)

local instance d028186 : IsProbabilityMeasure
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813 _root_.GD.N0232.N0719.d009182
  infer_instance




theorem d028187
    (hk : 0 < k) (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (hcov : ∀ t : ℝ, _root_.GD.N0097.d028174 sizes f t) :
    ∃ g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable g ∧ _root_.GD.N0097.d028173 sizes g ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, g =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  let i : Fin k := ⟨0, hk⟩
  let j : Fin (sizes i) := ⟨0, hn i⟩
  let fallback : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ := fun z => z i j
  have hfb : Measurable fallback := by unfold fallback; fun_prop
  obtain ⟨g, hg, hgf, hge⟩ :=
    _root_.GD.N0230.N0605.d000343
      (G := _root_.GD.N0097.d028176) (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      _root_.GD.N0097.d028183 f fallback hf hfb (fun _ _ => rfl)
      (fun t => hcov t.toAdd) _root_.GD.N0097.d028185
  refine ⟨g, hg, ?_, fun θ => (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hgf⟩
  intro t z
  exact hge (Multiplicative.ofAdd t) z

end
end GD.N0097

#print axioms _root_.GD.N0097.d028175
#print axioms _root_.GD.N0097.d028187
