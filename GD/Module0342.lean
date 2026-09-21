import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0024.N0264

open MeasureTheory Filter
open scoped Topology

noncomputable def d005086 (t U V : ℝ) : ℝ :=
  t * (1 - t) * (V - U) ^ 2 / ((1 - t) * U + t * V) ^ 2

noncomputable def d005087 (U V : ℝ) : ℝ :=
  (V / U + U / V - 2) / 4

theorem d005088 (U V : ℝ) (hU : 0 < U) (hV : 0 < V) :
    _root_.GD.N0024.N0264.d005087 U V = (V - U) ^ 2 / (4 * U * V) := by
  unfold _root_.GD.N0024.N0264.d005087
  field_simp [ne_of_gt hU, ne_of_gt hV]
  ring

theorem d005089 (U V : ℝ) (hU : 0 < U) (hV : 0 < V) :
    0 ≤ _root_.GD.N0024.N0264.d005087 U V := by
  rw [_root_.GD.N0024.N0264.d005088 U V hU hV]
  positivity

theorem d005090 (t U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < (1 - t) * U + t * V := by
  rcases lt_or_eq_of_le ht1 with ht | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) hU)
      (mul_nonneg ht0 (le_of_lt hV))
  · simpa using hV

theorem d005091 (t U V : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ _root_.GD.N0024.N0264.d005086 t U V := by
  unfold _root_.GD.N0024.N0264.d005086
  exact div_nonneg
    (mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sq_nonneg _)) (sq_nonneg _)

theorem d005092 (t U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : _root_.GD.N0024.N0264.d005086 t U V ≤ _root_.GD.N0024.N0264.d005087 U V := by
  have hd : 0 < ((1 - t) * U + t * V) ^ 2 :=
    sq_pos_of_pos (_root_.GD.N0024.N0264.d005090 t U V hU hV ht0 ht1)
  have hUV : 0 < 4 * U * V := by positivity
  rw [_root_.GD.N0024.N0264.d005088 U V hU hV]
  unfold _root_.GD.N0024.N0264.d005086
  apply (div_le_div_iff₀ hd hUV).mpr
  have h := mul_nonneg (sq_nonneg (V - U)) (sq_nonneg ((1 - t) * U - t * V))
  nlinarith

theorem d005093 (t U V : ℝ) : _root_.GD.N0024.N0264.d005086 (1 - t) V U = _root_.GD.N0024.N0264.d005086 t U V := by
  unfold _root_.GD.N0024.N0264.d005086
  congr 1 <;> ring

@[simp] theorem d005094 (U V : ℝ) : _root_.GD.N0024.N0264.d005086 0 U V = 0 := by
  simp [_root_.GD.N0024.N0264.d005086]

@[simp] theorem d005095 (U V : ℝ) : _root_.GD.N0024.N0264.d005086 1 U V = 0 := by
  simp [_root_.GD.N0024.N0264.d005086]

theorem d005096 (U V : ℝ) (hU : U ≠ 0) :
    ContinuousAt (fun t => _root_.GD.N0024.N0264.d005086 t U V) 0 := by
  unfold _root_.GD.N0024.N0264.d005086
  fun_prop (disch := simp [hU])

theorem d005097 (U V : ℝ) (hV : V ≠ 0) :
    ContinuousAt (fun t => _root_.GD.N0024.N0264.d005086 t U V) 1 := by
  unfold _root_.GD.N0024.N0264.d005086
  fun_prop (disch := simp [hV])

theorem d005098 {ι : Type*} {l : Filter ι} (t : ι → ℝ)
    (U V : ℝ) (hU : U ≠ 0) (ht : Tendsto t l (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0024.N0264.d005086 (t n) U V) l (𝓝 0) := by
  simpa only [Function.comp_def, _root_.GD.N0024.N0264.d005094] using (_root_.GD.N0024.N0264.d005096 U V hU).tendsto.comp ht

theorem d005099 {ι : Type*} {l : Filter ι} (t : ι → ℝ)
    (U V : ℝ) (hV : V ≠ 0) (ht : Tendsto t l (𝓝 1)) :
    Tendsto (fun n => _root_.GD.N0024.N0264.d005086 (t n) U V) l (𝓝 0) := by
  simpa only [Function.comp_def, _root_.GD.N0024.N0264.d005095] using (_root_.GD.N0024.N0264.d005097 U V hV).tendsto.comp ht

section Integral

variable {Ω : Type*} [MeasurableSpace Ω]

theorem d005100 (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (t : ℝ) : Measurable (fun z => _root_.GD.N0024.N0264.d005086 t (U z) (V z)) := by
  unfold _root_.GD.N0024.N0264.d005086
  fun_prop

theorem d005101
    (ν : Measure Ω) [IsFiniteMeasure ν] (U V : Ω → ℝ)
    (hVU : Integrable (fun z => V z / U z) ν)
    (hUV : Integrable (fun z => U z / V z) ν) :
    Integrable (fun z => _root_.GD.N0024.N0264.d005087 (U z) (V z)) ν := by
  exact ((hVU.add hUV).sub (integrable_const (2 : ℝ))).div_const 4

theorem d005102
    (ν : Measure Ω) (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hpos : ∀ᵐ z ∂ν, 0 < U z ∧ 0 < V z)
    (henv : Integrable (fun z => _root_.GD.N0024.N0264.d005087 (U z) (V z)) ν)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun z => _root_.GD.N0024.N0264.d005086 t (U z) (V z)) ν := by
  apply henv.mono' (_root_.GD.N0024.N0264.d005100 U V hU hV t).aestronglyMeasurable
  filter_upwards [hpos] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0024.N0264.d005091 t (U z) (V z) ht0 ht1)]
  exact _root_.GD.N0024.N0264.d005092 t (U z) (V z) hz.1 hz.2 ht0 ht1

theorem d005103
    (ν : Measure Ω) (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hpos : ∀ᵐ z ∂ν, 0 < U z ∧ 0 < V z)
    (henv : Integrable (fun z => _root_.GD.N0024.N0264.d005087 (U z) (V z)) ν)
    (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, _root_.GD.N0024.N0264.d005086 (t n) (U z) (V z) ∂ν) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (fun z => _root_.GD.N0024.N0264.d005087 (U z) (V z))
    (fun n => (_root_.GD.N0024.N0264.d005100 U V hU hV (t n)).aestronglyMeasurable) henv
    (fun n => ?_) (f := fun _ => (0 : ℝ)) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [hpos] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0024.N0264.d005091 (t n) (U z) (V z) (ht0 n) (ht1 n))]
    exact _root_.GD.N0024.N0264.d005092 (t n) (U z) (V z) hz.1 hz.2 (ht0 n) (ht1 n)
  · filter_upwards [hpos] with z hz
    exact _root_.GD.N0024.N0264.d005098 t (U z) (V z) (ne_of_gt hz.1) ht

theorem d005104
    (ν : Measure Ω) (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hpos : ∀ᵐ z ∂ν, 0 < U z ∧ 0 < V z)
    (henv : Integrable (fun z => _root_.GD.N0024.N0264.d005087 (U z) (V z)) ν)
    (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1)
    (ht : Tendsto t atTop (𝓝 1)) :
    Tendsto (fun n => ∫ z, _root_.GD.N0024.N0264.d005086 (t n) (U z) (V z) ∂ν) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (fun z => _root_.GD.N0024.N0264.d005087 (U z) (V z))
    (fun n => (_root_.GD.N0024.N0264.d005100 U V hU hV (t n)).aestronglyMeasurable) henv
    (fun n => ?_) (f := fun _ => (0 : ℝ)) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [hpos] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0024.N0264.d005091 (t n) (U z) (V z) (ht0 n) (ht1 n))]
    exact _root_.GD.N0024.N0264.d005092 (t n) (U z) (V z) hz.1 hz.2 (ht0 n) (ht1 n)
  · filter_upwards [hpos] with z hz
    exact _root_.GD.N0024.N0264.d005099 t (U z) (V z) (ne_of_gt hz.2) ht

end Integral

#print axioms _root_.GD.N0024.N0264.d005088
#print axioms _root_.GD.N0024.N0264.d005089
#print axioms _root_.GD.N0024.N0264.d005090
#print axioms _root_.GD.N0024.N0264.d005091
#print axioms _root_.GD.N0024.N0264.d005092
#print axioms _root_.GD.N0024.N0264.d005093
#print axioms _root_.GD.N0024.N0264.d005094
#print axioms _root_.GD.N0024.N0264.d005095
#print axioms _root_.GD.N0024.N0264.d005096
#print axioms _root_.GD.N0024.N0264.d005097
#print axioms _root_.GD.N0024.N0264.d005098
#print axioms _root_.GD.N0024.N0264.d005099
#print axioms _root_.GD.N0024.N0264.d005100
#print axioms _root_.GD.N0024.N0264.d005101
#print axioms _root_.GD.N0024.N0264.d005102
#print axioms _root_.GD.N0024.N0264.d005103
#print axioms _root_.GD.N0024.N0264.d005104

end GD.N0024.N0264
