import GD.Module0488
import GD.Module1323
import GD.Module0708
import Mathlib.Probability.Independence.Integration






set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace GD.N0232.N0719.N0877
noncomputable section
open _root_.GD.N0232.N0719.N0938 _root_.GD.N0232.N0719.N0876 _root_.GD.N0232.N0719.N0910
open _root_.GD.N0232.N0719.N0924 (d010432)

variable {k : ℕ}

def d020693 (h : Fin k) (a : Fin k → ℝ) (i : Fin k) : ℝ :=
  if i = h then 0 else a h / a i



theorem d020694 {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (gammaMeasure a r) := by
  letI := isProbabilityMeasure_gammaMeasure ha hr
  have h2 : MemLp (fun x : ℝ => x) 2 (gammaMeasure a r) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (_root_.GD.N0232.N0719.N0924.d010432 ha hr)
  exact h2.integrable (by norm_num)



theorem d020695
    (shape rate : Fin k → ℝ) (hs : ∀ i, 0 < shape i) (hr : ∀ i, 0 < rate i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 1 < shape i) (i : Fin k) :
    Integrable (fun a => _root_.GD.N0232.N0719.N0877.d020693 h a i)
      (Measure.pi fun j => gammaMeasure (shape j) (rate j)) := by
  let μ := fun j => gammaMeasure (shape j) (rate j)
  letI (j : Fin k) : IsProbabilityMeasure (μ j) := isProbabilityMeasure_gammaMeasure (hs j) (hr j)
  by_cases hi : i = h
  · simp only [_root_.GD.N0232.N0719.N0877.d020693, if_pos hi]
    exact integrable_const 0
  · have hret : Integrable (fun a : Fin k → ℝ => a h) (Measure.pi μ) :=
      (measurePreserving_eval μ h).integrable_comp_of_integrable
        (_root_.GD.N0232.N0719.N0877.d020694 (hs h) (hr h))
    have hinv : Integrable (fun a : Fin k → ℝ => (a i)⁻¹) (Measure.pi μ) :=
      (measurePreserving_eval μ i).integrable_comp_of_integrable
        (_root_.GD.N0232.N0719.N0876.d020682 (hother i hi) (hr i))
    have hind : IndepFun (fun a : Fin k → ℝ => a h) (fun a => (a i)⁻¹) (Measure.pi μ) := by
      have hb : IndepFun (fun a : Fin k → ℝ => a h) (fun a => a i) (Measure.pi μ) :=
        (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun (Ne.symm hi)
      exact hb.comp measurable_id measurable_inv
    have hp := hind.integrable_mul hret hinv
    change Integrable (fun a => a h * (a i)⁻¹) (Measure.pi μ) at hp
    simpa only [_root_.GD.N0232.N0719.N0877.d020693, if_neg hi, div_eq_mul_inv, μ] using hp

theorem d020696
    (shape rate : Fin k → ℝ) (hs : ∀ i, 0 < shape i) (hr : ∀ i, 0 < rate i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 1 < shape i)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 h a)
      ∂(Measure.pi fun j => gammaMeasure (shape j) (rate j))) atTop (𝓝 1) := by
  let μ := fun j => gammaMeasure (shape j) (rate j)
  letI (j : Fin k) : IsProbabilityMeasure (μ j) := isProbabilityMeasure_gammaMeasure (hs j) (hr j)
  apply _root_.GD.N0232.N0719.N0938.d007534 (Measure.pi μ) (fun i a => _root_.GD.N0232.N0719.N0877.d020693 h a i)
  · intro i
    unfold _root_.GD.N0232.N0719.N0877.d020693
    split_ifs <;> fun_prop
  · have hpos : ∀ᵐ a ∂Measure.pi μ, ∀ i, 0 < a i := _root_.GD.N0232.N0719.N0910.d010287 hs hr
    filter_upwards [hpos] with a ha
    intro i
    unfold _root_.GD.N0232.N0719.N0877.d020693
    split_ifs
    · exact le_rfl
    · exact (div_pos (ha h) (ha i)).le
  · exact _root_.GD.N0232.N0719.N0877.d020695 shape rate hs hr h hother
  · exact he
  · exact he0


theorem d020697
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 h a)
      ∂(Measure.pi fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
        (((sizes j - 1 : ℕ) : ℝ) / 2))) atTop (𝓝 1) := by
  have hs (j : Fin k) : 0 < (((sizes j - 1 : ℕ) : ℝ) / 2) := by
    have hj : 0 < sizes j - 1 := by have := hn j; omega
    exact div_pos (Nat.cast_pos.mpr hj) (by norm_num)
  apply _root_.GD.N0232.N0719.N0877.d020696 _ _ hs hs h _ e he he0
  intro i hi
  have hnat : 2 < sizes i - 1 := by have := hother i hi; omega
  have hreal : (2 : ℝ) < (sizes i - 1 : ℕ) := by exact_mod_cast hnat
  linarith

end
end GD.N0232.N0719.N0877

#print axioms _root_.GD.N0232.N0719.N0877.d020695
#print axioms _root_.GD.N0232.N0719.N0877.d020696
#print axioms _root_.GD.N0232.N0719.N0877.d020697
