import GD.Module1664
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0033
noncomputable section
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0938 _root_.GD.N0232.N0719.N0877 _root_.GD.N0232.N0719.N0939

variable {k : ℕ}

theorem d028323 (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (h i : Fin k) (hi : 1 < shape i) :
    Integrable (fun a => _root_.GD.N0232.N0719.N0877.d020693 h a i) (_root_.GD.N0033.d028239 shape) := by
  let μ : Fin k → Measure ℝ := fun l => gammaMeasure (shape l) (shape l)
  letI (l : Fin k) : IsProbabilityMeasure (μ l) := isProbabilityMeasure_gammaMeasure (hs l) (hs l)
  by_cases hih : i = h
  · simp only [_root_.GD.N0232.N0719.N0877.d020693, if_pos hih]
    exact integrable_const 0
  · have hret : Integrable (fun a : Fin k → ℝ => a h) (_root_.GD.N0033.d028239 shape) :=
      (measurePreserving_eval μ h).integrable_comp_of_integrable
        (_root_.GD.N0232.N0719.N0877.d020694 (hs h) (hs h))
    have hinv : Integrable (fun a : Fin k → ℝ => (a i)⁻¹) (_root_.GD.N0033.d028239 shape) :=
      (measurePreserving_eval μ i).integrable_comp_of_integrable
        (_root_.GD.N0232.N0719.N0876.d020682 hi (hs i))
    have hind : IndepFun (fun a : Fin k → ℝ => a h) (fun a => (a i)⁻¹) (_root_.GD.N0033.d028239 shape) := by
      have hb : IndepFun (fun a : Fin k → ℝ => a h) (fun a => a i) (Measure.pi μ) :=
        (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun (Ne.symm hih)
      exact hb.comp measurable_id measurable_inv
    have hp := hind.integrable_mul hret hinv
    change Integrable (fun a => a h * (a i)⁻¹) (_root_.GD.N0033.d028239 shape) at hp
    simpa only [_root_.GD.N0232.N0719.N0877.d020693, if_neg hih, div_eq_mul_inv] using hp

theorem d028324
    (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (h i : Fin k) (hi : 1 < shape i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ l, _root_.GD.N0232.N0719.N0877.d020693 h a l)
      (_root_.GD.N0232.N0719.N0877.d020693 h a i) ∂_root_.GD.N0033.d028239 shape) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ l, _root_.GD.N0232.N0719.N0877.d020693 h a l)
      (_root_.GD.N0232.N0719.N0877.d020693 h a i) ∂_root_.GD.N0033.d028239 shape) atTop (𝓝 (∫ _a, (0 : ℝ) ∂_root_.GD.N0033.d028239 shape)) := by
    apply tendsto_integral_of_dominated_convergence (fun a => _root_.GD.N0232.N0719.N0877.d020693 h a i / 4)
    · intro n
      exact (_root_.GD.N0033.d028247 shape hs h i (he n)).aestronglyMeasurable
    · exact (_root_.GD.N0033.d028323 shape hs h i hi).div_const 4
    · intro n
      filter_upwards [_root_.GD.N0033.d028240 shape hs] with a ha
      have hnn : 0 ≤ _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ l, _root_.GD.N0232.N0719.N0877.d020693 h a l) (_root_.GD.N0232.N0719.N0877.d020693 h a i) := by
        unfold _root_.GD.N0232.N0719.N0938.d007528
        exact div_nonneg (mul_nonneg (he n).le (sq_nonneg _)) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact _root_.GD.N0232.N0719.N0938.d007529 (he n).le (_root_.GD.N0033.d028242 h a ha i)
        (Finset.single_le_sum (fun l _ => _root_.GD.N0033.d028242 h a ha l) (Finset.mem_univ i))
    · apply ae_of_all
      intro a
      have hd : Tendsto (fun n => 1 + e n * ∑ l, _root_.GD.N0232.N0719.N0877.d020693 h a l) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add (he0.mul_const (∑ l, _root_.GD.N0232.N0719.N0877.d020693 h a l))
      have ht := (he0.mul_const (_root_.GD.N0232.N0719.N0877.d020693 h a i ^ 2)).div (hd.pow 2)
        (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
      convert ht using 1
      · rfl
      · norm_num
  simpa using hh

def d028325 (shape : Fin k → ℝ) (h : Fin k) : ℝ :=
  ∑ i, if i ≠ h ∧ shape i = 1 then 1 else 0

theorem d028326 (shape : Fin k → ℝ) (h : Fin k) : 0 ≤ _root_.GD.N0033.d028325 shape h := by
  unfold _root_.GD.N0033.d028325
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

theorem d028327
    (shape : Fin (k + 1) → ℝ) (hs : ∀ i, 0 < shape i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 1 ≤ shape i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 h a) ∂_root_.GD.N0033.d028239 shape)
      atTop (𝓝 (1 + _root_.GD.N0033.d028325 shape h)) := by
  have hterm (i : Fin (k + 1)) : Tendsto (fun n => ∫ a,
      _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ l, _root_.GD.N0232.N0719.N0877.d020693 h a l) (_root_.GD.N0232.N0719.N0877.d020693 h a i) ∂_root_.GD.N0033.d028239 shape)
      atTop (𝓝 (if i ≠ h ∧ shape i = 1 then 1 else 0)) := by
    by_cases hih : i = h
    · subst i
      simp [_root_.GD.N0232.N0719.N0877.d020693, _root_.GD.N0232.N0719.N0938.d007528]
    · by_cases hi : shape i = 1
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hih)
        have hh := _root_.GD.N0033.d028252 shape hs i j hi e he he0
        simpa only [hj, if_pos (And.intro hih hi)] using hh
      · simpa only [if_neg (not_and.mpr fun _ => hi)] using
          _root_.GD.N0033.d028324 shape hs h i
            (lt_of_le_of_ne (hother i hih) (Ne.symm hi)) e he he0
  have hid (n : ℕ) : (∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 h a) ∂_root_.GD.N0033.d028239 shape) =
      (∫ a, _root_.GD.N0232.N0719.N0938.d007527 (e n) (∑ l, _root_.GD.N0232.N0719.N0877.d020693 h a l) ∂_root_.GD.N0033.d028239 shape) +
      ∑ i, ∫ a, _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ l, _root_.GD.N0232.N0719.N0877.d020693 h a l) (_root_.GD.N0232.N0719.N0877.d020693 h a i) ∂_root_.GD.N0033.d028239 shape := by
    simp only [_root_.GD.N0232.N0719.N0938.d007530]
    rw [integral_add (_root_.GD.N0033.d028244 shape hs h (he n).le)
      (integrable_finsetSum _ fun i _ => _root_.GD.N0033.d028247 shape hs h i (he n)),
      integral_finsetSum _ fun i _ => _root_.GD.N0033.d028247 shape hs h i (he n)]
  simp_rw [hid]
  exact (_root_.GD.N0033.d028245 shape hs h e (fun n => (he n).le) he0).add
    (tendsto_finsetSum Finset.univ fun i _ => hterm i)

def d028328 (sizes : Fin k → ℕ) : Fin k → ℝ :=
  fun i => ((sizes i - 1 : ℕ) : ℝ) / 2

def d028329 (sizes : Fin k → ℕ) (h : Fin k) : ℝ :=
  ∑ i, if i ≠ h ∧ sizes i = 3 then 1 else 0

theorem d028330 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    ∀ i, 0 < _root_.GD.N0033.d028328 sizes i := by
  intro i
  unfold _root_.GD.N0033.d028328
  have hh : 0 < sizes i - 1 := by have := hn i; omega
  exact div_pos (Nat.cast_pos.mpr hh) (by norm_num)

theorem d028331
    (sizes : Fin (k + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 3 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0972.d012340 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)) / e n)
      atTop (𝓝 (1 + _root_.GD.N0033.d028329 sizes h)) := by
  have hother' : ∀ i, i ≠ h → 1 ≤ _root_.GD.N0033.d028328 sizes i := by
    intro i hi
    have hnat : 2 ≤ sizes i - 1 := by have := hother i hi; omega
    have hreal : (2 : ℝ) ≤ (sizes i - 1 : ℕ) := by exact_mod_cast hnat
    unfold _root_.GD.N0033.d028328
    linarith
  have hcount : _root_.GD.N0033.d028325 (_root_.GD.N0033.d028328 sizes) h = _root_.GD.N0033.d028329 sizes h := by
    unfold _root_.GD.N0033.d028325 _root_.GD.N0033.d028329
    apply Finset.sum_congr rfl
    intro i _
    have heq : _root_.GD.N0033.d028328 sizes i = 1 ↔ sizes i = 3 := by
      unfold _root_.GD.N0033.d028328
      constructor
      · intro hh
        have hreal : ((sizes i - 1 : ℕ) : ℝ) = 2 := by linarith
        have hnat : sizes i - 1 = 2 := by exact_mod_cast hreal
        omega
      · intro hh
        norm_num [hh]
    simp only [heq]
  have hh := _root_.GD.N0033.d028327 (_root_.GD.N0033.d028328 sizes) (_root_.GD.N0033.d028330 sizes hn)
    h hother' e he he0
  rw [hcount] at hh
  convert hh using 1
  funext n
  rw [_root_.GD.N0232.N0719.N0939.d020708 sizes hn h (he n), mul_div_cancel_left₀ _ (he n).ne']
  rfl

theorem d028332
    (sizes : Fin (k + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 3 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)))
      atTop (𝓝 (1 / (1 + _root_.GD.N0033.d028329 sizes h))) := by
  have hb := _root_.GD.N0033.d028331 sizes hn h hother e he he0
  have ho : Tendsto (fun n =>
      (∑ i, (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)).scale i ^ 2)⁻¹ / e n)
      atTop (𝓝 1) := by
    have hd : Tendsto (fun n => 1 + (((k + 1 : ℕ) : ℝ) - 1) * e n) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (he0.const_mul (((k + 1 : ℕ) : ℝ) - 1))
    have hx := hd.inv₀ one_ne_zero
    simp only [inv_one] at hx
    convert hx using 1
    funext n
    rw [_root_.GD.N0232.N0719.N0939.d020710 sizes hn h (he n), div_right_comm, div_self (he n).ne', one_div]
  have hc : 0 ≤ _root_.GD.N0033.d028329 sizes h := by
    unfold _root_.GD.N0033.d028329
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hlim := ho.div hb (by linarith : 1 + _root_.GD.N0033.d028329 sizes h ≠ 0)
  convert hlim using 1
  funext n
  exact (div_div_div_cancel_right₀ (he n).ne' _ _).symm



theorem d028333
    (sizes : Fin (k + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 3 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n))) atTop (𝓝 1) ↔
      ∀ i, i ≠ h → 4 ≤ sizes i := by
  constructor
  · intro hsat i hi
    by_contra hn4
    have hi3 : sizes i = 3 := by have := hother i hi; omega
    have hc1 : (1 : ℝ) ≤ _root_.GD.N0033.d028329 sizes h := by
      have hh := Finset.single_le_sum
        (s := Finset.univ) (f := fun j : Fin (k + 1) => if j ≠ h ∧ sizes j = 3 then (1 : ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
      simpa only [if_pos (And.intro hi hi3), _root_.GD.N0033.d028329] using hh
    have heq := tendsto_nhds_unique
      (_root_.GD.N0033.d028332 sizes hn h hother e he he0) hsat
    have heq' := (div_eq_iff (by linarith : 1 + _root_.GD.N0033.d028329 sizes h ≠ 0)).mp heq
    linarith
  · intro hn4
    exact _root_.GD.N0232.N0719.N0939.d020711 sizes hn h hn4 e he he0



theorem d028334
    (sizes : Fin (k + 1) → ℕ) (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 3 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 (k + 1) sizes → ℝ) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 1) sizes θ f ≤
      ENNReal.ofReal (c * _root_.GD.N0232.N0719.N0972.d012340 (k + 1) sizes θ)) :
    1 / (1 + _root_.GD.N0033.d028329 sizes h) ≤ c := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n := fun n => by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto (_root_.GD.N0033.d028332 sizes hn h hother e he he0)
    (Eventually.of_forall fun n => _root_.GD.N0232.N0719.N0941.d020688
      (k + 1) sizes hk hn f hf c hc hb (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)))

end
end GD.N0033

#print axioms _root_.GD.N0033.d028324
#print axioms _root_.GD.N0033.d028327
#print axioms _root_.GD.N0033.d028331
#print axioms _root_.GD.N0033.d028332
#print axioms _root_.GD.N0033.d028333
#print axioms _root_.GD.N0033.d028334
