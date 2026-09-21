import GD.Module1663

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0033
noncomputable section
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0938 _root_.GD.N0232.N0719.N0877 _root_.GD.N0232.N0719.N0939
open _root_.GD.N0213.N0527
open _root_.GD.N0213.N0488 (d028223)

variable {k : ℕ}

abbrev d028239 (shape : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (shape i) (shape i)

theorem d028240 (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i) :
    ∀ᵐ a ∂_root_.GD.N0033.d028239 shape, ∀ i, 0 < a i :=
  _root_.GD.N0232.N0719.N0910.d010287 hs hs

@[fun_prop] theorem d028241 (h i : Fin k) : Measurable (fun a => _root_.GD.N0232.N0719.N0877.d020693 h a i) := by
  unfold _root_.GD.N0232.N0719.N0877.d020693
  split_ifs <;> fun_prop

theorem d028242 (h : Fin k) (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0719.N0877.d020693 h a i := by
  intro i
  unfold _root_.GD.N0232.N0719.N0877.d020693
  split_ifs
  · exact le_rfl
  · exact (div_pos (ha h) (ha i)).le

theorem d028243 {e : ℝ} (he : 0 ≤ e) (h : Fin k)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    0 ≤ _root_.GD.N0232.N0719.N0938.d007527 e (∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i) ∧
    _root_.GD.N0232.N0719.N0938.d007527 e (∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i) ≤ 1 := by
  have hB : 0 ≤ ∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i := Finset.sum_nonneg fun i _ => _root_.GD.N0033.d028242 h a ha i
  have hinv : (1 + e * ∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_right (mul_nonneg he hB))
  have hpos : 0 ≤ (1 + e * ∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i)⁻¹ := by positivity
  exact ⟨sq_nonneg _, by unfold _root_.GD.N0232.N0719.N0938.d007527; nlinarith⟩

theorem d028244 (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (h : Fin k) {e : ℝ} (he : 0 ≤ e) :
    Integrable (fun a => _root_.GD.N0232.N0719.N0938.d007527 e (∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i)) (_root_.GD.N0033.d028239 shape) := by
  letI (i : Fin k) : IsProbabilityMeasure (gammaMeasure (shape i) (shape i)) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  apply (integrable_const 1).mono'
  · have hm : Measurable (fun a => _root_.GD.N0232.N0719.N0938.d007527 e (∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i)) := by
      unfold _root_.GD.N0232.N0719.N0938.d007527
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [_root_.GD.N0033.d028240 shape hs] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0033.d028243 he h a ha).1]
    exact (_root_.GD.N0033.d028243 he h a ha).2

theorem d028245 (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (h : Fin k) (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007527 (e n) (∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i) ∂_root_.GD.N0033.d028239 shape)
      atTop (𝓝 1) := by
  letI (i : Fin k) : IsProbabilityMeasure (gammaMeasure (shape i) (shape i)) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  have hh : Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007527 (e n) (∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i) ∂_root_.GD.N0033.d028239 shape)
      atTop (𝓝 (∫ _a, (1 : ℝ) ∂_root_.GD.N0033.d028239 shape)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n
      exact (_root_.GD.N0033.d028244 shape hs h (he n)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [_root_.GD.N0033.d028240 shape hs] with a ha
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0033.d028243 (he n) h a ha).1]
      exact (_root_.GD.N0033.d028243 (he n) h a ha).2
    · apply ae_of_all
      intro a
      have hd : Tendsto (fun n => 1 + e n * ∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add (he0.mul_const (∑ i, _root_.GD.N0232.N0719.N0877.d020693 h a i))
      simpa only [_root_.GD.N0232.N0719.N0938.d007527, inv_one, one_pow] using (hd.inv₀ one_ne_zero).pow 2
  simpa [_root_.GD.N0033.d028239] using hh

theorem d028246 {e B q : ℝ} (he : 0 < e) (hq : 0 ≤ q) (hBq : q ≤ B) :
    _root_.GD.N0232.N0719.N0938.d007528 e B q ≤ 1 / e := by
  have hB : 0 ≤ B := hq.trans hBq
  have hd : 0 < 1 + e * B := by positivity
  have hh : (e * q) ^ 2 ≤ (1 + e * B) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg he.le hq) (by nlinarith) 2
  unfold _root_.GD.N0232.N0719.N0938.d007528
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) he).mpr
  nlinarith

theorem d028247 (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (h i : Fin k) {e : ℝ} (he : 0 < e) :
    Integrable (fun a => _root_.GD.N0232.N0719.N0938.d007528 e (∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j) (_root_.GD.N0232.N0719.N0877.d020693 h a i)) (_root_.GD.N0033.d028239 shape) := by
  letI (i : Fin k) : IsProbabilityMeasure (gammaMeasure (shape i) (shape i)) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  apply (integrable_const (1 / e)).mono'
  · have hm : Measurable (fun a => _root_.GD.N0232.N0719.N0938.d007528 e (∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j) (_root_.GD.N0232.N0719.N0877.d020693 h a i)) := by
      unfold _root_.GD.N0232.N0719.N0938.d007528
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [_root_.GD.N0033.d028240 shape hs] with a ha
    have hnn : 0 ≤ _root_.GD.N0232.N0719.N0938.d007528 e (∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j) (_root_.GD.N0232.N0719.N0877.d020693 h a i) := by
      unfold _root_.GD.N0232.N0719.N0938.d007528
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact _root_.GD.N0033.d028246 he (_root_.GD.N0033.d028242 h a ha i)
      (Finset.single_le_sum (fun j _ => _root_.GD.N0033.d028242 h a ha j) (Finset.mem_univ i))

def d028248 (j : Fin k) (b : Fin k → ℝ) : ℝ := ∑ l, _root_.GD.N0232.N0719.N0877.d020693 j b l

@[fun_prop] theorem d028249 (j : Fin k) : Measurable (_root_.GD.N0033.d028248 j) := by
  unfold _root_.GD.N0033.d028248
  exact Finset.measurable_sum _ fun l _ => _root_.GD.N0033.d028241 j l

theorem d028250 (i : Fin (k + 1)) (j : Fin k) (a : Fin (k + 1) → ℝ) :
    (∑ l, _root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a l) = a (i.succAbove j) / a i +
      _root_.GD.N0033.d028248 j (fun l => a (i.succAbove l)) := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [_root_.GD.N0232.N0719.N0877.d020693, ne_of_eq_of_ne rfl (Fin.succAbove_ne i j).symm, if_false,
    Fin.succAbove_right_inj, _root_.GD.N0033.d028248]

theorem d028251 (i : Fin (k + 1)) (j : Fin k)
    (a : Fin (k + 1) → ℝ) (ha : a i ≠ 0) (e : ℝ) :
    _root_.GD.N0232.N0719.N0938.d007528 e (∑ l, _root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a l) (_root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a i) =
      _root_.GD.N0213.N0527.d028204 e (a (i.succAbove j))
        (_root_.GD.N0033.d028248 j (fun l => a (i.succAbove l))) (a i) := by
  rw [_root_.GD.N0033.d028250, _root_.GD.N0232.N0719.N0938.d007528]
  rw [show _root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a i = a (i.succAbove j) / a i by
    simp [_root_.GD.N0232.N0719.N0877.d020693, (Fin.succAbove_ne i j).symm]]
  exact _root_.GD.N0213.N0527.d028206 _ _ _ _ ha

theorem d028252
    (shape : Fin (k + 1) → ℝ) (hs : ∀ i, 0 < shape i)
    (i : Fin (k + 1)) (j : Fin k) (hi : shape i = 1)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ l, _root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a l)
      (_root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a i) ∂_root_.GD.N0033.d028239 shape) atTop (𝓝 1) := by
  let μ : Fin (k + 1) → Measure ℝ := fun l => gammaMeasure (shape l) (shape l)
  let ν := _root_.GD.N0033.d028239 (fun l => shape (i.succAbove l))
  letI (l : Fin (k + 1)) : IsProbabilityMeasure (μ l) :=
    isProbabilityMeasure_gammaMeasure (hs l) (hs l)
  letI : IsProbabilityMeasure (gammaMeasure 1 1) := isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hμ : μ i = gammaMeasure 1 1 := by simp [μ, hi]
  have hpos : ∀ᵐ b ∂ν, ∀ l, 0 < b l := _root_.GD.N0033.d028240 _ (fun l => hs (i.succAbove l))
  have hC : ∀ᵐ b ∂ν, 0 < b j ∧ 0 ≤ _root_.GD.N0033.d028248 j b := by
    filter_upwards [hpos] with b hb
    exact ⟨hb j, Finset.sum_nonneg fun l _ => _root_.GD.N0033.d028242 j b hb l⟩
  have hint : Integrable (fun b : Fin k → ℝ => b j) ν :=
    (measurePreserving_eval (fun l => μ (i.succAbove l)) j).integrable_comp_of_integrable
      (_root_.GD.N0232.N0719.N0877.d020694 (hs _) (hs _))
  have hmean : (∫ b : Fin k → ℝ, b j ∂ν) = 1 := by
    have hh := _root_.GD.N0232.N0719.N0960.d009682 (hs (i.succAbove j)) (hs (i.succAbove j))
    change (∫ x, x ∂μ (i.succAbove j)) = _ at hh
    rw [← (measurePreserving_eval (fun l => μ (i.succAbove l)) j).map_eq] at hh
    change (∫ x, id x ∂Measure.map (fun b : Fin k → ℝ => b j) ν) = _ at hh
    rw [integral_map_of_stronglyMeasurable (μ := ν)
      (φ := fun b : Fin k → ℝ => b j) (f := id) (measurable_pi_apply j)
      stronglyMeasurable_id] at hh
    simpa only [id_eq, div_self (hs (i.succAbove j)).ne'] using hh
  have havg := _root_.GD.N0213.N0527.d028218 ν (fun b => b j)
    (_root_.GD.N0033.d028248 j) (by fun_prop) (_root_.GD.N0033.d028249 j) hC hint e he he0
  rw [hmean] at havg
  convert havg using 1
  funext n
  let g : ℝ × (Fin k → ℝ) → ℝ := fun p => _root_.GD.N0213.N0527.d028204 (e n) (p.2 j) (_root_.GD.N0033.d028248 j p.2) p.1
  have hsplit := (measurePreserving_piFinSuccAbove μ i).integral_comp' g
  have hg : Integrable g ((μ i).prod ν) := by
    rw [hμ]
    apply (integrable_const (1 / e n)).mono'
    · exact (show Measurable g by unfold g _root_.GD.N0213.N0527.d028204; fun_prop).aestronglyMeasurable
    · filter_upwards [
        (Measure.quasiMeasurePreserving_fst (μ := gammaMeasure 1 1) (ν := ν)).ae
          (_root_.GD.N0232.N0719.N0910.d010286 (by norm_num) (by norm_num)),
        (Measure.quasiMeasurePreserving_snd (μ := gammaMeasure 1 1) (ν := ν)).ae hC] with p hp hb
      have hnn : 0 ≤ g p := by
        unfold g _root_.GD.N0213.N0527.d028204
        exact div_nonneg (mul_nonneg (he n).le (sq_nonneg _)) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact _root_.GD.N0213.N0488.d028223 _ _ _ _ (he n) hb.1 hb.2 hp.le
  calc
    _ = ∫ a, g (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i a) ∂_root_.GD.N0033.d028239 shape := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0033.d028240 shape hs] with a ha
      exact _root_.GD.N0033.d028251 i j a (ha i).ne' (e n)
    _ = ∫ p, g p ∂((μ i).prod ν) := hsplit
    _ = _ := by rw [integral_prod_symm g hg, hμ]

end
end GD.N0033

#print axioms _root_.GD.N0033.d028245
#print axioms _root_.GD.N0033.d028247
#print axioms _root_.GD.N0033.d028251
#print axioms _root_.GD.N0033.d028252
