import GD.Module1662
import GD.Module1419

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0488

noncomputable section

open _root_.GD.N0213.N0527
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0938 _root_.GD.N0232.N0719.N0877 _root_.GD.N0232.N0719.N0939
open _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0960

abbrev d028219 : Measure ℝ := gammaMeasure 1 1

local instance d028220 : IsProbabilityMeasure _root_.GD.N0213.N0488.d028219 :=
  isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)

abbrev d028221 (k : ℕ) : Measure (Fin k → ℝ) := Measure.pi (fun _ => _root_.GD.N0213.N0488.d028219)

theorem d028222 (k : ℕ) :
    ∀ᵐ a ∂_root_.GD.N0213.N0488.d028221 k, ∀ i, 0 < a i :=
  _root_.GD.N0232.N0719.N0910.d010287 (fun _ => by norm_num) (fun _ => by norm_num)

theorem d028223 (e a C x : ℝ)
    (he : 0 < e) (ha : 0 < a) (hC : 0 ≤ C) (hx : 0 ≤ x) :
    _root_.GD.N0213.N0527.d028204 e a C x ≤ 1 / e := by
  have hprod : 0 ≤ e * C * x := mul_nonneg (mul_nonneg he.le hC) hx
  have hden : 0 < x + e * a + e * C * x := by nlinarith [mul_pos he ha]
  have hsquare : (e * a) ^ 2 ≤ (x + e * a + e * C * x) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg he.le ha.le) (by linarith) 2
  unfold _root_.GD.N0213.N0527.d028204
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) he).mpr
  nlinarith

def d028224 (e : ℝ) (i : Fin 3) (j l : Fin 2) (a : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0213.N0527.d028204 e (a (i.succAbove j)) (a (i.succAbove j) / a (i.succAbove l)) (a i)

theorem d028225 (e : ℝ) (he : 0 < e)
    (i : Fin 3) (j l : Fin 2) : Integrable (_root_.GD.N0213.N0488.d028224 e i j l) (_root_.GD.N0213.N0488.d028221 3) := by
  apply (integrable_const (1 / e)).mono'
  · exact (show Measurable (_root_.GD.N0213.N0488.d028224 e i j l) by
      unfold _root_.GD.N0213.N0488.d028224 _root_.GD.N0213.N0527.d028204
      fun_prop).aestronglyMeasurable
  · filter_upwards [_root_.GD.N0213.N0488.d028222 3] with a ha
    have hnonneg : 0 ≤ _root_.GD.N0213.N0488.d028224 e i j l a := by
      unfold _root_.GD.N0213.N0488.d028224 _root_.GD.N0213.N0527.d028204
      exact div_nonneg (mul_nonneg he.le (sq_nonneg _)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact _root_.GD.N0213.N0488.d028223 _ _ _ _ he (ha _) (div_nonneg (ha _).le (ha _).le) (ha _).le

theorem d028226 (e : ℝ) (he : 0 < e)
    (i : Fin 3) (j l : Fin 2) :
    (∫ a, _root_.GD.N0213.N0488.d028224 e i j l a ∂_root_.GD.N0213.N0488.d028221 3) =
      ∫ b, ∫ x, _root_.GD.N0213.N0527.d028204 e (b j) (b j / b l) x ∂_root_.GD.N0213.N0488.d028219 ∂_root_.GD.N0213.N0488.d028221 2 := by
  let g : ℝ × (Fin 2 → ℝ) → ℝ :=
    fun p => _root_.GD.N0213.N0527.d028204 e (p.2 j) (p.2 j / p.2 l) p.1
  have hg : Integrable g (_root_.GD.N0213.N0488.d028219.prod (_root_.GD.N0213.N0488.d028221 2)) := by
    apply (integrable_const (1 / e)).mono'
    · exact (show Measurable g by
        unfold g _root_.GD.N0213.N0527.d028204
        fun_prop).aestronglyMeasurable
    · filter_upwards [
        (Measure.quasiMeasurePreserving_fst (μ := _root_.GD.N0213.N0488.d028219) (ν := _root_.GD.N0213.N0488.d028221 2)).ae
          (_root_.GD.N0232.N0719.N0910.d010286 (by norm_num) (by norm_num)),
        (Measure.quasiMeasurePreserving_snd (μ := _root_.GD.N0213.N0488.d028219) (ν := _root_.GD.N0213.N0488.d028221 2)).ae
          (_root_.GD.N0213.N0488.d028222 2)] with p hp hb
      have hnonneg : 0 ≤ g p := by
        unfold g _root_.GD.N0213.N0527.d028204
        exact div_nonneg (mul_nonneg he.le (sq_nonneg _)) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact _root_.GD.N0213.N0488.d028223 _ _ _ _ he (hb _) (div_nonneg (hb _).le (hb _).le) hp.le
  have hsplit := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => _root_.GD.N0213.N0488.d028219) i).integral_comp' g
  change (∫ a, _root_.GD.N0213.N0488.d028224 e i j l a ∂_root_.GD.N0213.N0488.d028221 3) =
    ∫ p, g p ∂(_root_.GD.N0213.N0488.d028219.prod (_root_.GD.N0213.N0488.d028221 2)) at hsplit
  exact hsplit.trans (integral_prod_symm g hg)

theorem d028227 (i : Fin 3) (j l : Fin 2)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0213.N0488.d028224 (e n) i j l a ∂_root_.GD.N0213.N0488.d028221 3) atTop (𝓝 1) := by
  have hint : Integrable (fun b : Fin 2 → ℝ => b j) (_root_.GD.N0213.N0488.d028221 2) :=
    (measurePreserving_eval (fun _ : Fin 2 => _root_.GD.N0213.N0488.d028219) j).integrable_comp_of_integrable
      (_root_.GD.N0232.N0719.N0960.d009683 (by norm_num) (by norm_num))
  have hmean : (∫ b : Fin 2 → ℝ, b j ∂_root_.GD.N0213.N0488.d028221 2) = 1 := by
    have h := _root_.GD.N0232.N0719.N0960.d009682 (a := (1 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num)
    change (∫ x, x ∂_root_.GD.N0213.N0488.d028219) = 1 / 1 at h
    rw [← (measurePreserving_eval (fun _ : Fin 2 => _root_.GD.N0213.N0488.d028219) j).map_eq] at h
    change (∫ x, id x ∂Measure.map (fun b : Fin 2 → ℝ => b j) (_root_.GD.N0213.N0488.d028221 2)) = 1 / 1 at h
    rw [integral_map_of_stronglyMeasurable (μ := _root_.GD.N0213.N0488.d028221 2)
      (φ := fun b : Fin 2 → ℝ => b j) (f := id) (measurable_pi_apply j)
      stronglyMeasurable_id] at h
    simpa using h
  have hpos : ∀ᵐ b ∂_root_.GD.N0213.N0488.d028221 2, 0 < b j ∧ 0 ≤ b j / b l := by
    filter_upwards [_root_.GD.N0213.N0488.d028222 2] with b hb
    exact ⟨hb j, div_nonneg (hb j).le (hb l).le⟩
  have h := _root_.GD.N0213.N0527.d028218 (_root_.GD.N0213.N0488.d028221 2)
    (fun b => b j) (fun b => b j / b l) (by fun_prop) (by fun_prop) hpos hint e he he0
  rw [hmean] at h
  simpa only [_root_.GD.N0213.N0488.d028226 _ (he _)] using h

def d028228 (e : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  (1 + e * (a 1 / a 0 + a 1 / a 2))⁻¹ ^ 2

theorem d028229 (e : ℝ) (he : 0 ≤ e)
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    0 ≤ _root_.GD.N0213.N0488.d028228 e a ∧ _root_.GD.N0213.N0488.d028228 e a ≤ 1 := by
  have hq : 0 ≤ a 1 / a 0 + a 1 / a 2 :=
    add_nonneg (div_nonneg (ha 1).le (ha 0).le) (div_nonneg (ha 1).le (ha 2).le)
  have hinv : (1 + e * (a 1 / a 0 + a 1 / a 2))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_right (mul_nonneg he hq))
  have hnonneg : 0 ≤ (1 + e * (a 1 / a 0 + a 1 / a 2))⁻¹ := by positivity
  unfold _root_.GD.N0213.N0488.d028228
  exact ⟨sq_nonneg _, by nlinarith⟩

theorem d028230 (e : ℝ) (he : 0 ≤ e) :
    Integrable (_root_.GD.N0213.N0488.d028228 e) (_root_.GD.N0213.N0488.d028221 3) := by
  apply (integrable_const 1).mono'
  · exact (show Measurable (_root_.GD.N0213.N0488.d028228 e) by
      unfold _root_.GD.N0213.N0488.d028228
      fun_prop).aestronglyMeasurable
  · filter_upwards [_root_.GD.N0213.N0488.d028222 3] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0213.N0488.d028229 e he a ha).1]
    exact (_root_.GD.N0213.N0488.d028229 e he a ha).2

theorem d028231
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0213.N0488.d028228 (e n) a ∂_root_.GD.N0213.N0488.d028221 3) atTop (𝓝 1) := by
  have h : Tendsto (fun n => ∫ a, _root_.GD.N0213.N0488.d028228 (e n) a ∂_root_.GD.N0213.N0488.d028221 3)
      atTop (𝓝 (∫ _a : Fin 3 → ℝ, (1 : ℝ) ∂_root_.GD.N0213.N0488.d028221 3)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n
      exact (show Measurable (_root_.GD.N0213.N0488.d028228 (e n)) by
        unfold _root_.GD.N0213.N0488.d028228
        fun_prop).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [_root_.GD.N0213.N0488.d028222 3] with a ha
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0213.N0488.d028229 _ (he n).le a ha).1]
      exact (_root_.GD.N0213.N0488.d028229 _ (he n).le a ha).2
    · apply ae_of_all
      intro a
      have hd : Tendsto (fun n => 1 + e n * (a 1 / a 0 + a 1 / a 2)) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
          (he0.mul_const (a 1 / a 0 + a 1 / a 2))
      simpa only [_root_.GD.N0213.N0488.d028228, inv_one, one_pow] using (hd.inv₀ one_ne_zero).pow 2
  simpa using h

theorem d028232 (e : ℝ) (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    _root_.GD.N0232.N0719.N0938.d007530 e (_root_.GD.N0232.N0719.N0877.d020693 1 a) =
      _root_.GD.N0213.N0488.d028228 e a + _root_.GD.N0213.N0488.d028224 e 0 0 1 a + _root_.GD.N0213.N0488.d028224 e 2 1 0 a := by
  change _root_.GD.N0232.N0719.N0938.d007530 e (_root_.GD.N0232.N0719.N0877.d020693 1 a) = _root_.GD.N0213.N0488.d028228 e a +
    _root_.GD.N0213.N0527.d028204 e (a 1) (a 1 / a 2) (a 0) + _root_.GD.N0213.N0527.d028204 e (a 1) (a 1 / a 0) (a 2)
  rw [← _root_.GD.N0213.N0527.d028206 e (a 1) (a 1 / a 2) (a 0) (ha 0).ne',
    ← _root_.GD.N0213.N0527.d028206 e (a 1) (a 1 / a 0) (a 2) (ha 2).ne']
  norm_num [_root_.GD.N0232.N0719.N0938.d007530, _root_.GD.N0232.N0719.N0877.d020693, Fin.sum_univ_succ, _root_.GD.N0232.N0719.N0938.d007527, _root_.GD.N0232.N0719.N0938.d007528, _root_.GD.N0213.N0488.d028228,
    show (2 : Fin 3) ≠ 1 by decide]
  ring

theorem d028233
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 1 a) ∂_root_.GD.N0213.N0488.d028221 3) atTop (𝓝 3) := by
  have hid (n : ℕ) : (∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 1 a) ∂_root_.GD.N0213.N0488.d028221 3) =
      (∫ a, _root_.GD.N0213.N0488.d028228 (e n) a ∂_root_.GD.N0213.N0488.d028221 3) +
      (∫ a, _root_.GD.N0213.N0488.d028224 (e n) 0 0 1 a ∂_root_.GD.N0213.N0488.d028221 3) +
      (∫ a, _root_.GD.N0213.N0488.d028224 (e n) 2 1 0 a ∂_root_.GD.N0213.N0488.d028221 3) := by
    calc
      _ = ∫ a, _root_.GD.N0213.N0488.d028228 (e n) a + _root_.GD.N0213.N0488.d028224 (e n) 0 0 1 a +
          _root_.GD.N0213.N0488.d028224 (e n) 2 1 0 a ∂_root_.GD.N0213.N0488.d028221 3 := by
        apply integral_congr_ae
        filter_upwards [_root_.GD.N0213.N0488.d028222 3] with a ha
        exact _root_.GD.N0213.N0488.d028232 _ a ha
      _ = _ := by
        have hA : Integrable (fun a => _root_.GD.N0213.N0488.d028228 (e n) a + _root_.GD.N0213.N0488.d028224 (e n) 0 0 1 a)
            (_root_.GD.N0213.N0488.d028221 3) := (_root_.GD.N0213.N0488.d028230 _ (he n).le).add
              (_root_.GD.N0213.N0488.d028225 _ (he n) 0 0 1)
        rw [integral_add hA (_root_.GD.N0213.N0488.d028225 _ (he n) 2 1 0),
          integral_add (_root_.GD.N0213.N0488.d028230 _ (he n).le) (_root_.GD.N0213.N0488.d028225 _ (he n) 0 0 1)]
  simp_rw [hid]
  convert ((_root_.GD.N0213.N0488.d028231 e he he0).add
    (_root_.GD.N0213.N0488.d028227 0 0 1 e he he0)).add
    (_root_.GD.N0213.N0488.d028227 2 1 0 e he he0) using 1
  norm_num

def d028234 : Fin 3 → ℕ := fun _ => 3

theorem d028235 : ∀ i, 2 ≤ _root_.GD.N0213.N0488.d028234 i := fun _ => by norm_num [_root_.GD.N0213.N0488.d028234]

theorem d028236
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0972.d012340 3 _root_.GD.N0213.N0488.d028234
      (_root_.GD.N0232.N0719.N0939.d020700 _root_.GD.N0213.N0488.d028234 _root_.GD.N0213.N0488.d028235 1 (e n) (he n)) / e n) atTop (𝓝 3) := by
  convert _root_.GD.N0213.N0488.d028233 e he he0 using 1
  funext n
  rw [_root_.GD.N0232.N0719.N0939.d020708 _root_.GD.N0213.N0488.d028234 _root_.GD.N0213.N0488.d028235 1 (he n)]
  norm_num [_root_.GD.N0213.N0488.d028234, _root_.GD.N0213.N0488.d028221, _root_.GD.N0213.N0488.d028219]
  exact mul_div_cancel_left₀ _ (he n).ne'

theorem d028237
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 3 _root_.GD.N0213.N0488.d028234
      (_root_.GD.N0232.N0719.N0939.d020700 _root_.GD.N0213.N0488.d028234 _root_.GD.N0213.N0488.d028235 1 (e n) (he n)))
      atTop (𝓝 (1 / 3 : ℝ)) := by
  have hb := _root_.GD.N0213.N0488.d028236 e he he0
  have ho : Tendsto (fun n =>
      (∑ i, (_root_.GD.N0213.N0488.d028234 i : ℝ) /
        (_root_.GD.N0232.N0719.N0939.d020700 _root_.GD.N0213.N0488.d028234 _root_.GD.N0213.N0488.d028235 1 (e n) (he n)).scale i ^ 2)⁻¹ / e n)
      atTop (𝓝 1) := by
    have hx : Tendsto (fun n => (1 + ((3 : ℝ) - 1) * e n)⁻¹) atTop (𝓝 1) := by
      have hd : Tendsto (fun n => 1 + ((3 : ℝ) - 1) * e n) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add (he0.const_mul ((3 : ℝ) - 1))
      simpa using hd.inv₀ one_ne_zero
    convert hx using 1
    funext n
    rw [_root_.GD.N0232.N0719.N0939.d020710 _root_.GD.N0213.N0488.d028234 _root_.GD.N0213.N0488.d028235 1 (he n),
      div_right_comm, div_self (he n).ne', one_div]
    norm_num
  have hlim := ho.div hb (by norm_num : (3 : ℝ) ≠ 0)
  convert hlim using 1
  funext n
  exact (div_div_div_cancel_right₀ (he n).ne' _ _).symm

theorem d028238
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ¬ Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 3 _root_.GD.N0213.N0488.d028234
      (_root_.GD.N0232.N0719.N0939.d020700 _root_.GD.N0213.N0488.d028234 _root_.GD.N0213.N0488.d028235 1 (e n) (he n))) atTop (𝓝 1) := by
  intro h
  have := tendsto_nhds_unique (_root_.GD.N0213.N0488.d028237 e he he0) h
  norm_num at this

end
end GD.N0213.N0488

#print axioms _root_.GD.N0213.N0488.d028222
#print axioms _root_.GD.N0213.N0488.d028223
#print axioms _root_.GD.N0213.N0488.d028225
#print axioms _root_.GD.N0213.N0488.d028226
#print axioms _root_.GD.N0213.N0488.d028227
#print axioms _root_.GD.N0213.N0488.d028229
#print axioms _root_.GD.N0213.N0488.d028230
#print axioms _root_.GD.N0213.N0488.d028231
#print axioms _root_.GD.N0213.N0488.d028232
#print axioms _root_.GD.N0213.N0488.d028233
#print axioms _root_.GD.N0213.N0488.d028235
#print axioms _root_.GD.N0213.N0488.d028236
#print axioms _root_.GD.N0213.N0488.d028237
#print axioms _root_.GD.N0213.N0488.d028238
