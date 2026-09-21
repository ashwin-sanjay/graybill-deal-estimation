import GD.Module0699
import GD.Module0630
import Mathlib.MeasureTheory.Integral.DominatedConvergence















open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace GD.N0232.N0719.N0915

noncomputable section

open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910

def d010390 {k : ℕ} (j : Fin k) (e : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean i := if i = j then e * s.mean i else s.mean i
  meanVariance i := if i = j then e ^ 2 * s.meanVariance i else s.meanVariance i

theorem d010391 {k : ℕ} (j : Fin k) {e : ℝ} (he : 0 < e)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : ∀ i, 0 < s.meanVariance i) :
    ∀ i, 0 < (_root_.GD.N0232.N0719.N0915.d010390 j e s).meanVariance i := by
  intro i
  by_cases h : i = j
  · simp only [_root_.GD.N0232.N0719.N0915.d010390, h, if_true]
    exact mul_pos (sq_pos_of_pos he) (hs j)
  · simpa only [_root_.GD.N0232.N0719.N0915.d010390, if_neg h] using hs i

theorem d010392 {k : ℕ} (j : Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hs : ∀ i, 0 < s.meanVariance i) : 0 < _root_.GD.N0232.N0719.N0900.d009107 s := by
  have hle : _root_.GD.N0232.N0719.N0900.d009106 s j ≤ _root_.GD.N0232.N0719.N0900.d009107 s :=
    Finset.single_le_sum (fun i _ ↦ _root_.GD.N0232.N0719.N0900.d009129 s i) (Finset.mem_univ j)
  have hpos : 0 < _root_.GD.N0232.N0719.N0900.d009106 s j := by
    simp only [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009105, if_pos (hs j)]
    exact inv_pos.mpr (hs j)
  exact hpos.trans_le hle



theorem d010393 {k : ℕ} (j i : Fin k) (hij : i ≠ j)
    {e : ℝ} (he : 0 < e) (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : ∀ l, 0 < s.meanVariance l) :
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0915.d010390 j e s) i ≤ e ^ 2 * s.meanVariance j / s.meanVariance i := by
  have hp := _root_.GD.N0232.N0719.N0915.d010391 j he s hs
  have ht := _root_.GD.N0232.N0719.N0915.d010392 j (_root_.GD.N0232.N0719.N0915.d010390 j e s) hp
  have hj : (e ^ 2 * s.meanVariance j)⁻¹ ≤ _root_.GD.N0232.N0719.N0900.d009107 (_root_.GD.N0232.N0719.N0915.d010390 j e s) := by
    have h : _root_.GD.N0232.N0719.N0900.d009106 (_root_.GD.N0232.N0719.N0915.d010390 j e s) j ≤ _root_.GD.N0232.N0719.N0900.d009107 (_root_.GD.N0232.N0719.N0915.d010390 j e s) := Finset.single_le_sum
      (fun l _ ↦ _root_.GD.N0232.N0719.N0900.d009129 (_root_.GD.N0232.N0719.N0915.d010390 j e s) l) (Finset.mem_univ j)
    rw [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009127 (hp j)] at h
    simpa only [_root_.GD.N0232.N0719.N0915.d010390, if_true] using h
  have hi : _root_.GD.N0232.N0719.N0900.d009106 (_root_.GD.N0232.N0719.N0915.d010390 j e s) i = (s.meanVariance i)⁻¹ := by
    rw [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009127 (hp i)]
    simp only [_root_.GD.N0232.N0719.N0915.d010390, if_neg hij]
  rw [_root_.GD.N0232.N0719.N0900.d009108, if_neg ht.ne', hi]
  calc
    (s.meanVariance i)⁻¹ / _root_.GD.N0232.N0719.N0900.d009107 (_root_.GD.N0232.N0719.N0915.d010390 j e s) ≤
        (s.meanVariance i)⁻¹ / (e ^ 2 * s.meanVariance j)⁻¹ :=
      div_le_div_of_nonneg_left (inv_nonneg.mpr (hs i).le)
        (inv_pos.mpr (mul_pos (sq_pos_of_pos he) (hs j))) hj
    _ = _ := by rw [div_inv_eq_mul]; ring

theorem d010394 {k : ℕ} (j i : Fin k) (hij : i ≠ j)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : ∀ l, 0 < s.meanVariance l)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0915.d010390 j (e n) s) i) atTop (𝓝 0) := by
  have hk : 0 < k := Fin.pos j
  apply squeeze_zero (fun n ↦ _root_.GD.N0232.N0719.N0900.d009132 hk _ i)
    (fun n ↦ _root_.GD.N0232.N0719.N0915.d010393 j i hij (he n) s hs)
  simpa using ((he0.pow 2).mul_const (s.meanVariance j)).div_const (s.meanVariance i)



theorem d010395 {k : ℕ} (j : Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : ∀ l, 0 < s.meanVariance l)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0915.d010390 j (e n) s)) atTop (𝓝 0) := by
  have hk : 0 < k := Fin.pos j
  have hterm : ∀ i : Fin k, Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0915.d010390 j (e n) s) i *
        (_root_.GD.N0232.N0719.N0915.d010390 j (e n) s).mean i) atTop (𝓝 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      simp only [_root_.GD.N0232.N0719.N0915.d010390, if_true]
      apply squeeze_zero_norm (fun n ↦ ?_)
        (show Tendsto (fun n ↦ |e n * s.mean j|) atTop (𝓝 0) by
          simpa using (he0.mul_const (s.mean j)).abs)
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (_root_.GD.N0232.N0719.N0900.d009132 hk _ j)]
      exact mul_le_of_le_one_left (abs_nonneg _) (_root_.GD.N0232.N0719.N0900.d009133 hk _ j)
    · simpa only [_root_.GD.N0232.N0719.N0915.d010390, if_neg hij, zero_mul] using
        (_root_.GD.N0232.N0719.N0915.d010394 j i hij s hs e he he0).mul_const (s.mean i)
  simpa only [_root_.GD.N0232.N0719.N0900.d009110, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
    (fun i _ ↦ hterm i)

theorem d010396 {k : ℕ} (j : Fin k) {e : ℝ}
    (he : 0 ≤ e) (he1 : e ≤ 1) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    |_root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0915.d010390 j e s)| ≤ _root_.GD.N0232.N0719.N0910.d010278 0 s.mean := by
  have h := _root_.GD.N0232.N0719.N0910.d010281 (Fin.pos j) 0 (_root_.GD.N0232.N0719.N0915.d010390 j e s)
  simp only [sub_zero] at h
  refine h.trans (Finset.sum_le_sum fun i _ ↦ ?_)
  by_cases hij : i = j
  · simp only [_root_.GD.N0232.N0719.N0915.d010390, hij, if_true, sub_zero, abs_mul, abs_of_nonneg he]
    exact mul_le_of_le_one_left (abs_nonneg _) he1
  · simp only [_root_.GD.N0232.N0719.N0915.d010390, if_neg hij, sub_zero, le_refl]

theorem d010397 {k : ℕ} (j : Fin k) (e : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0915.d010390 j e) := by
  rw [measurable_comap_iff]
  change Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦
    ((fun i ↦ if i = j then e * s.mean i else s.mean i),
     (fun i ↦ if i = j then e ^ 2 * s.meanVariance i else s.meanVariance i)))
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ fun i ↦ by
      split_ifs <;> fun_prop
  · exact measurable_pi_lambda _ fun i ↦ by
      split_ifs <;> fun_prop



theorem d010398
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {k : ℕ} (j : Fin k)
    (s : Ω → _root_.GD.N0232.N0719.N0900.d009096 k) (hs : Measurable s)
    (hpos : ∀ᵐ ω ∂μ, ∀ i, 0 < (s ω).meanVariance i)
    (henv : Integrable (fun ω ↦ _root_.GD.N0232.N0719.N0910.d010278 0 (s ω).mean ^ 2) μ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he1 : ∀ n, e n ≤ 1)
    (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0915.d010390 j (e n) (s ω)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun n ↦ ∫ ω, _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0915.d010390 j (e n) (s ω)) ^ 2 ∂μ)
      atTop (𝓝 (∫ _ω, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun ω ↦ _root_.GD.N0232.N0719.N0910.d010278 0 (s ω).mean ^ 2)
    · intro n
      exact ((_root_.GD.N0232.N0719.N0900.d009121.comp ((_root_.GD.N0232.N0719.N0915.d010397 j (e n)).comp hs)).pow_const 2).aestronglyMeasurable
    · exact henv
    · intro n
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := _root_.GD.N0232.N0719.N0915.d010396 j (he n).le (he1 n) (s ω)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    · filter_upwards [hpos] with ω hω
      simpa using (_root_.GD.N0232.N0719.N0915.d010395 j (s ω) hω e he he0).pow 2
  simpa using hlim

open _root_.GD.N0107 _root_.GD.N0232.N0719.N0933

def d010399 {k : ℕ} (j : Fin k) (e : ℝ) : Fin k → ℝ :=
  fun i ↦ if i = j then e else 1

def d010400 {k : ℕ} (sizes : Fin k → ℕ) (j : Fin k) (e : ℝ)
    (x : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.d009173 k sizes :=
  fun i ↦ _root_.GD.N0107.d009018 (sizes i) 0 (_root_.GD.N0232.N0719.N0915.d010399 j e i) (x i)

theorem d010401 {k : ℕ} (sizes : Fin k → ℕ) (j : Fin k) (e : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0915.d010400 sizes j e) := by
  exact measurable_pi_lambda _ fun i ↦
    (_root_.GD.N0107.d009020 (sizes i) 0 (_root_.GD.N0232.N0719.N0915.d010399 j e i)).comp (measurable_pi_apply i)



theorem d010402 {k : ℕ} (sizes : Fin k → ℕ) (j : Fin k) (e : ℝ) :
    (_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1)).map (_root_.GD.N0232.N0719.N0915.d010400 sizes j e) =
      _root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e) := by
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N0915.d010400
  rw [Measure.pi_map_pi]
  · congr 1
    funext i
    simpa using _root_.GD.N0232.N0719.d009186 (sizes i) 0 (_root_.GD.N0232.N0719.N0915.d010399 j e i) 0 1
  · intro i
    exact (_root_.GD.N0107.d009020 (sizes i) 0 (_root_.GD.N0232.N0719.N0915.d010399 j e i)).aemeasurable

theorem d010403 {k : ℕ} (sizes : Fin k → ℕ)
    (hn : ∀ i, 0 < sizes i) (j : Fin k) (e : ℝ)
    (x : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009104 k sizes (_root_.GD.N0232.N0719.N0915.d010400 sizes j e x) =
      _root_.GD.N0232.N0719.N0915.d010390 j e (_root_.GD.N0232.N0719.N0900.d009104 k sizes x) := by
  ext i
  · simp only [_root_.GD.N0232.N0719.N0900.d009104, _root_.GD.N0232.N0719.N0900.d009102, _root_.GD.N0232.N0719.N0915.d010400,
      _root_.GD.N0232.N0719.N0900.d009135 (hn i), zero_add, _root_.GD.N0232.N0719.N0915.d010390, _root_.GD.N0232.N0719.N0915.d010399]
    split_ifs <;> simp
  · simp only [_root_.GD.N0232.N0719.N0900.d009104, _root_.GD.N0232.N0719.N0900.d009103, _root_.GD.N0232.N0719.N0915.d010400,
      _root_.GD.N0232.N0719.N0900.d009136 (hn i), _root_.GD.N0232.N0719.N0915.d010390, _root_.GD.N0232.N0719.N0915.d010399]
    split_ifs <;> ring



theorem d010404 {k : ℕ} (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (j : Fin k)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he1 : ∀ n, e n ≤ 1)
    (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, _root_.GD.N0232.N0719.N0900.d009111 k sizes x ^ 2
      ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j (e n))) atTop (𝓝 0) := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1)
  let μy := _root_.GD.N0232.N0719.N0933.d009300 k sizes 0 (fun _ ↦ 1)
  let μv := _root_.GD.N0232.N0719.N0933.d009301 k sizes (fun _ ↦ 1)
  letI : IsProbabilityMeasure μv := _root_.GD.N0232.N0719.N0910.d010289 sizes hn _
  have hmp : MeasurePreserving (_root_.GD.N0232.N0719.N0933.d009304 k sizes) μ (μy.prod μv) :=
    ⟨_root_.GD.N0232.N0719.N0933.d009308 k sizes,
      _root_.GD.N0232.N0719.N0933.d009309 k sizes hn 0 _⟩
  have hpos : ∀ᵐ x ∂μ, ∀ i, 0 < (_root_.GD.N0232.N0719.N0900.d009104 k sizes x).meanVariance i := by
    have hvar : ∀ᵐ z ∂μy.prod μv, ∀ i, 0 < z.2 i :=
      (Measure.quasiMeasurePreserving_snd (μ := μy) (ν := μv)).ae
        (_root_.GD.N0232.N0719.N0910.d010288 hn (fun _ ↦ by norm_num))
    exact hmp.quasiMeasurePreserving.ae hvar
  have henv : Integrable (fun x ↦ _root_.GD.N0232.N0719.N0910.d010278 0 (_root_.GD.N0232.N0719.N0900.d009104 k sizes x).mean ^ 2) μ := by
    have h := ((_root_.GD.N0232.N0719.N0910.d010291 sizes hn 0 (fun _ ↦ 1)).comp_fst μv).comp_measurePreserving hmp
    exact h.integrable_sq
  have hlim := _root_.GD.N0232.N0719.N0915.d010398 μ j (_root_.GD.N0232.N0719.N0900.d009104 k sizes)
    (_root_.GD.N0232.N0719.N0900.d009115 k sizes) hpos henv e he he1 he0
  have heq : ∀ n, (∫ x, _root_.GD.N0232.N0719.N0900.d009111 k sizes x ^ 2
      ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j (e n))) =
      ∫ x, _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0915.d010390 j (e n) (_root_.GD.N0232.N0719.N0900.d009104 k sizes x)) ^ 2 ∂μ := by
    intro n
    rw [← _root_.GD.N0232.N0719.N0915.d010402 sizes j (e n),
      integral_map_of_stronglyMeasurable (_root_.GD.N0232.N0719.N0915.d010401 sizes j (e n))
        ((_root_.GD.N0232.N0719.N0900.d009122 k sizes).pow_const 2).stronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with x
    rw [_root_.GD.N0232.N0719.N0900.d009111, _root_.GD.N0232.N0719.N0915.d010403 sizes (fun i ↦ by have := hn i; omega)]
  exact hlim.congr' (Eventually.of_forall fun n ↦ (heq n).symm)




theorem d010405 {k : ℕ} (sizes : Fin k → ℕ)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hf : MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1)))
    (hshift : ∀ x, f (_root_.GD.N0232.N0719.N0900.d009095 k sizes 1 1 x) = f x + 1) :
    0 < ∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1) := by
  apply lt_of_le_of_ne (integral_nonneg fun x ↦ sq_nonneg (f x))
  intro hzero
  have hzsq := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (f x))
    hf.integrable_sq).mp hzero.symm
  have hz : ∀ᵐ x ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1), f x = 0 := by
    filter_upwards [hzsq] with x hx
    exact sq_eq_zero_iff.mp hx
  have hz1 := (_root_.GD.N0232.N0719.d009181 k sizes 1 0
    (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ one_ne_zero) (fun _ ↦ one_ne_zero)).ae_le hz
  have hmp : MeasurePreserving (_root_.GD.N0232.N0719.N0900.d009095 k sizes 1 1)
      (_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1))
      (_root_.GD.N0232.N0719.d009176 k sizes 1 (fun _ ↦ 1)) :=
    ⟨_root_.GD.N0232.N0719.N0900.d009112 k sizes 1 1,
      _root_.GD.N0232.N0719.d009178 k sizes 1 (fun _ ↦ 1)⟩
  have hzT := hmp.quasiMeasurePreserving.ae hz1
  obtain ⟨x, hx, hxT⟩ := (hz.and hzT).exists
  have h := hshift x
  rw [hx, hxT] at h
  norm_num at h





theorem d010406 {k : ℕ}
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (j : Fin k)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1)))
    (hshift : ∀ x, f (_root_.GD.N0232.N0719.N0900.d009095 k sizes 1 1 x) = f x + 1)
    (hinv : ∀ e : ℝ, 0 < e → ∀ x, f (_root_.GD.N0232.N0719.N0915.d010400 sizes j e x) = f x) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧
      (∫ x, _root_.GD.N0232.N0719.N0900.d009111 k sizes x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e)) <
        ∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e) := by
  let e : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n := fun n ↦ by dsimp [e]; positivity
  have he1 : ∀ n, e n ≤ 1 := fun n ↦ by
    dsimp [e]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hr := _root_.GD.N0232.N0719.N0915.d010404 sizes hn j e he he1 he0
  have hp := _root_.GD.N0232.N0719.N0915.d010405 sizes f hf hshift
  obtain ⟨n, hnlt⟩ := ((tendsto_order.mp hr).2 _ hp).exists
  refine ⟨e n, he n, he1 n, ?_⟩
  have hsame : (∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j (e n))) =
      ∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1) := by
    rw [← _root_.GD.N0232.N0719.N0915.d010402 sizes j (e n),
      integral_map_of_stronglyMeasurable (_root_.GD.N0232.N0719.N0915.d010401 sizes j (e n))
        (hfm.pow_const 2).stronglyMeasurable]
    simp only [hinv (e n) (he n)]
  rw [hsame]
  exact hnlt

theorem d010407 {k : ℕ} (sizes : Fin k → ℕ)
    (j : Fin k) (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hignore : ∀ x y, (∀ i, i ≠ j → x i = y i) → f x = f y) :
    ∀ e : ℝ, ∀ x, f (_root_.GD.N0232.N0719.N0915.d010400 sizes j e x) = f x := by
  intro e x
  apply hignore
  intro i hij
  funext l
  simp [_root_.GD.N0232.N0719.N0915.d010400, _root_.GD.N0232.N0719.N0915.d010399, hij, _root_.GD.N0107.d009018]

end
end GD.N0232.N0719.N0915

#print axioms _root_.GD.N0232.N0719.N0915.d010398
#print axioms _root_.GD.N0232.N0719.N0915.d010404
#print axioms _root_.GD.N0232.N0719.N0915.d010406
