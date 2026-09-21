import GD.Module0705












open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

namespace GD.N0232.N0719.N0937

noncomputable section

open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0915

def d010572 {k : ℕ} (sizes : Fin k → ℕ) :
    Set (_root_.GD.N0232.N0719.d009173 k sizes) :=
  Set.pi Set.univ fun i ↦ Set.pi Set.univ fun _ : Fin (sizes i) ↦ Icc (1 : ℝ) 2

theorem d010573 {k : ℕ} (sizes : Fin k → ℕ) :
    MeasurableSet (_root_.GD.N0232.N0719.N0937.d010572 sizes) := by
  exact MeasurableSet.pi Set.countable_univ fun _ _ ↦
    MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc

theorem d010574 {k : ℕ} (sizes : Fin k → ℕ) :
    0 < _root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1) (_root_.GD.N0232.N0719.N0937.d010572 sizes) := by
  have hg : 0 < gaussianReal 0 1 (Icc (1 : ℝ) 2) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hv := (gaussianReal_absolutelyContinuous' 0 one_ne_zero) hz
    norm_num [Real.volume_Icc] at hv
  have hblock : ∀ n, _root_.GD.N0232.N0719.d009174 n 0 1 =
      Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
    intro n
    unfold _root_.GD.N0232.N0719.d009174
    have hi : _root_.GD.N0107.d009018 n 0 1 = id := by
      funext x i
      simp [_root_.GD.N0107.d009018]
    rw [hi, Measure.map_id]
    rfl
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N0937.d010572
  simp only [hblock, Measure.pi_pi]
  apply pos_iff_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
    Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hg.ne'

theorem d010575 {k : ℕ} (sizes : Fin k → ℕ)
    (hn : ∀ i, 0 < sizes i) {x : _root_.GD.N0232.N0719.d009173 k sizes}
    (hx : x ∈ _root_.GD.N0232.N0719.N0937.d010572 sizes) (i : Fin k) : 1 ≤ _root_.GD.N0232.N0719.N0900.d009102 k sizes x i := by
  have hxi : ∀ l, 1 ≤ x i l := fun l ↦
    (hx i (Set.mem_univ i) l (Set.mem_univ l)).1
  have hnR : 0 < (sizes i : ℝ) := Nat.cast_pos.mpr (hn i)
  unfold _root_.GD.N0232.N0719.N0900.d009102 _root_.GD.N0107.d009084 _root_.GD.N0126.d006420
    _root_.GD.N0126.d006419
  simp only [Fintype.card_fin]
  apply (le_div_iff₀ hnR).mpr
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun l _ ↦ hxi l)

def d010576 {k : ℕ} (sizes : Fin k → ℕ) (j : Fin k)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (c : ℝ) : Prop :=
  ∀ᵐ x ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1),
    ∃ w : Fin k → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ w j ≤ c ∧
      f x = ∑ i, w i * _root_.GD.N0232.N0719.N0900.d009102 k sizes x i

theorem d010577 {k : ℕ} (j : Fin k)
    (w y : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {c : ℝ} (hc : w j ≤ c) (hyj : 0 ≤ y j) (hy : ∀ i, i ≠ j → 1 ≤ y i) :
    1 - c ≤ ∑ i, w i * y i := by
  have hterm : ∀ i, (if i = j then 0 else w i) ≤ w i * y i := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa using mul_nonneg (hw j) hyj
    · simp only [if_neg hij]
      exact le_mul_of_one_le_right (hw i) (hy i hij)
  have hsum0 : (∑ i, if i = j then 0 else w i) = 1 - w j := by
    have heq : ∀ i, (if i = j then 0 else w i) = w i - (if i = j then w j else 0) := by
      intro i
      split_ifs with h <;> simp [h]
    simp only [heq, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hsum]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hterm i)
  rw [hsum0] at h
  linarith



theorem d010578 {k : ℕ} (sizes : Fin k → ℕ)
    (hn : ∀ i, 0 < sizes i) (j : Fin k)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) {c e : ℝ}
    (hc : _root_.GD.N0232.N0719.N0937.d010576 sizes j f c) (he : 0 < e) :
    ∀ᵐ x ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1), x ∈ _root_.GD.N0232.N0719.N0937.d010572 sizes →
      1 - c ≤ f (_root_.GD.N0232.N0719.N0915.d010400 sizes j e x) := by
  have hp : ∀ i, 0 < _root_.GD.N0232.N0719.N0915.d010399 j e i := by
    intro i
    unfold _root_.GD.N0232.N0719.N0915.d010399
    split_ifs <;> positivity
  have hphys := (_root_.GD.N0232.N0719.d009181 k sizes 0 0
    (_root_.GD.N0232.N0719.N0915.d010399 j e) (fun _ ↦ 1) (fun i ↦ (hp i).ne')
    (fun _ ↦ one_ne_zero)).ae_le hc
  have hmp : MeasurePreserving (_root_.GD.N0232.N0719.N0915.d010400 sizes j e)
      (_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1))
      (_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e)) :=
    ⟨_root_.GD.N0232.N0719.N0915.d010401 sizes j e, _root_.GD.N0232.N0719.N0915.d010402 sizes j e⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae hphys] with x hx
  intro hbox
  obtain ⟨w, hw, hsum, hcw, hfw⟩ := hx
  rw [hfw]
  apply _root_.GD.N0232.N0719.N0937.d010577 j w _ hw hsum hcw
  · have hm := _root_.GD.N0232.N0719.N0937.d010575 sizes hn hbox j
    have hs := congrArg (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦ s.mean j)
      (_root_.GD.N0232.N0719.N0915.d010403 sizes hn j e x)
    change _root_.GD.N0232.N0719.N0900.d009102 k sizes (_root_.GD.N0232.N0719.N0915.d010400 sizes j e x) j =
      (_root_.GD.N0232.N0719.N0915.d010390 j e (_root_.GD.N0232.N0719.N0900.d009104 k sizes x)).mean j at hs
    rw [hs]
    simpa only [_root_.GD.N0232.N0719.N0915.d010390, if_true, _root_.GD.N0232.N0719.N0900.d009104] using mul_nonneg he.le (le_trans zero_le_one hm)
  · intro i hij
    have hs := congrArg (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦ s.mean i)
      (_root_.GD.N0232.N0719.N0915.d010403 sizes hn j e x)
    change _root_.GD.N0232.N0719.N0900.d009102 k sizes (_root_.GD.N0232.N0719.N0915.d010400 sizes j e x) i =
      (_root_.GD.N0232.N0719.N0915.d010390 j e (_root_.GD.N0232.N0719.N0900.d009104 k sizes x)).mean i at hs
    rw [hs]
    simpa only [_root_.GD.N0232.N0719.N0915.d010390, if_neg hij, _root_.GD.N0232.N0719.N0900.d009104] using _root_.GD.N0232.N0719.N0937.d010575 sizes hn hbox i



theorem d010579 {k : ℕ} (sizes : Fin k → ℕ)
    (hn : ∀ i, 0 < sizes i) (j : Fin k)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    {c e : ℝ} (hc : _root_.GD.N0232.N0719.N0937.d010576 sizes j f c) (hc1 : c < 1) (he : 0 < e)
    (hf : MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e))) :
    (_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1)).real (_root_.GD.N0232.N0719.N0937.d010572 sizes) * (1-c)^2 ≤
      ∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e) := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1)
  have hmp : MeasurePreserving (_root_.GD.N0232.N0719.N0915.d010400 sizes j e) μ
      (_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e)) :=
    ⟨_root_.GD.N0232.N0719.N0915.d010401 sizes j e, _root_.GD.N0232.N0719.N0915.d010402 sizes j e⟩
  have hi : Integrable (fun x ↦ f (_root_.GD.N0232.N0719.N0915.d010400 sizes j e x) ^ 2) μ :=
    (hf.comp_measurePreserving hmp).integrable_sq
  have hib : Integrable ((_root_.GD.N0232.N0719.N0937.d010572 sizes).indicator (fun _ ↦ (1-c)^2)) μ :=
    (integrable_const _).indicator (_root_.GD.N0232.N0719.N0937.d010573 sizes)
  have hle : ∀ᵐ x ∂μ,
      (_root_.GD.N0232.N0719.N0937.d010572 sizes).indicator (fun _ ↦ (1-c)^2) x ≤
        f (_root_.GD.N0232.N0719.N0915.d010400 sizes j e x) ^ 2 := by
    filter_upwards [_root_.GD.N0232.N0719.N0937.d010578 sizes hn j f hc he] with x hx
    by_cases hb : x ∈ _root_.GD.N0232.N0719.N0937.d010572 sizes
    · rw [Set.indicator_of_mem hb]
      exact pow_le_pow_left₀ (sub_pos.mpr hc1).le (hx hb) 2
    · rw [Set.indicator_of_notMem hb]
      exact sq_nonneg _
  have hm := integral_mono_ae hib hi hle
  have hleft : (∫ x, (_root_.GD.N0232.N0719.N0937.d010572 sizes).indicator (fun _ ↦ (1-c)^2) x ∂μ) =
      μ.real (_root_.GD.N0232.N0719.N0937.d010572 sizes) * (1-c)^2 := by
    rw [integral_indicator (_root_.GD.N0232.N0719.N0937.d010573 sizes), setIntegral_const]
    rfl
  rw [hleft] at hm
  rw [← _root_.GD.N0232.N0719.N0915.d010402 sizes j e,
    integral_map_of_stronglyMeasurable (_root_.GD.N0232.N0719.N0915.d010401 sizes j e)
      (hfm.pow_const 2).stronglyMeasurable]
  exact hm

theorem d010580 {k : ℕ} (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (j : Fin k)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 s))
    {c : ℝ} (hc : _root_.GD.N0232.N0719.N0937.d010576 sizes j f c) (hc1 : c < 1) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧
      (∫ x, _root_.GD.N0232.N0719.N0900.d009111 k sizes x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e)) <
        ∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0915.d010399 j e) := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ ↦ 1)
  let b := μ.real (_root_.GD.N0232.N0719.N0937.d010572 sizes) * (1-c)^2
  have hb : 0 < b := mul_pos
    (ENNReal.toReal_pos (_root_.GD.N0232.N0719.N0937.d010574 sizes).ne' (measure_ne_top _ _))
    (sq_pos_of_pos (sub_pos.mpr hc1))
  let e : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ)+1)
  have he : ∀ n, 0 < e n := fun n ↦ by dsimp [e]; positivity
  have he1 : ∀ n, e n ≤ 1 := fun n ↦ by
    dsimp [e]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := _root_.GD.N0232.N0719.N0915.d010404 sizes hn j e he he1 he0
  obtain ⟨n, hlt⟩ := ((tendsto_order.mp hlim).2 b hb).exists
  refine ⟨e n, he n, he1 n, hlt.trans_le ?_⟩
  apply _root_.GD.N0232.N0719.N0937.d010579 sizes (fun i ↦ by have := hn i; omega) j f hfm hc hc1 (he n)
  apply hf
  intro i
  unfold _root_.GD.N0232.N0719.N0915.d010399
  split_ifs <;> positivity



theorem d010581 {k : ℕ} (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (j : Fin k)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 s))
    (hcap : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      (∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s) ≤
        ∫ x, _root_.GD.N0232.N0719.N0900.d009111 k sizes x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s)
    {c : ℝ} (hc1 : c < 1) : ¬ _root_.GD.N0232.N0719.N0937.d010576 sizes j f c := by
  intro hc
  obtain ⟨e, he, _, hlt⟩ := _root_.GD.N0232.N0719.N0937.d010580 sizes hn j f hfm hf hc hc1
  apply (not_lt_of_ge (hcap (_root_.GD.N0232.N0719.N0915.d010399 j e) ?_)) hlt
  intro i
  unfold _root_.GD.N0232.N0719.N0915.d010399
  split_ifs <;> positivity

end
end GD.N0232.N0719.N0937

#print axioms _root_.GD.N0232.N0719.N0937.d010579
#print axioms _root_.GD.N0232.N0719.N0937.d010581
