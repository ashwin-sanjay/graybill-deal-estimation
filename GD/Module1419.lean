import GD.Module1340
import GD.Module1324
import GD.Module1418
import GD.Module0705






set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace GD.N0232.N0719.N0939
noncomputable section
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0880 _root_.GD.N0232.N0719.N0877 _root_.GD.N0232.N0719.N0938
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973 _root_.GD.N0232.N0719.N0941
open _root_.GD.N0232.N0719.N0885

variable {k : ℕ}

def d020698 (h : Fin k) (e : ℝ) (i : Fin k) : ℝ := if i = h then e else 1

def d020699 (sizes : Fin k → ℕ) (h : Fin k) (e : ℝ) (i : Fin k) : ℝ :=
  Real.sqrt (sizes i) * Real.sqrt (_root_.GD.N0232.N0719.N0939.d020698 h e i)

def d020700 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (e : ℝ) (he : 0 < e) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := 0
  scale := _root_.GD.N0232.N0719.N0939.d020699 sizes h e
  scale_pos i := by
    have hn0 : (0 : ℝ) < sizes i := Nat.cast_pos.mpr (by have := hn i; omega)
    have hv : 0 < _root_.GD.N0232.N0719.N0939.d020698 h e i := by unfold _root_.GD.N0232.N0719.N0939.d020698; split_ifs <;> positivity
    exact mul_pos (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hv)

def d020701 (h : Fin k) (e : ℝ) (a : Fin k → ℝ) : Fin k → ℝ :=
  fun i => _root_.GD.N0232.N0719.N0939.d020698 h e i * a i

def d020702 (h : Fin k) (e : ℝ) (a : Fin k → ℝ) : _root_.GD.N0232.N0719.N0900.d009096 k :=
  _root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), _root_.GD.N0232.N0719.N0939.d020701 h e a)

theorem d020703 (h : Fin k) {e : ℝ} (he : 0 < e) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0939.d020698 h e i := by unfold _root_.GD.N0232.N0719.N0939.d020698; split_ifs <;> positivity

theorem d020704 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e) (i : Fin k) :
    _root_.GD.N0232.N0719.N0939.d020699 sizes h e i ^ 2 / (sizes i : ℝ) = _root_.GD.N0232.N0719.N0939.d020698 h e i := by
  have hn0 : (0 : ℝ) < sizes i := Nat.cast_pos.mpr (by have := hn i; omega)
  unfold _root_.GD.N0232.N0719.N0939.d020699
  rw [mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt (_root_.GD.N0232.N0719.N0939.d020703 h he i).le]
  field_simp [hn0.ne']



theorem d020705 (h : Fin k) {e : ℝ} (he : 0 < e)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0939.d020702 h e a) i =
      ((if i = h then 1 else 0) + e * _root_.GD.N0232.N0719.N0877.d020693 h a i) /
        (1 + e * ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j) := by
  let s := _root_.GD.N0232.N0719.N0939.d020702 h e a
  have ht (j : Fin k) : 0 < s.meanVariance j := mul_pos (_root_.GD.N0232.N0719.N0939.d020703 h he j) (ha j)
  have hP : 0 < _root_.GD.N0232.N0719.N0900.d009107 s := _root_.GD.N0232.N0719.N0915.d010392 h s ht
  have hsingle (j : Fin k) : _root_.GD.N0232.N0719.N0900.d009106 s j * (e * a h) =
      (if j = h then 1 else 0) + e * _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    rw [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009127 (ht j)]
    by_cases hj : j = h
    · subst j
      simp only [s, _root_.GD.N0232.N0719.N0939.d020702, _root_.GD.N0232.N0719.N0933.d009305, _root_.GD.N0232.N0719.N0939.d020701, _root_.GD.N0232.N0719.N0939.d020698, _root_.GD.N0232.N0719.N0877.d020693,
        if_true, mul_zero, add_zero]
      exact inv_mul_cancel₀ (mul_ne_zero he.ne' (ha h).ne')
    · simp [s, _root_.GD.N0232.N0719.N0939.d020702, _root_.GD.N0232.N0719.N0933.d009305, _root_.GD.N0232.N0719.N0939.d020701, _root_.GD.N0232.N0719.N0939.d020698, _root_.GD.N0232.N0719.N0877.d020693, hj, div_eq_mul_inv]
      ring
  have htotal : _root_.GD.N0232.N0719.N0900.d009107 s * (e * a h) = 1 + e * ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    change (∑ j, _root_.GD.N0232.N0719.N0900.d009106 s j) * (e * a h) = _
    rw [Finset.sum_mul]
    simp_rw [hsingle]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hq (j : Fin k) : 0 ≤ _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    unfold _root_.GD.N0232.N0719.N0877.d020693
    split_ifs
    · exact le_rfl
    · exact (div_pos (ha h) (ha j)).le
  have hden : 0 < 1 + e * ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    have hsum : 0 ≤ ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j := Finset.sum_nonneg fun j _ => hq j
    positivity
  rw [_root_.GD.N0232.N0719.N0900.d009108, if_neg hP.ne']
  apply (div_eq_div_iff hP.ne' hden.ne').mpr
  rw [← htotal, ← hsingle i]
  ring



theorem d020706 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    _root_.GD.N0232.N0719.N0880.d020684 (_root_.GD.N0232.N0719.N0885.d009329 sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e))
      (_root_.GD.N0232.N0719.N0939.d020701 h e a) = e * _root_.GD.N0232.N0719.N0938.d007530 e (_root_.GD.N0232.N0719.N0877.d020693 h a) := by
  let R := ∑ j, _root_.GD.N0232.N0719.N0877.d020693 h a j
  have hq (j : Fin k) : 0 ≤ _root_.GD.N0232.N0719.N0877.d020693 h a j := by
    unfold _root_.GD.N0232.N0719.N0877.d020693
    split_ifs
    · exact le_rfl
    · exact (div_pos (ha h) (ha j)).le
  have hden : 1 + e * R ≠ 0 := ne_of_gt (by
    have hsum : 0 ≤ R := Finset.sum_nonneg fun j _ => hq j
    positivity)
  have hi (i : Fin k) :
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0939.d020702 h e a) i ^ 2 *
        (_root_.GD.N0232.N0719.N0885.d009329 sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e) i : ℝ) =
      e * ((if i = h then _root_.GD.N0232.N0719.N0938.d007527 e R else 0) +
        _root_.GD.N0232.N0719.N0938.d007528 e R (_root_.GD.N0232.N0719.N0877.d020693 h a i)) := by
    rw [_root_.GD.N0232.N0719.N0939.d020705 h he a ha i]
    change ((_ + e * _root_.GD.N0232.N0719.N0877.d020693 h a i) / (1 + e * R)) ^ 2 *
      (_root_.GD.N0232.N0719.N0939.d020699 sizes h e i ^ 2 / (sizes i : ℝ)) = _
    rw [_root_.GD.N0232.N0719.N0939.d020704 sizes hn h he i]
    by_cases hih : i = h
    · subst i
      simp [_root_.GD.N0232.N0719.N0877.d020693, _root_.GD.N0232.N0719.N0939.d020698, _root_.GD.N0232.N0719.N0938.d007527, _root_.GD.N0232.N0719.N0938.d007528, div_eq_mul_inv]
      ring
    · simp only [if_neg hih, zero_add, _root_.GD.N0232.N0719.N0939.d020698, _root_.GD.N0232.N0719.N0938.d007527, _root_.GD.N0232.N0719.N0938.d007528]
      field_simp [hden]
  unfold _root_.GD.N0232.N0719.N0880.d020684
  change (∑ i, _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0939.d020702 h e a) i ^ 2 * _) = _
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  simp [_root_.GD.N0232.N0719.N0938.d007530, R]




theorem d020707
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0939.d020701 h e)
      (Measure.pi fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
        (((sizes j - 1 : ℕ) : ℝ) / 2))
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e)) := by
  let μ := fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
    (((sizes j - 1 : ℕ) : ℝ) / 2)
  have hs (j : Fin k) : 0 < (((sizes j - 1 : ℕ) : ℝ) / 2) := by
    have hj : 0 < sizes j - 1 := by have := hn j; omega
    exact div_pos (Nat.cast_pos.mpr hj) (by norm_num)
  letI (j : Fin k) : IsProbabilityMeasure (μ j) := isProbabilityMeasure_gammaMeasure (hs j) (hs j)
  have hfun : _root_.GD.N0232.N0719.N0939.d020701 h e = fun a i =>
      _root_.GD.N0232.N0719.N0933.d009287 (sizes i) (_root_.GD.N0232.N0719.N0939.d020699 sizes h e i) (a i) := by
    funext a i
    simp only [_root_.GD.N0232.N0719.N0939.d020701, _root_.GD.N0232.N0719.N0933.d009287, _root_.GD.N0232.N0719.N0939.d020704 sizes hn h he]
  refine ⟨by unfold _root_.GD.N0232.N0719.N0939.d020701; fun_prop, ?_⟩
  rw [hfun, Measure.pi_map_pi]
  · rfl
  · intro i
    exact (_root_.GD.N0232.N0719.N0933.d009294 (sizes i) (_root_.GD.N0232.N0719.N0939.d020699 sizes h e i)).aemeasurable



theorem d020708
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e) :
    _root_.GD.N0232.N0719.N0972.d012340 k sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he) = e *
      ∫ a, _root_.GD.N0232.N0719.N0938.d007530 e (_root_.GD.N0232.N0719.N0877.d020693 h a)
        ∂(Measure.pi fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
          (((sizes j - 1 : ℕ) : ℝ) / 2)) := by
  have hs (j : Fin k) : 0 < (((sizes j - 1 : ℕ) : ℝ) / 2) := by
    have hj : 0 < sizes j - 1 := by have := hn j; omega
    exact div_pos (Nat.cast_pos.mpr hj) (by norm_num)
  have hpos := _root_.GD.N0232.N0719.N0910.d010287 hs hs
  have hmp := _root_.GD.N0232.N0719.N0939.d020707 sizes hn h he
  have hm : Measurable (_root_.GD.N0232.N0719.N0880.d020684 (_root_.GD.N0232.N0719.N0885.d009329 sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e))) := by
    unfold _root_.GD.N0232.N0719.N0880.d020684
    apply Finset.measurable_sum
    intro i _
    exact (((_root_.GD.N0232.N0719.N0900.d009119 i).comp ((_root_.GD.N0232.N0719.N0933.d009306 k).comp
      (measurable_const.prodMk measurable_id))).pow_const 2).mul_const _
  rw [_root_.GD.N0232.N0719.N0880.d020686 sizes (Fin.pos h) hn _ rfl]
  change (∫ t, _root_.GD.N0232.N0719.N0880.d020684 (_root_.GD.N0232.N0719.N0885.d009329 sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e)) t
    ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes (_root_.GD.N0232.N0719.N0939.d020699 sizes h e)) = _
  rw [← hmp.map_eq, integral_map_of_stronglyMeasurable hmp.measurable hm.stronglyMeasurable]
  calc
    _ = ∫ a, e * _root_.GD.N0232.N0719.N0938.d007530 e (_root_.GD.N0232.N0719.N0877.d020693 h a)
        ∂(Measure.pi fun j => gammaMeasure (((sizes j - 1 : ℕ) : ℝ) / 2)
          (((sizes j - 1 : ℕ) : ℝ) / 2)) := by
      apply integral_congr_ae
      filter_upwards [hpos] with a ha
      exact _root_.GD.N0232.N0719.N0939.d020706 sizes hn h he a ha
    _ = _ := integral_const_mul _ _

theorem d020709
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0972.d012340 k sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)) / e n)
      atTop (𝓝 1) := by
  have hlim := _root_.GD.N0232.N0719.N0877.d020697 sizes hn h hother e (fun n => (he n).le) he0
  convert hlim using 1
  funext n
  rw [_root_.GD.N0232.N0719.N0939.d020708 sizes hn h (he n)]
  field_simp [(he n).ne']

theorem d020710
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) {e : ℝ} (he : 0 < e) :
    (∑ i, (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he).scale i ^ 2)⁻¹ =
      e / (1 + ((k : ℝ) - 1) * e) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Fin.pos h)
  have hden : 1 + ((k : ℝ) - 1) * e ≠ 0 := by positivity
  have hprec : (∑ i, (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he).scale i ^ 2) =
      e⁻¹ + ((k : ℝ) - 1) := by
    have hi (i : Fin k) : (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h e he).scale i ^ 2 =
        1 + if i = h then e⁻¹ - 1 else 0 := by
      change (sizes i : ℝ) / _root_.GD.N0232.N0719.N0939.d020699 sizes h e i ^ 2 = _
      rw [← inv_div, _root_.GD.N0232.N0719.N0939.d020704 sizes hn h he i]
      unfold _root_.GD.N0232.N0719.N0939.d020698
      split_ifs <;> simp
    simp_rw [hi]
    rw [Finset.sum_add_distrib]
    simp
    ring
  rw [hprec]
  field_simp [he.ne', hden]

theorem d020711
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)))
      atTop (𝓝 1) := by
  have hb := _root_.GD.N0232.N0719.N0939.d020709 sizes hn h hother e he he0
  have ho : Tendsto (fun n =>
      (∑ i, (sizes i : ℝ) / (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)).scale i ^ 2)⁻¹ / e n)
      atTop (𝓝 1) := by
    have hx : Tendsto (fun n => (1 + ((k : ℝ) - 1) * e n)⁻¹) atTop (𝓝 1) := by
      have hd : Tendsto (fun n => 1 + ((k : ℝ) - 1) * e n) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add (he0.const_mul ((k : ℝ) - 1))
      simpa using hd.inv₀ one_ne_zero
    convert hx using 1
    funext n
    rw [_root_.GD.N0232.N0719.N0939.d020710 sizes hn h (he n), div_right_comm, div_self (he n).ne', one_div]
  have hlim := ho.div hb one_ne_zero
  convert hlim using 1
  · funext n
    exact (div_div_div_cancel_right₀ (he n).ne' _ _).symm
  · norm_num



theorem d020712
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn = 1 ∧
    _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012190 k sizes) = 0 ∧
    _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012191 k sizes) = 0 := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n := fun n => by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsat := _root_.GD.N0232.N0719.N0939.d020711 sizes hn h hother e he he0
  exact ⟨_root_.GD.N0232.N0719.N0941.d020690 k sizes hk hn _ hsat,
    _root_.GD.N0232.N0719.N0941.d020691 k sizes hk hn _ hsat⟩




theorem d020713
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → 4 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) :
    _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn f = 0 := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n := fun n => by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact _root_.GD.N0232.N0719.N0941.d020692 k sizes hk hn _
    (_root_.GD.N0232.N0719.N0939.d020711 sizes hn h hother e he he0) f hf hb




theorem d020714
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hpositive : 0 < _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn
      (_root_.GD.N0232.N0719.N0962.d012190 k sizes)) :
    ∃ i j : Fin k, i ≠ j ∧ sizes i < 4 ∧ sizes j < 4 := by
  classical
  by_contra hpair
  have hret : ∃ h : Fin k, ∀ i, i ≠ h → 4 ≤ sizes i := by
    by_cases hs : ∃ h, sizes h < 4
    · obtain ⟨h, hh⟩ := hs
      refine ⟨h, fun i hi => ?_⟩
      by_contra hi4
      exact hpair ⟨h, i, Ne.symm hi, hh, by omega⟩
    · refine ⟨⟨0, by omega⟩, fun i _ => ?_⟩
      exact le_of_not_gt (fun hi => hs ⟨i, hi⟩)
  obtain ⟨h, hh⟩ := hret
  rw [(_root_.GD.N0232.N0719.N0939.d020712 sizes hk hn h hh).2.1] at hpositive
  exact (lt_irrefl 0) hpositive

theorem d020715
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hpositive : 0 < _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn
      (_root_.GD.N0232.N0719.N0962.d012190 k sizes)) :
    ∃ i j : Fin k, i ≠ j ∧ (sizes i = 2 ∨ sizes i = 3) ∧
      (sizes j = 2 ∨ sizes j = 3) := by
  obtain ⟨i, j, hij, hi, hj⟩ := _root_.GD.N0232.N0719.N0939.d020714 sizes hk hn hpositive
  exact ⟨i, j, hij, by have := hn i; omega, by have := hn j; omega⟩




def d020716 : Fin 3 → ℕ := ![2, 4, 4]

theorem d020717 : ∀ i, 2 ≤ _root_.GD.N0232.N0719.N0939.d020716 i := by
  intro i
  fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0939.d020716]

theorem d020718 :
    _root_.GD.N0232.N0719.N0973.d012377 3 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717 = 1 ∧
    _root_.GD.N0232.N0719.N0973.d012376 3 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717
      (_root_.GD.N0232.N0719.N0962.d012190 3 _root_.GD.N0232.N0719.N0939.d020716) = 0 ∧
    _root_.GD.N0232.N0719.N0973.d012376 3 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717
      (_root_.GD.N0232.N0719.N0962.d012191 3 _root_.GD.N0232.N0719.N0939.d020716) = 0 := by
  apply _root_.GD.N0232.N0719.N0939.d020712 _root_.GD.N0232.N0719.N0939.d020716 (by norm_num) _root_.GD.N0232.N0719.N0939.d020717 0
  intro i hi
  fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0939.d020716] at *

end
end GD.N0232.N0719.N0939

#print axioms _root_.GD.N0232.N0719.N0939.d020705
#print axioms _root_.GD.N0232.N0719.N0939.d020706

#print axioms _root_.GD.N0232.N0719.N0939.d020708
#print axioms _root_.GD.N0232.N0719.N0939.d020709
#print axioms _root_.GD.N0232.N0719.N0939.d020711
#print axioms _root_.GD.N0232.N0719.N0939.d020712

#print axioms _root_.GD.N0232.N0719.N0939.d020713

#print axioms _root_.GD.N0232.N0719.N0939.d020714
#print axioms _root_.GD.N0232.N0719.N0939.d020715

#print axioms _root_.GD.N0232.N0719.N0939.d020718
