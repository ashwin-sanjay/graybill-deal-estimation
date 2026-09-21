import GD.Module0940

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0024.N0278

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1091 _root_.GD.N0232.N0720.N1092
open _root_.GD.N0232.N0720.N1421 _root_.GD.N0232.N0720.N1438

noncomputable section

def d023550 (t : ℝ) : ℝ :=
  ∫ x : _root_.GD.N0232.N0720.N1436.d013217, (x.1 - t) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 6 6 t

def d023551 (t : ℝ) : ℝ := _root_.GD.N0024.N0278.d023550 t / (t * (1 - t))

def d023552 (t : ℝ) : ℝ := 1 + _root_.GD.N0024.N0278.d023551 t

theorem d023553 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0024.N0278.d023550 t = _root_.GD.N0232.N0720.N1091.d012790 (5 / 2) (5 / 2) t := by
  have h := _root_.GD.N0232.N0720.N1425.d014723
    (m := 6) (n := 6) (by norm_num) (by norm_num) ht0 ht1
    (fun x : _root_.GD.N0232.N0720.N1436.d013217 => (x.1 - t) ^ 2) (by fun_prop)
  norm_num [_root_.GD.N0232.N0720.N1436.d013207,
    _root_.GD.N0232.N0720.N1436.d013208] at h
  rw [_root_.GD.N0024.N0278.d023550, ← h,
    _root_.GD.N0232.N0720.N1423.d014020
      (by norm_num : (0 : ℝ) < 5 / 2) (by norm_num : (0 : ℝ) < 5 / 2) ht0 ht1]
  exact (_root_.GD.N0232.N0720.N1091.d012800
    (by norm_num : (0 : ℝ) < 5 / 2) (by norm_num : (0 : ℝ) < 5 / 2) ht0 ht1).symm

theorem d023554 (t : ℝ) : 0 ≤ _root_.GD.N0024.N0278.d023550 t :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem d023555 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ _root_.GD.N0024.N0278.d023551 t :=
  div_nonneg (_root_.GD.N0024.N0278.d023554 t) (mul_nonneg ht0.le (sub_pos.mpr ht1).le)

theorem d023556 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    1 ≤ _root_.GD.N0024.N0278.d023552 t := by
  have h := _root_.GD.N0024.N0278.d023555 t ht0 ht1
  unfold _root_.GD.N0024.N0278.d023552
  linarith

theorem d023557 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0024.N0278.d023551 t = _root_.GD.N0024.N0278.d023551 (1 - t) := by
  unfold _root_.GD.N0024.N0278.d023551
  rw [_root_.GD.N0024.N0278.d023553 t ht0 ht1,
    _root_.GD.N0024.N0278.d023553 (1 - t) (by linarith) (by linarith),
    _root_.GD.N0232.N0720.N1438.d013603 (by norm_num : (0 : ℝ) < 5 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) ht0 ht1]
  congr 1
  ring

theorem d023558
    (t : ℕ → ℝ) (ht0 : ∀ k, 0 < t k) (ht1 : ∀ k, t k < 1)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun k => _root_.GD.N0024.N0278.d023550 (t k) / (t k) ^ 2) atTop (𝓝 (28 / 3)) := by
  have h := _root_.GD.N0232.N0720.N1421.d013121
    (alpha := (5 / 2 : ℝ)) (beta := (5 / 2 : ℝ))
    (by norm_num) (by norm_num) ht ht0 ht1
  norm_num at h
  exact h.congr' (Eventually.of_forall fun k => by
    change _root_.GD.N0232.N0720.N1091.d012790 (5 / 2) (5 / 2) (t k) / (t k) ^ 2 =
      _root_.GD.N0024.N0278.d023550 (t k) / (t k) ^ 2
    rw [_root_.GD.N0024.N0278.d023553 (t k) (ht0 k) (ht1 k)])

theorem d023559
    (t : ℕ → ℝ) (ht0 : ∀ k, 0 < t k) (ht1 : ∀ k, t k < 1)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun k => _root_.GD.N0024.N0278.d023551 (t k)) atTop (𝓝 0) := by
  have hreg := _root_.GD.N0024.N0278.d023558 t ht0 ht1 ht
  have hone : Tendsto (fun k => 1 - t k) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub ht
  have hfrac : Tendsto (fun k => t k / (1 - t k)) atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (t / (fun k => 1 - t k)) atTop (𝓝 (0 : ℝ))
    simpa using ht.div hone (by norm_num : (1 : ℝ) ≠ 0)
  have h := hreg.mul hfrac
  simpa only [mul_zero] using h.congr' (Eventually.of_forall fun k => by
    unfold _root_.GD.N0024.N0278.d023551
    field_simp [(ht0 k).ne', (sub_pos.mpr (ht1 k)).ne'])

theorem d023560
    (t : ℕ → ℝ) (ht0 : ∀ k, 0 < t k) (ht1 : ∀ k, t k < 1)
    (ht : Tendsto t atTop (𝓝 1)) :
    Tendsto (fun k => _root_.GD.N0024.N0278.d023551 (t k)) atTop (𝓝 0) := by
  have hq : Tendsto (fun k => 1 - t k) atTop (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    simpa only [sub_self] using hc.sub ht
  have h := _root_.GD.N0024.N0278.d023559 (fun k => 1 - t k)
    (fun k => by linarith [ht1 k]) (fun k => by linarith [ht0 k]) hq
  exact h.congr' (Eventually.of_forall fun k =>
    (_root_.GD.N0024.N0278.d023557 (t k) (ht0 k) (ht1 k)).symm)

theorem d023561
    (t : ℕ → ℝ) (ht0 : ∀ k, 0 < t k) (ht1 : ∀ k, t k < 1)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun k => _root_.GD.N0024.N0278.d023552 (t k)) atTop (𝓝 1) := by
  simpa [_root_.GD.N0024.N0278.d023552] using
    tendsto_const_nhds.add (_root_.GD.N0024.N0278.d023559 t ht0 ht1 ht)

theorem d023562
    (t : ℕ → ℝ) (ht0 : ∀ k, 0 < t k) (ht1 : ∀ k, t k < 1)
    (ht : Tendsto t atTop (𝓝 1)) :
    Tendsto (fun k => _root_.GD.N0024.N0278.d023552 (t k)) atTop (𝓝 1) := by
  simpa [_root_.GD.N0024.N0278.d023552] using
    tendsto_const_nhds.add (_root_.GD.N0024.N0278.d023560 t ht0 ht1 ht)

def d023563 (u : ℝ) : ℝ := 8 * _root_.GD.N0232.N0720.N1092.d013024 u + 2

def d023564 : ℝ := ∫ u, _root_.GD.N0024.N0278.d023563 u ∂betaMeasure (5 / 2) (5 / 2)

theorem d023565 :
    Integrable _root_.GD.N0024.N0278.d023563 (betaMeasure (5 / 2) (5 / 2)) := by
  letI := isProbabilityMeasureBeta (by norm_num : (0 : ℝ) < 5 / 2)
    (by norm_num : (0 : ℝ) < 5 / 2)
  exact ((_root_.GD.N0232.N0720.N1092.d013029 (by norm_num : (2 : ℝ) < 5 / 2)
    (by norm_num : (0 : ℝ) < 5 / 2)).const_mul 8).add (integrable_const 2)

theorem d023566 : _root_.GD.N0024.N0278.d023564 = 286 / 3 := by
  letI := isProbabilityMeasureBeta (by norm_num : (0 : ℝ) < 5 / 2)
    (by norm_num : (0 : ℝ) < 5 / 2)
  unfold _root_.GD.N0024.N0278.d023564 _root_.GD.N0024.N0278.d023563
  rw [integral_add
    ((_root_.GD.N0232.N0720.N1092.d013029 (by norm_num : (2 : ℝ) < 5 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2)).const_mul 8) (integrable_const 2),
    integral_const_mul,
    _root_.GD.N0232.N0720.N1092.d013030 (by norm_num : (2 : ℝ) < 5 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2),
    _root_.GD.N0232.N0720.N1093.d013050
      (by norm_num : (2 : ℝ) < 5 / 2) (by norm_num : (0 : ℝ) < 5 / 2)]
  norm_num

theorem d023567
    (t u : ℝ) (ht0 : 0 < t) (htHalf : t ≤ 1 / 2) (hu : u ∈ Ioo (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1421.d013101 (5 / 2) (5 / 2) t u) ^ 2 ≤ _root_.GD.N0024.N0278.d023563 u := by
  have h := _root_.GD.N0232.N0720.N1421.d013118
    (alpha := (5 / 2 : ℝ)) (beta := (5 / 2 : ℝ))
    (by norm_num) (by norm_num) ht0 htHalf hu
  norm_num at h
  unfold _root_.GD.N0024.N0278.d023563
  nlinarith

theorem d023568
    (t : ℝ) (ht0 : 0 < t) (htHalf : t ≤ 1 / 2) :
    Integrable (fun u => (_root_.GD.N0232.N0720.N1421.d013101 (5 / 2) (5 / 2) t u) ^ 2)
      (betaMeasure (5 / 2) (5 / 2)) := by
  apply _root_.GD.N0024.N0278.d023565.mono'
    ((_root_.GD.N0232.N0720.N1421.d013103 (5 / 2) (5 / 2) t).pow_const 2).aestronglyMeasurable
  filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 (5 / 2) (5 / 2)] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact _root_.GD.N0024.N0278.d023567 t u ht0 htHalf hu

theorem d023569
    (t : ℝ) (ht0 : 0 < t) (htHalf : t ≤ 1 / 2) :
    (∫ u, (_root_.GD.N0232.N0720.N1421.d013101 (5 / 2) (5 / 2) t u) ^ 2
      ∂betaMeasure (5 / 2) (5 / 2)) ≤ _root_.GD.N0024.N0278.d023564 := by
  apply integral_mono_ae (_root_.GD.N0024.N0278.d023568 t ht0 htHalf)
    _root_.GD.N0024.N0278.d023565
  filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 (5 / 2) (5 / 2)] with u hu
  exact _root_.GD.N0024.N0278.d023567 t u ht0 htHalf hu

theorem d023570
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0024.N0278.d023551 t = t / (1 - t) *
      (∫ u, (_root_.GD.N0232.N0720.N1421.d013101 (5 / 2) (5 / 2) t u) ^ 2
        ∂betaMeasure (5 / 2) (5 / 2)) := by
  unfold _root_.GD.N0024.N0278.d023551
  rw [_root_.GD.N0024.N0278.d023553 t ht0 ht1,
    _root_.GD.N0232.N0720.N1421.d013106
      (by norm_num : (0 : ℝ) < 5 / 2) (by norm_num : (0 : ℝ) < 5 / 2) ht0 ht1]
  field_simp [ht0.ne', (sub_pos.mpr ht1).ne']

theorem d023571
    (t : ℝ) (ht0 : 0 < t) (htHalf : t ≤ 1 / 2) :
    _root_.GD.N0024.N0278.d023551 t ≤ _root_.GD.N0024.N0278.d023564 := by
  have ht1 : t < 1 := by linarith
  let E : ℝ := ∫ u, (_root_.GD.N0232.N0720.N1421.d013101 (5 / 2) (5 / 2) t u) ^ 2
    ∂betaMeasure (5 / 2) (5 / 2)
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hbound : E ≤ _root_.GD.N0024.N0278.d023564 := _root_.GD.N0024.N0278.d023569 t ht0 htHalf
  have heq : _root_.GD.N0024.N0278.d023551 t = t / (1 - t) * E :=
    _root_.GD.N0024.N0278.d023570 t ht0 ht1
  rw [heq]
  have hfrac : t / (1 - t) ≤ 1 :=
    (div_le_one (sub_pos.mpr ht1)).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_right hfrac hE).trans (by simpa using hbound)

theorem d023572
    (t : ℝ) (ht0 : 0 < t) (htHalf : t ≤ 1 / 2) :
    _root_.GD.N0024.N0278.d023551 t ≤ (572 / 3) * t := by
  have ht1 : t < 1 := by linarith
  have hfrac0 : 0 ≤ t / (1 - t) := div_nonneg ht0.le (sub_pos.mpr ht1).le
  have hfrac : t / (1 - t) ≤ 2 * t := by
    apply (div_le_iff₀ (sub_pos.mpr ht1)).mpr
    have h := mul_nonneg ht0.le (show 0 ≤ 1 - 2 * t by linarith)
    nlinarith
  rw [_root_.GD.N0024.N0278.d023570 t ht0 ht1]
  have h := mul_le_mul_of_nonneg_left
    (_root_.GD.N0024.N0278.d023569 t ht0 htHalf) hfrac0
  rw [_root_.GD.N0024.N0278.d023566] at h
  nlinarith

theorem d023573
    (t : ℝ) (htHalf : 1 / 2 ≤ t) (ht1 : t < 1) :
    _root_.GD.N0024.N0278.d023551 t ≤ (572 / 3) * (1 - t) := by
  rw [_root_.GD.N0024.N0278.d023557 t (by linarith) ht1]
  exact _root_.GD.N0024.N0278.d023572 (1 - t) (by linarith) (by linarith)

theorem d023574 (V : ℝ) (hV : 0 < V) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 2 ∧
      ∀ t : ℝ, 0 < t → t < 1 → (t < d ∨ 1 - d < t) →
        _root_.GD.N0024.N0278.d023551 t ≤ V / 2 := by
  let d : ℝ := min (1 / 4) (3 * V / 1144)
  have hd0 : 0 < d := lt_min (by norm_num) (by positivity)
  have hdQuarter : d ≤ 1 / 4 := min_le_left _ _
  have hdV : d ≤ 3 * V / 1144 := min_le_right _ _
  refine ⟨d, hd0, by linarith, ?_⟩
  intro t ht0 ht1 htail
  rcases htail with ht | ht
  · have hb := _root_.GD.N0024.N0278.d023572 t ht0 (by linarith)
    nlinarith
  · have hb := _root_.GD.N0024.N0278.d023573 t (by linarith) ht1
    nlinarith

theorem d023575 (V : ℝ) (hV : 0 < V) :
    ∃ d h : ℝ, 0 < d ∧ d < 1 / 2 ∧ 0 < h ∧
      ∀ t : Ioo (0 : ℝ) 1, (t.val < d ∨ 1 - d < t.val) →
        _root_.GD.N0024.N0278.d023551 t.val ≤ V - h := by
  obtain ⟨d, hd0, hdHalf, htail⟩ := _root_.GD.N0024.N0278.d023574 V hV
  refine ⟨d, V / 2, hd0, hdHalf, by positivity, ?_⟩
  intro t ht
  have h := htail t.val t.property.1 t.property.2 ht
  linarith

theorem d023576
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0024.N0278.d023551 t ≤ _root_.GD.N0024.N0278.d023564 := by
  by_cases htHalf : t ≤ 1 / 2
  · exact _root_.GD.N0024.N0278.d023571 t ht0 htHalf
  · rw [_root_.GD.N0024.N0278.d023557 t ht0 ht1]
    exact _root_.GD.N0024.N0278.d023571 (1 - t) (by linarith) (by linarith)

theorem d023577
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0024.N0278.d023552 t ≤ 1 + _root_.GD.N0024.N0278.d023564 := by
  have h := _root_.GD.N0024.N0278.d023576 t ht0 ht1
  unfold _root_.GD.N0024.N0278.d023552
  linarith

theorem d023578 :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < 1 → _root_.GD.N0024.N0278.d023552 t ≤ C :=
  ⟨1 + _root_.GD.N0024.N0278.d023564, _root_.GD.N0024.N0278.d023577⟩

theorem d023579
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : _root_.GD.N0024.N0278.d023552 t ≤ 289 / 3 := by
  have h := _root_.GD.N0024.N0278.d023577 t ht0 ht1
  rw [_root_.GD.N0024.N0278.d023566] at h
  norm_num at h ⊢
  exact h

#print axioms _root_.GD.N0024.N0278.d023553
#print axioms _root_.GD.N0024.N0278.d023554
#print axioms _root_.GD.N0024.N0278.d023555
#print axioms _root_.GD.N0024.N0278.d023556
#print axioms _root_.GD.N0024.N0278.d023557
#print axioms _root_.GD.N0024.N0278.d023558
#print axioms _root_.GD.N0024.N0278.d023559
#print axioms _root_.GD.N0024.N0278.d023560
#print axioms _root_.GD.N0024.N0278.d023561
#print axioms _root_.GD.N0024.N0278.d023562
#print axioms _root_.GD.N0024.N0278.d023565
#print axioms _root_.GD.N0024.N0278.d023566
#print axioms _root_.GD.N0024.N0278.d023567
#print axioms _root_.GD.N0024.N0278.d023568
#print axioms _root_.GD.N0024.N0278.d023569
#print axioms _root_.GD.N0024.N0278.d023570
#print axioms _root_.GD.N0024.N0278.d023571
#print axioms _root_.GD.N0024.N0278.d023572
#print axioms _root_.GD.N0024.N0278.d023573
#print axioms _root_.GD.N0024.N0278.d023574
#print axioms _root_.GD.N0024.N0278.d023575
#print axioms _root_.GD.N0024.N0278.d023576
#print axioms _root_.GD.N0024.N0278.d023577
#print axioms _root_.GD.N0024.N0278.d023578
#print axioms _root_.GD.N0024.N0278.d023579

end
end GD.N0024.N0278
