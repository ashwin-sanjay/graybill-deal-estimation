import GD.Module0342
import GD.Module1324
import GD.Module1236

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0023.N0258

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0232.N0720.N1423 _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1332
open _root_.GD.N0024 _root_.GD.N0024.N0264
open _root_.GD.N0232.N0719.N0876
open _root_.GD.N0232.N0719.N0877

abbrev d021865 := Ioo (0 : ℝ) 1

theorem d021866 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    Integrable (fun q : ℝ × ℝ => q.2 / q.1) (_root_.GD.N0232.N0720.N1091.d012754 a b) ∧
    Integrable (fun q : ℝ × ℝ => q.1 / q.2) (_root_.GD.N0232.N0720.N1091.d012754 a b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  constructor
  · simpa only [_root_.GD.N0232.N0720.N1091.d012754, div_eq_mul_inv, mul_comm] using
      (_root_.GD.N0232.N0719.N0876.d020682 ha ha0).mul_prod (_root_.GD.N0232.N0719.N0877.d020694 hb0 hb0)
  · simpa only [_root_.GD.N0232.N0720.N1091.d012754, div_eq_mul_inv] using
      (_root_.GD.N0232.N0719.N0877.d020694 ha0 ha0).mul_prod (_root_.GD.N0232.N0719.N0876.d020682 hb hb0)

theorem d021867 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    Integrable (fun q : ℝ × ℝ => _root_.GD.N0024.N0264.d005087 q.1 q.2) (_root_.GD.N0232.N0720.N1091.d012754 a b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  letI := isProbabilityMeasure_gammaMeasure ha0 ha0
  letI := isProbabilityMeasure_gammaMeasure hb0 hb0
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1091.d012754 a b) := by
    unfold _root_.GD.N0232.N0720.N1091.d012754
    infer_instance
  exact _root_.GD.N0024.N0264.d005101 (_root_.GD.N0232.N0720.N1091.d012754 a b) Prod.fst Prod.snd
    (_root_.GD.N0023.N0258.d021866 a b ha hb).1 (_root_.GD.N0023.N0258.d021866 a b ha hb).2

def d021868 (m n : ℕ) (t : _root_.GD.N0023.N0258.d021865) : ℝ :=
  _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 t.1 / (t.1 * (1 - t.1))

def d021869 (m n : ℕ) : ℝ :=
  ∫ q : ℝ × ℝ, _root_.GD.N0024.N0264.d005087 q.1 q.2
    ∂_root_.GD.N0232.N0720.N1091.d012754 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)

theorem d021870 (m : ℕ) (hm : 4 ≤ m) :
    1 < _root_.GD.N0232.N0720.N1436.d013207 m := by
  unfold _root_.GD.N0232.N0720.N1436.d013207
  have h : (2 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 < m - 1 by omega)
  linarith

theorem d021871 (n : ℕ) (hn : 4 ≤ n) :
    1 < _root_.GD.N0232.N0720.N1436.d013208 n := _root_.GD.N0023.N0258.d021870 n hn

theorem d021872
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0023.N0258.d021865) :
    _root_.GD.N0023.N0258.d021868 m n t = ∫ q : ℝ × ℝ, _root_.GD.N0024.N0264.d005086 t.1 q.1 q.2
      ∂_root_.GD.N0232.N0720.N1091.d012754 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) := by
  unfold _root_.GD.N0023.N0258.d021868
  rw [_root_.GD.N0232.N0720.N1332.d020114 hm hn t,
    ← _root_.GD.N0232.N0720.N1423.d014018
      (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) t.2.1 t.2.2,
    ← integral_div]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012774
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)] with q hq
  have hden := _root_.GD.N0024.N0264.d005090 t.1 q.1 q.2 hq.1 hq.2 t.2.1.le t.2.2.le
  unfold _root_.GD.N0232.N0720.N1091.d012759 _root_.GD.N0024.N0264.d005086
  field_simp [t.2.1.ne', (sub_pos.mpr t.2.2).ne', hden.ne']
  ring

theorem d021873
    (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) (t : _root_.GD.N0023.N0258.d021865) :
    _root_.GD.N0023.N0258.d021868 m n t ≤ _root_.GD.N0023.N0258.d021869 m n := by
  rw [_root_.GD.N0023.N0258.d021872 m n (by omega) (by omega) t]
  have ha := _root_.GD.N0023.N0258.d021870 m hm
  have hb := _root_.GD.N0023.N0258.d021871 n hn
  have henv := _root_.GD.N0023.N0258.d021867 _ _ ha hb
  have hpos := _root_.GD.N0232.N0720.N1091.d012774
    (_root_.GD.N0232.N0720.N1436.d013211 (by omega : 2 ≤ m)) (_root_.GD.N0232.N0720.N1436.d013212 (by omega : 2 ≤ n))
  apply integral_mono_ae
    (_root_.GD.N0024.N0264.d005102 _ Prod.fst Prod.snd measurable_fst measurable_snd
      hpos henv t.1 t.2.1.le t.2.2.le) henv
  filter_upwards [hpos] with q hq
  exact _root_.GD.N0024.N0264.d005092 t.1 q.1 q.2 hq.1 hq.2 t.2.1.le t.2.2.le

theorem d021874 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    0 ≤ _root_.GD.N0023.N0258.d021869 m n := by
  apply integral_nonneg_of_ae
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012774
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)] with q hq
  exact _root_.GD.N0024.N0264.d005089 q.1 q.2 hq.1 hq.2

theorem d021875
    (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) (t : ℕ → _root_.GD.N0023.N0258.d021865)
    (ht : Tendsto (fun k => (t k).1) atTop (𝓝 0)) :
    Tendsto (fun k => _root_.GD.N0023.N0258.d021868 m n (t k)) atTop (𝓝 0) := by
  have h := _root_.GD.N0024.N0264.d005103 _ Prod.fst Prod.snd measurable_fst measurable_snd
    (_root_.GD.N0232.N0720.N1091.d012774
      (_root_.GD.N0232.N0720.N1436.d013211 (by omega : 2 ≤ m)) (_root_.GD.N0232.N0720.N1436.d013212 (by omega : 2 ≤ n)))
    (_root_.GD.N0023.N0258.d021867 _ _ (_root_.GD.N0023.N0258.d021870 m hm)
      (_root_.GD.N0023.N0258.d021871 n hn)) (fun k => (t k).1)
    (fun k => (t k).2.1.le) (fun k => (t k).2.2.le) ht
  exact h.congr' (Eventually.of_forall fun k =>
    (_root_.GD.N0023.N0258.d021872 m n (by omega) (by omega) (t k)).symm)

theorem d021876
    (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) (t : ℕ → _root_.GD.N0023.N0258.d021865)
    (ht : Tendsto (fun k => (t k).1) atTop (𝓝 1)) :
    Tendsto (fun k => _root_.GD.N0023.N0258.d021868 m n (t k)) atTop (𝓝 0) := by
  have h := _root_.GD.N0024.N0264.d005104 _ Prod.fst Prod.snd measurable_fst measurable_snd
    (_root_.GD.N0232.N0720.N1091.d012774
      (_root_.GD.N0232.N0720.N1436.d013211 (by omega : 2 ≤ m)) (_root_.GD.N0232.N0720.N1436.d013212 (by omega : 2 ≤ n)))
    (_root_.GD.N0023.N0258.d021867 _ _ (_root_.GD.N0023.N0258.d021870 m hm)
      (_root_.GD.N0023.N0258.d021871 n hn)) (fun k => (t k).1)
    (fun k => (t k).2.1.le) (fun k => (t k).2.2.le) ht
  exact h.congr' (Eventually.of_forall fun k =>
    (_root_.GD.N0023.N0258.d021872 m n (by omega) (by omega) (t k)).symm)

theorem d021877 (f : _root_.GD.N0023.N0258.d021865 → ℝ)
    (hseq : ∀ t : ℕ → _root_.GD.N0023.N0258.d021865, Tendsto (fun k => (t k).1) atTop (𝓝 0) →
      Tendsto (fun k => f (t k)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : _root_.GD.N0023.N0258.d021865, t.1 < d → f t ≤ ε := by
  by_contra hnot
  push Not at hnot
  choose t ht hbad using fun k : ℕ => hnot (1 / ((k : ℝ) + 1)) (by positivity)
  have hlim : Tendsto (fun k => (t k).1) atTop (𝓝 0) :=
    squeeze_zero (fun k => (t k).2.1.le) (fun k => (ht k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall := (hseq t hlim).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_lt.mpr (hbad k).le) hk

theorem d021878 (f : _root_.GD.N0023.N0258.d021865 → ℝ)
    (hseq : ∀ t : ℕ → _root_.GD.N0023.N0258.d021865, Tendsto (fun k => (t k).1) atTop (𝓝 1) →
      Tendsto (fun k => f (t k)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : _root_.GD.N0023.N0258.d021865, 1 - d < t.1 → f t ≤ ε := by
  by_contra hnot
  push Not at hnot
  choose t ht hbad using fun k : ℕ => hnot (1 / ((k : ℝ) + 1)) (by positivity)
  have hlim : Tendsto (fun k => 1 - (t k).1) atTop (𝓝 0) :=
    squeeze_zero (fun k => (sub_pos.mpr (t k).2.2).le)
      (fun k => by linarith [ht k]) tendsto_one_div_add_atTop_nhds_zero_nat
  have htlim : Tendsto (fun k => (t k).1) atTop (𝓝 1) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_sub_cancel, sub_zero] using h1.sub hlim
  have hsmall := (hseq t htlim).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_lt.mpr (hbad k).le) hk

theorem d021879 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) (V : ℝ) (hV : 0 < V) :
    ∃ d h : ℝ, 0 < d ∧ d < 1 / 2 ∧ 0 < h ∧
      ∀ t : _root_.GD.N0023.N0258.d021865, (t.1 < d ∨ 1 - d < t.1) → _root_.GD.N0023.N0258.d021868 m n t ≤ V - h := by
  obtain ⟨dL, hdL, hL⟩ := _root_.GD.N0023.N0258.d021877 (_root_.GD.N0023.N0258.d021868 m n)
    (_root_.GD.N0023.N0258.d021875 m n hm hn) (V / 2) (by positivity)
  obtain ⟨dR, hdR, hR⟩ := _root_.GD.N0023.N0258.d021878 (_root_.GD.N0023.N0258.d021868 m n)
    (_root_.GD.N0023.N0258.d021876 m n hm hn) (V / 2) (by positivity)
  let d := min (1 / 4) (min dL dR)
  have hd0 : 0 < d := lt_min (by norm_num) (lt_min hdL hdR)
  have hdQ : d ≤ 1 / 4 := min_le_left _ _
  have hdL' : d ≤ dL := (min_le_right _ _).trans (min_le_left _ _)
  have hdR' : d ≤ dR := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨d, V / 2, hd0, by linarith, by positivity, ?_⟩
  intro t ht
  rcases ht with ht | ht
  · have h := hL t (ht.trans_le hdL')
    linarith
  · have h := hR t (by linarith)
    linarith

end
end GD.N0023.N0258

#print axioms _root_.GD.N0023.N0258.d021866
#print axioms _root_.GD.N0023.N0258.d021867
#print axioms _root_.GD.N0023.N0258.d021870
#print axioms _root_.GD.N0023.N0258.d021871
#print axioms _root_.GD.N0023.N0258.d021872
#print axioms _root_.GD.N0023.N0258.d021873
#print axioms _root_.GD.N0023.N0258.d021874
#print axioms _root_.GD.N0023.N0258.d021875
#print axioms _root_.GD.N0023.N0258.d021876
#print axioms _root_.GD.N0023.N0258.d021877
#print axioms _root_.GD.N0023.N0258.d021878
#print axioms _root_.GD.N0023.N0258.d021879
