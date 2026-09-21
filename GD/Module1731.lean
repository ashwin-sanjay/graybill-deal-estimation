import GD.Module1632

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0528
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0915 _root_.GD.N0232.N0719.N0937
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0862 _root_.GD.N0232.N0719.N1006
open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0156.N0444

variable {k : ℕ} (sizes : Fin k → ℕ)

def d028806 (j : Fin k) (n : ℕ) : Fin k → ℝ :=
  _root_.GD.N0232.N0719.N0915.d010399 j (1 / ((n : ℝ) + 1))

theorem d028807 (j : Fin k) (n : ℕ) (i : Fin k) : 0 < _root_.GD.N0213.N0528.d028806 j n i := by
  unfold _root_.GD.N0213.N0528.d028806 _root_.GD.N0232.N0719.N0915.d010399
  split_ifs <;> positivity

def d028808 (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : Prop :=
  ∀ j : Fin k, Tendsto (fun n : ℕ => ∫ z, f z ^ 2
    ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0213.N0528.d028806 j n)) atTop (𝓝 0)

theorem d028809
    (hn : ∀ i, 0 < sizes i) (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : ∀ sigma : Fin k → ℝ, (∀ i, 0 < sigma i) → MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 sigma))
    (hvanish : _root_.GD.N0213.N0528.d028808 sizes f) (j : Fin k) (c : ℝ) (hc : c < 1) :
    ¬ _root_.GD.N0232.N0719.N0937.d010576 sizes j f c := by
  intro hceil
  let b := (_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1)).real (_root_.GD.N0232.N0719.N0937.d010572 sizes) * (1 - c) ^ 2
  have hb : 0 < b := mul_pos
    (ENNReal.toReal_pos (_root_.GD.N0232.N0719.N0937.d010574 sizes).ne' (measure_ne_top _ _))
    (sq_pos_of_pos (sub_pos.mpr hc))
  have hlower (n : ℕ) : b ≤ ∫ z, f z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0213.N0528.d028806 j n) :=
    _root_.GD.N0232.N0719.N0937.d010579 sizes hn j f hfm hceil hc (by positivity)
      (hf _ (_root_.GD.N0213.N0528.d028807 j n))
  have hzero : b ≤ 0 := ge_of_tendsto (hvanish j) (Eventually.of_forall hlower)
  exact (not_le_of_gt hb) hzero

theorem d028810 (hn : ∀ i, 0 < sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (j : Fin k) :
    _root_.GD.N0232.N0719.N0963.d012141 k sizes theta ≤ theta.scale j ^ 2 / (sizes j : ℝ) := by
  have hnpos : 0 < (sizes j : ℝ) := Nat.cast_pos.mpr (hn j)
  have hspos : 0 < theta.scale j ^ 2 := sq_pos_of_pos (theta.scale_pos j)
  have hsingle : (sizes j : ℝ) / theta.scale j ^ 2 ≤
      ∑ i, (sizes i : ℝ) / theta.scale i ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin k => (sizes i : ℝ) / theta.scale i ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ j)
  have h := one_div_le_one_div_of_le (div_pos hnpos hspos) hsingle
  simpa only [_root_.GD.N0232.N0719.N0963.d012141, _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096, one_div, inv_div] using h

def d028811 (C : ℝ) (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : Prop :=
  ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta)

theorem d028812 (C : ℝ) (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hcap : _root_.GD.N0213.N0528.d028811 sizes C f) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
  _root_.GD.N0156.N0444.d020670 sizes f hfm theta (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hcap theta))

theorem d028813 (hn : ∀ i, 0 < sizes i)
    (C : ℝ) (hC : 0 ≤ C) (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hcap : _root_.GD.N0213.N0528.d028811 sizes C f) : _root_.GD.N0213.N0528.d028808 sizes f := by
  intro j
  have hbound (n : ℕ) : (∫ z, f z ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0213.N0528.d028806 j n)) ≤
      C * (1 / ((n : ℝ) + 1)) ^ 2 / (sizes j : ℝ) := by
    let theta : _root_.GD.N0232.N0719.N0859.d010809 k := ⟨0, _root_.GD.N0213.N0528.d028806 j n, _root_.GD.N0213.N0528.d028807 j n⟩
    have h := hcap theta
    rw [_root_.GD.N0156.N0444.d020671 sizes f theta (_root_.GD.N0213.N0528.d028812 sizes C f hfm hcap theta)] at h
    have hle := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hC (_root_.GD.N0232.N0719.N0963.d012142 k sizes theta))).mp h
    have ho := mul_le_mul_of_nonneg_left (_root_.GD.N0213.N0528.d028810 sizes hn theta j) hC
    have := hle.trans ho
    simpa only [theta, _root_.GD.N0232.N0719.N0859.d010812, sub_zero, _root_.GD.N0213.N0528.d028806, _root_.GD.N0232.N0719.N0915.d010399,
      if_true, mul_div_assoc] using this
  apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) hbound
  simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).const_mul C).div_const (sizes j : ℝ)

theorem d028814
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) (D : ℕ) (hD : 3 ≤ D)
    (mu : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure mu]
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : ∀ sigma : Fin k → ℝ, (∀ i, 0 < sigma i) → MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 sigma))
    (hvanish : _root_.GD.N0213.N0528.d028808 sizes f)
    (hrep : ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f z = _root_.GD.N0232.N0719.N0983.d009724 ((D : ℝ) / 2) (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z) mu) :
    ¬ Nonempty (_root_.GD.N0232.N0719.N0982.d020351 (D + 1)
      (fun x => _root_.GD.N0232.N0719.N0983.d009724 ((D : ℝ) / 2) x.1 x.2 mu)) := by
  have hr := _root_.GD.N0213.N0490.d027929 sizes hn
    ⟨0, fun _ => 1, fun _ => zero_lt_one⟩
  have hK := _root_.GD.N0213.N0484.d022036 sizes ((D : ℝ) / 2) mu hr
  have hweight : ∀ᵐ z ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f z = ∑ i, _root_.GD.N0232.N0719.N0862.d013361 mu _root_.GD.N0232.N0719.N0983.d009710
        (_root_.GD.N0232.N0719.N0983.d009720 ((D : ℝ) / 2) (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z)) i *
          _root_.GD.N0232.N0719.N0900.d009102 k sizes z i := by
    filter_upwards [hr, hrep] with z hz hrepz
    rw [hrepz, _root_.GD.N0232.N0719.N0983.d009730 _ _ _ hz mu]
    simp only [_root_.GD.N0232.N0719.N0986.d020363, _root_.GD.N0232.N0719.N0983.d009725, _root_.GD.N0232.N0719.N0862.d013361, _root_.GD.N0232.N0719.N0983.d009723]
  have hceiling (j : Fin k) (c : ℝ) (hc : c < 1) :
      ¬ (∀ᵐ z : _root_.GD.N0232.N0720.N1290.d004131 ∂_root_.GD.N0232.N0719.N1006.d013356 mu _root_.GD.N0232.N0719.N0983.d009710 j, (z : ℝ) ≤ c) := by
    intro hb
    have hraw : ∀ᵐ z ∂mu, (_root_.GD.N0232.N0719.N0983.d009710 j z : ℝ) ≤ c :=
      ae_of_ae_map (_root_.GD.N0232.N0719.N0983.d009711 j).measurable.aemeasurable hb
    exact _root_.GD.N0213.N0528.d028809 sizes (fun i => by have := hn i; omega)
      f hfm hf hvanish j c hc (_root_.GD.N0232.N0719.N0862.d013366 sizes mu _root_.GD.N0232.N0719.N0983.d009710
        (fun z => _root_.GD.N0232.N0719.N0983.d009720 ((D : ℝ) / 2) (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z)) hK
        (ae_of_all _ _root_.GD.N0232.N0719.N0983.d009712) f hweight j hraw)
  have h := _root_.GD.N0232.N0719.N0979.d020357
    (by simpa using hk) D hD mu _root_.GD.N0232.N0719.N0983.d009710 (fun i => (_root_.GD.N0232.N0719.N0983.d009711 i).measurable)
    (ae_of_all _ _root_.GD.N0232.N0719.N0983.d009712) hceiling
  simpa only [_root_.GD.N0213.N0484.d022034] using h

end
end GD.N0213.N0528

#print axioms _root_.GD.N0213.N0528.d028809
#print axioms _root_.GD.N0213.N0528.d028810
#print axioms _root_.GD.N0213.N0528.d028813
#print axioms _root_.GD.N0213.N0528.d028814
