import GD.Module1338

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0382
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0101.N0376 _root_.GD.N0101.N0387 _root_.GD.N0101.N0375

def d021727 (g u s a ε : ℝ) : ℝ :=
  ∫ t in Ioo a ε, (g - t) ^ 2 * _root_.GD.N0101.N0387.d021710 u s t

theorem d021728 (g : ℝ) {u s ε : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (he : ε < 1) :
    IntegrableOn (fun t => (g - t) ^ 2 * _root_.GD.N0101.N0387.d021710 u s t)
      (Ioo (0 : ℝ) ε) := by
  have hc0 := _root_.GD.N0101.N0387.d021712 hu hs.le (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_mul] using he)
  have hc : ContinuousOn (fun t =>
      (g - t) ^ 2 * (_root_.GD.N0101.N0387.d021709 u * _root_.GD.N0101.N0376.d021693 u (s * t) t)) (Icc (0 : ℝ) ε) := by
    apply ContinuousOn.mul (by fun_prop)
    exact continuousOn_const.mul (by simpa only [one_mul] using hc0)
  have hi := (hc.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioo
  intro t ht
  change (g - t) ^ 2 * (_root_.GD.N0101.N0387.d021709 u * _root_.GD.N0101.N0376.d021693 u (s * t) t) =
    (g - t) ^ 2 * _root_.GD.N0101.N0387.d021710 u s t
  rw [show _root_.GD.N0101.N0387.d021710 u s t = _root_.GD.N0101.N0387.d021709 u * _root_.GD.N0101.N0376.d021693 u (s * t) t from
    _root_.GD.N0101.N0376.d021696 ⟨ht.1, ht.2.trans he⟩ hu hs]



theorem d021729 (g : ℝ) {u s a ε : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (ha : 0 ≤ a) (he : ε < 1) :
    (max 0 (g - ε)) ^ 2 * (∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 u s t) ≤
      _root_.GD.N0101.N0382.d021727 g u s a ε := by
  have hset : Ioo a ε ⊆ Ioo (0 : ℝ) ε := fun _ ht => ⟨ha.trans_lt ht.1, ht.2⟩
  have hi := (_root_.GD.N0101.N0387.d021713 hu hs he).mono_set hset
  have hl := (_root_.GD.N0101.N0382.d021728 g hu hs he).mono_set hset
  have hm := setIntegral_mono_on (hi.const_mul ((max 0 (g - ε)) ^ 2)) hl
    measurableSet_Ioo (fun t ht => mul_le_mul_of_nonneg_right
      (_root_.GD.N0101.N0375.d021724 g ht.2.le)
      (show 0 ≤ _root_.GD.N0101.N0387.d021710 u s t from mul_nonneg
        (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2) (x := (u, s))
          (by norm_num) (by norm_num) (ha.trans_lt ht.1) (ht.2.trans he) ⟨hu, hs⟩).le
        (Real.rpow_nonneg (ha.trans_lt ht.1).le _)))
  simpa only [integral_const_mul, _root_.GD.N0101.N0382.d021727] using hm



theorem d021730 {u s H R a δ ε c η : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (hH : 0 < H) (hHR : H ≤ R)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδu : δ ≤ u) (he : ε < 1) (hc : 1 ≤ c)
    (hec : ε ≤ δ * (c - 1)) (haH : s * a ≤ H) (hRs : R ≤ s * ε)
    (hη : 0 ≤ η)
    (herr : (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) + 1 / R ≤
      (2 / 3 : ℝ) * η) :
    _root_.GD.N0101.N0387.d021709 u * ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) * (1 - η) *
        (2 / (3 * u)) ≤ s * ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 u s t := by
  have hbase : (2 / 3 : ℝ) ≤ 2 / (3 * u) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3)
      (mul_pos (by norm_num : (0 : ℝ) < 3) hu.1)).mpr
    nlinarith [hu.2]
  have hm : (1 - η) * (2 / (3 * u)) ≤
      2 / (3 * u) - (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) - 1 / R := by
    nlinarith [mul_le_mul_of_nonneg_left hbase hη]
  have hfactor : 0 ≤ _root_.GD.N0101.N0387.d021709 u * ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) :=
    mul_nonneg (_root_.GD.N0101.N0387.d021711 hu).le
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hc) _))
  calc
    _ = _root_.GD.N0101.N0387.d021709 u * ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) *
        ((1 - η) * (2 / (3 * u))) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hm hfactor).trans
      (_root_.GD.N0101.N0375.d021723 hu hs hH hHR ha hδ hδu he hc hec haH hRs)

theorem d021731 {u : ℝ} : _root_.GD.N0101.N0387.d021709 (1 - u) = _root_.GD.N0101.N0387.d021709 u := by
  unfold _root_.GD.N0101.N0387.d021709
  rw [sub_sub_cancel]
  ring




theorem d021732 (g : ℝ) {u s H R a δ ε c η : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (hH : 0 < H) (hHR : H ≤ R)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδu : δ ≤ u) (huδ : u ≤ 1 - δ)
    (he : ε ≤ 1 / 2) (hc : 1 ≤ c) (hec : ε ≤ δ * (c - 1))
    (haH : s * a ≤ H) (hRs : R ≤ s * ε) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (herr : (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) + 1 / R ≤
      (2 / 3 : ℝ) * η) :
    _root_.GD.N0101.N0387.d021709 u * (2 / 3 : ℝ) * ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) *
        (1 - η) * (1 - 2 * ε) ^ 2 ≤
      s * (_root_.GD.N0101.N0382.d021727 g u s a ε + _root_.GD.N0101.N0382.d021727 (1 - g) (1 - u) s a ε) := by
  have he1 : ε < 1 := by linarith
  have hv : 1 - u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hδv : δ ≤ 1 - u := by linarith
  let J := _root_.GD.N0101.N0387.d021709 u * (2 / 3 : ℝ) *
    ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) * (1 - η)
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact mul_nonneg (mul_nonneg (mul_nonneg (_root_.GD.N0101.N0387.d021711 hu).le (by norm_num))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hc) _)))
      (sub_nonneg.mpr hη1)
  have hleft := _root_.GD.N0101.N0382.d021730 hu hs hH hHR ha hδ hδu he1 hc
    hec haH hRs hη herr
  have hright := _root_.GD.N0101.N0382.d021730 hv hs hH hHR ha hδ hδv he1 hc
    hec haH hRs hη herr
  rw [_root_.GD.N0101.N0382.d021731] at hright
  have hleft' : J / u ≤ s * ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 u s t := by
    convert hleft using 1
    dsimp only [J]
    ring
  have hright' : J / (1 - u) ≤ s * ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 (1 - u) s t := by
    convert hright using 1
    dsimp only [J]
    field_simp [(sub_pos.mpr hu.2).ne']
  have hwl := _root_.GD.N0101.N0382.d021729 g hu hs ha he1
  have hwr := _root_.GD.N0101.N0382.d021729 (1 - g) hv hs ha he1
  have hml := mul_le_mul_of_nonneg_left hleft' (sq_nonneg (max 0 (g - ε)))
  have hmr := mul_le_mul_of_nonneg_left hright' (sq_nonneg (max 0 (1 - g - ε)))
  have hp := mul_le_mul_of_nonneg_left (_root_.GD.N0101.N0375.d021726 g hu he) hJ
  have hl := mul_le_mul_of_nonneg_left hwl hs.le
  have hr := mul_le_mul_of_nonneg_left hwr hs.le
  have hleftLoss : J * ((max 0 (g - ε)) ^ 2 / u) ≤ s * _root_.GD.N0101.N0382.d021727 g u s a ε := by
    calc
      _ = (max 0 (g - ε)) ^ 2 * (J / u) := by ring
      _ ≤ (max 0 (g - ε)) ^ 2 * (s * ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 u s t) := hml
      _ = s * ((max 0 (g - ε)) ^ 2 * ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 u s t) := by ring
      _ ≤ _ := hl
  have hrightLoss : J * ((max 0 (1 - g - ε)) ^ 2 / (1 - u)) ≤
      s * _root_.GD.N0101.N0382.d021727 (1 - g) (1 - u) s a ε := by
    calc
      _ = (max 0 (1 - g - ε)) ^ 2 * (J / (1 - u)) := by ring
      _ ≤ (max 0 (1 - g - ε)) ^ 2 *
        (s * ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 (1 - u) s t) := hmr
      _ = s * ((max 0 (1 - g - ε)) ^ 2 *
        ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 (1 - u) s t) := by ring
      _ ≤ _ := hr
  change J * (1 - 2 * ε) ^ 2 ≤ _
  calc
    _ ≤ J * ((max 0 (g - ε)) ^ 2 / u + (max 0 (1 - g - ε)) ^ 2 / (1 - u)) := hp
    _ = J * ((max 0 (g - ε)) ^ 2 / u) +
        J * ((max 0 (1 - g - ε)) ^ 2 / (1 - u)) := by ring
    _ ≤ s * _root_.GD.N0101.N0382.d021727 g u s a ε + s * _root_.GD.N0101.N0382.d021727 (1 - g) (1 - u) s a ε :=
      add_le_add hleftLoss hrightLoss
    _ = _ := by ring

end
end GD.N0101.N0382

#print axioms _root_.GD.N0101.N0382.d021728
#print axioms _root_.GD.N0101.N0382.d021729
#print axioms _root_.GD.N0101.N0382.d021730
#print axioms _root_.GD.N0101.N0382.d021732
