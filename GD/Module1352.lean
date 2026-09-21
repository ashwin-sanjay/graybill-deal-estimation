import GD.Module1351








set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace GD.N0106.N0428.N0770.N1697
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0106.N0428.N0770.N1751 _root_.GD.N0106.N0428.N0770.N1753 _root_.GD.N0106.N0428.N0770.N1750 _root_.GD.N0106.N0428.N0770.N1745


def d021838 (r : ℝ) : Fin 3 → ℝ := ![1, 1, r]


def d021839 (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  ((fun i => p.1 i.castSucc), (fun i => p.2 i.castSucc))

@[fun_prop] theorem d021840 : Measurable _root_.GD.N0106.N0428.N0770.N1697.d021839 := by
  unfold _root_.GD.N0106.N0428.N0770.N1697.d021839
  fun_prop



theorem d021841 :
    MeasurePreserving _root_.GD.N0106.N0428.N0770.N1697.d021839 (_root_.GD.N0106.N0428.N0770.N1745.d021822 3) (_root_.GD.N0106.N0428.N0770.N1745.d021822 2) := by
  have hsplit := measurePreserving_piFinSuccAbove
    (fun _ : Fin 3 => gaussianReal 0 1) (Fin.last 2)
  have h := (measurePreserving_snd
    (μ := gaussianReal 0 1)
    (ν := Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))).comp hsplit
  change MeasurePreserving
    (fun z : Fin 3 → ℝ => fun i : Fin 2 => z ((Fin.last 2).succAbove i))
    (_root_.GD.N0106.N0428.N0770.N1751.d021742 3) (_root_.GD.N0106.N0428.N0770.N1751.d021742 2) at h
  simp only [Fin.succAbove_last] at h
  exact h.prod h



theorem d021842 {k : ℕ} (hk : 0 < k)
    (mu : ℝ) (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i)
    (p : (Fin k → ℝ) × (Fin k → ℝ)) (hz : ∀ i, p.2 i ≠ 0) :
    _root_.GD.N0106.N0428.N0770.N1745.d021824 k mu sigma p =
      (∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i p.2 * (sigma i * p.1 i / Real.sqrt 2)) /
        _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma p.2 := by
  let j : Fin k := ⟨0, hk⟩
  have hp : 0 < _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma j p.2 :=
    div_pos (by norm_num) (mul_pos (sq_pos_of_pos (hsigma j))
      (sq_pos_of_ne_zero (hz j)))
  have hD := hp.trans_le (_root_.GD.N0106.N0428.N0770.N1750.d008387 sigma j p.2)
  have hw : ∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i p.2 = 1 := by
    simp only [_root_.GD.N0106.N0428.N0770.N1750.d008382, ← Finset.sum_div]
    exact div_self hD.ne'
  change _root_.GD.N0232.N0719.N0900.d009110
      (_root_.GD.N0232.N0719.N0933.d009305 k ((fun i => mu + sigma i * p.1 i / Real.sqrt 2),
        _root_.GD.N0106.N0428.N0770.N1753.d021759 sigma p.2)) - mu = _
  rw [_root_.GD.N0106.N0428.N0770.N1753.d021766 hk sigma _ p.2 hsigma hz]
  calc
    _ = (∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i p.2) * mu +
        (∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i p.2 *
          (sigma i * p.1 i / Real.sqrt 2)) - mu := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ = ∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i p.2 *
        (sigma i * p.1 i / Real.sqrt 2) := by rw [hw]; ring
    _ = _ := by
      simp only [_root_.GD.N0106.N0428.N0770.N1750.d008382, div_mul_eq_mul_div, Finset.sum_div]



theorem d021843 (mu : ℝ) {r : ℝ} (hr : 0 < r)
    (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (hz : ∀ i, p.2 i ≠ 0) :
    _root_.GD.N0106.N0428.N0770.N1745.d021824 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) p =
      (2 / p.2 0 ^ 2 * p.1 0 / Real.sqrt 2 +
        2 / p.2 1 ^ 2 * p.1 1 / Real.sqrt 2 +
        (2 / p.2 2 ^ 2 * p.1 2 / Real.sqrt 2) * r⁻¹) /
      (2 / p.2 0 ^ 2 + 2 / p.2 1 ^ 2 +
        (2 / p.2 2 ^ 2) * (r⁻¹) ^ 2) := by
  have hs : ∀ i, 0 < _root_.GD.N0106.N0428.N0770.N1697.d021838 r i := by
    intro i
    fin_cases i <;> simp [_root_.GD.N0106.N0428.N0770.N1697.d021838, hr]
  rw [_root_.GD.N0106.N0428.N0770.N1697.d021842 (by norm_num) mu _ hs p hz]
  have hnum : (∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008366 (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) i p.2 *
      (_root_.GD.N0106.N0428.N0770.N1697.d021838 r i * p.1 i / Real.sqrt 2)) =
      2 / p.2 0 ^ 2 * p.1 0 / Real.sqrt 2 +
        2 / p.2 1 ^ 2 * p.1 1 / Real.sqrt 2 +
        (2 / p.2 2 ^ 2 * p.1 2 / Real.sqrt 2) * r⁻¹ := by
    simp [Fin.sum_univ_succ, _root_.GD.N0106.N0428.N0770.N1697.d021838, _root_.GD.N0106.N0428.N0770.N1750.d008366,
      _root_.GD.N0106.N0428.N0770.N1702.d008357]
    <;> field_simp [hr.ne', hz 0, hz 1, hz 2,
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']
    <;> ring
  have hden : _root_.GD.N0106.N0428.N0770.N1750.d008367 (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) p.2 =
      2 / p.2 0 ^ 2 + 2 / p.2 1 ^ 2 +
        (2 / p.2 2 ^ 2) * (r⁻¹) ^ 2 := by
    simp [_root_.GD.N0106.N0428.N0770.N1750.d008367, Fin.sum_univ_succ, _root_.GD.N0106.N0428.N0770.N1697.d021838,
      _root_.GD.N0106.N0428.N0770.N1750.d008366, _root_.GD.N0106.N0428.N0770.N1702.d008357]
    <;> field_simp [hr.ne', hz 0, hz 1, hz 2]
    <;> ring
  rw [hnum, hden]



theorem d021844 (mu : ℝ)
    (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (hz : ∀ i, p.2 i ≠ 0) :
    _root_.GD.N0106.N0428.N0770.N1745.d021824 2 mu (fun _ => 1) (_root_.GD.N0106.N0428.N0770.N1697.d021839 p) =
      (2 / p.2 0 ^ 2 * p.1 0 / Real.sqrt 2 +
        2 / p.2 1 ^ 2 * p.1 1 / Real.sqrt 2) /
        (2 / p.2 0 ^ 2 + 2 / p.2 1 ^ 2) := by
  rw [_root_.GD.N0106.N0428.N0770.N1697.d021842 (by norm_num) mu _
    (fun _ => by norm_num) (_root_.GD.N0106.N0428.N0770.N1697.d021839 p) (fun i => hz i.castSucc)]
  simp [_root_.GD.N0106.N0428.N0770.N1750.d008367, Fin.sum_univ_two, _root_.GD.N0106.N0428.N0770.N1697.d021839,
    _root_.GD.N0106.N0428.N0770.N1750.d008366, _root_.GD.N0106.N0428.N0770.N1702.d008357, mul_div_assoc]



theorem d021845 (mu : ℝ)
    (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (hz : ∀ i, p.2 i ≠ 0) :
    Tendsto (fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1745.d021824 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) p) atTop
      (𝓝 (_root_.GD.N0106.N0428.N0770.N1745.d021824 2 mu (fun _ => 1) (_root_.GD.N0106.N0428.N0770.N1697.d021839 p))) := by
  let n : ℝ := 2 / p.2 0 ^ 2 * p.1 0 / Real.sqrt 2 +
    2 / p.2 1 ^ 2 * p.1 1 / Real.sqrt 2
  let d : ℝ := 2 / p.2 0 ^ 2 + 2 / p.2 1 ^ 2
  let c : ℝ := 2 / p.2 2 ^ 2 * p.1 2 / Real.sqrt 2
  let q : ℝ := 2 / p.2 2 ^ 2
  have hd : 0 < d := add_pos
    (div_pos (by norm_num) (sq_pos_of_ne_zero (hz 0)))
    (div_pos (by norm_num) (sq_pos_of_ne_zero (hz 1)))
  have hi : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hn : Tendsto (fun r : ℝ => n + c * r⁻¹) atTop (𝓝 n) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := n)).add ((tendsto_const_nhds (x := c)).mul hi)
  have hden : Tendsto (fun r : ℝ => d + q * (r⁻¹) ^ 2) atTop (𝓝 d) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using
      (tendsto_const_nhds (x := d)).add ((tendsto_const_nhds (x := q)).mul (hi.pow 2))
  rw [_root_.GD.N0106.N0428.N0770.N1697.d021844 mu p hz]
  have hlimit := hn.div hden hd.ne'
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (_root_.GD.N0106.N0428.N0770.N1697.d021843 mu hr p hz).symm



theorem d021846 (mu : ℝ) :
    ∀ᵐ p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3,
      Tendsto (fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1745.d021824 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) p) atTop
        (𝓝 (_root_.GD.N0106.N0428.N0770.N1745.d021824 2 mu (fun _ => 1) (_root_.GD.N0106.N0428.N0770.N1697.d021839 p))) := by
  have hz : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3, ∀ i, p.2 i ≠ 0 := by
    exact (Measure.quasiMeasurePreserving_snd
      (μ := _root_.GD.N0106.N0428.N0770.N1751.d021742 3) (ν := _root_.GD.N0106.N0428.N0770.N1751.d021742 3)).ae
        (_root_.GD.N0106.N0428.N0770.N1753.d021767 3)
  filter_upwards [hz] with p hp
  exact _root_.GD.N0106.N0428.N0770.N1697.d021845 mu p hp



theorem d021847 (mu : ℝ) :
    ∀ᵐ p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3,
      Tendsto (fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1745.d021825 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) p) atTop
        (𝓝 (_root_.GD.N0106.N0428.N0770.N1745.d021825 2 mu (fun _ => 1) (_root_.GD.N0106.N0428.N0770.N1697.d021839 p))) := by
  filter_upwards [_root_.GD.N0106.N0428.N0770.N1697.d021846 mu] with p hp
  exact hp.pow 2




theorem d021848 (mu : ℝ) :
    (∫ p, _root_.GD.N0106.N0428.N0770.N1745.d021825 2 mu (fun _ => 1) (_root_.GD.N0106.N0428.N0770.N1697.d021839 p) ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3) =
      3 / 8 := by
  let theta : _root_.GD.N0232.N0719.N0859.d010809 2 :=
    ⟨mu, (fun _ => 1), (fun _ => by norm_num)⟩
  calc
    _ = ∫ q, _root_.GD.N0106.N0428.N0770.N1745.d021825 2 mu (fun _ => 1) q
        ∂(_root_.GD.N0106.N0428.N0770.N1745.d021822 3).map _root_.GD.N0106.N0428.N0770.N1697.d021839 :=
      (integral_map_of_stronglyMeasurable _root_.GD.N0106.N0428.N0770.N1697.d021840
        (_root_.GD.N0106.N0428.N0770.N1745.d021827 2 mu (fun _ => 1)).stronglyMeasurable).symm
    _ = ∫ q, _root_.GD.N0106.N0428.N0770.N1745.d021825 2 mu (fun _ => 1) q ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 2 := by
      rw [_root_.GD.N0106.N0428.N0770.N1697.d021841.map_eq]
    _ = 3 / 8 := (_root_.GD.N0106.N0428.N0770.N1745.d021828 2 theta).trans
      (_root_.GD.N0106.N0428.N0770.N1749.d021806 theta rfl)


theorem d021849 (mu : ℝ) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1745.d021825 2 mu (fun _ => 1) (_root_.GD.N0106.N0428.N0770.N1697.d021839 p))
      (_root_.GD.N0106.N0428.N0770.N1745.d021822 3) := by
  by_contra h
  have hzero := integral_undef h
  rw [_root_.GD.N0106.N0428.N0770.N1697.d021848 mu] at hzero
  norm_num at hzero

end
end GD.N0106.N0428.N0770.N1697

#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021841
#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021842
#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021843
#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021844
#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021845
#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021846
#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021847

#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021848
#print axioms _root_.GD.N0106.N0428.N0770.N1697.d021849
