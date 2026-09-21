import GD.Module1714
import GD.Module1667
import GD.Module1425
import GD.Module1440
import GD.Module1371

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace GD.N0040
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0072 _root_.GD.N0021 _root_.GD.N0033
open _root_.GD.N0102.N0420 _root_.GD.N0102.N0422
open _root_.GD.N0099
open _root_.GD.N0076.N0310.N0759
open _root_.GD.N0232.N0720.N1467

variable {k : ℕ}


def d028692 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (i : Fin k) : ℝ := (sizes i : ℝ) / θ.scale i ^ 2

theorem d028693 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    0 < _root_.GD.N0040.d028692 sizes θ i :=
  div_pos (Nat.cast_pos.mpr (by have := hn i; omega)) (sq_pos_of_pos (θ.scale_pos i))



theorem d028694 (hk : 0 < k) (v q : Fin k → ℝ)
    (hv : ∀ i, 0 < v i) (hq : ∀ i, 0 < q i) :
    _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i)) = _root_.GD.N0102.N0420.d028256 (fun i => (v i)⁻¹) q := by
  have hd : _root_.GD.N0102.N0420.d028253 (fun i => (v i)⁻¹) q = _root_.GD.N0102.N0422.d028281 (fun i => v i * q i) := by
    unfold _root_.GD.N0102.N0420.d028253 _root_.GD.N0102.N0422.d028281
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hS := _root_.GD.N0102.N0422.d028283 hk (fun i => v i * q i) (fun i => mul_pos (hv i) (hq i))
  unfold _root_.GD.N0072.d007621 _root_.GD.N0102.N0420.d028256 _root_.GD.N0102.N0420.d028255
  rw [hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0102.N0422.d028289 hk _ (fun j => mul_pos (hv j) (hq j))]
  field_simp [(hv i).ne', (hq i).ne', hS.ne']


theorem d028695
    (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0232.N0719.N0859.d010840 k sizes θ
      (_root_.GD.N0232.N0719.N0900.d009111 k sizes)).toReal =
      ∫ q, _root_.GD.N0102.N0420.d028256 (_root_.GD.N0040.d028692 sizes θ) q
        ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273 sizes) := by
  let v : Fin k → ℝ := fun i => θ.scale i ^ 2 / (sizes i : ℝ)
  have hv (i : Fin k) : 0 < v i :=
    div_pos (sq_pos_of_pos (θ.scale_pos i))
      (Nat.cast_pos.mpr (by have := hn i; omega))
  rw [_root_.GD.N0102.N0423.d028277 sizes hk hn θ]
  have heq : (∫ q, _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i))
      ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273 sizes)) =
      (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i)))
        ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273 sizes)).toReal := by
    apply integral_eq_lintegral_of_nonneg_ae
    · exact ae_of_all _ fun q => _root_.GD.N0072.d007622 v _ (fun i => (hv i).le)
    · have hg : Measurable (fun q : Fin k → ℝ =>
          _root_.GD.N0021.d023313 (fun i => v i * q i)) :=
        _root_.GD.N0021.d023314.comp (by fun_prop)
      have hm : Measurable (fun q : Fin k → ℝ =>
          _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i))) := by
        unfold _root_.GD.N0072.d007621
        apply Finset.measurable_sum
        intro i _
        exact (((measurable_pi_apply i).comp hg).pow_const 2).mul_const (v i)
      exact hm.aestronglyMeasurable
  change (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i)))
    ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273 sizes)).toReal = _
  rw [← heq]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0033.d028240 _
    (_root_.GD.N0102.N0423.d028275 sizes hn)] with q hq
  rw [_root_.GD.N0040.d028694 hk v q hv hq]
  congr 1
  funext i
  simp only [v, _root_.GD.N0040.d028692, inv_div]



def d028696 (i : Fin (k + 2)) (j : Fin (k + 1)) (a b : ℝ)
    (l : Fin (k + 2)) : ℝ :=
  if l = i then a else if l = i.succAbove j then b else 0

theorem d028697 (i : Fin (k + 2)) (j : Fin (k + 1))
    (a b : ℝ) (q : Fin (k + 2) → ℝ) :
    _root_.GD.N0102.N0420.d028256 (_root_.GD.N0040.d028696 i j a b) q =
      (a / (q i) ^ 2 + b / (q (i.succAbove j)) ^ 2) /
        (a / q i + b / q (i.succAbove j)) ^ 2 := by
  have hd : _root_.GD.N0102.N0420.d028253 (_root_.GD.N0040.d028696 i j a b) q =
      a / q i + b / q (i.succAbove j) := by
    unfold _root_.GD.N0102.N0420.d028253
    rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ j]
    simp [_root_.GD.N0040.d028696, Fin.succAbove_ne]
  unfold _root_.GD.N0102.N0420.d028256 _root_.GD.N0102.N0420.d028255
  rw [hd, Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ j]
  simp [_root_.GD.N0040.d028696, Fin.succAbove_ne, add_div]

private theorem d028698
    (shape : Fin k → ℝ) (hs : ∀ i, 0 < shape i)
    (i j : Fin k) (hij : i ≠ j) (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    (∫ q, f (q i, q j) ∂_root_.GD.N0033.d028239 shape) =
      ∫ z, f z ∂(gammaMeasure (shape i) (shape i)).prod
        (gammaMeasure (shape j) (shape j)) := by
  let μ : Fin k → Measure ℝ := fun i => gammaMeasure (shape i) (shape i)
  letI (i : Fin k) : IsProbabilityMeasure (μ i) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  have hp := _root_.GD.N0069.d022755 μ i j hij
  rw [← hp.map_eq]
  exact (integral_map_of_stronglyMeasurable hp.measurable hf.stronglyMeasurable).symm



theorem d028699
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (∫ q, _root_.GD.N0102.N0420.d028256 (_root_.GD.N0040.d028696 i j
        ((sizes i : ℝ) / θ.scale₁ ^ 2)
        ((sizes (i.succAbove j) : ℝ) / θ.scale₂ ^ 2)) q
      ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273 sizes)) =
      (_root_.GD.N0232.N0720.N1080.d014197
        (sizes i) (sizes (i.succAbove j)) θ
        (_root_.GD.N0232.N0720.N1080.d014175
          (sizes i) (sizes (i.succAbove j)))).toReal := by
  let f : ℝ × ℝ → ℝ := fun z =>
    (((sizes i : ℝ) / θ.scale₁ ^ 2) / z.1 ^ 2 +
      ((sizes (i.succAbove j) : ℝ) / θ.scale₂ ^ 2) / z.2 ^ 2) /
    (((sizes i : ℝ) / θ.scale₁ ^ 2) / z.1 +
      ((sizes (i.succAbove j) : ℝ) / θ.scale₂ ^ 2) / z.2) ^ 2
  have hf : Measurable f := by unfold f; fun_prop
  rw [← _root_.GD.N0076.N0310.N0759.d014247 (sizes i) (sizes (i.succAbove j)) (hn i)
    (hn (i.succAbove j)) θ]
  change _ = (_root_.GD.N0232.N0719.N0859.d010840 2
    (_root_.GD.N0232.N0720.N1467.d012537 (sizes i) (sizes (i.succAbove j))) (_root_.GD.N0076.N0310.N0759.d014240 θ)
    (_root_.GD.N0232.N0719.N0900.d009111 2
      (_root_.GD.N0232.N0720.N1467.d012537 (sizes i) (sizes (i.succAbove j))))).toReal
  rw [_root_.GD.N0040.d028695
    (_root_.GD.N0232.N0720.N1467.d012537 (sizes i) (sizes (i.succAbove j))) (by decide)
    (_root_.GD.N0076.N0310.N0759.d014241 _ _ (hn i) (hn (i.succAbove j))) (_root_.GD.N0076.N0310.N0759.d014240 θ)]
  have hleft := _root_.GD.N0040.d028698
    (_root_.GD.N0102.N0423.d028273 sizes)
    (_root_.GD.N0102.N0423.d028275 sizes hn)
    i (i.succAbove j) (Fin.succAbove_ne i j).symm f hf
  have hright := _root_.GD.N0040.d028698
    (_root_.GD.N0102.N0423.d028273
      (_root_.GD.N0232.N0720.N1467.d012537 (sizes i) (sizes (i.succAbove j))))
    (_root_.GD.N0102.N0423.d028275 _
      (_root_.GD.N0076.N0310.N0759.d014241 _ _ (hn i) (hn _))) 0 1 (by decide) f hf
  calc
    _ = ∫ q, f (q i, q (i.succAbove j))
      ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273 sizes) := by
        apply integral_congr_ae
        exact ae_of_all _ fun q => _root_.GD.N0040.d028697 i j _ _ q
    _ = _ := hleft
    _ = ∫ q, f (q 0, q 1)
      ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273
        (_root_.GD.N0232.N0720.N1467.d012537 (sizes i) (sizes (i.succAbove j)))) := by
      simpa only [_root_.GD.N0102.N0423.d028273,
        _root_.GD.N0232.N0720.N1467.d012538, _root_.GD.N0232.N0720.N1467.d012539] using hright.symm
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro q
      simp only [_root_.GD.N0102.N0420.d028256, _root_.GD.N0102.N0420.d028255, _root_.GD.N0102.N0420.d028253, Fin.sum_univ_two,
        _root_.GD.N0040.d028692, _root_.GD.N0076.N0310.N0759.d014240, Matrix.cons_val_zero, Matrix.cons_val_one,
        _root_.GD.N0232.N0720.N1467.d012538, _root_.GD.N0232.N0720.N1467.d012539, f, add_div]




theorem d028700
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l)
    (θ : _root_.GD.N0232.N0720.N1080.d014168)
    (H : ℕ → ℝ) (hH : ∀ r, 0 < H r) (hHt : Tendsto H atTop atTop) :
    Tendsto (fun r => (_root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes
      (_root_.GD.N0099.d022905 i j θ (H r) (hH r))
      (_root_.GD.N0232.N0719.N0900.d009111 (k + 2) sizes)).toReal) atTop
      (𝓝 ((_root_.GD.N0232.N0720.N1080.d014197
        (sizes i) (sizes (i.succAbove j)) θ
        (_root_.GD.N0232.N0720.N1080.d014175
          (sizes i) (sizes (i.succAbove j)))).toReal)) := by
  classical
  let S : Finset (Fin (k + 2)) := {i, i.succAbove j}
  let p0 := _root_.GD.N0040.d028696 i j ((sizes i : ℝ) / θ.scale₁ ^ 2)
    ((sizes (i.succAbove j) : ℝ) / θ.scale₂ ^ 2)
  let p : ℕ → Fin (k + 2) → ℝ := fun r =>
    _root_.GD.N0040.d028692 sizes (_root_.GD.N0099.d022905 i j θ (H r) (hH r))
  have hp0 : ∀ l ∈ S, 0 < p0 l := by
    intro l hl
    rcases Finset.mem_insert.mp hl with hl' | hl
    · subst l
      simp only [p0, _root_.GD.N0040.d028696]
      exact div_pos (Nat.cast_pos.mpr (by have := hn i; omega))
        (sq_pos_of_pos θ.scale₁_pos)
    · have hl' : l = i.succAbove j := Finset.mem_singleton.mp hl
      subst l
      simp only [p0, _root_.GD.N0040.d028696, Fin.succAbove_ne, if_false, if_true]
      exact div_pos (Nat.cast_pos.mpr (by have := hn (i.succAbove j); omega))
        (sq_pos_of_pos θ.scale₂_pos)
  have hz : ∀ l ∉ S, p0 l = 0 := by
    intro l hl
    have hi : l ≠ i := by intro h; apply hl; simp [S, h]
    have hj : l ≠ i.succAbove j := by intro h; apply hl; simp [S, h]
    simp [p0, _root_.GD.N0040.d028696, hi, hj]
  have hp : ∀ r l, 0 ≤ p r l := fun r l =>
    (_root_.GD.N0040.d028693 sizes hn _ l).le
  have hkeep : ∀ r, ∀ l ∈ S, p r l = p0 l := by
    intro r l hl
    rcases Finset.mem_insert.mp hl with hl' | hl
    · subst l
      simp [p, p0, _root_.GD.N0040.d028692, _root_.GD.N0099.d022905, _root_.GD.N0040.d028696]
    · have hl' : l = i.succAbove j := Finset.mem_singleton.mp hl
      subst l
      simp [p, p0, _root_.GD.N0040.d028692, _root_.GD.N0099.d022905, _root_.GD.N0040.d028696, Fin.succAbove_ne]
  have hlim : ∀ l, Tendsto (fun r => p r l) atTop (𝓝 (p0 l)) := by
    intro l
    by_cases hl : l ∈ S
    · simpa only [hkeep _ l hl] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => p0 l) atTop (𝓝 (p0 l)))
    · have hi : l ≠ i := by intro h; apply hl; simp [S, h]
      have hj : l ≠ i.succAbove j := by intro h; apply hl; simp [S, h]
      have hh := (hHt.inv_tendsto_atTop.pow 2).const_mul ((sizes l : ℝ) / 4)
      convert hh using 1
      · funext r
        simp only [p, _root_.GD.N0040.d028692, _root_.GD.N0099.d022905, if_neg hi, if_neg hj]
        simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, ← inv_pow]
        norm_num
        ring
      · simp [hz l hl]
  have hshape : ∀ l ∉ S,
      1 < _root_.GD.N0102.N0423.d028273 sizes l := by
    intro l hl
    have hi : l ≠ i := by intro h; apply hl; simp [S, h]
    have hj : l ≠ i.succAbove j := by intro h; apply hl; simp [S, h]
    have hn4 := hdeleted l hi hj
    have hnsub : 2 < sizes l - 1 := by omega
    have hr : (2 : ℝ) < (sizes l - 1 : ℕ) := by exact_mod_cast hnsub
    unfold _root_.GD.N0102.N0423.d028273
    linarith
  have hconv := _root_.GD.N0085.d028691
    (_root_.GD.N0102.N0423.d028273 sizes)
    (_root_.GD.N0102.N0423.d028275 sizes hn)
    S i (by simp [S]) p0 hp0 hz p hp hkeep hlim hshape
  simp_rw [_root_.GD.N0040.d028695 sizes (by omega) hn]
  rw [← _root_.GD.N0040.d028699 sizes hn i j θ]
  exact hconv

end
end GD.N0040

#print axioms _root_.GD.N0040.d028694
#print axioms _root_.GD.N0040.d028695
#print axioms _root_.GD.N0040.d028697
#print axioms _root_.GD.N0040.d028699
#print axioms _root_.GD.N0040.d028700
