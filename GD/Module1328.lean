import GD.Module1326
import GD.Module1327
import GD.Module0549

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0151
noncomputable section
open _root_.GD.N0150
open _root_.GD.N0225.N0539
open _root_.GD.N0225.N0542
open _root_.GD.N0213.N0495

variable {k : ℕ}

def d021637 (a b : ℝ) (i j : Fin k) (β : Fin k → ℝ) : ℝ :=
  ∫ q, _root_.GD.N0150.d021618 (_root_.GD.N0150.d021619 (a * β i) (b * β j) q)
    ∂(gammaMeasure a 1).prod (gammaMeasure b 1)

def d021638 (a b : ℝ) (i j : Fin k) (β : Fin k → ℝ) : ℝ :=
  ∫ q, _root_.GD.N0150.d021618 q ∂(gammaMeasure a (a * β i)).prod (gammaMeasure b (b * β j))

theorem d021639 (a b : ℝ)
    (i j : Fin k) : Measurable (_root_.GD.N0151.d021637 a b i j) := by
  have hm : Measurable (fun p : (Fin k → ℝ) × (ℝ × ℝ) =>
      _root_.GD.N0150.d021618 (_root_.GD.N0150.d021619 (a * p.1 i) (b * p.1 j) p.2)) := by
    unfold _root_.GD.N0150.d021618 _root_.GD.N0150.d021619
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem d021640 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i j : Fin k) {β : Fin k → ℝ} (hi : 0 < β i) (hj : 0 < β j) :
    _root_.GD.N0151.d021637 a b i j β = _root_.GD.N0151.d021638 a b i j β := by
  unfold _root_.GD.N0151.d021637 _root_.GD.N0151.d021638
  rw [← _root_.GD.N0150.d021625 ha hb (mul_pos ha hi) (mul_pos hb hj),
    integral_map (_root_.GD.N0150.d021621 _ _).aemeasurable
      _root_.GD.N0150.d021620.aestronglyMeasurable]

theorem d021641 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i j : Fin k) {β : Fin k → ℝ} (hi : 0 < β i) (hj : 0 < β j) :
    0 ≤ _root_.GD.N0151.d021638 a b i j β := by
  apply integral_nonneg_of_ae
  filter_upwards [_root_.GD.N0150.d021627 ha hb (mul_pos ha hi) (mul_pos hb hj)] with q hq
  exact inv_nonneg.mpr (add_nonneg hq.1.le hq.2.le)

theorem d021642 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : 1 < a + b) (i j : Fin k) {β : Fin k → ℝ} (hβ : ∀ l, 0 < β l) :
    _root_.GD.N0151.d021638 a b i j β ≤ max a b / (a + b - 1) * (∑ l, β l) := by
  have hi : β i ≤ ∑ l, β l :=
    Finset.single_le_sum (fun l _ => (hβ l).le) (Finset.mem_univ i)
  have hj : β j ≤ ∑ l, β l :=
    Finset.single_le_sum (fun l _ => (hβ l).le) (Finset.mem_univ j)
  have hM : max (a * β i) (b * β j) ≤ max a b * (∑ l, β l) := by
    apply max_le
    · exact (mul_le_mul_of_nonneg_right (le_max_left a b) (hβ i).le).trans
        (mul_le_mul_of_nonneg_left hi (ha.le.trans (le_max_left a b)))
    · exact (mul_le_mul_of_nonneg_right (le_max_right a b) (hβ j).le).trans
        (mul_le_mul_of_nonneg_left hj (ha.le.trans (le_max_left a b)))
  exact (_root_.GD.N0150.d021630 ha hb hab (mul_pos ha (hβ i))
    (mul_pos hb (hβ j))).trans ((div_le_div_of_nonneg_right hM (by linarith)).trans_eq
      (by ring))

theorem d021643 (α : Fin k → ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i j : Fin k) :
    _root_.GD.N0151.d021638 a b i j =ᵐ[_root_.GD.N0225.N0539.d008044 α] _root_.GD.N0151.d021637 a b i j := by
  filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
  exact (_root_.GD.N0151.d021640 ha hb i j (hβ i) (hβ j)).symm

theorem d021644 (α : Fin k → ℝ)
    (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b)
    (i j : Fin k) {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => _root_.GD.N0151.d021638 a b i j β *
      _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2) (_root_.GD.N0225.N0539.d008044 α) := by
  have hm : Measurable (fun β : Fin k → ℝ => _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2) := by
    dsimp only [_root_.GD.N0213.N0495.d007175, _root_.GD.N0213.N0495.d007174]
    fun_prop
  have hpm : AEStronglyMeasurable (_root_.GD.N0151.d021638 a b i j) (_root_.GD.N0225.N0539.d008044 α) :=
    (_root_.GD.N0151.d021639 a b i j).aestronglyMeasurable.congr
      (_root_.GD.N0151.d021643 α ha hb i j).symm
  apply ((_root_.GD.N0225.N0542.d008165 α hα hsum hL).const_mul
    (max a b / (a + b - 1))).mono' (hpm.mul hm.aestronglyMeasurable)
  filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (_root_.GD.N0151.d021641 ha hb i j (hβ i) (hβ j)) (sq_nonneg _))]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (_root_.GD.N0151.d021642 ha hb hab i j hβ) (sq_nonneg (_root_.GD.N0213.N0495.d007175 L (∑ l, β l)))

theorem d021645 (α : Fin k → ℝ)
    (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b)
    (i j : Fin k) {L : ℝ} (hL : 0 < L) :
    0 ≤ (∫ β, _root_.GD.N0151.d021638 a b i j β * _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) ∧
      (∫ β, _root_.GD.N0151.d021638 a b i j β * _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) ≤
        max a b / (a + b - 1) *
          (∫ β, (∑ l, β l) * _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
    exact mul_nonneg (_root_.GD.N0151.d021641 ha hb i j (hβ i) (hβ j)) (sq_nonneg _)
  · rw [← integral_const_mul]
    apply integral_mono_ae (_root_.GD.N0151.d021644 α hα hsum ha hb hab i j hL)
      ((_root_.GD.N0225.N0542.d008165 α hα hsum hL).const_mul (max a b / (a + b - 1)))
    filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (_root_.GD.N0151.d021642 ha hb hab i j hβ) (sq_nonneg (_root_.GD.N0213.N0495.d007175 L (∑ l, β l)))

theorem d021646 (α : Fin k → ℝ)
    (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b) (i j : Fin k) :
    Tendsto (fun n : ℕ => ∫ β, _root_.GD.N0151.d021638 a b i j β *
      _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ l, β l) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n : ℕ =>
    (_root_.GD.N0151.d021645 α hα hsum ha hb hab i j (L := (n : ℝ) + 1)
      (by positivity)).1) (Eventually.of_forall fun n : ℕ =>
    (_root_.GD.N0151.d021645 α hα hsum ha hb hab i j (L := (n : ℝ) + 1)
      (by positivity)).2)
  simpa only [mul_zero] using
    (_root_.GD.N0225.N0539.d008061 α hα hsum).const_mul (max a b / (a + b - 1))

def d021647 (a : Fin k → ℝ) (i j : Fin k) (β : Fin k → ℝ) : ℝ :=
  ∫ t, (t i + t j)⁻¹ ∂Measure.pi (fun l => gammaMeasure (a l) (a l * β l))

theorem d021648 (a : Fin k → ℝ) (ha : ∀ l, 0 < a l)
    (i j : Fin k) (hij : i ≠ j) {β : Fin k → ℝ} (hβ : ∀ l, 0 < β l) :
    _root_.GD.N0151.d021647 a i j β = _root_.GD.N0151.d021638 (a i) (a j) i j β := by
  letI (l : Fin k) := isProbabilityMeasure_gammaMeasure (ha l) (mul_pos (ha l) (hβ l))
  have h := integral_map
    (μ := Measure.pi (fun l => gammaMeasure (a l) (a l * β l)))
    (f := _root_.GD.N0150.d021618)
    (show Measurable (fun t : Fin k → ℝ => (t i, t j)) by fun_prop).aemeasurable
    _root_.GD.N0150.d021620.aestronglyMeasurable
  rw [_root_.GD.N0105.d021633 _ i j hij] at h
  exact h.symm

theorem d021649 (α a : Fin k → ℝ)
    (ha : ∀ l, 0 < a l) (i j : Fin k) (hij : i ≠ j) :
    _root_.GD.N0151.d021647 a i j =ᵐ[_root_.GD.N0225.N0539.d008044 α] _root_.GD.N0151.d021638 (a i) (a j) i j := by
  filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
  exact _root_.GD.N0151.d021648 a ha i j hij hβ

theorem d021650 (α a : Fin k → ℝ)
    (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1) (ha : ∀ l, 0 < a l)
    (i j : Fin k) (hij : i ≠ j) (hab : 1 < a i + a j) {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => _root_.GD.N0151.d021647 a i j β *
      _root_.GD.N0213.N0495.d007175 L (∑ l, β l) ^ 2) (_root_.GD.N0225.N0539.d008044 α) := by
  apply (_root_.GD.N0151.d021644 α hα hsum (ha i) (ha j) hab i j hL).congr
  filter_upwards [_root_.GD.N0151.d021649 α a ha i j hij] with β hβ
  rw [hβ]

theorem d021651 (α a : Fin k → ℝ)
    (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1) (ha : ∀ l, 0 < a l)
    (i j : Fin k) (hij : i ≠ j) (hab : 1 < a i + a j) :
    Tendsto (fun n : ℕ => ∫ β, _root_.GD.N0151.d021647 a i j β *
      _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ l, β l) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) atTop (𝓝 0) := by
  have heq (n : ℕ) :
      (∫ β, _root_.GD.N0151.d021647 a i j β * _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ l, β l) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) =
      (∫ β, _root_.GD.N0151.d021638 (a i) (a j) i j β *
        _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ l, β l) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) := by
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0151.d021649 α a ha i j hij] with β hβ
    rw [hβ]
  simp_rw [heq]
  exact _root_.GD.N0151.d021646 α hα hsum (ha i) (ha j) hab i j

theorem d021652 (α a : Fin k → ℝ)
    (hα : ∀ l, 0 < α l) (hsum : ∑ l, α l = 1) (ha : ∀ l, 0 < a l)
    (S : Finset (Fin k × Fin k)) (c : Fin k × Fin k → ℝ)
    (hS : ∀ p ∈ S, p.1 ≠ p.2) (hab : ∀ p ∈ S, 1 < a p.1 + a p.2) :
    Tendsto (fun n : ℕ => ∫ β, ∑ p ∈ S, c p * (_root_.GD.N0151.d021647 a p.1 p.2 β *
      _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ l, β l) ^ 2) ∂_root_.GD.N0225.N0539.d008044 α) atTop (𝓝 0) := by
  have heq (n : ℕ) :
      (∫ β, ∑ p ∈ S, c p * (_root_.GD.N0151.d021647 a p.1 p.2 β *
        _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ l, β l) ^ 2) ∂_root_.GD.N0225.N0539.d008044 α) =
      ∑ p ∈ S, c p * (∫ β, _root_.GD.N0151.d021647 a p.1 p.2 β *
        _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ l, β l) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) := by
    rw [integral_finsetSum S (fun p hp =>
      (_root_.GD.N0151.d021650 α a hα hsum ha p.1 p.2 (hS p hp)
        (hab p hp) (by positivity)).const_mul (c p))]
    simp only [integral_const_mul]
  simp_rw [heq]
  simpa only [mul_zero, Finset.sum_const_zero] using
    tendsto_finsetSum S (fun p hp =>
      (_root_.GD.N0151.d021651 α a hα hsum ha p.1 p.2 (hS p hp)
        (hab p hp)).const_mul (c p))

theorem d021653 (n m : ℕ) :
    1 < ((n : ℝ) - 1) / 2 + ((m : ℝ) - 1) / 2 ↔ 4 < n + m := by
  constructor
  · intro h
    have hr : (4 : ℝ) < (n : ℝ) + (m : ℝ) := by linarith
    exact_mod_cast hr
  · intro h
    have hr : (4 : ℝ) < (n : ℝ) + (m : ℝ) := by exact_mod_cast h
    linarith

theorem d021654 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    1 < ((n : ℝ) - 1) / 2 + ((m : ℝ) - 1) / 2 ↔ (n, m) ≠ (2, 2) := by
  rw [_root_.GD.N0151.d021653]
  constructor
  · intro h heq
    have hn2 : n = 2 := congrArg Prod.fst heq
    have hm2 : m = 2 := congrArg Prod.snd heq
    omega
  · intro h
    by_contra hsum
    have hn2 : n = 2 := by omega
    have hm2 : m = 2 := by omega
    exact h (by simp only [hn2, hm2])

#print axioms _root_.GD.N0151.d021639
#print axioms _root_.GD.N0151.d021640
#print axioms _root_.GD.N0151.d021641
#print axioms _root_.GD.N0151.d021642
#print axioms _root_.GD.N0151.d021643
#print axioms _root_.GD.N0151.d021644
#print axioms _root_.GD.N0151.d021645
#print axioms _root_.GD.N0151.d021646
#print axioms _root_.GD.N0151.d021648
#print axioms _root_.GD.N0151.d021649
#print axioms _root_.GD.N0151.d021650
#print axioms _root_.GD.N0151.d021651
#print axioms _root_.GD.N0151.d021652
#print axioms _root_.GD.N0151.d021653
#print axioms _root_.GD.N0151.d021654

end
end GD.N0151
