import GD.Module1560
import GD.Module0598






set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0766.N1691
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def d024082 (center : ι → ℝ × ℝ) (coeff : ι → ℝ) (w : ℝ)
    (x : ℝ × ℝ) : ℝ :=
  ∑ i, coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x

def d024083 (center : ℝ × ℝ) (w : ℝ) : Set (ℝ × ℝ) :=
  Icc (center.1 - w) (center.1 + w) ×ˢ Icc (center.2 - w) (center.2 + w)

theorem d024084 (center : ℝ × ℝ) (w : ℝ) :
    IsCompact (_root_.GD.N0106.N0428.N0766.N1691.d024083 center w) := isCompact_Icc.prod isCompact_Icc

theorem d024085 (center : ι → ℝ × ℝ) (coeff : ι → ℝ)
    {w : ℝ} (hw : 0 < w) : Continuous (_root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w) := by
  exact continuous_finset_sum _ fun i _ =>
    continuous_const.mul (_root_.GD.N0106.N0428.N0766.N1691.d024069 (center i).1 (center i).2 w hw)


theorem d024086 {center : ℝ × ℝ} {w : ℝ} (hw : 0 ≤ w)
    {x : ℝ × ℝ} (hx : _root_.GD.N0118.d008583 center.1 center.2 w x ≠ 0) :
    x ∈ _root_.GD.N0106.N0428.N0766.N1691.d024083 center w :=
  _root_.GD.N0106.N0428.N0766.N1691.d024079 center.1 center.2 w hw
    (subset_tsupport _ hx)

theorem d024087 (center : ι → ℝ × ℝ) (coeff : ι → ℝ)
    {w : ℝ} (hw : 0 ≤ w) :
    tsupport (_root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w) ⊆ ⋃ i, _root_.GD.N0106.N0428.N0766.N1691.d024083 (center i) w := by
  apply closure_minimal ?_ (isClosed_iUnion_of_finite fun i =>
    (_root_.GD.N0106.N0428.N0766.N1691.d024084 (center i) w).isClosed)
  intro x hx
  change _root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w x ≠ 0 at hx
  by_contra hout
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  have hz : _root_.GD.N0118.d008583 (center i).1 (center i).2 w x = 0 := by
    by_contra hn
    exact hout (mem_iUnion.mpr ⟨i, _root_.GD.N0106.N0428.N0766.N1691.d024086 hw hn⟩)
  rw [hz, mul_zero]

theorem d024088 (center : ι → ℝ × ℝ) (coeff : ι → ℝ)
    {w : ℝ} (hw : 0 ≤ w) : HasCompactSupport (_root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w) := by
  exact (isCompact_iUnion fun i => _root_.GD.N0106.N0428.N0766.N1691.d024084 (center i) w).of_isClosed_subset
    (isClosed_tsupport _) (_root_.GD.N0106.N0428.N0766.N1691.d024087 center coeff hw)


theorem d024089 (center : ι → ℝ × ℝ) (coeff : ι → ℝ)
    {w : ℝ} (hw : 0 < w) (x : ℝ × ℝ) :
    |_root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w x| ≤ (∑ i, |coeff i|) * (w⁻¹)^2 := by
  unfold _root_.GD.N0106.N0428.N0766.N1691.d024082
  calc
    _ ≤ ∑ i, |coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |coeff i| * (w⁻¹)^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (_root_.GD.N0106.N0428.N0766.N1691.d024072 _ _ _ x hw)]
      exact mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0766.N1691.d024073 _ _ _ x hw) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem d024090 (center : ι → ℝ × ℝ) (coeff : ι → ℝ)
    {w : ℝ} (hw : 0 < w) :
    Integrable (_root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w) (volume.prod volume) :=
  (_root_.GD.N0106.N0428.N0766.N1691.d024085 center coeff hw).integrable_of_hasCompactSupport
    (_root_.GD.N0106.N0428.N0766.N1691.d024088 center coeff hw.le)




theorem d024091 (center : ι → ℝ × ℝ) (coeff : ι → ℝ)
    {w : ℝ} (hw : 0 ≤ w)
    (hdisj : Pairwise fun i j => Disjoint (_root_.GD.N0106.N0428.N0766.N1691.d024083 (center i) w) (_root_.GD.N0106.N0428.N0766.N1691.d024083 (center j) w))
    {i j : ι} (hij : i ≠ j) (x : ℝ × ℝ) :
    (coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x) *
      (coeff j * _root_.GD.N0118.d008583 (center j).1 (center j).2 w x) = 0 := by
  by_cases hi : _root_.GD.N0118.d008583 (center i).1 (center i).2 w x = 0
  · simp [hi]
  by_cases hj : _root_.GD.N0118.d008583 (center j).1 (center j).2 w x = 0
  · simp [hj]
  exact False.elim (Set.disjoint_left.mp (hdisj hij)
    (_root_.GD.N0106.N0428.N0766.N1691.d024086 hw hi) (_root_.GD.N0106.N0428.N0766.N1691.d024086 hw hj))

theorem d024092 (center : ι → ℝ × ℝ) (coeff : ι → ℝ)
    {w : ℝ} (hw : 0 ≤ w)
    (hdisj : Pairwise fun i j => Disjoint (_root_.GD.N0106.N0428.N0766.N1691.d024083 (center i) w) (_root_.GD.N0106.N0428.N0766.N1691.d024083 (center j) w))
    (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w x ^ 2 =
      ∑ i, (coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x)^2 := by
  exact _root_.GD.N0147.d008609 Finset.univ
    (fun i x => coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x)
    (fun _ _ _ _ hij x => _root_.GD.N0106.N0428.N0766.N1691.d024091 center coeff hw hdisj hij x) x

end
end GD.N0106.N0428.N0766.N1691

#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024085
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024087
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024088
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024089
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024090
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024091
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024092
