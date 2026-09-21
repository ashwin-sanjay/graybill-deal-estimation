import GD.Module1725
import GD.Module0524
import GD.Module0610
import GD.Module0613
import GD.Module0429







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory

namespace GD.N0106.N0428.N0766.N1694
noncomputable section

open _root_.GD.N0232.N0720.N1254
open _root_.GD.N0106.N0428.N0766.N1692 _root_.GD.N0106.N0428.N0766.N1692.N1763 _root_.GD.N0106.N0428.N0766.N1691


def d028769 (alpha beta e : ℝ) : ℝ :=
  (alpha ^ alpha * beta ^ beta * Real.Gamma (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) /
    ((2 : ℝ) ^ ((3 : ℝ) / 2) * Real.Gamma alpha * Real.Gamma beta *
      Real.Gamma ((3 : ℝ) / 2))) *
    e ^ (alpha + (3 : ℝ) / 2) * (1 - e) ^ (beta + (3 : ℝ) / 2)

theorem d028770 (alpha beta e : ℝ) :
    _root_.GD.N0120.d008813 alpha beta e = _root_.GD.N0106.N0428.N0766.N1694.d028769 alpha beta e := by
  unfold _root_.GD.N0120.d008813 _root_.GD.N0116.d006507
    _root_.GD.N0116.d006506 _root_.GD.N0116.d006508 _root_.GD.N0106.N0428.N0766.N1694.d028769
    _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
  ring

theorem d028771 {alpha beta e : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he0 : 0 < e) (he1 : e < 1) :
    0 < _root_.GD.N0106.N0428.N0766.N1694.d028769 alpha beta e := by
  rw [← _root_.GD.N0106.N0428.N0766.N1694.d028770]
  exact _root_.GD.N0120.d008823 ha hb he0 he1



theorem d028772 (alpha beta e : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0120.d008811 alpha beta e x = _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) := by
  simp only [_root_.GD.N0120.d008811, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847,
    _root_.GD.N0116.d006509, _root_.GD.N0232.N0720.N1254.d002513, _root_.GD.N0232.N0720.N1254.d002510, Real.sqrt_eq_rpow]

theorem d028773 (alpha beta e : ℝ) (q : ℝ × ℝ → ℝ)
    (hs : tsupport q ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844)
    (hint : Integrable (fun x => q x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x)) (volume.prod volume)) :
    _root_.GD.N0120.d008816 alpha beta e q = _root_.GD.N0106.N0428.N0766.d028738 alpha beta q e := by
  rw [_root_.GD.N0106.N0428.N0766.d028746 alpha beta e q hs hint]
  unfold _root_.GD.N0120.d008816 _root_.GD.N0120.d008812
  apply setIntegral_congr_fun measurableSet_Ioo
  intro L _
  apply setIntegral_congr_fun measurableSet_Ioi
  intro F _
  dsimp only
  rw [_root_.GD.N0106.N0428.N0766.N1694.d028772]
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848
  ring

theorem d028774 (alpha beta e : ℝ) (q : ℝ × ℝ → ℝ)
    (hs : tsupport q ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844)
    (hint : Integrable (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * q x ^ 2)
      (volume.prod volume)) :
    _root_.GD.N0120.d008817 alpha beta e q = _root_.GD.N0106.N0428.N0766.d028739 alpha beta q e := by
  rw [_root_.GD.N0106.N0428.N0766.d028747 alpha beta e q hs hint]
  unfold _root_.GD.N0120.d008817 _root_.GD.N0120.d008812
  apply setIntegral_congr_fun measurableSet_Ioo
  intro L _
  apply setIntegral_congr_fun measurableSet_Ioi
  intro F _
  dsimp only
  rw [_root_.GD.N0106.N0428.N0766.N1694.d028772]
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848
  ring




theorem d028775 {alpha beta e C : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he0 : 0 < e) (he1 : e < 1)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q) (hC : ∀ x, |q x| ≤ C)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsupport : Function.support q ⊆ K) (hOmega : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    _root_.GD.N0120.d008814 alpha beta e q =
        _root_.GD.N0106.N0428.N0766.N1694.d028769 alpha beta e * _root_.GD.N0106.N0428.N0766.d028738 alpha beta q e ∧
      _root_.GD.N0120.d008815 alpha beta e q =
        _root_.GD.N0106.N0428.N0766.N1694.d028769 alpha beta e * _root_.GD.N0106.N0428.N0766.d028739 alpha beta q e := by
  have hs : tsupport q ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 :=
    (show tsupport q ⊆ K from closure_minimal hsupport hK.isClosed).trans hOmega
  have hInt := _root_.GD.N0106.N0428.N0766.d007877
    ha hb ⟨he0.le, he1.le⟩ q hq hC hK hsupport hOmega
  have htrace : Integrable (fun x => q x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x))
      (volume.prod volume) := by
    simpa only [mul_comm] using hInt.1
  have hTargetTrace := _root_.GD.N0108.d008886
    ha hb he0 he1 q hq hC
  have hTargetEnergy := _root_.GD.N0108.d008887
    ha hb he0 he1 q hq hC
  have hTraceFubini := _root_.GD.N0143.d006698 _ hTargetTrace
  have hEnergyFubini := _root_.GD.N0143.d006698 _ hTargetEnergy
  have hT := _root_.GD.N0120.d008825
    ha hb he0 he1 q hTargetTrace hTraceFubini
  have hE := _root_.GD.N0120.d008826
    ha hb he0 he1 q hTargetEnergy hEnergyFubini
  rw [_root_.GD.N0106.N0428.N0766.N1694.d028770, _root_.GD.N0106.N0428.N0766.N1694.d028773 alpha beta e q hs htrace] at hT
  rw [_root_.GD.N0106.N0428.N0766.N1694.d028770, _root_.GD.N0106.N0428.N0766.N1694.d028774 alpha beta e q hs hInt.2] at hE
  exact ⟨hT, hE⟩


abbrev d028776 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : ℝ × ℝ → ℝ :=
  _root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b)

theorem d028777 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    _root_.GD.N0120.d008814 a.val b.val e (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) =
        _root_.GD.N0106.N0428.N0766.N1694.d028769 a.val b.val e * _root_.GD.N0106.N0428.N0766.d028738 a.val b.val (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) e ∧
      _root_.GD.N0120.d008815 a.val b.val e (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) =
        _root_.GD.N0106.N0428.N0766.N1694.d028769 a.val b.val e * _root_.GD.N0106.N0428.N0766.d028739 a.val b.val (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) e := by
  have hp := _root_.GD.N0106.N0428.N0766.d028760 a b
  obtain ⟨C, _, hC⟩ := hp.bounded
  exact _root_.GD.N0106.N0428.N0766.N1694.d028775 a.property b.property he0 he1 (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b)
    hp.continuous.measurable hC hp.compact (subset_tsupport _) hp.inside




theorem d028778 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    ∃ epsilon > 0, ∀ e ∈ Ioo (0 : ℝ) 1,
      2 * epsilon * _root_.GD.N0120.d008814 a.val b.val e (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) +
        epsilon ^ 2 * _root_.GD.N0120.d008815 a.val b.val e (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) < 0 := by
  obtain ⟨epsilon, hepsilon, hnegative⟩ := (_root_.GD.N0106.N0428.N0766.d028760 a b).improves
  refine ⟨epsilon, hepsilon, ?_⟩
  intro e he
  obtain ⟨hT, hE⟩ := _root_.GD.N0106.N0428.N0766.N1694.d028777 a b he.1 he.2
  rw [hT, hE]
  calc
    _ = _root_.GD.N0106.N0428.N0766.N1694.d028769 a.val b.val e *
        (2 * epsilon * _root_.GD.N0106.N0428.N0766.d028738 a.val b.val (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) e +
          epsilon ^ 2 * _root_.GD.N0106.N0428.N0766.d028739 a.val b.val (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) e) := by ring
    _ < 0 := mul_neg_of_pos_of_neg
      (_root_.GD.N0106.N0428.N0766.N1694.d028771 a.property b.property he.1 he.2)
      (hnegative e ⟨he.1.le, he.2.le⟩)



theorem d028779 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794)
    {totalScale : ℝ} (hscale : 0 < totalScale) :
    ∃ epsilon > 0, ∀ e ∈ Ioo (0 : ℝ) 1,
      totalScale *
        (2 * epsilon * _root_.GD.N0120.d008814 a.val b.val e (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b) +
          epsilon ^ 2 * _root_.GD.N0120.d008815 a.val b.val e (_root_.GD.N0106.N0428.N0766.N1694.d028776 a b)) < 0 := by
  obtain ⟨epsilon, hepsilon, hnegative⟩ := _root_.GD.N0106.N0428.N0766.N1694.d028778 a b
  exact ⟨epsilon, hepsilon, fun e he => mul_neg_of_pos_of_neg hscale (hnegative e he)⟩

end
end GD.N0106.N0428.N0766.N1694

#print axioms _root_.GD.N0106.N0428.N0766.N1694.d028770
#print axioms _root_.GD.N0106.N0428.N0766.N1694.d028771
#print axioms _root_.GD.N0106.N0428.N0766.N1694.d028772
#print axioms _root_.GD.N0106.N0428.N0766.N1694.d028775
#print axioms _root_.GD.N0106.N0428.N0766.N1694.d028777
#print axioms _root_.GD.N0106.N0428.N0766.N1694.d028778
#print axioms _root_.GD.N0106.N0428.N0766.N1694.d028779
