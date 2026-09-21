import GD.Module0008
import GD.Module0097
import GD.Module0934















open Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1143

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1142
open _root_.GD.N0230.N0584
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0712

variable (m n : ℕ)



theorem d014680
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {a : ℝ} (ha : a < ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (delta : NNReal), 0 < delta ∧
      ∀ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        (∀ theta ∈ F,
          _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤
            _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (delta : ENNReal)) →
          a < ‖d‖ ^ 2 := by
  classical
  by_cases ha0 : a < 0
  · refine ⟨∅, 1, by norm_num, ?_⟩
    intro d hd
    exact ha0.trans_le (sq_nonneg ‖d‖)
  · have ha_nonneg : 0 ≤ a := le_of_not_gt ha0
    obtain ⟨F, hF⟩ :=
      _root_.GD.N0232.N0720.N1142.d014678 m n s.value ha
    let H := _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)
    let r : ℝ := Real.sqrt a
    let K : Set (WeakSpace ℝ H) :=
      toWeakSpace ℝ H '' Metric.closedBall (0 : H) r
    let packet : ↑F → _root_.GD.N0232.N0720.N1080.d014168 := fun i ↦ i.1
    let weakRisk : ↑F → WeakSpace ℝ H → ENNReal := fun i ↦
      _root_.GD.N0230.N0712.d001258 (_root_.GD.N0232.N0720.N1080.d014172 m n)
        (_root_.GD.N0232.N0720.N1080.d014171 m n (packet i)) (packet i).location
    let cap : ↑F → ENNReal := fun i ↦
      _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value
    have hKcompact : IsCompact K := by
      exact _root_.GD.N0230.N0633.d001199 (H := H) r
    have hweakRisk : ∀ i, LowerSemicontinuous (weakRisk i) := by
      intro i
      exact _root_.GD.N0230.N0712.d001260
        (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n (packet i))
        (_root_.GD.N0232.N0720.N1080.d014173 m n (packet i))
        (packet i).location
    have hdisjoint :
        Disjoint K
          (⋂ i, (weakRisk i) ⁻¹' Set.Iic (cap i)) := by
      rw [Set.disjoint_left]
      intro w hwK hwcap
      obtain ⟨d, hdball, rfl⟩ := hwK
      have hdcap : ∀ theta ∈ F,
          _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value := by
        intro theta htheta
        let i : ↑F := ⟨theta, htheta⟩
        have hi := Set.mem_iInter.mp hwcap i
        simpa [weakRisk, cap, packet, _root_.GD.N0230.N0712.d001258, _root_.GD.N0232.N0720.N1080.d014182, H, i] using hi
      have hstrict := hF d hdcap
      have hnorm : ‖d‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hdball
      have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg a
      have hr_sq : r ^ 2 = a := Real.sq_sqrt ha_nonneg
      have hsq : ‖d‖ ^ 2 ≤ r ^ 2 := by
        nlinarith [norm_nonneg d]
      linarith
    obtain ⟨delta, hdelta, hrelaxed⟩ :=
      _root_.GD.N0230.N0584.d000065
        K hKcompact weakRisk cap hweakRisk hdisjoint
    refine ⟨F, delta, hdelta, ?_⟩
    intro d hdcap
    by_contra hnot
    push Not at hnot
    have hnorm : ‖d‖ ≤ r := by
      have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg a
      have hr_sq : r ^ 2 = a := Real.sq_sqrt ha_nonneg
      nlinarith [norm_nonneg d]
    have hdK : toWeakSpace ℝ H d ∈ K := by
      exact ⟨d, by simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm, rfl⟩
    have hdrelaxed :
        toWeakSpace ℝ H d ∈
          ⋂ i, (weakRisk i) ⁻¹'
            Set.Iic (cap i + (delta : ENNReal)) := by
      apply Set.mem_iInter.2
      intro i
      have hi := hdcap (packet i) i.2
      simpa [weakRisk, cap, packet, _root_.GD.N0230.N0712.d001258, _root_.GD.N0232.N0720.N1080.d014182, H] using hi
    exact Set.disjoint_left.mp hrelaxed hdK hdrelaxed

end

end N1143
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1143.d014680
