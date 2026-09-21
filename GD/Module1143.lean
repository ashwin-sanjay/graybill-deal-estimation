import GD.Module1140
import GD.Module1077


















namespace GD
namespace N0232
namespace N0720
namespace N1134

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1055
open _root_.GD.N0232.N0720.N1058
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1159

variable {m n : ℕ}



theorem d018394
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value := by
  intro hdom
  obtain ⟨theta, hstrict⟩ :=
    _root_.GD.N0232.N0720.N1058.d018349
      m n s candidate
  have hle := hdom theta
  have hleReal := ENNReal.toReal_mono (s.finiteRisk theta) hle
  exact (not_lt_of_ge hleReal) hstrict



theorem d018395
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) := by
  intro hdom
  have heq := _root_.GD.N0232.N0720.N1125.d017263
    (m := m) (n := n) candidate.packet candidate.weight
      candidate.weight_nonneg s.value hdom
  have hnot := _root_.GD.N0232.N0720.N1055.d017240
    (m := m) (n := n) candidate.packet candidate.weight
      candidate.weight_nonneg
  apply hnot
  simpa only [_root_.GD.N0232.N0720.N1130.d017075, ← heq] using s.riskCharacter


theorem d018396
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ∃ thetaWorse thetaBetter : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014182 m n thetaWorse s.value <
          _root_.GD.N0232.N0720.N1080.d014182 m n thetaWorse (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) ∧
        _root_.GD.N0232.N0720.N1080.d014182 m n thetaBetter (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) <
          _root_.GD.N0232.N0720.N1080.d014182 m n thetaBetter s.value := by
  have hleft := _root_.GD.N0232.N0720.N1134.d018394 s candidate
  have hright := _root_.GD.N0232.N0720.N1134.d018395 s candidate
  simp only [_root_.GD.N0230.N0608.d000672, not_forall] at hleft hright
  obtain ⟨thetaWorse, hthetaWorse⟩ := hleft
  obtain ⟨thetaBetter, hthetaBetter⟩ := hright
  exact ⟨thetaWorse, thetaBetter, not_le.mp hthetaWorse,
    not_le.mp hthetaBetter⟩



theorem d018397
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1130.d017075 m n candidate ∉
      _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
  simpa only [_root_.GD.N0232.N0720.N1159.d014630, Set.mem_setOf_eq, _root_.GD.N0230.N0608.d000673] using
    _root_.GD.N0232.N0720.N1134.d018394 s candidate

end

end N1134
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1134.d018395
#print axioms _root_.GD.N0232.N0720.N1134.d018396
#print axioms _root_.GD.N0232.N0720.N1134.d018397
