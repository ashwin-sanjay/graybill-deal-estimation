import GD.Module1143
import GD.Module1139























namespace GD
namespace N0232
namespace N0720
namespace N1061

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1055
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1134
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201

variable {m n : ℕ}



def d018398
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value < ε ∧
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - s.value‖ ^ 2 < ε ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) ∧
        ¬ _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) ∧
        ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value ∧
        ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)




theorem d018399
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1061.d018398 s ↔
      _root_.GD.N0232.N0720.N1135.d018324 s := by
  constructor
  · intro h ε hε
    obtain ⟨candidate, hcalibration, _hnorm, _hterminal, _hnaffine,
      _hleft, _hright⟩ := h ε hε
    exact ⟨candidate, hcalibration⟩
  · intro h ε hε
    obtain ⟨candidate, hcalibration⟩ := h ε hε
    have hseedMem : s.value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
      _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
    have hnorm :=
      _root_.GD.N0232.N0720.N1131.d017158
        m n s candidate s.value hseedMem
    refine ⟨candidate, hcalibration, hnorm.trans_lt hcalibration, ?_, ?_,
      _root_.GD.N0232.N0720.N1134.d018394 s candidate,
      _root_.GD.N0232.N0720.N1134.d018395 s candidate⟩
    · simpa only [_root_.GD.N0232.N0720.N1130.d017075] using
        _root_.GD.N0232.N0720.N1125.d017263
          (m := m) (n := n) candidate.packet candidate.weight
            candidate.weight_nonneg
    · simpa only [_root_.GD.N0232.N0720.N1130.d017075] using
        _root_.GD.N0232.N0720.N1055.d017240
          (m := m) (n := n) candidate.packet candidate.weight
            candidate.weight_nonneg



theorem d018400
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 ↔
      _root_.GD.N0232.N0720.N1061.d018398 s := by
  rw [_root_.GD.N0232.N0720.N1061.d018399]
  exact
    (_root_.GD.N0232.N0720.N1135.d018328
      s).symm




theorem d018401
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1061.d018398
            s := by
  rw [_root_.GD.N0232.N0720.N1135.d018339
    (m := m) (n := n) hm hn]
  apply exists_congr
  intro s
  apply and_congr_right
  intro _hstrict
  exact
    (_root_.GD.N0232.N0720.N1061.d018399
      s).symm

end

end N1061
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1061.d018399
#print axioms _root_.GD.N0232.N0720.N1061.d018400
#print axioms _root_.GD.N0232.N0720.N1061.d018401
