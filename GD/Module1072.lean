import GD.Module1070
import GD.Module0225












namespace GD
namespace N0232
namespace N0720
namespace N1119

noncomputable section

open MeasureTheory
open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0619
open _root_.GD.N0233.N0725
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131



theorem d017181
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate q =
      ∫ omega,
        _root_.GD.N0230.N0619.d000389
          candidate.weight (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
          (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega (q omega)
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  unfold _root_.GD.N0232.N0720.N1131.d017154
  apply integral_congr_ae
  filter_upwards with omega
  have hmass : _root_.GD.N0230.N0617.d000163 candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega).ne'
  simpa [_root_.GD.N0232.N0720.N1126.d016415, _root_.GD.N0232.N0720.N1126.d016416] using
    (_root_.GD.N0230.N0619.d000395
      candidate.weight (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
      (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega (q omega) hmass).symm

end

end N1119
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1119.d017181
