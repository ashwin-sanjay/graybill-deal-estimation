import GD.Module1214











open MeasureTheory Set

namespace GD.N0232.N0720.N1400

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1274
open _root_.GD.N0230.N0608

def d020124 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) : _root_.GD.N0232.N0720.N1441.d013681 2 2 :=
  _root_.GD.N0232.N0720.N1441.d013688 (by omega) (by omega) (_root_.GD.N0232.N0720.N1398.d019601 d)
    (_root_.GD.N0232.N0720.N1398.d019602 hd.1) (_root_.GD.N0232.N0720.N1398.d019603 d)

theorem d020125 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    (_root_.GD.N0232.N0720.N1400.d020124 hd : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2]
      _root_.GD.N0232.N0720.N1441.d013686 (_root_.GD.N0232.N0720.N1398.d019601 d) :=
  (_root_.GD.N0232.N0720.N1441.d013687 (by omega) (by omega) (_root_.GD.N0232.N0720.N1398.d019601 d)
    (_root_.GD.N0232.N0720.N1398.d019602 hd.1)
    (_root_.GD.N0232.N0720.N1398.d019603 d)).coeFn_toLp


theorem d020126 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    _root_.GD.N0232.N0720.N1400.d020124 hd = _root_.GD.N0232.N0720.N1441.d013690 (by omega) (by omega)
      (_root_.GD.N0232.N0720.N1398.d019601 d) (_root_.GD.N0232.N0720.N1398.d019602 hd.1)
      (_root_.GD.N0232.N0720.N1398.d019603 d) := by
  let seed := _root_.GD.N0232.N0720.N1398.d019601 d
  have hm : Measurable seed := _root_.GD.N0232.N0720.N1398.d019602 hd.1
  have hb : ∀ x, seed x ∈ Icc (0 : ℝ) 1 := _root_.GD.N0232.N0720.N1398.d019603 d
  have hselected := _root_.GD.N0232.N0720.N1274.d019632 hd
    (_root_.GD.N0232.N0720.N1441.d013702 (by omega) (by omega) seed hm hb)
    (_root_.GD.N0232.N0720.N1441.d013703 (by omega) (by omega) seed hm hb)
    (_root_.GD.N0232.N0720.N1441.d013708 (by omega) (by omega) seed hm hb)
  have hrep := _root_.GD.N0232.N0720.N1441.d013704 (m := 2) (n := 2)
    (by omega) (by omega) seed hm hb
  apply Lp.ext
  filter_upwards [_root_.GD.N0232.N0720.N1400.d020125 hd, hselected, hrep] with x hx hsel hrepX
  rw [hx, ← hrepX]
  change seed x - 1 / 2 = _ - 1 / 2
  exact congrArg (fun a : ℝ ↦ a - 1 / 2) hsel.symm



theorem d020127 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1441.d013689 2 2) (_root_.GD.N0232.N0720.N1400.d020124 hd) := by
  rw [_root_.GD.N0232.N0720.N1400.d020126 hd]
  exact (_root_.GD.N0232.N0720.N1441.d013691 (by omega) (by omega) (_root_.GD.N0232.N0720.N1398.d019601 d)
    (_root_.GD.N0232.N0720.N1398.d019602 hd.1)
    (_root_.GD.N0232.N0720.N1398.d019603 d)).2.1

end
end GD.N0232.N0720.N1400

#print axioms _root_.GD.N0232.N0720.N1400.d020126
#print axioms _root_.GD.N0232.N0720.N1400.d020127
