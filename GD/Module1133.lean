import GD.Module1132
import GD.Module1105
import Mathlib.Tactic











namespace GD.N0232.N0720.N1407

noncomputable section

open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1085
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1346
open _root_.GD.N0232.N0720.N1416



theorem d018235
    (m n : ℕ)
    (p e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) e p) :
    ¬ _root_.GD.N0232.N0720.N1036.d014669 m n p := by
  intro hterminal
  have hweak : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e p := fun theta ↦
    (hstrict theta).le
  let theta : _root_.GD.N0232.N0720.N1080.d014168 := _root_.GD.N0232.N0720.N1080.d014169
  have heq := hterminal e hweak theta
  exact (ne_of_lt (hstrict theta)) heq



theorem d018236 :
    ¬ _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1185.d017526 := by
  exact _root_.GD.N0232.N0720.N1407.d018235
    2 2 _root_.GD.N0232.N0720.N1185.d017526 _root_.GD.N0232.N0720.N1416.d017758
      _root_.GD.N0232.N0720.N1416.d017761











noncomputable def d018237 : _root_.GD.N0232.N0720.N1159.d014639 2 2 :=
  _root_.GD.N0232.N0720.N1085.d015420 2 2 (by norm_num) (by norm_num)
    _root_.GD.N0232.N0720.N1416.d017756

@[simp] theorem d018238 :
    _root_.GD.N0232.N0720.N1407.d018237.value = _root_.GD.N0232.N0720.N1416.d017758 := by
  rfl



theorem d018239 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1416.d017758
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
  intro theta
  exact (_root_.GD.N0232.N0720.N1416.d017761 theta).trans
    (_root_.GD.N0232.N0720.N1185.d017532 theta)





theorem d018240
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 2 2
      _root_.GD.N0232.N0720.N1416.d017758) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1346.d018226
    _root_.GD.N0232.N0720.N1407.d018237
  · simpa only [_root_.GD.N0232.N0720.N1407.d018238] using
      _root_.GD.N0232.N0720.N1407.d018239
  · simpa only [_root_.GD.N0232.N0720.N1407.d018238] using hterminal

end

end GD.N0232.N0720.N1407

#print axioms _root_.GD.N0232.N0720.N1407.d018235
#print axioms _root_.GD.N0232.N0720.N1407.d018236
#print axioms _root_.GD.N0232.N0720.N1407.d018239
#print axioms _root_.GD.N0232.N0720.N1407.d018240
