import GD.Module0921
import GD.Module1114














open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1217

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1069
open _root_.GD.N0232.N0720.N1035
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)



theorem d017936
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) p ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) q ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta q := by
  have hpForward := hp g theta
  have hqForward := hq g theta
  have hpInverse := hp g⁻¹ (_root_.GD.N0232.N0720.N1215.d014272 g theta)
  have hqInverse := hq g⁻¹ (_root_.GD.N0232.N0720.N1215.d014272 g theta)
  rw [_root_.GD.N0232.N0720.N1215.d014280] at hpInverse hqInverse
  constructor
  · intro htransported
    rw [hpInverse, hqInverse]
    exact mul_le_mul_right htransported _
  · intro horiginal
    rw [hpForward, hqForward]
    exact mul_le_mul_right horiginal _



theorem d017937
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) p <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) q ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n theta p < _root_.GD.N0232.N0720.N1080.d014182 m n theta q := by
  simpa only [not_le] using not_congr
    (_root_.GD.N0232.N0720.N1217.d017936
      m n q p hq hp g theta)

variable (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn



theorem d017938
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168}
    (hfrac : _root_.GD.N0232.N0720.N1069.d014352 m n theta = _root_.GD.N0232.N0720.N1069.d014352 m n eta)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta q ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n eta p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n eta q := by
  have hmap := _root_.GD.N0232.N0720.N1035.d014379 m n hm hn hfrac
  have horbit := _root_.GD.N0232.N0720.N1217.d017936
    m n p q hp hq (_root_.GD.N0232.N0720.N1035.d014376 theta eta) theta
  rw [hmap] at horbit
  exact horbit.symm



theorem d017939
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168}
    (hfrac : _root_.GD.N0232.N0720.N1069.d014352 m n theta = _root_.GD.N0232.N0720.N1069.d014352 m n eta)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta p < _root_.GD.N0232.N0720.N1080.d014182 m n theta q ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n eta p < _root_.GD.N0232.N0720.N1080.d014182 m n eta q := by
  simpa only [not_le] using not_congr
    (_root_.GD.N0232.N0720.N1217.d017938
      m n hm hn hfrac q p hq hp)



theorem d017940
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168}
    (hfrac : _root_.GD.N0232.N0720.N1069.d014352 m n theta = _root_.GD.N0232.N0720.N1069.d014352 m n eta)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta q ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n eta q ≤ _root_.GD.N0232.N0720.N1080.d014182 m n eta s.value := by
  exact _root_.GD.N0232.N0720.N1217.d017938
    m n hm hn hfrac q s.value hq s.riskCharacter



theorem d017941
    {theta eta : _root_.GD.N0232.N0720.N1080.d014168}
    (hfrac : _root_.GD.N0232.N0720.N1069.d014352 m n theta = _root_.GD.N0232.N0720.N1069.d014352 m n eta)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta q < _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n eta q < _root_.GD.N0232.N0720.N1080.d014182 m n eta s.value := by
  exact _root_.GD.N0232.N0720.N1217.d017939
    m n hm hn hfrac q s.value hq s.riskCharacter

end


end N1217
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1217.d017936
#print axioms _root_.GD.N0232.N0720.N1217.d017937
#print axioms _root_.GD.N0232.N0720.N1217.d017938
#print axioms _root_.GD.N0232.N0720.N1217.d017939
#print axioms _root_.GD.N0232.N0720.N1217.d017940
#print axioms _root_.GD.N0232.N0720.N1217.d017941
