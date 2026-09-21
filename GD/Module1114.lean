import GD.Module1113


























open Filter Function MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1033

noncomputable section

set_option maxHeartbeats 4000000

open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1503
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)





theorem d017920
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (g : _root_.GD.N0232.N0720.N1482.d015118)
    (hfixed : _root_.GD.N0232.N0720.N1159.d014642 m n g q hq = q) :
    _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) q := by
  have htransport := _root_.GD.N0232.N0720.N1159.d014643
    m n g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) q hq
  rw [_root_.GD.N0232.N0720.N1215.d014279, hfixed] at htransport
  exact htransport



theorem d017921
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (g : _root_.GD.N0232.N0720.N1482.d015118)
    (hfixed : _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ q hq = q) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) q =
      ENNReal.ofReal (g⁻¹.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q := by
  have htransport := _root_.GD.N0232.N0720.N1159.d014643
    m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169 q hq
  rw [hfixed] at htransport
  exact htransport



theorem d017922
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 s.value =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) s.value := by
  have hcharacter := s.riskCharacter g
    (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
  rw [_root_.GD.N0232.N0720.N1215.d014279] at hcharacter
  exact hcharacter



theorem d017923
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) s.value =
      ENNReal.ofReal (g⁻¹.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 s.value := by
  exact s.riskCharacter g⁻¹ _root_.GD.N0232.N0720.N1080.d014169






theorem d017924
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q)
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) p ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) q ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q := by
  have hpForward := hp g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
  have hqForward := hq g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
  rw [_root_.GD.N0232.N0720.N1215.d014279] at hpForward hqForward
  have hpInverse := hp g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  have hqInverse := hq g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  constructor
  · intro horbit
    rw [hpForward, hqForward]
    exact mul_le_mul_right horbit _
  · intro href
    rw [hpInverse, hqInverse]
    exact mul_le_mul_right href _





theorem d017925
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q)
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) p <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) q ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p <
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q := by
  simpa only [not_le] using not_congr
    (_root_.GD.N0232.N0720.N1033.d017924
      m n q p hq hp g)



theorem d017926
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
      _root_.GD.N0232.N0720.N1159.d014642 m n g q hq = q) :
    _root_.GD.N0232.N0720.N1159.d014638 m n q := by
  intro g theta
  have htransport := _root_.GD.N0232.N0720.N1159.d014643
    m n g theta q hq
  rw [hfixed g] at htransport
  exact htransport



theorem d017927
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 q hq = q)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 q hq = q) :
    _root_.GD.N0232.N0720.N1159.d014638 m n q := by
  exact _root_.GD.N0232.N0720.N1033.d017926 m n q hq
    (_root_.GD.N0232.N0720.N1482.d015167
      (m := m) (n := n) q hq hTwo hThree)











theorem d017928
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (g : _root_.GD.N0232.N0720.N1482.d015118)
    (hfixed : _root_.GD.N0232.N0720.N1159.d014642 m n g q hq = q)
    (hfixedInv : _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ q hq = q) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) q ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) s.value ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 s.value := by
  constructor
  · intro horbit
    rw [_root_.GD.N0232.N0720.N1033.d017920
      m n q hq g hfixed,
      _root_.GD.N0232.N0720.N1033.d017922 m n s g]
    exact mul_le_mul_right horbit _
  · intro href
    rw [_root_.GD.N0232.N0720.N1033.d017921
      m n q hq g hfixedInv,
      _root_.GD.N0232.N0720.N1033.d017923 m n s g]
    exact mul_le_mul_right href _


theorem d017929
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
      _root_.GD.N0232.N0720.N1159.d014642 m n g q hq = q)
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) q ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) s.value ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 s.value := by
  exact _root_.GD.N0232.N0720.N1033.d017928
    m n s q hq g (hfixed g) (hfixed g⁻¹)





theorem d017930
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 q hq = q)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 q hq = q)
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) q ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) s.value ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 s.value := by
  have hall := _root_.GD.N0232.N0720.N1482.d015167
    (m := m) (n := n) q hq hTwo hThree
  exact _root_.GD.N0232.N0720.N1033.d017929
    m n s q hq hall g





theorem d017931
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015130 q hq = q)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015131 q hq = q) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q =
      ENNReal.ofReal (1 / 4 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q := by
  have hall := _root_.GD.N0232.N0720.N1482.d015167
    (m := 2) (n := 2) q hq hTwo hThree
  have hscale : _root_.GD.N0232.N0720.N1503.d017874⁻¹.d009239 = 1 / 2 := by
    rw [_root_.GD.N0232.N0720.N1146.d015204, _root_.GD.N0232.N0720.N1503.d017885]
    norm_num
  rw [_root_.GD.N0232.N0720.N1503.d017876, _root_.GD.N0232.N0720.N1484.d015099]
  calc
    _root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1503.d017874⁻¹
        _root_.GD.N0232.N0720.N1080.d014169) q =
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1503.d017874⁻¹.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q :=
      _root_.GD.N0232.N0720.N1033.d017921
        2 2 q hq _root_.GD.N0232.N0720.N1503.d017874 (hall _root_.GD.N0232.N0720.N1503.d017874⁻¹)
    _ = ENNReal.ofReal (1 / 4 : ℝ) *
          _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q := by
      rw [hscale]
      norm_num



theorem d017932
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015130 q hq = q)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015131 q hq = q) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q =
      ENNReal.ofReal (1 / 4 : ℝ) * _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q := by
  have hall := _root_.GD.N0232.N0720.N1482.d015167
    (m := 2) (n := 2) q hq hTwo hThree
  have hscale : _root_.GD.N0232.N0720.N1503.d017875⁻¹.d009239 = 1 / 2 := by
    rw [_root_.GD.N0232.N0720.N1146.d015204, _root_.GD.N0232.N0720.N1503.d017886]
    norm_num
  rw [_root_.GD.N0232.N0720.N1503.d017877, _root_.GD.N0232.N0720.N1484.d015099]
  calc
    _root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1503.d017875⁻¹
        _root_.GD.N0232.N0720.N1080.d014169) q =
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1503.d017875⁻¹.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q :=
      _root_.GD.N0232.N0720.N1033.d017921
        2 2 q hq _root_.GD.N0232.N0720.N1503.d017875 (hall _root_.GD.N0232.N0720.N1503.d017875⁻¹)
    _ = ENNReal.ofReal (1 / 4 : ℝ) *
          _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q := by
      rw [hscale]
      norm_num



theorem d017933
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015130 q hq = q)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015131 q hq = q) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 s.value ↔
      _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 s.value := by
  simpa only [_root_.GD.N0232.N0720.N1503.d017876, _root_.GD.N0232.N0720.N1484.d015099] using
    (_root_.GD.N0232.N0720.N1033.d017930
      2 2 s q hq hTwo hThree _root_.GD.N0232.N0720.N1503.d017874)



theorem d017934
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015130 q hq = q)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015131 q hq = q) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 s.value ↔
      _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 s.value := by
  simpa only [_root_.GD.N0232.N0720.N1503.d017877, _root_.GD.N0232.N0720.N1484.d015099] using
    (_root_.GD.N0232.N0720.N1033.d017930
      2 2 s q hq hTwo hThree _root_.GD.N0232.N0720.N1503.d017875)



theorem d017935
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    (hTwo : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015130 q hq = q)
    (hThree : _root_.GD.N0232.N0720.N1159.d014642 2 2 _root_.GD.N0232.N0720.N1482.d015131 q hq = q) :
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017876 s.value ∧
      _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1503.d017877 s.value) ↔
      _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 q ≤
        _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 s.value := by
  rw [_root_.GD.N0232.N0720.N1033.d017933
      s q hq hTwo hThree,
    _root_.GD.N0232.N0720.N1033.d017934
      s q hq hTwo hThree,
    and_self]

end
end N1033
end N0720
end N0232
end GD

namespace GD.N0232.N0720.N1033

#print axioms _root_.GD.N0232.N0720.N1033.d017928
#print axioms _root_.GD.N0232.N0720.N1033.d017924
#print axioms _root_.GD.N0232.N0720.N1033.d017925
#print axioms _root_.GD.N0232.N0720.N1033.d017927
#print axioms _root_.GD.N0232.N0720.N1033.d017930
#print axioms _root_.GD.N0232.N0720.N1033.d017931
#print axioms _root_.GD.N0232.N0720.N1033.d017932
#print axioms _root_.GD.N0232.N0720.N1033.d017935

end GD.N0232.N0720.N1033
