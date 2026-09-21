import GD.Module1168
import GD.Module1169
import GD.Module1116
import GD.Module1159






















namespace GD
namespace N0232
namespace N0720
namespace N1370

noncomputable section

open Set
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1202
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1219
open _root_.GD.N0232.N0720.N1408
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1355
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}



theorem d018789
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  intro g theta
  exact _root_.GD.N0232.N0720.N1215.d014293 m n hm hn g theta



def d018790
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) <
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz)
        (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)



theorem d018791
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (haverage :
      _root_.GD.N0232.N0720.N1408.d018758 (1 / 2 : ℝ) s ≤
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  have hmaster :=
    (_root_.GD.N0232.N0720.N1408.d018762 s).1 haverage
  have henergy :=
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).1 hmaster
  exact
    _root_.GD.N0232.N0720.N1202.d018573
      s henergy



theorem d018792
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (haverage :
      _root_.GD.N0232.N0720.N1408.d018758 (1 / 2 : ℝ) s ≤
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1370.d018790 hm hn s := by
  exact _root_.GD.N0232.N0720.N1219.d017953
    m n hm hn
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)
      (_root_.GD.N0232.N0720.N1370.d018791
        s haverage)
      (_root_.GD.N0232.N0720.N1370.d018789 hm hn)






theorem d018793
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1408.d018758 (1 / 2 : ℝ) s ≤
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ∧
          _root_.GD.N0232.N0720.N1370.d018790 hm hn s := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, haverage⟩ :=
      (_root_.GD.N0232.N0720.N1408.d018764
        (m := m) (n := n) hm hn).1 hendpoint
    have hprojectionStrict :
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
      _root_.GD.N0232.N0720.N1159.d014636
        m n s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict
    exact ⟨s, haverage,
      (_root_.GD.N0232.N0720.N1370.d018792
        hm hn s haverage).1 hprojectionStrict⟩
  · rintro ⟨s, haverage, hsection⟩
    have hcharacter :
        _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
      _root_.GD.N0232.N0720.N1370.d018791
        s haverage
    have hstrict :
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
      (_root_.GD.N0232.N0720.N1370.d018792
        hm hn s haverage).2 hsection
    have hfinite :
        _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    let terminalSeed : _root_.GD.N0232.N0720.N1159.d014639 m n :=
      { value := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
        finiteRisk := hfinite
        riskCharacter := hcharacter }
    have hterminal :
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) terminalSeed.value := by
      exact (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1
    exact
      (_root_.GD.N0232.N0720.N1409.d018620
        (m := m) (n := n) hm hn).2
        ⟨terminalSeed, hstrict, hterminal⟩



theorem d018794
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (haverage :
      _root_.GD.N0232.N0720.N1408.d018758 (1 / 2 : ℝ) s ≤
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) :
    _root_.GD.N0232.N0720.N1370.d018790 hm hn s := by
  apply (_root_.GD.N0232.N0720.N1370.d018792
    hm hn s haverage).1
  exact _root_.GD.N0232.N0720.N1159.d014636
    m n s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict





theorem d018795
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (href : _root_.GD.N0232.N0720.N1355.d018776 weight s ≤
      _root_.GD.N0232.N0720.N1355.d018777 s) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  have hmaster :=
    (_root_.GD.N0232.N0720.N1355.d018780
      weight hweight0 hweight1 s).1 href
  have henergy :=
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).1 hmaster
  exact
    _root_.GD.N0232.N0720.N1202.d018573
      s henergy



theorem d018796
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (href : _root_.GD.N0232.N0720.N1355.d018776 weight s ≤
      _root_.GD.N0232.N0720.N1355.d018777 s) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1370.d018790 hm hn s := by
  exact _root_.GD.N0232.N0720.N1219.d017953
    m n hm hn
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)
      (_root_.GD.N0232.N0720.N1370.d018795
        weight hweight0 hweight1 s href)
      (_root_.GD.N0232.N0720.N1370.d018789 hm hn)






theorem d018797
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1355.d018776 weight s ≤
            _root_.GD.N0232.N0720.N1355.d018777 s ∧
          _root_.GD.N0232.N0720.N1370.d018790 hm hn s := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, href⟩ :=
      (_root_.GD.N0232.N0720.N1355.d018783
        (m := m) (n := n) hm hn weight hweight0 hweight1).1 hendpoint
    have hprojectionStrict :
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
      _root_.GD.N0232.N0720.N1159.d014636
        m n s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict
    exact ⟨s, href,
      (_root_.GD.N0232.N0720.N1370.d018796
        hm hn weight hweight0 hweight1 s href).1 hprojectionStrict⟩
  · rintro ⟨s, href, hsection⟩
    have hcharacter :
        _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
      _root_.GD.N0232.N0720.N1370.d018795
        weight hweight0 hweight1 s href
    have hstrict :
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
      (_root_.GD.N0232.N0720.N1370.d018796
        hm hn weight hweight0 hweight1 s href).2 hsection
    have hfinite :
        _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    let terminalSeed : _root_.GD.N0232.N0720.N1159.d014639 m n :=
      { value := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
        finiteRisk := hfinite
        riskCharacter := hcharacter }
    have hterminal :
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) terminalSeed.value := by
      exact (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1
    exact
      (_root_.GD.N0232.N0720.N1409.d018620
        (m := m) (n := n) hm hn).2
        ⟨terminalSeed, hstrict, hterminal⟩

end

end N1370
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1370.d018789
#print axioms _root_.GD.N0232.N0720.N1370.d018791
#print axioms _root_.GD.N0232.N0720.N1370.d018792
#print axioms _root_.GD.N0232.N0720.N1370.d018793
#print axioms _root_.GD.N0232.N0720.N1370.d018794
#print axioms _root_.GD.N0232.N0720.N1370.d018795
#print axioms _root_.GD.N0232.N0720.N1370.d018796
#print axioms _root_.GD.N0232.N0720.N1370.d018797
