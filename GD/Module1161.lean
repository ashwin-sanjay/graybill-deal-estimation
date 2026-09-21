import GD.Module1159

























namespace GD
namespace N0232
namespace N0720
namespace N1409

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1158
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1202
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}







theorem d018605
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hpCharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hpTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p)
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite = p := by
  apply hpTerminal
  intro eta
  let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by
    simp [theta]
  have heq :
      _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite) =
        _root_.GD.N0232.N0720.N1080.d014182 m n eta p := by
    calc
      _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite) =
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
            (_root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite) := by rw [heta]
      _ = ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p :=
        _root_.GD.N0232.N0720.N1159.d014643 m n g theta p hpFinite
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) p :=
        (hpCharacter g theta).symm
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n eta p := by rw [heta]
  exact le_of_eq heq



theorem d018606
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk = s.value := by
  intro g
  exact _root_.GD.N0232.N0720.N1409.d018605
    s.value s.finiteRisk s.riskCharacter hsTerminal g





theorem d018607
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    _root_.GD.N0232.N0720.N1159.d014652 m n s.value := by
  apply (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn
    s.value s.finiteRisk).1
  exact _root_.GD.N0232.N0720.N1409.d018606
    s hsTerminal



theorem d018608
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value :=
  (_root_.GD.N0232.N0720.N1159.d014635 m n s.value).2 hsTerminal




theorem d018609
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  have hself : _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value :=
    _root_.GD.N0232.N0720.N1409.d018608 s hsTerminal
  have hfixed : ∀ g :
      _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk = s.value :=
    _root_.GD.N0232.N0720.N1409.d018606
      s hsTerminal
  intro g
  apply (_root_.GD.N0232.N0720.N1159.d014651 m n s g).2
  apply Subtype.ext
  simpa only [_root_.GD.N0232.N0720.N1159.d014645, _root_.GD.N0232.N0720.N1159.d014646, hself] using
    hfixed g



theorem d018610
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  exact
    (_root_.GD.N0232.N0720.N1482.d015171
      (m := m) (n := n) s).2
      (_root_.GD.N0232.N0720.N1409.d018609
        s hsTerminal)



theorem d018611
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  exact
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).1
      (_root_.GD.N0232.N0720.N1409.d018610
        s hsTerminal)






def d018612
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    _root_.GD.N0232.N0720.N1159.d014639 m n where
  value := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  finiteRisk := _root_.GD.N0232.N0720.N1159.d014644 m n s
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  riskCharacter :=
    _root_.GD.N0232.N0720.N1202.d018573
      s henergy

@[simp] theorem d018613
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    (_root_.GD.N0232.N0720.N1409.d018612 s henergy).value =
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value := rfl



theorem d018614
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1409.d018612 s henergy).value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  simpa only [_root_.GD.N0232.N0720.N1409.d018613] using
    _root_.GD.N0232.N0720.N1159.d014636
      m n s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict


theorem d018615
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1409.d018612 s henergy).value := by
  simpa only [_root_.GD.N0232.N0720.N1409.d018613] using
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1



theorem d018616
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    _root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1409.d018612 s henergy).value =
      (_root_.GD.N0232.N0720.N1409.d018612 s henergy).value := by
  exact (_root_.GD.N0232.N0720.N1159.d014635 m n
    (_root_.GD.N0232.N0720.N1409.d018612 s henergy).value).2
    (_root_.GD.N0232.N0720.N1409.d018615 s henergy)





theorem d018617
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1409.d018612 s henergy).value
          (_root_.GD.N0232.N0720.N1409.d018612 s henergy).finiteRisk =
        (_root_.GD.N0232.N0720.N1409.d018612 s henergy).value := by
  exact _root_.GD.N0232.N0720.N1409.d018606
    (_root_.GD.N0232.N0720.N1409.d018612 s henergy)
    (_root_.GD.N0232.N0720.N1409.d018615 s henergy)


theorem d018618
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    _root_.GD.N0232.N0720.N1477.d015749 m n (_root_.GD.N0232.N0720.N1409.d018612 s henergy) = 0 := by
  apply (_root_.GD.N0232.N0720.N1158.d018490
    (_root_.GD.N0232.N0720.N1409.d018612 s henergy)).2
  have hold :=
    (_root_.GD.N0232.N0720.N1158.d018490 s).1 henergy
  rw [_root_.GD.N0232.N0720.N1409.d018616 s henergy]
  change
    _root_.GD.N0232.N0720.N1146.d015228 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∧
      _root_.GD.N0232.N0720.N1146.d015229 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  exact hold


theorem d018619
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n)
      (_root_.GD.N0232.N0720.N1409.d018612 s henergy) = 0 := by
  exact
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) (_root_.GD.N0232.N0720.N1409.d018612 s henergy)).2
      (_root_.GD.N0232.N0720.N1409.d018618 s henergy)







theorem d018620
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  rw [_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn]
  constructor
  · rintro ⟨p, hrep, hstrict, hterminal⟩
    let s := _root_.GD.N0232.N0720.N1159.d014657
      m n hm hn p hrep hstrict
    exact ⟨s, hstrict, hterminal⟩
  · rintro ⟨s, hstrict, hterminal⟩
    exact ⟨s.value,
      _root_.GD.N0232.N0720.N1409.d018607
        hm hn s hterminal,
      hstrict, hterminal⟩



theorem d018621
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hterminal⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1159.d014635 m n s.value).2 hterminal⟩
  · rintro ⟨s, hstrict, hself⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1159.d014635 m n s.value).1 hself⟩

end

end N1409
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1409.d018605
#print axioms _root_.GD.N0232.N0720.N1409.d018607
#print axioms _root_.GD.N0232.N0720.N1409.d018609
#print axioms _root_.GD.N0232.N0720.N1409.d018610
#print axioms _root_.GD.N0232.N0720.N1409.d018611
#print axioms _root_.GD.N0232.N0720.N1409.d018616
#print axioms _root_.GD.N0232.N0720.N1409.d018617
#print axioms _root_.GD.N0232.N0720.N1409.d018618
#print axioms _root_.GD.N0232.N0720.N1409.d018619
#print axioms _root_.GD.N0232.N0720.N1409.d018620
#print axioms _root_.GD.N0232.N0720.N1409.d018621
