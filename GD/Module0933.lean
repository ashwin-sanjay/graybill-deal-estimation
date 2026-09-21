import GD.Module0932





















open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1036

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1081
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)






def d014669
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e p →
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014182 m n theta e = _root_.GD.N0232.N0720.N1080.d014182 m n theta p







theorem d014670
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 m n s.value)
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
      _root_.GD.N0232.N0720.N1159.d014646 m n s := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hpBelow : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value p :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hpProfile :
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value :=
    hterminal p hpBelow
  have hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s p hpBelow
  have htransport :
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (_root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite) p := by
    intro eta
    let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
    have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by
      simp [theta]
    apply le_of_eq
    calc
      _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite) =
          ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p := by
        rw [← heta]
        exact _root_.GD.N0232.N0720.N1159.d014643 m n g theta p hpFinite
      _ = ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value := by
        rw [hpProfile theta]
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) s.value :=
        (s.riskCharacter g theta).symm
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n eta s.value := by
        rw [heta]
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n eta p := (hpProfile eta).symm
  have hfixed : _root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite = p :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1 _ htransport
  apply Subtype.ext
  simpa only [_root_.GD.N0232.N0720.N1159.d014645, _root_.GD.N0232.N0720.N1159.d014646, p] using hfixed



theorem d014671
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 m n s.value) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  intro g
  exact (_root_.GD.N0232.N0720.N1159.d014651 m n s g).2
    (_root_.GD.N0232.N0720.N1036.d014670
      m n s hterminal g)













theorem d014672
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 m n s.value) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply
    (_root_.GD.N0232.N0720.N1159.d014666
      m n hm hn).2
  exact ⟨s, hstrict,
    _root_.GD.N0232.N0720.N1036.d014671
      m n s hterminal⟩

end

end N1036
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1036.d014670
#print axioms _root_.GD.N0232.N0720.N1036.d014672
