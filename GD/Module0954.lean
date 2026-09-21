import GD.Module0953























open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1090

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1065
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1081
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1260
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0230.N0608

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)





noncomputable def d014979
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : ℝ :=
  _root_.GD.N0232.N0720.N1260.d014970 m n hm hn
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q)



theorem d014980
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1090.d014979 m n hm hn q = 0 ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 := by
  have hstrong :=
    _root_.GD.N0232.N0720.N1260.d014973
      m n hm hn ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q)
  have hweak := _root_.GD.N0232.N0720.N1025.d014315 m n q.1
  simpa only [_root_.GD.N0232.N0720.N1090.d014979, _root_.GD.N0232.N0720.N1025.d014309] using
    hstrong.trans hweak.symm




theorem d014981
    (q : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (_hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g q = q) :
    _root_.GD.N0232.N0720.N1260.d014970 m n hm hn q = 0 ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) q.1 :=
  _root_.GD.N0232.N0720.N1260.d014973 m n hm hn q



theorem d014982
    (q : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g q = q)
    (hgap : _root_.GD.N0232.N0720.N1260.d014970 m n hm hn q = 0) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply
    _root_.GD.N0232.N0720.N1260.d014976
      m n hm hn
  refine ⟨q, ?_, hgap⟩
  exact
    (_root_.GD.N0232.N0720.N1081.d014627
      m n hm hn q).1 hfixed



theorem d014983
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q = q)
    (hgap : _root_.GD.N0232.N0720.N1090.d014979 m n hm hn q = 0) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let qStrong : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q
  have hfixedStrong : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g qStrong = qStrong :=
    _root_.GD.N0232.N0720.N1025.d014318 m n hm hn q hfixed
  exact
    _root_.GD.N0232.N0720.N1090.d014982
      m n hm hn qStrong hfixedStrong hgap





noncomputable def d014984 :
    _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
  Classical.choose
    (_root_.GD.N0232.N0720.N1483.d014906 m n hm hn)



theorem d014985 :
    (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn).1 ∈
      _root_.GD.N0232.N0720.N1065.d014568 m n hm hn :=
  (Classical.choose_spec
    (_root_.GD.N0232.N0720.N1483.d014906
      m n hm hn)).1


theorem d014986
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g
        (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn) =
      _root_.GD.N0232.N0720.N1090.d014984 m n hm hn :=
  (Classical.choose_spec
    (_root_.GD.N0232.N0720.N1483.d014906
      m n hm hn)).2 g


noncomputable def d014987 : ℝ :=
  _root_.GD.N0232.N0720.N1090.d014979 m n hm hn (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn)

theorem d014988 :
    0 ≤ _root_.GD.N0232.N0720.N1090.d014987 m n hm hn := by
  exact _root_.GD.N0232.N0720.N1260.d014971 m n hm hn
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
      (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn))



theorem d014989 :
    _root_.GD.N0232.N0720.N1090.d014987 m n hm hn = 0 ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n)
        (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn).1 := by
  exact _root_.GD.N0232.N0720.N1090.d014980 m n hm hn
    (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn)



theorem d014990
    (hgap : _root_.GD.N0232.N0720.N1090.d014987 m n hm hn = 0) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact
    _root_.GD.N0232.N0720.N1090.d014983
      m n hm hn (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn)
      (_root_.GD.N0232.N0720.N1090.d014986 m n hm hn) hgap



theorem d014991
    (hfail : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n) :
    0 < _root_.GD.N0232.N0720.N1090.d014987 m n hm hn := by
  let q : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
      (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn)
  have hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g q = q :=
    _root_.GD.N0232.N0720.N1025.d014318 m n hm hn
      (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn)
      (_root_.GD.N0232.N0720.N1090.d014986 m n hm hn)
  have hrep : _root_.GD.N0232.N0720.N1081.d014624 m n hm hn q :=
    (_root_.GD.N0232.N0720.N1081.d014627
      m n hm hn q).1 hfixed
  exact
    _root_.GD.N0232.N0720.N1260.d014978
      m n hm hn hfail q hrep


theorem d014992
    (hgap : _root_.GD.N0232.N0720.N1090.d014987 2 2 (by omega) (by omega) = 0) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 :=
  _root_.GD.N0232.N0720.N1090.d014990
    2 2 (by omega) (by omega) hgap

end

end N1090
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1090.d014980
#print axioms _root_.GD.N0232.N0720.N1090.d014982
#print axioms _root_.GD.N0232.N0720.N1090.d014989
#print axioms _root_.GD.N0232.N0720.N1090.d014990
#print axioms _root_.GD.N0232.N0720.N1090.d014991
#print axioms _root_.GD.N0232.N0720.N1090.d014992
