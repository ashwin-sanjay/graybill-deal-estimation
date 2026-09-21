import GD.Module1067

























open Set

namespace GD
namespace N0232
namespace N0720
namespace N1113

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1105
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201

variable (m n : ℕ)




def d017124
    (kappa : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value ∧
    _root_.GD.N0232.N0720.N1159.d014638 m n p ∧
    _root_.GD.N0232.N0720.N1105.d017112 m n p s.value ∧
    ‖p‖ ^ 2 ≤ ‖s.value‖ ^ 2 - kappa *
      (‖s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight)



theorem d017125
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  have hprojection : _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∈
      _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hreserve :=
    _root_.GD.N0232.N0720.N1126.d016436
      s candidate.packet candidate.weight candidate.weight_nonneg
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hprojection
  nlinarith [sq_nonneg
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value -
      _root_.GD.N0232.N0720.N1126.d016426 candidate.packet candidate.weight
        candidate.weight_nonneg‖]



theorem d017126
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcert : _root_.GD.N0232.N0720.N1113.d017124 m n kappa s candidate p) :
    _root_.GD.N0232.N0720.N1105.d017120 m n kappa s := by
  rcases hcert with ⟨hp, hchar, htax, hnorm⟩
  refine ⟨p, hp, hchar, htax, ?_⟩
  have hreserve :=
    _root_.GD.N0232.N0720.N1113.d017125
      m n s candidate
  have hmul : 0 ≤ kappa *
      (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight) :=
    mul_nonneg hkappa (sub_nonneg.mpr hreserve)
  have hgap : _root_.GD.N0232.N0720.N1201.d015333 m n s =
      ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := rfl
  rw [hgap]
  nlinarith




theorem d017127
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₀.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (kappa : ℝ) (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (hcapture : ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₀.value s.value →
      0 < _root_.GD.N0232.N0720.N1201.d015333 m n s →
      ∃ (candidate : _root_.GD.N0232.N0720.N1130.d017074)
        (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
        _root_.GD.N0232.N0720.N1113.d017124 m n kappa s candidate p) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1105.d017122
    m n hm hn s₀ hstrict kappa hkappa hkappa_one
  intro s hs hgap
  obtain ⟨candidate, p, hcert⟩ := hcapture s hs hgap
  exact _root_.GD.N0232.N0720.N1113.d017126
    m n kappa hkappa.le s candidate p hcert



theorem d017128
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (kappa : ℝ) (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (hcapture : ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) s.value →
      0 < _root_.GD.N0232.N0720.N1201.d015333 m n s →
      ∃ (candidate : _root_.GD.N0232.N0720.N1130.d017074)
        (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
        _root_.GD.N0232.N0720.N1113.d017124 m n kappa s candidate p) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply
    _root_.GD.N0232.N0720.N1105.d017123
      m n hm hn kappa hkappa hkappa_one
  intro s hs hgap
  obtain ⟨candidate, p, hcert⟩ := hcapture s hs hgap
  exact _root_.GD.N0232.N0720.N1113.d017126
    m n kappa hkappa.le s candidate p hcert

end

end N1113
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1113.d017125
#print axioms _root_.GD.N0232.N0720.N1113.d017126
#print axioms _root_.GD.N0232.N0720.N1113.d017127
#print axioms _root_.GD.N0232.N0720.N1113.d017128
