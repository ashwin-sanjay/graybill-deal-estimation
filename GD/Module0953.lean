import GD.Module0952
import GD.Module0932
































open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1260

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1081
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1262

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



noncomputable def d014970
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) : ℝ :=
  ‖p.1‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n p.1‖ ^ 2


theorem d014971
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    0 ≤ _root_.GD.N0232.N0720.N1260.d014970 m n hm hn p := by
  have href := (_root_.GD.N0232.N0720.N1159.d014634 m n p.1).1 _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm :
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n p.1‖ ^ 2 ≤ ‖p.1‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖p.1‖)).mp href
  exact sub_nonneg.mpr hnorm


theorem d014972
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1260.d014970 m n hm hn p = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014633 m n p.1 = p.1 := by
  constructor
  · intro hgap
    have htax := _root_.GD.N0232.N0720.N1159.d014648
      m n p.1 p.1 (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) p.1)
    have hsq : ‖p.1 - _root_.GD.N0232.N0720.N1159.d014633 m n p.1‖ ^ 2 ≤ 0 := by
      exact htax.trans_eq hgap
    have hnorm : ‖p.1 - _root_.GD.N0232.N0720.N1159.d014633 m n p.1‖ = 0 := by
      nlinarith [norm_nonneg
        (p.1 - _root_.GD.N0232.N0720.N1159.d014633 m n p.1)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm
  · intro heq
    unfold _root_.GD.N0232.N0720.N1260.d014970
    rw [heq, sub_self]



theorem d014973
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1260.d014970 m n hm hn p = 0 ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p.1 := by
  rw [_root_.GD.N0232.N0720.N1260.d014972]
  exact _root_.GD.N0232.N0720.N1159.d014635 m n p.1







theorem d014974 :
    _root_.GD.N0232.N0720.N1262.d014965 m n hm hn ↔
      ∃ p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn,
        _root_.GD.N0232.N0720.N1081.d014624 m n hm hn p ∧
          _root_.GD.N0232.N0720.N1260.d014970 m n hm hn p = 0 := by
  constructor
  · rintro ⟨pWeak, hpWeak⟩
    let p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
      (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm pWeak
    have hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
        _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p = p := by
      exact _root_.GD.N0232.N0720.N1025.d014318
        m n hm hn pWeak hpWeak.fixed
    have hrep : _root_.GD.N0232.N0720.N1081.d014624 m n hm hn p :=
      (_root_.GD.N0232.N0720.N1081.d014627
        m n hm hn p).1 hfixed
    have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p.1 := by
      have h := (_root_.GD.N0232.N0720.N1025.d014315 m n pWeak.1).1
        hpWeak.terminal
      simpa only [p, _root_.GD.N0232.N0720.N1025.d014309] using h
    exact ⟨p, hrep,
      (_root_.GD.N0232.N0720.N1260.d014973
        m n hm hn p).2 hterminal⟩
  · rintro ⟨p, hrep, hgap⟩
    let pWeak : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
      _root_.GD.N0232.N0720.N1025.d014307 m n hm hn p
    have hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
        _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p = p :=
      (_root_.GD.N0232.N0720.N1081.d014627
        m n hm hn p).2 hrep
    have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p.1 :=
      (_root_.GD.N0232.N0720.N1260.d014973
        m n hm hn p).1 hgap
    refine ⟨pWeak, ?_⟩
    constructor
    · intro g
      change _root_.GD.N0232.N0720.N1025.d014307 m n hm hn
          (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
            ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm pWeak)) = pWeak
      rw [show (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm pWeak = p by rfl,
        hfixed g]
    · apply (_root_.GD.N0232.N0720.N1025.d014315 m n pWeak.1).2
      simpa [pWeak] using hterminal




theorem d014975 :
    (¬ _root_.GD.N0232.N0720.N1262.d014965 m n hm hn) ↔
      ∀ p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn,
        _root_.GD.N0232.N0720.N1081.d014624 m n hm hn p →
          0 < _root_.GD.N0232.N0720.N1260.d014970 m n hm hn p := by
  constructor
  · intro hnone p hrep
    have hne : _root_.GD.N0232.N0720.N1260.d014970 m n hm hn p ≠ 0 := by
      intro hzero
      apply hnone
      exact (_root_.GD.N0232.N0720.N1260.d014974
        m n hm hn).2 ⟨p, hrep, hzero⟩
    exact lt_of_le_of_ne
      (_root_.GD.N0232.N0720.N1260.d014971 m n hm hn p) hne.symm
  · intro hpos hexists
    obtain ⟨p, hrep, hzero⟩ :=
      (_root_.GD.N0232.N0720.N1260.d014974
        m n hm hn).1 hexists
    exact (ne_of_gt (hpos p hrep)) hzero




theorem d014976
    (hzero : ∃ p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn,
      _root_.GD.N0232.N0720.N1081.d014624 m n hm hn p ∧
        _root_.GD.N0232.N0720.N1260.d014970 m n hm hn p = 0) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨p, hrep, hgap⟩ := hzero
  have hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p = p :=
    (_root_.GD.N0232.N0720.N1081.d014627
      m n hm hn p).2 hrep
  have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p.1 :=
    (_root_.GD.N0232.N0720.N1260.d014973
      m n hm hn p).1 hgap
  exact
    _root_.GD.N0232.N0720.N1215.d014300
      m n hm hn p hterminal hfixed




theorem d014977
    (hselected : _root_.GD.N0232.N0720.N1262.d014965 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply
    _root_.GD.N0232.N0720.N1260.d014976
      m n hm hn
  exact (_root_.GD.N0232.N0720.N1260.d014974
    m n hm hn).1 hselected





theorem d014978
    (hfail : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n) :
    ∀ p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn,
      _root_.GD.N0232.N0720.N1081.d014624 m n hm hn p →
        0 < _root_.GD.N0232.N0720.N1260.d014970 m n hm hn p := by
  apply
    (_root_.GD.N0232.N0720.N1260.d014975
      m n hm hn).1
  intro hselected
  exact hfail
    (_root_.GD.N0232.N0720.N1260.d014977
      m n hm hn hselected)

end

end N1260
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1260.d014971
#print axioms _root_.GD.N0232.N0720.N1260.d014973
#print axioms _root_.GD.N0232.N0720.N1260.d014974
#print axioms _root_.GD.N0232.N0720.N1260.d014975
#print axioms _root_.GD.N0232.N0720.N1260.d014977
#print axioms _root_.GD.N0232.N0720.N1260.d014978
