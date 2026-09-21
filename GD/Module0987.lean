import GD.Module0986






















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1356

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1288

variable (m n : ℕ)



theorem d015639
    (s d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s)
    (hnorm : ‖d‖ ^ 2 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2) :
    d = _root_.GD.N0232.N0720.N1159.d014633 m n s := by
  have htax := _root_.GD.N0232.N0720.N1159.d014648 m n s d hd
  have h0 : ‖d - _root_.GD.N0232.N0720.N1159.d014633 m n s‖ = 0 := by
    nlinarith [norm_nonneg (d - _root_.GD.N0232.N0720.N1159.d014633 m n s)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)



theorem d015640
    (s d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s)
    (hrisk : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 d ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014633 m n s)) :
    d = _root_.GD.N0232.N0720.N1159.d014633 m n s := by
  apply _root_.GD.N0232.N0720.N1356.d015639 m n s d hd
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hrisk
  simp only [zero_sub, norm_neg] at hrisk
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hrisk


theorem d015641
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g
        (_root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d
          (_root_.GD.N0232.N0720.N1159.d014644 m n s d hd))
        (_root_.GD.N0232.N0720.N1482.d015158 (m := m) (n := n) g⁻¹ d
          (_root_.GD.N0232.N0720.N1159.d014644 m n s d hd)) = d := by
  rw [_root_.GD.N0232.N0720.N1482.d015161, mul_inv_cancel, _root_.GD.N0232.N0720.N1482.d015159]



theorem d015642
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d := by
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hdF : _root_.GD.N0232.N0720.N1159.d014637 m n d := _root_.GD.N0232.N0720.N1159.d014644 m n s d hd
  have hd'mem :
      _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d hdF ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014645 m n s g⁻¹ ⟨d, hd⟩).2
  have hL :
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP) =
        ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014643 m n g _ _ hP
  have hR :
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d =
        ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d hdF) := by
    conv_lhs => rw [← _root_.GD.N0232.N0720.N1356.d015641 m n s g d hd]
    exact _root_.GD.N0232.N0720.N1159.d014643 m n g _ _ _
  change _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP) ≤ _
  rw [hL, hR]
  exact mul_le_mul_right
    ((_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.2 _ hd'mem) _



theorem d015643
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hrisk : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1) :
    d = (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 := by
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hdF : _root_.GD.N0232.N0720.N1159.d014637 m n d := _root_.GD.N0232.N0720.N1159.d014644 m n s d hd
  have hd'mem :
      _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d hdF ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014645 m n s g⁻¹ ⟨d, hd⟩).2
  have hL :
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP) =
        ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014643 m n g _ _ hP
  have hR :
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d =
        ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d hdF) := by
    conv_lhs => rw [← _root_.GD.N0232.N0720.N1356.d015641 m n s g d hd]
    exact _root_.GD.N0232.N0720.N1159.d014643 m n g _ _ _
  change _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d ≤
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP) at hrisk
  rw [hL, hR, _root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hrisk
  simp only [zero_sub, norm_neg] at hrisk
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)] at hrisk
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hrisk
  have hle : ‖_root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d hdF‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 :=
    le_of_mul_le_mul_left hreal (pow_pos g.d009240 2)
  have hinv :
      _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d hdF = _root_.GD.N0232.N0720.N1159.d014633 m n s.value :=
    _root_.GD.N0232.N0720.N1356.d015639 m n s.value _ hd'mem hle
  change d = _root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP
  rw [← _root_.GD.N0232.N0720.N1356.d015641 m n s g d hd]
  congr 1



theorem d015644
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 ↔
      ∀ d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d := by
  rw [_root_.GD.N0232.N0720.N1159.d014651]
  constructor
  · intro hfix d hd
    have hval := congrArg Subtype.val hfix
    change (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 =
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value at hval
    rw [← hval]
    exact _root_.GD.N0232.N0720.N1356.d015642 m n s g d hd
  · intro hmin
    apply Subtype.ext
    symm
    exact _root_.GD.N0232.N0720.N1356.d015643 m n s g _
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
      (hmin _ (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2)





theorem d015645
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          (∀ d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169)
                (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ≤
              _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169) d) ∧
          (∀ d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131 _root_.GD.N0232.N0720.N1080.d014169)
                (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ≤
              _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131 _root_.GD.N0232.N0720.N1080.d014169) d) := by
  rw [_root_.GD.N0232.N0720.N1482.d015172
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hs, htwo, hthree⟩
    exact ⟨s, hs,
      (_root_.GD.N0232.N0720.N1356.d015644 m n s _).1 htwo,
      (_root_.GD.N0232.N0720.N1356.d015644 m n s _).1 hthree⟩
  · rintro ⟨s, hs, htwo, hthree⟩
    exact ⟨s, hs,
      (_root_.GD.N0232.N0720.N1356.d015644 m n s _).2 htwo,
      (_root_.GD.N0232.N0720.N1356.d015644 m n s _).2 hthree⟩

end

end N1356
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1356.d015642
#print axioms _root_.GD.N0232.N0720.N1356.d015643
#print axioms _root_.GD.N0232.N0720.N1356.d015644
#print axioms _root_.GD.N0232.N0720.N1356.d015645
