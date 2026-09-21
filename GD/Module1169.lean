import GD.Module1168





























namespace GD
namespace N0232
namespace N0720
namespace N1355

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1158
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1202
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1408
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}

abbrev d018767 :=
  _root_.GD.N0232.N0719.N0946.d009229





noncomputable def d018768
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1355.d018767) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  (_root_.GD.N0232.N0720.N1159.d014645 m n s g
    (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1

@[simp] theorem d018769
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1355.d018767) :
    _root_.GD.N0232.N0720.N1355.d018768 s g =
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g
        (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 := rfl




theorem d018770
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1355.d018767) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1355.d018768 s g)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ↔
      _root_.GD.N0232.N0720.N1355.d018768 s g = _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  constructor
  · intro hdom
    exact (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1 _ hdom
  · intro hfixed
    rw [hfixed]
    exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)



theorem d018771
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q).toReal = ‖q‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1080.d014190]
  simp only [zero_sub, norm_neg, ENNReal.toReal_ofReal (sq_nonneg ‖q‖)]




theorem d018772
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1355.d018767) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1355.d018768 s g)).toReal ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal ↔
      _root_.GD.N0232.N0720.N1355.d018768 s g = _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  have hdefect : 0 ≤ _root_.GD.N0232.N0720.N1159.d014647 m n s g :=
    _root_.GD.N0232.N0720.N1159.d014650 m n s g
  constructor
  · intro href
    have hzero : _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
      rw [_root_.GD.N0232.N0720.N1355.d018771,
        _root_.GD.N0232.N0720.N1355.d018771] at href
      apply le_antisymm
      · unfold _root_.GD.N0232.N0720.N1159.d014647
        change ‖_root_.GD.N0232.N0720.N1355.d018768 s g‖ ^ 2 -
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ 0
        linarith
      · exact hdefect
    have hpoint := (_root_.GD.N0232.N0720.N1159.d014651 m n s g).1 hzero
    exact congrArg Subtype.val hpoint
  · intro hfixed
    rw [hfixed]




theorem d018773
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1355.d018767) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1355.d018768 s g)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ↔
      (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1355.d018768 s g)).toReal ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal := by
  rw [_root_.GD.N0232.N0720.N1355.d018770,
    _root_.GD.N0232.N0720.N1355.d018772]





def d018774
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1355.d018768 s _root_.GD.N0232.N0720.N1482.d015130)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ∧
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1355.d018768 s _root_.GD.N0232.N0720.N1482.d015131)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)


theorem d018775
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1355.d018774 s ↔
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  constructor
  · rintro ⟨hTwo, hThree⟩
    have hTwoFixed :=
      (_root_.GD.N0232.N0720.N1355.d018770
        s _root_.GD.N0232.N0720.N1482.d015130).1 hTwo
    have hThreeFixed :=
      (_root_.GD.N0232.N0720.N1355.d018770
        s _root_.GD.N0232.N0720.N1482.d015131).1 hThree
    have hTwoZero : _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 := by
      apply (_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).2
      apply Subtype.ext
      exact hTwoFixed
    have hThreeZero :
        _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0 := by
      apply (_root_.GD.N0232.N0720.N1159.d014651
        m n s _root_.GD.N0232.N0720.N1482.d015131).2
      apply Subtype.ext
      exact hThreeFixed
    unfold _root_.GD.N0232.N0720.N1482.d015169
    rw [hTwoZero, hThreeZero, add_zero]
  · intro hmaster
    have hall :=
      (_root_.GD.N0232.N0720.N1482.d015171
        (m := m) (n := n) s).1 hmaster
    constructor
    · apply (_root_.GD.N0232.N0720.N1355.d018770
        s _root_.GD.N0232.N0720.N1482.d015130).2
      have hpoint :=
        (_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).1
          (hall _root_.GD.N0232.N0720.N1482.d015130)
      exact congrArg Subtype.val hpoint
    · apply (_root_.GD.N0232.N0720.N1355.d018770
        s _root_.GD.N0232.N0720.N1482.d015131).2
      have hpoint :=
        (_root_.GD.N0232.N0720.N1159.d014651
          m n s _root_.GD.N0232.N0720.N1482.d015131).1
          (hall _root_.GD.N0232.N0720.N1482.d015131)
      exact congrArg Subtype.val hpoint




noncomputable def d018776
    (weight : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : ℝ :=
  weight * (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
      (_root_.GD.N0232.N0720.N1355.d018768 s _root_.GD.N0232.N0720.N1482.d015130)).toReal +
    (1 - weight) * (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
      (_root_.GD.N0232.N0720.N1355.d018768 s _root_.GD.N0232.N0720.N1482.d015131)).toReal


noncomputable def d018777
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal



theorem d018778
    (weight : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1355.d018776 weight s =
      _root_.GD.N0232.N0720.N1408.d018758 weight s := by
  unfold _root_.GD.N0232.N0720.N1355.d018776
    _root_.GD.N0232.N0720.N1408.d018758 _root_.GD.N0232.N0720.N1408.d018757
    _root_.GD.N0232.N0720.N1355.d018768
  rw [_root_.GD.N0232.N0720.N1355.d018771,
    _root_.GD.N0232.N0720.N1355.d018771]


theorem d018779
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1355.d018777 s =
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  exact _root_.GD.N0232.N0720.N1355.d018771 _




theorem d018780
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1355.d018776 weight s ≤
        _root_.GD.N0232.N0720.N1355.d018777 s ↔
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  rw [_root_.GD.N0232.N0720.N1355.d018778,
    _root_.GD.N0232.N0720.N1355.d018779]
  exact _root_.GD.N0232.N0720.N1408.d018761
    weight hweight0 hweight1 s



theorem d018781
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1355.d018774 s ↔
      _root_.GD.N0232.N0720.N1355.d018776 weight s ≤
        _root_.GD.N0232.N0720.N1355.d018777 s := by
  rw [_root_.GD.N0232.N0720.N1355.d018775,
    _root_.GD.N0232.N0720.N1355.d018780
      weight hweight0 hweight1]






theorem d018782
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (href : _root_.GD.N0232.N0720.N1355.d018776 weight s ≤
      _root_.GD.N0232.N0720.N1355.d018777 s) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ∧
      _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ∧
      ∀ g : _root_.GD.N0232.N0720.N1355.d018767,
        _root_.GD.N0232.N0720.N1159.d014642 m n g
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
            (_root_.GD.N0232.N0720.N1159.d014644 m n s
              (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
              (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  have hmaster :=
    (_root_.GD.N0232.N0720.N1355.d018780
      weight hweight0 hweight1 s).1 href
  have henergy :=
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).1 hmaster
  have hcharacter :=
    _root_.GD.N0232.N0720.N1202.d018574
      s hmaster
  have hallDefects :=
    (_root_.GD.N0232.N0720.N1482.d015171
      (m := m) (n := n) s).1 hmaster
  have hrepresentative :
      _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    (_root_.GD.N0232.N0720.N1159.d014656 m n hm hn s).1 hallDefects
  refine ⟨hcharacter, hrepresentative, ?_⟩
  exact
    (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1159.d014644 m n s
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1)).2
      hrepresentative






theorem d018783
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1355.d018776 weight s ≤
            _root_.GD.N0232.N0720.N1355.d018777 s := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hmaster⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1355.d018780
        weight hweight0 hweight1 s).2 hmaster⟩
  · rintro ⟨s, hstrict, href⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1355.d018780
        weight hweight0 hweight1 s).1 href⟩




theorem d018784
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) →
          _root_.GD.N0232.N0720.N1355.d018777 s <
            _root_.GD.N0232.N0720.N1355.d018776 weight s := by
  rw [_root_.GD.N0232.N0720.N1355.d018783
    (m := m) (n := n) hm hn weight hweight0 hweight1]
  push Not
  rfl



theorem d018785
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1355.d018776 1 s ≤
        _root_.GD.N0232.N0720.N1355.d018777 s ↔
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 := by
  rw [_root_.GD.N0232.N0720.N1355.d018778,
    _root_.GD.N0232.N0720.N1355.d018779]
  have hnonneg := _root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015130
  unfold _root_.GD.N0232.N0720.N1408.d018758 _root_.GD.N0232.N0720.N1408.d018757
    _root_.GD.N0232.N0720.N1159.d014647
  norm_num
  constructor <;> intro h
  · exact le_antisymm (by linarith) hnonneg
  · linarith



theorem d018786
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1355.d018776 0 s ≤
        _root_.GD.N0232.N0720.N1355.d018777 s ↔
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0 := by
  rw [_root_.GD.N0232.N0720.N1355.d018778,
    _root_.GD.N0232.N0720.N1355.d018779]
  have hnonneg :=
    _root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015131
  unfold _root_.GD.N0232.N0720.N1408.d018758 _root_.GD.N0232.N0720.N1408.d018757
    _root_.GD.N0232.N0720.N1159.d014647
  norm_num
  constructor <;> intro h
  · exact le_antisymm (by linarith) hnonneg
  · linarith




theorem d018787 :
    ∃ d₂ d₃ : ℝ,
      0 ≤ d₂ ∧ 0 ≤ d₃ ∧
      (0 : ℝ) * d₂ + 1 * d₃ ≤ 0 ∧
      d₂ + d₃ ≠ 0 := by
  exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩





theorem d018788
    (weight : ℝ) :
    (∀ d₂ d₃ : ℝ,
        0 ≤ d₂ → 0 ≤ d₃ →
        weight * d₂ + (1 - weight) * d₃ ≤ 0 →
        d₂ + d₃ = 0) ↔
      0 < weight ∧ weight < 1 := by
  constructor
  · intro h
    constructor
    · by_contra hnot
      have hweight : weight ≤ 0 := le_of_not_gt hnot
      have hzero := h 1 0 (by norm_num) (by norm_num) (by simpa using hweight)
      norm_num at hzero
    · by_contra hnot
      have hweight : 1 ≤ weight := le_of_not_gt hnot
      have hright : 1 - weight ≤ 0 := sub_nonpos.mpr hweight
      have hzero := h 0 1 (by norm_num) (by norm_num) (by simpa using hright)
      norm_num at hzero
  · rintro ⟨hweight0, hweight1⟩ d₂ d₃ hd₂ hd₃ hle
    have hright : 0 < 1 - weight := sub_pos.mpr hweight1
    have hleftNonneg : 0 ≤ weight * d₂ :=
      mul_nonneg hweight0.le hd₂
    have hrightNonneg : 0 ≤ (1 - weight) * d₃ :=
      mul_nonneg hright.le hd₃
    have hsum : weight * d₂ + (1 - weight) * d₃ = 0 :=
      le_antisymm hle (add_nonneg hleftNonneg hrightNonneg)
    have hparts :=
      (add_eq_zero_iff_of_nonneg hleftNonneg hrightNonneg).1 hsum
    have hd₂zero : d₂ = 0 :=
      (mul_eq_zero.mp hparts.1).resolve_left (ne_of_gt hweight0)
    have hd₃zero : d₃ = 0 :=
      (mul_eq_zero.mp hparts.2).resolve_left (ne_of_gt hright)
    rw [hd₂zero, hd₃zero, add_zero]

end

end N1355
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1355.d018770
#print axioms _root_.GD.N0232.N0720.N1355.d018773
#print axioms _root_.GD.N0232.N0720.N1355.d018775
#print axioms _root_.GD.N0232.N0720.N1355.d018780
#print axioms _root_.GD.N0232.N0720.N1355.d018781
#print axioms _root_.GD.N0232.N0720.N1355.d018782
#print axioms _root_.GD.N0232.N0720.N1355.d018783
#print axioms _root_.GD.N0232.N0720.N1355.d018784
#print axioms _root_.GD.N0232.N0720.N1355.d018785
#print axioms _root_.GD.N0232.N0720.N1355.d018786
#print axioms _root_.GD.N0232.N0720.N1355.d018787
#print axioms _root_.GD.N0232.N0720.N1355.d018788
