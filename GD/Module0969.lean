import GD.Module0966




























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1201

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1482



variable (m n : ℕ)


noncomputable def d015333
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : ℝ :=
  ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2


theorem d015334
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  have href := (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1 _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm :
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
  exact sub_nonneg.mpr hnorm


theorem d015335
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  have href :=
    (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2
      _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm :
      ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g
          (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1‖ ^ 2 ≤
        ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
  unfold _root_.GD.N0232.N0720.N1159.d014647 _root_.GD.N0232.N0720.N1201.d015333
  linarith



theorem d015336
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s ≤
      2 * _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  have htwo := _root_.GD.N0232.N0720.N1201.d015335
    m n s _root_.GD.N0232.N0720.N1482.d015130
  have hthree := _root_.GD.N0232.N0720.N1201.d015335
    m n s _root_.GD.N0232.N0720.N1482.d015131
  unfold _root_.GD.N0232.N0720.N1482.d015169
  linarith



theorem d015337
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hgap : _root_.GD.N0232.N0720.N1201.d015333 m n s = 0) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  apply le_antisymm
  · exact (_root_.GD.N0232.N0720.N1201.d015336
      m n s).trans_eq (by simp [hgap])
  · exact _root_.GD.N0232.N0720.N1482.d015170 s



theorem d015338
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value d) :
    ‖s.value‖ ^ 2 - ‖d‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  have href := (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.2 d hd
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm : ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ ‖d‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖d‖)).mp href
  unfold _root_.GD.N0232.N0720.N1201.d015333
  linarith




theorem d015339
    {SeedIndex : Type*}
    (seed : SeedIndex → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ε : ℝ) (_hε : 0 < ε)
    (hbelow : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value d)
    (hseparated : ∀ j, ε ≤ ‖(seed j).value‖ ^ 2 - ‖d‖ ^ 2) :
    ∀ j, ε ≤ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j) := by
  intro j
  exact (hseparated j).trans
    (_root_.GD.N0232.N0720.N1201.d015338
      m n (seed j) d (hbelow j))




theorem d015340
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hgap : ∀ ε : ℝ, 0 < ε →
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s ∧
          _root_.GD.N0232.N0720.N1201.d015333 m n s < ε) :
    _root_.GD.N0232.N0720.N1200.d015252 m n hm hn := by
  intro ε hε
  obtain ⟨s, hs, hsmall⟩ := hgap (ε / 2) (by linarith)
  refine ⟨s, hs, lt_of_le_of_lt
    (_root_.GD.N0232.N0720.N1201.d015336 m n s) ?_⟩
  linarith







theorem d015341
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s ∧
          _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 := by
  constructor
  · intro hendpoint
    obtain ⟨p, hrep, hstrict, hterminal⟩ :=
      (_root_.GD.N0232.N0720.N1159.d014664
        m n hm hn).1 hendpoint
    let s := _root_.GD.N0232.N0720.N1159.d014657
      m n hm hn p hrep hstrict
    refine ⟨s, ?_, ?_⟩
    · simpa only [_root_.GD.N0232.N0720.N1200.d015250, s,
        _root_.GD.N0232.N0720.N1159.d014657] using hstrict
    · have heq :=
        (_root_.GD.N0232.N0720.N1159.d014658
          m n hm hn p hrep hstrict hterminal).1
      unfold _root_.GD.N0232.N0720.N1201.d015333
      change ‖p‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n p‖ ^ 2 = 0
      have heq' : _root_.GD.N0232.N0720.N1159.d014633 m n p = p := by
        simpa only [s, _root_.GD.N0232.N0720.N1159.d014657] using heq
      rw [heq', sub_self]
  · rintro ⟨s, hstrict, hgap⟩
    apply
      (_root_.GD.N0232.N0720.N1482.d015173
        (m := m) (n := n) hm hn).2
    exact ⟨s, hstrict,
      _root_.GD.N0232.N0720.N1201.d015337
        m n s hgap⟩







theorem d015342
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s →
          0 < _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  constructor
  · intro hno s hs
    exact lt_of_le_of_ne (_root_.GD.N0232.N0720.N1201.d015334 m n s) fun hzero ↦
      hno
        ((_root_.GD.N0232.N0720.N1201.d015341
          m n hm hn).2 ⟨s, hs, hzero.symm⟩)
  · intro hpositive hendpoint
    obtain ⟨s, hs, hzero⟩ :=
      (_root_.GD.N0232.N0720.N1201.d015341
        m n hm hn).1 hendpoint
    exact (ne_of_gt (hpositive s hs)) hzero



namespace N1758

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N1022

variable (k : ℕ) (sizes : Fin k → ℕ)


noncomputable def d015343
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) : ℝ :=
  ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2

theorem d015344
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) :
    0 ≤ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s := by
  have href := (_root_.GD.N0232.N0719.N0896.d011100 k sizes s.value).1
    (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes, _root_.GD.N0232.N0719.N0859.d010829 k sizes] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm :
      ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2 ≤ ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
  exact sub_nonneg.mpr hnorm

theorem d015345
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0719.N0896.d011114 k sizes s g ≤
      _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s := by
  have href :=
    (_root_.GD.N0232.N0719.N0896.d011112 k sizes s g (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).2
      (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes, _root_.GD.N0232.N0719.N0859.d010829 k sizes] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm :
      ‖(_root_.GD.N0232.N0719.N0896.d011112 k sizes s g
          (_root_.GD.N0232.N0719.N0896.d011113 k sizes s)).1‖ ^ 2 ≤
        ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
  unfold
    _root_.GD.N0232.N0719.N0896.d011114
    _root_.GD.N0232.N0720.N1201.N1758.d015343
  linarith

theorem d015346
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes) :
    _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s ≤
      2 * _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s := by
  have htwo := _root_.GD.N0232.N0720.N1201.N1758.d015345
    k sizes s _root_.GD.N0232.N0720.N1482.d015130
  have hthree := _root_.GD.N0232.N0720.N1201.N1758.d015345
    k sizes s _root_.GD.N0232.N0720.N1482.d015131
  unfold
    _root_.GD.N0232.N0719.N1022.d015189
  linarith

theorem d015347
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hgap : _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s = 0) :
    _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s = 0 := by
  apply le_antisymm
  · exact (_root_.GD.N0232.N0720.N1201.N1758.d015346
      k sizes s).trans_eq (by simp [hgap])
  · exact _root_.GD.N0232.N0719.N1022.d015190 k sizes s

theorem d015348
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value d) :
    ‖s.value‖ ^ 2 - ‖d‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s := by
  have href := (_root_.GD.N0232.N0719.N0896.d011100 k sizes s.value).2.2 d hd
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes, _root_.GD.N0232.N0719.N0859.d010829 k sizes] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm : ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2 ≤ ‖d‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖d‖)).mp href
  unfold _root_.GD.N0232.N0720.N1201.N1758.d015343
  linarith

theorem d015349
    {SeedIndex : Type*}
    (seed : SeedIndex → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (ε : ℝ) (_hε : 0 < ε)
    (hbelow : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value d)
    (hseparated : ∀ j, ε ≤ ‖(seed j).value‖ ^ 2 - ‖d‖ ^ 2) :
    ∀ j, ε ≤ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed j) := by
  intro j
  exact (hseparated j).trans
    (_root_.GD.N0232.N0720.N1201.N1758.d015348
      k sizes (seed j) d (hbelow j))

theorem d015350
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hgap : ∀ ε : ℝ, 0 < ε →
      ∃ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0232.N0720.N1200.d015258 k sizes hk hsizes s ∧
          _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s < ε) :
    _root_.GD.N0232.N0720.N1200.d015260 k sizes hk hsizes := by
  intro ε hε
  obtain ⟨s, hs, hsmall⟩ := hgap (ε / 2) (by linarith)
  refine ⟨s, hs, lt_of_le_of_lt
    (_root_.GD.N0232.N0720.N1201.N1758.d015346
      k sizes s) ?_⟩
  linarith




theorem d015351
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      ∃ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0232.N0720.N1200.d015258 k sizes hk hsizes s ∧
          _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s = 0 := by
  constructor
  · intro hendpoint
    obtain ⟨p, hrep, hstrict, hterminal⟩ :=
      (_root_.GD.N0232.N0719.N0896.d011133
        k sizes hk hsizes).1 hendpoint
    let s :=
      _root_.GD.N0232.N0719.N0896.d011129
      k sizes hk hsizes p hrep hstrict
    refine ⟨s, ?_, ?_⟩
    · change _root_.GD.N0230.N0608.d000675
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)
      simpa only [s,
        _root_.GD.N0232.N0719.N0896.d011129]
        using hstrict
    · have heq :=
        (_root_.GD.N0232.N0719.N0896.d011134
          k sizes hk hsizes p hrep hstrict hterminal).1
      unfold _root_.GD.N0232.N0720.N1201.N1758.d015343
      have hsvalue : s.value = p := rfl
      rw [hsvalue]
      have heq' : _root_.GD.N0232.N0719.N0896.d011099 k sizes p = p := by
        simpa only [s,
          _root_.GD.N0232.N0719.N0896.d011129]
          using heq
      rw [heq', sub_self]
  · rintro ⟨s, hstrict, hgap⟩
    apply
      (_root_.GD.N0232.N0719.N1022.d015193
        k sizes hk hsizes).2
    exact ⟨s, hstrict,
      _root_.GD.N0232.N0720.N1201.N1758.d015347
        k sizes s hgap⟩




theorem d015352
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      ∀ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
        _root_.GD.N0232.N0720.N1200.d015258 k sizes hk hsizes s →
          0 < _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s := by
  constructor
  · intro hno s hs
    exact lt_of_le_of_ne (_root_.GD.N0232.N0720.N1201.N1758.d015344 k sizes s) fun hzero ↦
      hno
        ((_root_.GD.N0232.N0720.N1201.N1758.d015351
          k sizes hk hsizes).2 ⟨s, hs, hzero.symm⟩)
  · intro hpositive hendpoint
    obtain ⟨s, hs, hzero⟩ :=
      (_root_.GD.N0232.N0720.N1201.N1758.d015351
        k sizes hk hsizes).1 hendpoint
    exact (ne_of_gt (hpositive s hs)) hzero

end N1758

end

end N1201
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1201.d015336
#print axioms _root_.GD.N0232.N0720.N1201.d015338
#print axioms _root_.GD.N0232.N0720.N1201.d015339
#print axioms _root_.GD.N0232.N0720.N1201.d015340
#print axioms _root_.GD.N0232.N0720.N1201.d015341
#print axioms _root_.GD.N0232.N0720.N1201.d015342
#print axioms _root_.GD.N0232.N0720.N1201.N1758.d015346
#print axioms _root_.GD.N0232.N0720.N1201.N1758.d015348
#print axioms _root_.GD.N0232.N0720.N1201.N1758.d015349
#print axioms _root_.GD.N0232.N0720.N1201.N1758.d015350
#print axioms _root_.GD.N0232.N0720.N1201.N1758.d015351
#print axioms _root_.GD.N0232.N0720.N1201.N1758.d015352
