import GD.Module1144
import GD.Module0974
















namespace GD
namespace N0232
namespace N0720
namespace N1109

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1055
open _root_.GD.N0232.N0720.N1061
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1110
open _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1134
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201

variable {m n : ℕ}




def d018402
    {I : Type*} (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ (i : I) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
      _root_.GD.N0232.N0720.N1131.d017154
        m n candidate (seed i).value < epsilon




def d018403
    {I : Type*} (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ (i : I) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
      _root_.GD.N0232.N0720.N1131.d017154
          m n candidate (seed i).value < epsilon ∧
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - (seed i).value‖ ^ 2 < epsilon ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) ∧
        ¬ _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) ∧
        ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) (seed i).value ∧
        ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)



theorem d018404
    {I : Type*} (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1109.d018403 seed ↔
      _root_.GD.N0232.N0720.N1109.d018402 seed := by
  constructor
  · intro h epsilon hepsilon
    obtain ⟨i, candidate, hcalibration, _hnorm, _hterminal,
      _hnaffine, _hleft, _hright⟩ := h epsilon hepsilon
    exact ⟨i, candidate, hcalibration⟩
  · intro h epsilon hepsilon
    obtain ⟨i, candidate, hcalibration⟩ := h epsilon hepsilon
    have hseedMem : (seed i).value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n (seed i).value :=
      _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value
    have hnorm :=
      _root_.GD.N0232.N0720.N1131.d017158
        m n (seed i) candidate (seed i).value hseedMem
    refine ⟨i, candidate, hcalibration, hnorm.trans_lt hcalibration,
      ?_, ?_, _root_.GD.N0232.N0720.N1134.d018394 (seed i) candidate,
      _root_.GD.N0232.N0720.N1134.d018395 (seed i) candidate⟩
    · simpa only [_root_.GD.N0232.N0720.N1130.d017075] using
        _root_.GD.N0232.N0720.N1125.d017263
          (m := m) (n := n) candidate.packet candidate.weight
            candidate.weight_nonneg
    · simpa only [_root_.GD.N0232.N0720.N1130.d017075] using
        _root_.GD.N0232.N0720.N1055.d017240
          (m := m) (n := n) candidate.packet candidate.weight
            candidate.weight_nonneg




def d018405
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∃ seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1110.d015460 m n seed ∧
      _root_.GD.N0232.N0720.N1109.d018402 seed ∧
      ∃ iStrict,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)




theorem d018406
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      _root_.GD.N0232.N0720.N1109.d018405 hm hn := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, hgap⟩ :=
      (_root_.GD.N0232.N0720.N1201.d015341
        m n hm hn).1 hendpoint
    refine ⟨fun _ ↦ s, ?_, ?_, 0, hstrict⟩
    · intro u
      refine ⟨s.value, ?_⟩
      intro i hi
      exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
    · intro epsilon hepsilon
      obtain ⟨candidate, hcandidate⟩ :=
        _root_.GD.N0232.N0720.N1135.d018325 s epsilon hepsilon
      rw [hgap, zero_add] at hcandidate
      exact ⟨0, candidate, hcandidate⟩
  · rintro ⟨seed, hfinite, hsmall, iStrict, hstrict⟩
    apply _root_.GD.N0232.N0720.N1110.d015463
      m n hm hn seed hfinite _ iStrict hstrict
    intro epsilon hepsilon
    obtain ⟨i, candidate, hcandidate⟩ := hsmall epsilon hepsilon
    exact ⟨i, lt_of_le_of_lt
      (_root_.GD.N0232.N0720.N1135.d018316
        (seed i) candidate) hcandidate⟩



theorem d018407
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1110.d015460 m n seed ∧
          _root_.GD.N0232.N0720.N1109.d018403 seed ∧
          ∃ iStrict,
            _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
              (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  rw [_root_.GD.N0232.N0720.N1109.d018406
    hm hn]
  unfold _root_.GD.N0232.N0720.N1109.d018405
  apply exists_congr
  intro seed
  rw [_root_.GD.N0232.N0720.N1109.d018404 seed]




theorem d018408
    {I : Type*}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hfinite : ∀ u : Finset I,
      ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (hsmall : _root_.GD.N0232.N0720.N1109.d018402 seed)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply
    _root_.GD.N0232.N0720.N1110.d015468
      m n hm hn seed hfinite _ iStrict hstrict
  intro epsilon hepsilon
  obtain ⟨i, candidate, hcandidate⟩ := hsmall epsilon hepsilon
  exact ⟨i, lt_of_le_of_lt
    (_root_.GD.N0232.N0720.N1135.d018316
      (seed i) candidate) hcandidate⟩





theorem d018409
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : _root_.GD.N0232.N0720.N1109.d018402 seed)
    (iStrict : ℕ)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ u : Finset ℕ,
      ¬ ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d := by
  apply _root_.GD.N0232.N0720.N1110.d015466
    m n hm hn hno seed _ iStrict hstrict
  intro epsilon hepsilon
  obtain ⟨i, candidate, hcandidate⟩ := hsmall epsilon hepsilon
  exact ⟨i, lt_of_le_of_lt
    (_root_.GD.N0232.N0720.N1135.d018316
      (seed i) candidate) hcandidate⟩




theorem d018410
    {I : Type*}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : _root_.GD.N0232.N0720.N1109.d018402 seed)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ u : Finset I,
      ¬ ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d := by
  apply
    _root_.GD.N0232.N0720.N1110.d015470
      m n hm hn hno seed _ iStrict hstrict
  intro epsilon hepsilon
  obtain ⟨i, candidate, hcandidate⟩ := hsmall epsilon hepsilon
  exact ⟨i, lt_of_le_of_lt
    (_root_.GD.N0232.N0720.N1135.d018316
      (seed i) candidate) hcandidate⟩




theorem d018411
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (¬ _root_.GD.N0232.N0720.N1159.d014661 m n) ↔
      ∀ (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n),
        _root_.GD.N0232.N0720.N1109.d018402 seed →
        (∃ iStrict,
          _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
            (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) →
        ∃ u : Finset ℕ,
          ¬ ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
            ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d := by
  constructor
  · intro hno seed hsmall
    rintro ⟨iStrict, hstrict⟩
    exact _root_.GD.N0232.N0720.N1109.d018409
      hm hn hno seed hsmall iStrict hstrict
  · intro hobstruction hendpoint
    obtain ⟨seed, hfinite, hsmall, iStrict, hstrict⟩ :=
      (_root_.GD.N0232.N0720.N1109.d018406
        hm hn).1 hendpoint
    obtain ⟨u, hu⟩ := hobstruction seed hsmall ⟨iStrict, hstrict⟩
    exact hu (hfinite u)




theorem d018412
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (¬ _root_.GD.N0232.N0720.N1159.d014661 m n) ↔
      ∀ (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n),
        _root_.GD.N0232.N0720.N1110.d015460 m n seed →
        (∃ iStrict,
          _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
            (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) →
        ∃ epsilon : ℝ, 0 < epsilon ∧
          ∀ (i : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
            epsilon ≤ _root_.GD.N0232.N0720.N1131.d017154
              m n candidate (seed i).value := by
  constructor
  · intro hno seed hfinite hstrict
    by_contra hfloor
    have hsmall : _root_.GD.N0232.N0720.N1109.d018402 seed := by
      intro epsilon hepsilon
      by_contra hnone
      apply hfloor
      refine ⟨epsilon, hepsilon, ?_⟩
      intro i candidate
      exact le_of_not_gt fun hlt ↦ hnone ⟨i, candidate, hlt⟩
    exact hno
      ((_root_.GD.N0232.N0720.N1109.d018406
        hm hn).2 ⟨seed, hfinite, hsmall, hstrict⟩)
  · intro hfloor hendpoint
    obtain ⟨seed, hfinite, hsmall, iStrict, hstrict⟩ :=
      (_root_.GD.N0232.N0720.N1109.d018406
        hm hn).1 hendpoint
    obtain ⟨epsilon, hepsilon, hbound⟩ :=
      hfloor seed hfinite ⟨iStrict, hstrict⟩
    obtain ⟨i, candidate, hlt⟩ := hsmall epsilon hepsilon
    exact (not_lt_of_ge (hbound i candidate)) hlt

end

end N1109
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1109.d018404
#print axioms _root_.GD.N0232.N0720.N1109.d018406
#print axioms _root_.GD.N0232.N0720.N1109.d018407
#print axioms _root_.GD.N0232.N0720.N1109.d018408
#print axioms _root_.GD.N0232.N0720.N1109.d018409
#print axioms _root_.GD.N0232.N0720.N1109.d018410
#print axioms _root_.GD.N0232.N0720.N1109.d018411
#print axioms _root_.GD.N0232.N0720.N1109.d018412
