import GD.Module1206
import GD.Module1197
















open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1457

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1106
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1109
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1298
open _root_.GD.N0232.N0720.N1451
open _root_.GD.N0232.N0720.N1455
open _root_.GD.N0232.N0720.N1456
open _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1471



def d019488
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate c.d019473 < ε


def d019489
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      ε ≤ _root_.GD.N0232.N0720.N1131.d017154 m n candidate c.d019473


def d019490
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : Prop :=
  ¬ _root_.GD.N0232.N0720.N1457.d019489 m n c



def d019491
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : Prop :=
  ∀ (B ε : ℝ), 0 < ε →
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      B < _root_.GD.N0232.N0720.N1298.d018713 candidate ∧
        _root_.GD.N0232.N0720.N1131.d017154 m n candidate c.d019473 < ε



theorem d019492
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1456.d019472 m n) :
    _root_.GD.N0232.N0720.N1457.d019490 m n c ↔
      _root_.GD.N0232.N0720.N1457.d019488 m n c := by
  constructor
  · intro hno ε hε
    by_contra hnone
    apply hno
    refine ⟨ε, hε, ?_⟩
    intro candidate
    exact le_of_not_gt (fun hlt ↦ hnone ⟨candidate, hlt⟩)
  · intro hsmall hfloor
    obtain ⟨ε, hε, hbound⟩ := hfloor
    obtain ⟨candidate, hlt⟩ := hsmall ε hε
    exact (not_lt_of_ge (hbound candidate)) hlt



def d019493
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014639 m n :=
  _root_.GD.N0232.N0720.N1471.N1760.d019433 m n hm hn
    (c.d019477 m n (lt_of_lt_of_le (by omega) hm)
      (lt_of_lt_of_le (by omega) hn)) hstrict

@[simp] theorem d019494
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    (_root_.GD.N0232.N0720.N1457.d019493 m n hm hn c hstrict).value = c.d019473 := rfl




def d019495
    (m n : ℕ) (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : ℝ :=
  ‖c.d019473‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n c.d019473‖ ^ 2



theorem d019496
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (a : ℝ) :
    (∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      a ≤ _root_.GD.N0232.N0720.N1131.d017154 m n candidate c.d019473) ↔
      a ≤ _root_.GD.N0232.N0720.N1457.d019495 m n c := by
  let s := _root_.GD.N0232.N0720.N1457.d019493 m n hm hn c hstrict
  simpa only [s, _root_.GD.N0232.N0720.N1457.d019494,
    _root_.GD.N0232.N0720.N1457.d019495, _root_.GD.N0232.N0720.N1201.d015333] using
    _root_.GD.N0232.N0720.N1135.d018326 s a



theorem d019497
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1457.d019489 m n c ↔
      0 < _root_.GD.N0232.N0720.N1457.d019495 m n c := by
  constructor
  · rintro ⟨ε, hε, hbound⟩
    exact hε.trans_le
      ((_root_.GD.N0232.N0720.N1457.d019496
        m n hm hn c hstrict ε).1 hbound)
  · intro hgap
    refine ⟨_root_.GD.N0232.N0720.N1457.d019495 m n c, hgap, ?_⟩
    exact (_root_.GD.N0232.N0720.N1457.d019496
      m n hm hn c hstrict (_root_.GD.N0232.N0720.N1457.d019495 m n c)).2 le_rfl



theorem d019498
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1457.d019488 m n c ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) c.d019473 := by
  let s := _root_.GD.N0232.N0720.N1457.d019493 m n hm hn c hstrict
  change _root_.GD.N0232.N0720.N1135.d018324 s ↔
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
  rw [_root_.GD.N0232.N0720.N1135.d018328,
    _root_.GD.N0232.N0720.N1082.d015401]






theorem d019499
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1457.d019488 m n c ↔
      _root_.GD.N0232.N0720.N1457.d019491 m n c := by
  let s := _root_.GD.N0232.N0720.N1457.d019493 m n hm hn c hstrict
  constructor
  · intro hsmall B ε hε
    have hfamily : _root_.GD.N0232.N0720.N1109.d018402 (fun _ : Unit ↦ s) := by
      intro η hη
      obtain ⟨candidate, hcandidate⟩ := hsmall η hη
      exact ⟨(), candidate, by simpa only [s,
        _root_.GD.N0232.N0720.N1457.d019494] using hcandidate⟩
    obtain ⟨_index, candidate, hlocation, hcalibration⟩ :=
      _root_.GD.N0232.N0720.N1451.d019347
        hm hn (fun _ : Unit ↦ s) s.value
          (fun _ ↦ _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
          hfamily B ε hε
    exact ⟨candidate, hlocation, by simpa only [s,
      _root_.GD.N0232.N0720.N1457.d019494] using hcalibration⟩
  · intro hescaping ε hε
    obtain ⟨candidate, _hlocation, hcalibration⟩ :=
      hescaping 0 ε hε
    exact ⟨candidate, hcalibration⟩








theorem d019500
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    (∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0232.N0720.N1468.d018953 m n e c.d019473) ↔
      _root_.GD.N0232.N0720.N1457.d019489 m n c := by
  let s := _root_.GD.N0232.N0720.N1457.d019493 m n hm hn c hstrict
  constructor
  · intro hdominator
    by_contra hnoFloor
    have hsmall : _root_.GD.N0232.N0720.N1457.d019488 m n c :=
      (_root_.GD.N0232.N0720.N1457.d019492 m n c).1
        hnoFloor
    have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
      exact (_root_.GD.N0232.N0720.N1457.d019498
        m n hm hn c hstrict).1 hsmall
    have hadmissible : _root_.GD.N0232.N0720.N1468.d018954 m n s.value :=
      (_root_.GD.N0232.N0720.N1468.d018965 m n s).2
        hterminal
    exact hadmissible hdominator
  · intro hfloor
    by_contra hnoDominator
    have hadmissible : _root_.GD.N0232.N0720.N1468.d018954 m n s.value := hnoDominator
    have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value :=
      (_root_.GD.N0232.N0720.N1468.d018965 m n s).1
        hadmissible
    have hsmall : _root_.GD.N0232.N0720.N1457.d019488 m n c :=
      (_root_.GD.N0232.N0720.N1457.d019498
        m n hm hn c hstrict).2 hterminal
    have hnoFloor : _root_.GD.N0232.N0720.N1457.d019490 m n c :=
      (_root_.GD.N0232.N0720.N1457.d019492 m n c).2 hsmall
    exact hnoFloor hfloor




theorem d019501
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    (∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0232.N0720.N1468.d018953 m n e c.d019473) ↔
      0 < _root_.GD.N0232.N0720.N1457.d019495 m n c := by
  rw [_root_.GD.N0232.N0720.N1457.d019500
      m n hm hn c hstrict,
    _root_.GD.N0232.N0720.N1457.d019497
      m n hm hn c hstrict]






theorem d019502
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
        (∀ (ρ : ℝ) (hρ : 0 < ρ),
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) ∧
        _root_.GD.N0232.N0720.N1457.d019488 m n c := by
  rw [_root_.GD.N0232.N0720.N1455.d019485
    m n hm hn]
  apply exists_congr
  intro c
  unfold _root_.GD.N0232.N0720.N1455.d019483
  apply and_congr_right
  intro hstrict
  rw [_root_.GD.N0232.N0720.N1457.d019498
    m n hm hn c hstrict]
  let s := _root_.GD.N0232.N0720.N1457.d019493 m n hm hn c hstrict
  change (¬ ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0232.N0720.N1468.d018953 m n e s.value) ↔
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
  exact _root_.GD.N0232.N0720.N1468.d018965 m n s



theorem d019503
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
        (∀ (ρ : ℝ) (hρ : 0 < ρ),
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) ∧
        _root_.GD.N0232.N0720.N1457.d019490 m n c := by
  rw [_root_.GD.N0232.N0720.N1457.d019502
    m n hm hn]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  exact (_root_.GD.N0232.N0720.N1457.d019492 m n c).symm



theorem d019504
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
        (∀ (ρ : ℝ) (hρ : 0 < ρ),
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) ∧
        _root_.GD.N0232.N0720.N1457.d019491 m n c := by
  rw [_root_.GD.N0232.N0720.N1457.d019502
    m n hm hn]
  apply exists_congr
  intro c
  apply and_congr_right
  intro hstrict
  exact _root_.GD.N0232.N0720.N1457.d019499
    m n hm hn c hstrict




theorem d019505
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (¬ _root_.GD.N0232.N0720.N1159.d014661 m n) ↔
      ∀ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
        (∀ (ρ : ℝ) (hρ : 0 < ρ),
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) →
        _root_.GD.N0232.N0720.N1457.d019489 m n c := by
  rw [_root_.GD.N0232.N0720.N1457.d019503
    m n hm hn]
  unfold _root_.GD.N0232.N0720.N1457.d019490
  push Not
  rfl




theorem d019506
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n)
    (hstrict : ∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 < _root_.GD.N0232.N0720.N1131.d017154 m n candidate c.d019473 := by
  let s := _root_.GD.N0232.N0720.N1457.d019493 m n hm hn c hstrict
  simpa only [s, _root_.GD.N0232.N0720.N1457.d019494] using
    _root_.GD.N0232.N0720.N1135.d018323 s candidate

end

end N1457
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1457.d019492
#print axioms _root_.GD.N0232.N0720.N1457.d019496
#print axioms _root_.GD.N0232.N0720.N1457.d019497
#print axioms _root_.GD.N0232.N0720.N1457.d019498
#print axioms _root_.GD.N0232.N0720.N1457.d019499
#print axioms _root_.GD.N0232.N0720.N1457.d019500
#print axioms _root_.GD.N0232.N0720.N1457.d019501
#print axioms _root_.GD.N0232.N0720.N1457.d019502
#print axioms _root_.GD.N0232.N0720.N1457.d019503
#print axioms _root_.GD.N0232.N0720.N1457.d019504
#print axioms _root_.GD.N0232.N0720.N1457.d019505
#print axioms _root_.GD.N0232.N0720.N1457.d019506
