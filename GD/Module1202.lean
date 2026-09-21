import GD.Module1164
import GD.Module1178
import GD.Module1201






















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1471

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1086
open _root_.GD.N0232.N0720.N1047
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1106
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1501

variable (m n : ℕ)



def d019425
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) s.value <
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)



def d019426
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    _root_.GD.N0232.N0720.N1468.d018955 m n e ∧ _root_.GD.N0232.N0720.N1468.d018953 m n e s.value



def d019427 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), _root_.GD.N0232.N0720.N1468.d018953 m n e s.value



def d019428
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1471.d019425 m n hm hn s →
      _root_.GD.N0232.N0720.N1468.d018955 m n s.value →
        _root_.GD.N0232.N0720.N1471.d019426 m n s



def d019429
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1471.d019425 m n hm hn s → _root_.GD.N0232.N0720.N1471.d019427 m n s



def d019430
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1086.d019414 m n) : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) s.value <
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)


def d019431 (s : _root_.GD.N0232.N0720.N1086.d019414 m n) : Prop :=
  ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), _root_.GD.N0232.N0720.N1468.d018953 m n e s.value



def d019432
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1086.d019414 m n,
    _root_.GD.N0232.N0720.N1471.d019430 m n hm hn s →
      _root_.GD.N0232.N0720.N1471.d019431 m n s




def N1760.d019433
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1086.d019414 m n)
    (hstrict : _root_.GD.N0232.N0720.N1471.d019430 m n hm hn s) :
    _root_.GD.N0232.N0720.N1159.d014639 m n where
  value := s.value
  finiteRisk := by
    have hall : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
        (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
      (_root_.GD.N0232.N0720.N1106.d018689 m n s.value
        (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) s.riskCharacter
        (_root_.GD.N0232.N0720.N1047.d018647 m n hm hn)).2 hstrict
    exact fun theta ↦ ne_top_of_lt (hall theta)
  riskCharacter := s.riskCharacter




theorem d019434
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1471.d019426 m n s ↔ _root_.GD.N0232.N0720.N1471.d019427 m n s := by
  unfold _root_.GD.N0232.N0720.N1471.d019426 _root_.GD.N0232.N0720.N1471.d019427
  exact (_root_.GD.N0232.N0720.N1468.d018960 m n hm hn s.value).symm





theorem d019435
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hno : ¬ _root_.GD.N0232.N0720.N1471.d019426 m n s) :
    _root_.GD.N0232.N0720.N1468.d018955 m n s.value := by
  by_contra hnot
  apply hno
  exact ⟨_root_.GD.N0232.N0720.N1501.d016291 m n s.value,
    _root_.GD.N0232.N0720.N1468.d018951 m n s.value,
    _root_.GD.N0232.N0720.N1468.d018962 m n hm hn s.value hnot⟩






theorem d019436
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1471.d019425 m n hm hn s ∧
          _root_.GD.N0232.N0720.N1468.d018955 m n s.value ∧
            ¬ _root_.GD.N0232.N0720.N1471.d019426 m n s := by
  rw [_root_.GD.N0232.N0720.N1106.d018691
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hterminal⟩
    obtain ⟨hsummary, hnodominator⟩ :=
      (_root_.GD.N0232.N0720.N1468.d018966
        m n hm hn s).1 hterminal
    exact ⟨s, hstrict, hsummary, by
      simpa only [_root_.GD.N0232.N0720.N1471.d019426] using hnodominator⟩
  · rintro ⟨s, hstrict, hsummary, hnodominator⟩
    refine ⟨s, hstrict, ?_⟩
    exact (_root_.GD.N0232.N0720.N1468.d018966
      m n hm hn s).2 ⟨hsummary, by
        simpa only [_root_.GD.N0232.N0720.N1471.d019426] using hnodominator⟩





theorem d019437
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ _root_.GD.N0232.N0720.N1471.d019428 m n hm hn := by
  rw [_root_.GD.N0232.N0720.N1471.d019436
    m n hm hn]
  unfold _root_.GD.N0232.N0720.N1471.d019428
  constructor
  · rintro ⟨s, hstrict, hsummary, hnodominator⟩ hall
    exact hnodominator (hall s hstrict hsummary)
  · intro hnot
    by_contra hnoCounterexample
    apply hnot
    intro s hstrict hsummary
    by_contra hnoDominator
    exact hnoCounterexample ⟨s, hstrict, hsummary, hnoDominator⟩






theorem d019438
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1471.d019425 m n hm hn s ∧ ¬ _root_.GD.N0232.N0720.N1471.d019427 m n s := by
  rw [_root_.GD.N0232.N0720.N1471.d019436
    m n hm hn]
  constructor
  · rintro ⟨s, hstrict, _hsummary, hno⟩
    exact ⟨s, hstrict,
      fun hdom ↦ hno ((_root_.GD.N0232.N0720.N1471.d019434
        m n hm hn s).2 hdom)⟩
  · rintro ⟨s, hstrict, hno⟩
    have hnoSummary : ¬ _root_.GD.N0232.N0720.N1471.d019426 m n s :=
      fun hdom ↦ hno ((_root_.GD.N0232.N0720.N1471.d019434
        m n hm hn s).1 hdom)
    exact ⟨s, hstrict,
      _root_.GD.N0232.N0720.N1471.d019435 m n hm hn s hnoSummary,
      hnoSummary⟩







theorem d019439
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ _root_.GD.N0232.N0720.N1471.d019429 m n hm hn := by
  rw [_root_.GD.N0232.N0720.N1471.d019438
    m n hm hn]
  unfold _root_.GD.N0232.N0720.N1471.d019429
  constructor
  · rintro ⟨s, hstrict, hno⟩ hall
    exact hno (hall s hstrict)
  · intro hnot
    by_contra hnoCounterexample
    apply hnot
    intro s hstrict
    by_contra hnoDominator
    exact hnoCounterexample ⟨s, hstrict, hnoDominator⟩





theorem d019440
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1086.d019414 m n,
        _root_.GD.N0232.N0720.N1471.d019430 m n hm hn s ∧
          ¬ _root_.GD.N0232.N0720.N1471.d019431 m n s := by
  rw [_root_.GD.N0232.N0720.N1471.d019438
    m n hm hn]
  constructor
  · rintro ⟨s, hstrict, hno⟩
    exact ⟨⟨s.value, s.riskCharacter⟩, hstrict, hno⟩
  · rintro ⟨s, hstrict, hno⟩
    let t := _root_.GD.N0232.N0720.N1471.N1760.d019433 m n hm hn s hstrict
    refine ⟨t, hstrict, ?_⟩
    exact hno








theorem d019441
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1086.d019414 m n)
    (hstrict : _root_.GD.N0232.N0720.N1471.d019430 m n hm hn s)
    (hno : ¬ _root_.GD.N0232.N0720.N1471.d019431 m n s) :
    _root_.GD.N0232.N0720.N1159.d014637 m n s.value ∧
      _root_.GD.N0232.N0720.N1468.d018955 m n s.value ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value ∧
          _root_.GD.N0232.N0720.N1159.d014652 m n s.value := by
  let t := _root_.GD.N0232.N0720.N1471.N1760.d019433 m n hm hn s hstrict
  have hadmissible : _root_.GD.N0232.N0720.N1468.d018954 m n t.value := by
    change ¬ ∃ e, _root_.GD.N0232.N0720.N1468.d018953 m n e t.value
    simpa only [t, _root_.GD.N0232.N0720.N1471.N1760.d019433,
      _root_.GD.N0232.N0720.N1471.d019431] using hno
  have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value :=
    (_root_.GD.N0232.N0720.N1468.d018965 m n t).1 hadmissible
  have hsummary : _root_.GD.N0232.N0720.N1468.d018955 m n t.value :=
    _root_.GD.N0232.N0720.N1468.d018963 m n hm hn hadmissible
  have hrepresentative : _root_.GD.N0232.N0720.N1159.d014652 m n t.value :=
    _root_.GD.N0232.N0720.N1409.d018607
      (m := m) (n := n) hm hn t hterminal
  exact ⟨t.finiteRisk, hsummary, hterminal, hrepresentative⟩







theorem d019442
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ _root_.GD.N0232.N0720.N1471.d019432 m n hm hn := by
  rw [_root_.GD.N0232.N0720.N1471.d019440
    m n hm hn]
  unfold _root_.GD.N0232.N0720.N1471.d019432
  constructor
  · rintro ⟨s, hstrict, hno⟩ hall
    exact hno (hall s hstrict)
  · intro hnot
    by_contra hnoCounterexample
    apply hnot
    intro s hstrict
    by_contra hnoDominator
    exact hnoCounterexample ⟨s, hstrict, hnoDominator⟩

end

end N1471
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1471.d019441
#print axioms _root_.GD.N0232.N0720.N1471.d019442
