import GD.Module1205
















namespace GD
namespace N0232
namespace N0720
namespace N1455

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1106
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1456
open _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1471


def d019483
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1456.d019472 m n) : Prop :=
  (∀ (ρ : ℝ) (hρ : 0 < ρ),
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) ∧
  ¬ ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), _root_.GD.N0232.N0720.N1468.d018953 m n e c.d019473



def d019484
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
    (∀ (ρ : ℝ) (hρ : 0 < ρ),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) c.d019473 <
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) →
      ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), _root_.GD.N0232.N0720.N1468.d018953 m n e c.d019473







theorem d019485
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ c : _root_.GD.N0232.N0720.N1456.d019472 m n,
        _root_.GD.N0232.N0720.N1455.d019483 m n hm hn c := by
  constructor
  · intro hendpoint
    obtain ⟨c, _hodd, hstrict, hno⟩ :=
      (_root_.GD.N0232.N0720.N1456.d019481
        m n hm hn).mp hendpoint
    exact ⟨c, hstrict, hno⟩
  · rintro ⟨c, hstrict, hno⟩
    apply (_root_.GD.N0232.N0720.N1471.d019440
      m n hm hn).mpr
    let s := c.d019477 m n (lt_of_lt_of_le (by omega) hm)
      (lt_of_lt_of_le (by omega) hn)
    exact ⟨s, hstrict, hno⟩





theorem d019486
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ _root_.GD.N0232.N0720.N1455.d019484
        m n hm hn := by
  rw [_root_.GD.N0232.N0720.N1455.d019485
    m n hm hn]
  unfold _root_.GD.N0232.N0720.N1455.d019484
    _root_.GD.N0232.N0720.N1455.d019483
  constructor
  · rintro ⟨c, hstrict, hno⟩ hall
    exact hno (hall c hstrict)
  · intro hnot
    by_contra hnone
    apply hnot
    intro c hstrict
    by_contra hnoDominator
    exact hnone ⟨c, hstrict, hnoDominator⟩




theorem d019487
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1455.d019484
        m n hm hn ↔
      _root_.GD.N0232.N0720.N1456.d019479 m n hm hn := by
  constructor
  · intro hall c _hodd hstrict
    exact hall c hstrict
  · intro hodd c hstrict
    by_contra hno
    have hendpoint : _root_.GD.N0232.N0720.N1159.d014661 m n :=
      (_root_.GD.N0232.N0720.N1455.d019485
        m n hm hn).mpr ⟨c, hstrict, hno⟩
    have hnodd :=
      (_root_.GD.N0232.N0720.N1456.d019482
        m n hm hn).mp hendpoint
    exact hnodd hodd

end
end N1455
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1455.d019485
#print axioms _root_.GD.N0232.N0720.N1455.d019486
#print axioms _root_.GD.N0232.N0720.N1455.d019487
