import GD.Module1854
import GD.Module1855
import GD.Module1543

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0063
noncomputable section
open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0046.N0305

private theorem d030486 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hp : (m-1)*(n-1)=4) :
    (m=2  ∧  n=5)  ∨  (m=3  ∧  n=3)  ∨  (m=5  ∧  n=2) := by
  have hml : m-1 ≤ (m-1)*(n-1) := by
    calc
      m-1=(m-1)*1 := by omega
      _ ≤ (m-1)*(n-1) := Nat.mul_le_mul_left _ (by omega)
  have hnl : n-1 ≤ (m-1)*(n-1) := by
    calc
      n-1=1*(n-1) := by omega
      _ ≤ (m-1)*(n-1) := Nat.mul_le_mul_right _ (by omega)
  have hm5 : m ≤ 5 := by omega
  have hn5 : n ≤ 5 := by omega
  interval_cases m <;> omega

theorem d030487 : ¬_root_.GD.N0232.N0720.N1226.d015578 5 2 := by
  have hempty := _root_.GD.N0037.d030435 5 2 (by omega) (by omega)
    _root_.GD.N0029.d030442
  intro h
  obtain ⟨p,hp,_⟩ := (_root_.GD.N0046.N0305.d030214
    5 2 (by omega) (by omega)).mp h
  rw [hempty] at hp
  exact hp



theorem d030488
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1226.d015578 m n  ↔
      _root_.GD.N0232.N0720.N1256.d015549 m n=⊤  ∨  (m=3  ∧  n=3  ∧  _root_.GD.N0232.N0720.N1226.d015578 3 3) := by
  constructor
  · intro h
    by_cases ht : _root_.GD.N0232.N0720.N1256.d015549 m n=⊤
    · exact Or.inl ht
    · have hlow := (_root_.GD.N0067.d023923 m n hm hn).mp ht
      have hupp : (m-1)*(n-1) ≤ 4 := by
        by_contra hnot
        exact _root_.GD.N0037.d030438
          m n hm hn (by omega) h
      have heq : (m-1)*(n-1)=4 := by omega
      rcases _root_.GD.N0063.d030486 m n hm hn heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact False.elim (_root_.GD.N0029.d030444 h)
      · exact Or.inr ⟨rfl,rfl,h⟩
      · exact False.elim (_root_.GD.N0063.d030487 h)
  · rintro (ht | ⟨rfl,rfl,h⟩)
    · exact _root_.GD.N0232.N0720.N1226.d015586 m n hm hn ht
    · exact h


theorem d030489
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1226.d015578 m n  ↔
      (m=2  ∧  n ≤ 4)  ∨  (n=2  ∧  m ≤ 4)  ∨
        (m=3  ∧  n=3  ∧  _root_.GD.N0232.N0720.N1226.d015578 3 3) := by
  rw [_root_.GD.N0063.d030488 m n hm hn,
    _root_.GD.N0067.d023924 m n hm hn, or_assoc]


theorem d030490
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    _root_.GD.N0232.N0720.N1226.d015578 m n  ↔
      m=3  ∧  n=3  ∧  _root_.GD.N0232.N0720.N1226.d015578 3 3 := by
  rw [_root_.GD.N0063.d030488 m n hm hn,
    or_iff_right hfinite]

end
end GD.N0063

#print axioms _root_.GD.N0063.d030487
#print axioms _root_.GD.N0063.d030488
#print axioms _root_.GD.N0063.d030489
#print axioms _root_.GD.N0063.d030490
