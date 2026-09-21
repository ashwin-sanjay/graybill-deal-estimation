import GD.Module1656
import GD.Module1677

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0098
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1256


theorem d028729 (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≤ 2 := by
  let sizes : Fin 2 → ℕ := ![m, n]
  have hs : ∀ i, 3 ≤ sizes i := by
    intro i
    fin_cases i
    · change 3 ≤ m; exact hm
    · change 3 ≤ n; exact hn
  have hs2 : ∀ i, 2 ≤ sizes i := fun i => by have := hs i; omega
  have hh := _root_.GD.N0036.d022916 sizes hs2 0 0
    (_root_.GD.N0232.N0719.N0900.d009111 2 sizes)
    (_root_.GD.N0232.N0719.N0900.d009122 2 sizes)
  have hb := _root_.GD.N0070.d028368 (by decide : 0 < 2) sizes hs
  exact hh.trans (by simpa using hb)

theorem d028730 (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ :=
  ne_top_of_le_ne_top (by norm_num) (_root_.GD.N0098.d028729 m n hm hn)


theorem d028731 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤) :
    (m = 2 ∧ n ≤ 5) ∨ (n = 2 ∧ m ≤ 5) := by
  have hlarge : ¬ (6 ≤ m ∨ 6 ≤ n) := fun h => _root_.GD.N0098.d028159 m n hm hn h htop
  have hinterior : ¬ (3 ≤ m ∧ 3 ≤ n) :=
    fun h => _root_.GD.N0098.d028730 m n h.1 h.2 htop
  omega


theorem d028732 (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, _root_.GD.N0098.d028160 m n d ∧
      _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n ∧ _root_.GD.N0232.N0720.N1256.d015548 m n d ≤ 2 := by
  obtain ⟨d, hd, ht, hv⟩ := _root_.GD.N0098.d028161 m n (by omega) (by omega)
  refine ⟨d, hd, ht, hv, ?_⟩
  rw [hv]
  exact _root_.GD.N0098.d028729 m n hm hn

theorem d028733 (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015552 m n,
      _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n ∧ _root_.GD.N0232.N0720.N1256.d015548 m n d ≤ 2 := by
  obtain ⟨d, hd, hv⟩ := _root_.GD.N0232.N0720.N1222.d015570
    m n (by omega) (by omega)
  refine ⟨d, hd, hv, ?_⟩
  rw [hv]
  exact _root_.GD.N0098.d028729 m n hm hn



theorem d028734 :
    ¬ (∀ m n : ℕ, 2 ≤ m → 2 ≤ n → _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ →
      4 < (m - 1) * (n - 1)) := by
  intro h
  have hh := h 3 3 (by decide) (by decide)
    (_root_.GD.N0098.d028730 3 3 (by decide) (by decide))
  norm_num at hh

end
end GD.N0098

#print axioms _root_.GD.N0098.d028729
#print axioms _root_.GD.N0098.d028731
#print axioms _root_.GD.N0098.d028732
#print axioms _root_.GD.N0098.d028733
#print axioms _root_.GD.N0098.d028734
