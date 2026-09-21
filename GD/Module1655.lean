import GD.Module1443
import GD.Module1634

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0098
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1256


theorem d028155 (m n : ℕ) (hm : 2 ≤ m) (hn : 6 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≤ ENNReal.ofReal (6 * _root_.GD.N0090.d027947 ![m, n, 6]) := by
  let sizes : Fin 3 → ℕ := ![m, n, 6]
  have hs : ∀ i, 2 ≤ sizes i := by
    intro i
    fin_cases i
    · change 2 ≤ m; exact hm
    · change 2 ≤ n; omega
    · change 2 ≤ 6; decide
  have hh := _root_.GD.N0036.d022918 sizes hs 0 1 (by decide)
  have hb := _root_.GD.N0090.d027950 sizes hm hn (by change 6 ≤ 6; decide)
  exact hh.trans hb

theorem d028156 (m n : ℕ) (hm : 2 ≤ m) (hn : 6 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0098.d028155 m n hm hn)


theorem d028157 (m n : ℕ) (hm : 6 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≤ ENNReal.ofReal (6 * _root_.GD.N0090.d027947 ![n, m, 6]) := by
  let sizes : Fin 3 → ℕ := ![n, m, 6]
  have hs : ∀ i, 2 ≤ sizes i := by
    intro i
    fin_cases i
    · change 2 ≤ n; exact hn
    · change 2 ≤ m; omega
    · change 2 ≤ 6; decide
  have hh := _root_.GD.N0036.d022918 sizes hs 1 0 (by decide)
  have hb := _root_.GD.N0090.d027950 sizes hn hm (by change 6 ≤ 6; decide)
  exact hh.trans hb

theorem d028158 (m n : ℕ) (hm : 6 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0098.d028157 m n hm hn)


theorem d028159 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hlarge : 6 ≤ m ∨ 6 ≤ n) : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ := by
  rcases hlarge with hm6 | hn6
  · exact _root_.GD.N0098.d028158 m n hm6 hn
  · exact _root_.GD.N0098.d028156 m n hm hn6

end
end GD.N0098

#print axioms _root_.GD.N0098.d028155
#print axioms _root_.GD.N0098.d028157
#print axioms _root_.GD.N0098.d028159
