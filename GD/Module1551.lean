import GD.Module1262

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped Topology BigOperators

namespace GD.N0212.N0474
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0986 _root_.GD.N0232.N0719.N0982

noncomputable section
variable {k : ℕ}

theorem d023991 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (b a : ℝ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a z) i =
      b + a * _root_.GD.N0232.N0719.N0986.d020360 sizes z i := by
  have hi : (sizes i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn i).ne'
  simp only [_root_.GD.N0232.N0719.N0986.d020360, _root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018,
    Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, add_div]
  field_simp

theorem d023992 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (b a : ℝ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a z) i =
      a ^ 2 * _root_.GD.N0232.N0719.N0986.d020361 sizes z i := by
  unfold _root_.GD.N0232.N0719.N0986.d020361
  rw [_root_.GD.N0212.N0474.d023991 sizes hn b a z i]
  have hsq (j : Fin (sizes i)) :
      (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a z i j - (b + a * _root_.GD.N0232.N0719.N0986.d020360 sizes z i)) ^ 2 =
        a ^ 2 * (z i j - _root_.GD.N0232.N0719.N0986.d020360 sizes z i) ^ 2 := by
    unfold _root_.GD.N0232.N0719.N0900.d009095 _root_.GD.N0107.d009018
    ring
  simp_rw [hsq]
  rw [← Finset.mul_sum]
  ring

theorem d023993 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (b a : ℝ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) :
    _root_.GD.N0232.N0719.N0986.d020362 sizes (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a z) =
      (fun i => b + a * (_root_.GD.N0232.N0719.N0986.d020362 sizes z).1 i, fun i => a ^ 2 * (_root_.GD.N0232.N0719.N0986.d020362 sizes z).2 i) := by
  ext i
  · exact _root_.GD.N0212.N0474.d023991 sizes hn b a z i
  · exact _root_.GD.N0212.N0474.d023992 sizes hn b a z i

theorem d023994 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (b a : ℝ) (ha : 0 < a) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) :
    _root_.GD.N0232.N0719.N0986.d020362 sizes (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a z) ∈ _root_.GD.N0232.N0719.N0982.d020342 ↔
      _root_.GD.N0232.N0719.N0986.d020362 sizes z ∈ _root_.GD.N0232.N0719.N0982.d020342 := by
  rw [_root_.GD.N0212.N0474.d023993 sizes hn b a z]
  change (∀ i, 0 < a ^ 2 * (_root_.GD.N0232.N0719.N0986.d020362 sizes z).2 i) ↔ ∀ i, 0 < (_root_.GD.N0232.N0719.N0986.d020362 sizes z).2 i
  exact forall_congr' fun _ => mul_pos_iff_of_pos_left (sq_pos_of_pos ha)

end
end GD.N0212.N0474

#print axioms _root_.GD.N0212.N0474.d023993
#print axioms _root_.GD.N0212.N0474.d023994
