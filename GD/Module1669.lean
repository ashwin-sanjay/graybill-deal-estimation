import GD.Module1667
import GD.Module0444

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0071
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0102.N0420
open _root_.GD.N0102.N0423
open _root_.GD.N0102.N0422
open _root_.GD.N0033.N0285

variable {k : ℕ}

theorem d028306 (sizes : Fin k → ℕ) (hn : ∀ i, 3 ≤ sizes i)
    (i : Fin k) : 1 ≤ _root_.GD.N0102.N0423.d028273 sizes i := by
  have h : 2 ≤ sizes i - 1 := by have := hn i; omega
  have hr : (2 : ℝ) ≤ (sizes i - 1 : ℕ) := by exact_mod_cast h
  unfold _root_.GD.N0102.N0423.d028273
  linarith



theorem d028307 (sizes : Fin k → ℕ)
    (hk : 0 < k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤
      ENNReal.ofReal (∑ i, _root_.GD.N0102.N0423.d028273 sizes i) := by
  apply _root_.GD.N0102.N0422.d028297 hk sizes
    (fun i => by have := hn i; omega)
  intro i a B ha hB
  exact _root_.GD.N0033.N0285.d006808 a B (_root_.GD.N0102.N0423.d028273 sizes i) ha hB
    (_root_.GD.N0071.d028306 sizes hn i)

theorem d028308 (sizes : Fin k → ℕ)
    (hk : 0 < k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (_root_.GD.N0071.d028307 sizes hk hn)


theorem d028309 (hk : 0 < k) :
    _root_.GD.N0232.N0719.N0962.d012187 k (fun _ => 3) (_root_.GD.N0232.N0719.N0900.d009111 k (fun _ => 3)) ≤
      ENNReal.ofReal (k : ℝ) := by
  simpa [_root_.GD.N0102.N0423.d028273] using
    _root_.GD.N0071.d028307 (fun _ : Fin k => 3) hk (by norm_num)

end
end GD.N0071

#print axioms _root_.GD.N0071.d028307
#print axioms _root_.GD.N0071.d028308
#print axioms _root_.GD.N0071.d028309
