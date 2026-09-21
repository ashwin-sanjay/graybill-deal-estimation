import GD.Module1711
import GD.Module1698




set_option autoImplicit false
set_option warningAsError true

namespace GD.N0101.N0388
noncomputable section

open _root_.GD.N0213.N0485
open _root_.GD.N0213.N0486


theorem d028675 :
    _root_.GD.N0213.N0485.d028566 (fun _ : Fin 2 => 2) :=
  _root_.GD.N0101.N0385.d028674



theorem d028676 (sizes : Fin 2 → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) : _root_.GD.N0213.N0485.d028566 sizes := by
  by_cases hlarge : 3 ≤ sizes 0 ∨ 3 ≤ sizes 1
  · exact _root_.GD.N0213.N0486.d028584 sizes hn hlarge
  · have h₀ := hn 0
    have h₁ := hn 1
    have hsizes : sizes = (fun _ : Fin 2 => 2) := by
      funext i
      fin_cases i <;> dsimp <;> omega
    rw [hsizes]
    exact _root_.GD.N0101.N0388.d028675

end
end GD.N0101.N0388

#print axioms _root_.GD.N0101.N0388.d028675
#print axioms _root_.GD.N0101.N0388.d028676
