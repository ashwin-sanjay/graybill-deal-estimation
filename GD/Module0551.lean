import GD.Module0039









set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace GD.N0106.N0428.N0769.N1695

open _root_.GD.N0230.N0681



theorem d008174
    {Θ Ξ Rule : Type*} (risk : Θ → Rule → ℝ≥0∞) (inclusion : Ξ → Θ)
    {e d : Rule} (hstrict : ∀ θ, risk θ e < risk θ d) :
    ∀ ξ, risk (inclusion ξ) e < risk (inclusion ξ) d :=
  fun ξ => hstrict (inclusion ξ)


theorem d008175 :
    _root_.GD.N0230.N0681.d000487 false false = 0 ∧ _root_.GD.N0230.N0681.d000487 false true = 1 ∧
      _root_.GD.N0230.N0681.d000487 true false = 4 ∧ _root_.GD.N0230.N0681.d000487 true true = 1 := by
  norm_num [_root_.GD.N0230.N0681.d000487, _root_.GD.N0230.N0681.d000482]



theorem d008176 :
    _root_.GD.N0230.N0681.d000484 _root_.GD.N0230.N0681.d000487 false = 4 ∧ _root_.GD.N0230.N0681.d000484 _root_.GD.N0230.N0681.d000487 true = 1 ∧
      _root_.GD.N0230.N0681.d000484 (_root_.GD.N0230.N0681.d000472 _root_.GD.N0230.N0681.d000487 _root_.GD.N0230.N0681.d000488) false = 4 ∧
      _root_.GD.N0230.N0681.d000484 (_root_.GD.N0230.N0681.d000472 _root_.GD.N0230.N0681.d000487 _root_.GD.N0230.N0681.d000488) true = 9 := by
  norm_num [_root_.GD.N0230.N0681.d000484, _root_.GD.N0230.N0681.d000487, _root_.GD.N0230.N0681.d000482, _root_.GD.N0230.N0681.d000472, _root_.GD.N0230.N0681.d000488]



theorem d008177 :
    _root_.GD.N0230.N0681.d000495 false false = 0 ∧ _root_.GD.N0230.N0681.d000495 false true = 4 ∧
      _root_.GD.N0230.N0681.d000495 true false = 1 ∧ _root_.GD.N0230.N0681.d000495 true true = 1 := by
  norm_num [_root_.GD.N0230.N0681.d000495, _root_.GD.N0230.N0681.d000482]

end GD.N0106.N0428.N0769.N1695

#print axioms _root_.GD.N0106.N0428.N0769.N1695.d008174
#print axioms _root_.GD.N0106.N0428.N0769.N1695.d008175
#print axioms _root_.GD.N0106.N0428.N0769.N1695.d008176
#print axioms _root_.GD.N0106.N0428.N0769.N1695.d008177
