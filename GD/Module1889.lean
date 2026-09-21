import GD.Module1888
import GD.Module1887
import GD.Module1868

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0082.N0330

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0076.N0313
open _root_.GD.N0082.N0336 _root_.GD.N0082.N0334

theorem d030755 : _root_.GD.N0082.d030603 3 3 (by omega) (by omega) := by
  apply _root_.GD.N0082.N0333.d030740 3 3 (by omega) (by omega)
    _root_.GD.N0082.N0336.d030751 _root_.GD.N0082.N0336.d030752 _root_.GD.N0082.N0334.d008259
    (fun t _ => _root_.GD.N0082.N0336.d030754 t) _root_.GD.N0082.N0334.d008269
    (by rw [_root_.GD.N0082.N0334.d008274]; norm_num) (by rw [_root_.GD.N0082.N0334.d008279]; norm_num)
  intro θ
  exact (_root_.GD.N0082.N0336.d030753 θ).le

theorem d030756 : ¬ _root_.GD.N0082.d030602 3 3 (by omega) (by omega) :=
  (_root_.GD.N0082.d030610 3 3 (by omega) (by omega)).mpr _root_.GD.N0082.N0330.d030755

theorem d030757 : _root_.GD.N0076.N0313.d030569 3 3 (by omega) (by omega) < 1 :=
  (_root_.GD.N0082.d030609 3 3 (by omega) (by omega)).mp _root_.GD.N0082.N0330.d030755

theorem d030758 :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168)
        (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) →
          _root_.GD.N0082.N0332.d030616 3 3 (by omega) (by omega) F w ≤ 1 - ε := by
  have hv : (_root_.GD.N0076.N0313.d030569 3 3 (by omega) (by omega)).toReal < 1 :=
    ENNReal.toReal_lt_of_lt_ofReal (by simpa using _root_.GD.N0082.N0330.d030757)
  refine ⟨1 - (_root_.GD.N0076.N0313.d030569 3 3 (by omega) (by omega)).toReal, sub_pos.mpr hv, ?_⟩
  intro F w hw
  simpa using _root_.GD.N0082.N0332.d030625 3 3 (by omega) (by omega) F w hw

theorem d030759 :
    (¬ _root_.GD.N0082.d030602 3 3 (by omega) (by omega)) ∧
    _root_.GD.N0082.d030603 3 3 (by omega) (by omega) ∧
    _root_.GD.N0076.N0313.d030569 3 3 (by omega) (by omega) < 1 ∧
    _root_.GD.N0076.N0313.d030569 3 3 (by omega) (by omega) =
      _root_.GD.N0082.N0332.d030623 3 3 (by omega) (by omega) :=
  ⟨_root_.GD.N0082.N0330.d030756, _root_.GD.N0082.N0330.d030755, _root_.GD.N0082.N0330.d030757,
    _root_.GD.N0082.N0332.d030624 3 3 (by omega) (by omega)⟩

end
end GD.N0082.N0330

#print axioms _root_.GD.N0082.N0330.d030755
#print axioms _root_.GD.N0082.N0330.d030756
#print axioms _root_.GD.N0082.N0330.d030758
#print axioms _root_.GD.N0082.N0330.d030759
