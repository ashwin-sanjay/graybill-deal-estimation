import GD.Module1889
import GD.Module1886
import GD.Module0562

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal

namespace GD.N0082.N0328

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1066 _root_.GD.N0232.N0720.N1069
open _root_.GD.N0076.N0313
open _root_.GD.N0082.N0335 _root_.GD.N0082.N0336 _root_.GD.N0082.N0334

theorem d030760 :
    ∃ (J : ℕ) (f : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ), 1 ≤ J ∧
      f ∈ _root_.GD.N0232.N0720.N1256.d015552 3 3 ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ f ≤
        ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ := by
  apply _root_.GD.N0082.N0329.d030735 3 3 (by omega) (by omega)
    (_root_.GD.N0232.N0720.N1080.d014176 3 3 (by omega) (by omega)) _root_.GD.N0082.N0336.d030751
    (_root_.GD.N0232.N0720.N1221.d015562
      3 3 (by omega) (by omega))
    (_root_.GD.N0082.N0329.d030732 3 3 (by omega) (by omega)
      _root_.GD.N0082.N0335.d030714 _root_.GD.N0082.N0335.d030717 _root_.GD.N0082.N0335.d030715)
    (_root_.GD.N0232.N0720.N1069.d014352 3 3) (fun θ => _root_.GD.N0082.N0336.d030742 θ)
    (_root_.GD.N0082.N0335.d030720 3 3 (by omega) (by omega)) _root_.GD.N0082.N0334.d008259
    (fun t _ => _root_.GD.N0082.N0333.d030739 3 3 (by omega) (by omega) t)
    (fun t _ => _root_.GD.N0082.N0336.d030754 t)
    (_root_.GD.N0082.N0335.d030721 3 3 (by omega) (by omega))
    (_root_.GD.N0082.N0335.d030722 3 3 (by omega) (by omega))
    _root_.GD.N0082.N0334.d008269 (by rw [_root_.GD.N0082.N0334.d008274]; norm_num) (by rw [_root_.GD.N0082.N0334.d008279]; norm_num)
    (fun θ => (_root_.GD.N0082.N0333.d030738
      3 3 (by omega) (by omega) θ).le)
    (fun θ => (_root_.GD.N0082.N0336.d030753 θ).le)

theorem d030761 :
    (¬ _root_.GD.N0082.d030602 3 3 (by omega) (by omega)) ∧
    _root_.GD.N0076.N0313.d030569 3 3 (by omega) (by omega) < 1 ∧
    (∃ (J : ℕ) (f : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ), 1 ≤ J ∧
      f ∈ _root_.GD.N0232.N0720.N1256.d015552 3 3 ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ f ≤
        ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ) ∧
    ContinuousOn _root_.GD.N0082.N0334.d008259 (Icc (0 : ℝ) 1) ∧
      _root_.GD.N0082.N0334.d008259 0 = (9 / 10 : ℝ) ∧ _root_.GD.N0082.N0334.d008259 1 = (9 / 10 : ℝ) ∧
      _root_.GD.N0082.N0334.d008259 (1 / 2) = (39 / 35 : ℝ) :=
  ⟨_root_.GD.N0082.N0330.d030756, _root_.GD.N0082.N0330.d030757,
    _root_.GD.N0082.N0328.d030760, _root_.GD.N0082.N0334.d008269, _root_.GD.N0082.N0334.d008274, _root_.GD.N0082.N0334.d008279, _root_.GD.N0082.N0334.d008340⟩

end
end GD.N0082.N0328

#print axioms _root_.GD.N0082.N0328.d030760
#print axioms _root_.GD.N0082.N0328.d030761
