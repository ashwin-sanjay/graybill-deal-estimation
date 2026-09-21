import GD.Module1463
import GD.Module1902















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0184
noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0611
open _root_.GD.N0149.N0432
open _root_.GD.N0185


theorem d030934
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d) :
    ENNReal.ofReal (1 + Real.pi / 4) ≤ _root_.GD.N0232.N0720.N1256.d015548 3 3 d := by
  by_cases htop : _root_.GD.N0232.N0720.N1256.d015548 3 3 d = ⊤
  · rw [htop]
    exact le_top
  let C : ℝ := (_root_.GD.N0232.N0720.N1256.d015548 3 3 d).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hvalue : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015548 3 3 d :=
    ENNReal.ofReal_toReal htop
  have hcap (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 3 3 theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 3 3 theta) := by
    apply (_root_.GD.N0232.N0720.N1256.d015553 3 3 (by norm_num) C hC theta d).mp
    rw [hvalue]
    exact le_iSup (fun eta => _root_.GD.N0232.N0720.N1256.d015547 3 3 eta d) theta
  have hlower := _root_.GD.N0185.d023077 C hC d hd hcap
  rw [← hvalue]
  exact ENNReal.ofReal_le_ofReal hlower


theorem d030935 :
    ENNReal.ofReal (1 + Real.pi / 4) ≤ _root_.GD.N0232.N0720.N1256.d015549 3 3 := by
  unfold _root_.GD.N0232.N0720.N1256.d015549 _root_.GD.N0230.N0611.d003517
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact _root_.GD.N0184.d030934 d hd


theorem d030936 :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 = ENNReal.ofReal (1 + Real.pi / 4) :=
  le_antisymm _root_.GD.N0010.d030855
    _root_.GD.N0184.d030935



theorem d030937 :
    _root_.GD.N0149.N0432.d030808 ∈ _root_.GD.N0232.N0720.N1256.d015551 3 3 ∧
      _root_.GD.N0232.N0720.N1256.d015548 3 3 _root_.GD.N0149.N0432.d030808 = _root_.GD.N0232.N0720.N1256.d015549 3 3 ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1256.d015547 3 3 theta _root_.GD.N0149.N0432.d030808 < _root_.GD.N0232.N0720.N1256.d015549 3 3 := by
  refine ⟨_root_.GD.N0149.N0432.d030809, ?_, ?_⟩
  · rw [_root_.GD.N0184.d030936]
    exact _root_.GD.N0010.d030853
  · intro theta
    rw [_root_.GD.N0184.d030936]
    exact _root_.GD.N0010.d030852 theta


theorem d030938 :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 3 3) (_root_.GD.N0232.N0720.N1256.d015551 3 3) =
      ENNReal.ofReal (1 + Real.pi / 4) := by
  rw [← _root_.GD.N0232.N0720.N1256.d015559 3 3 (by norm_num)]
  exact _root_.GD.N0184.d030936


theorem d030939 :
    _root_.GD.N0232.N0720.N1256.d015550 3 3 = ENNReal.ofReal (1 + Real.pi / 4) := by
  rw [← _root_.GD.N0232.N0720.N1256.d015555 3 3 (by norm_num) (by norm_num)]
  exact _root_.GD.N0184.d030936


theorem d030940 :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 3 3) (_root_.GD.N0232.N0720.N1256.d015552 3 3) =
      ENNReal.ofReal (1 + Real.pi / 4) := by
  rw [← _root_.GD.N0232.N0720.N1256.d015560 3 3 (by norm_num) (by norm_num)]
  exact _root_.GD.N0184.d030938

end
end GD.N0184

#print axioms _root_.GD.N0184.d030934
#print axioms _root_.GD.N0184.d030935
#print axioms _root_.GD.N0184.d030936
#print axioms _root_.GD.N0184.d030937
#print axioms _root_.GD.N0184.d030938
#print axioms _root_.GD.N0184.d030939
#print axioms _root_.GD.N0184.d030940
