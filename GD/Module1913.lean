import GD.Module1910
import GD.Module1900
import GD.Module0624



set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter
open scoped ENNReal Topology
open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0720.N1089
open _root_.GD.N0149.N0432 _root_.GD.N0149.N0433
open _root_.GD.N0082.N0334
open _root_.GD.N0082.N0335
open _root_.GD.N0082.N0336
open _root_.GD.N0200 _root_.GD.N0184

namespace GD.N0199
noncomputable section


theorem d030961 (g : ℝ → ℝ → ℝ)
    (shift dilation x y vx vy : ℝ) (hd : dilation ≠ 0) :
    _root_.GD.N0232.N0720.N1437.d003016 g (shift + dilation * x)
      (shift + dilation * y) (dilation ^ 2 * vx) (dilation ^ 2 * vy) =
      shift + dilation * _root_.GD.N0232.N0720.N1437.d003016 g x y vx vy := by
  have hstratum := _root_.GD.N0232.N0720.N1437.d003013 dilation vx vy hd
  by_cases h : _root_.GD.N0232.N0720.N1437.d003012 vx vy
  · simp only [_root_.GD.N0232.N0720.N1437.d003016, if_pos h,
      if_pos (hstratum.mpr h), _root_.GD.N0232.N0720.N1437.d002998]
    rw [_root_.GD.N0232.N0720.N1437.d003001 dilation vx vy hd,
      _root_.GD.N0232.N0720.N1437.d003002 shift dilation x y vx vy hd]
    ring
  · have h' : ¬ _root_.GD.N0232.N0720.N1437.d003012 (dilation ^ 2 * vx) (dilation ^ 2 * vy) :=
      fun hh => h (hstratum.mp hh)
    simp only [_root_.GD.N0232.N0720.N1437.d003016, if_neg h, if_neg h', _root_.GD.N0232.N0720.N1437.d003014]
    ring


theorem d030962 (shift dilation : ℝ) (hd : dilation ≠ 0)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 3 3) :
    _root_.GD.N0200.d030833 (_root_.GD.N0107.d009024 3 3 shift dilation dilation omega) =
      shift + dilation * _root_.GD.N0200.d030833 omega := by
  unfold _root_.GD.N0200.d030833 _root_.GD.N0107.d009024
  simp only [_root_.GD.N0232.N0719.N0900.d009135 (by norm_num : 0 < 3),
    _root_.GD.N0232.N0719.N0900.d009136 (by norm_num : 0 < 3),
    mul_div_assoc]
  exact _root_.GD.N0199.d030961 _ _ _ _ _ _ _ hd


theorem d030963 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 theta _root_.GD.N0200.d030833 =
      ENNReal.ofReal (1 + _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 (_root_.GD.N0082.N0336.d030741 theta)) := by
  rw [_root_.GD.N0200.d030843]
  exact _root_.GD.N0011.d030818
    _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282 _root_.GD.N0149.N0432.d008281 theta

theorem d030964 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 theta _root_.GD.N0200.d030833 <
      ENNReal.ofReal (1 + Real.pi / 4) := by
  rw [_root_.GD.N0200.d030843]
  exact _root_.GD.N0010.d030852 theta


theorem d030965 {X : Type*} {F : Filter X}
    (theta : X → _root_.GD.N0232.N0720.N1080.d014168) {b : ℝ} (hb : b = 0 ∨ b = 1)
    (htheta : Tendsto (fun x => _root_.GD.N0082.N0336.d030741 (theta x)) F (𝓝 b)) :
    Tendsto (fun x => _root_.GD.N0232.N0720.N1256.d015547 3 3 (theta x) _root_.GD.N0200.d030833)
      F (𝓝 (ENNReal.ofReal (1 + Real.pi / 4))) := by
  simpa only [_root_.GD.N0200.d030843] using
    _root_.GD.N0011.d030821 theta hb htheta

theorem d030966 :
    _root_.GD.N0232.N0720.N1256.d015548 3 3 _root_.GD.N0200.d030833 = ENNReal.ofReal (1 + Real.pi / 4) := by
  calc
    _ = _root_.GD.N0232.N0720.N1256.d015548 3 3 _root_.GD.N0149.N0432.d030808 := by
      unfold _root_.GD.N0232.N0720.N1256.d015548 _root_.GD.N0230.N0611.d003516
      exact iSup_congr (fun theta => _root_.GD.N0200.d030843 theta)
    _ = _ := _root_.GD.N0010.d030853

theorem d030967 :
    _root_.GD.N0200.d030833 ∈ _root_.GD.N0232.N0720.N1256.d015551 3 3 ∧
      _root_.GD.N0232.N0720.N1256.d015548 3 3 _root_.GD.N0200.d030833 = _root_.GD.N0232.N0720.N1256.d015549 3 3 := by
  exact ⟨_root_.GD.N0200.d030842, _root_.GD.N0199.d030966.trans
    _root_.GD.N0184.d030936.symm⟩

end
end GD.N0199

#print axioms _root_.GD.N0199.d030961
#print axioms _root_.GD.N0199.d030962
#print axioms _root_.GD.N0199.d030963
#print axioms _root_.GD.N0199.d030964
#print axioms _root_.GD.N0199.d030965
#print axioms _root_.GD.N0199.d030966
#print axioms _root_.GD.N0199.d030967
