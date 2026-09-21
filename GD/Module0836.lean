import GD.Module0612
import GD.Module0835



















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1207

noncomputable section

open _root_.GD.N0141
open _root_.GD.N0120
open _root_.GD.N0137
open _root_.GD.N0107

variable {Omega : Type*} [MeasurableSpace Omega]





theorem d012750
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    (∫ omega,
        _root_.GD.N0137.d008945 m n e Sigma omega *
          (_root_.GD.N0137.d008942 m n e Sigma omega *
            (_root_.GD.N0137.d008943 m n e omega - e))
      ∂_root_.GD.N0137.d008914 m n) = 0 := by
  have hIndepDLF :=
    _root_.GD.N0137.d008947 m n hm hn
      (Sigma := Sigma) he0.le he1.le
  have hIndepWeight :
      IndepFun (_root_.GD.N0137.d008945 m n e Sigma)
        (fun omega =>
          _root_.GD.N0137.d008942 m n e Sigma omega *
            (_root_.GD.N0137.d008943 m n e omega - e))
        (_root_.GD.N0137.d008914 m n) := by
    have h := hIndepDLF.comp measurable_id
      (show Measurable
        (fun p : ℝ × (ℝ × ℝ) => p.1 * (p.2.1 - e)) by fun_prop)
    simpa [Function.comp_def] using h
  exact _root_.GD.N0141.d006692
    hIndepWeight
    (_root_.GD.N0107.d012744
      m n hm hn he0.le he1.le).aestronglyMeasurable
    (_root_.GD.N0119.d009080
      m n hm hn he0 he1 (Sigma := Sigma)).aestronglyMeasurable
    (_root_.GD.N0137.d008948
      m n hm hn he0.le he1.le)







theorem d012751
    {P : Measure Omega} [IsProbabilityMeasure P]
    {U D L : Omega -> Real} {e : Real}
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun omega => D omega * (L omega - e)) 2 P)
    (hOrthogonality :
      (∫ omega, U omega * (D omega * (L omega - e)) ∂P) = 0) :
    _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) - _root_.GD.N0141.d006684 P U =
      ∫ omega, D omega ^ 2 * (L omega - e) ^ 2 ∂P := by
  have hBase : MemLp (_root_.GD.N0141.d006685 U D L e) 2 P := by
    have h := hU.add hWeight
    apply (memLp_congr_ae ?_).2 h
    filter_upwards [] with omega
    rfl
  have hCross : Integrable
      (fun omega => U omega * (D omega * (L omega - e))) P :=
    MemLp.integrable_mul (p := 2) (q := 2) hU hWeight
  have hRegret : Integrable
      (fun omega => D omega ^ 2 * (L omega - e) ^ 2) P := by
    have hsquare := hWeight.integrable_sq
    apply hsquare.congr
    filter_upwards [] with omega
    ring
  rw [_root_.GD.N0141.d006684, _root_.GD.N0141.d006684,
    <- integral_sub hBase.integrable_sq hU.integrable_sq]
  have hpointwise :
      (fun omega =>
          _root_.GD.N0141.d006685 U D L e omega ^ 2 - U omega ^ 2) =
        (fun omega =>
          2 * (U omega * (D omega * (L omega - e))) +
            D omega ^ 2 * (L omega - e) ^ 2) := by
    funext omega
    unfold _root_.GD.N0141.d006685
    ring
  rw [hpointwise, integral_add (hCross.const_mul 2) hRegret,
    integral_const_mul, hOrthogonality]
  ring




theorem d012752
    {P : Measure Omega}
    {D L F : Omega -> Real}
    {alpha beta e Sigma : Real}
    (hLaw : _root_.GD.N0125.d008847
      P D L F alpha beta e Sigma) :
    (∫ omega, D omega ^ 2 * (L omega - e) ^ 2 ∂P) =
      Sigma * _root_.GD.N0120.d008809 alpha beta e
        (fun p : Real × Real => (p.1 - e) ^ 2) := by
  simpa using hLaw
    (fun p : Real × Real => (p.1 - e) ^ 2) (by fun_prop)



theorem d012753
    {P : Measure Omega} [IsProbabilityMeasure P]
    {U D L F : Omega -> Real}
    {alpha beta e Sigma : Real}
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun omega => D omega * (L omega - e)) 2 P)
    (hOrthogonality :
      (∫ omega, U omega * (D omega * (L omega - e)) ∂P) = 0)
    (hLaw : _root_.GD.N0125.d008847
      P D L F alpha beta e Sigma) :
    _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) - _root_.GD.N0141.d006684 P U =
      Sigma * _root_.GD.N0120.d008809 alpha beta e
        (fun p : Real × Real => (p.1 - e) ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1207.d012751 hU hWeight hOrthogonality]
  exact _root_.GD.N0232.N0720.N1207.d012752 hLaw

#print axioms _root_.GD.N0232.N0720.N1207.d012750
#print axioms _root_.GD.N0232.N0720.N1207.d012751
#print axioms _root_.GD.N0232.N0720.N1207.d012752
#print axioms _root_.GD.N0232.N0720.N1207.d012753

end

end N1207
end N0720
end N0232
end GD
