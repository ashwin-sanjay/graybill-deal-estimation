import GD.Module1767
import GD.Module1764
import GD.Module1422
import GD.Module1421
import GD.Module1761
import GD.Module0364




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Topology
open scoped FourierTransform
namespace GD.N0106.N0428.N0765.N1589
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1602 _root_.GD.N0106.N0428.N0765.N1587 _root_.GD.N0106.N0428.N0765.N1586
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1592 _root_.GD.N0106.N0428.N0765.N1550

theorem d029318 (z : ℂ) : _root_.GD.N0106.N0428.N0765.N1537.d021524 z.re z.im = z := by
  exact Complex.re_add_im z

theorem d029319 (e b β s : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1550.d005474 (fun z => _root_.GD.N0106.N0428.N0765.N1586.d022740 e z (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β)) s =
      fun x => _root_.GD.N0106.N0428.N0765.N1537.d021532 e s β (x,b) := by
  funext x
  exact _root_.GD.N0106.N0428.N0765.N1586.d022745 e x b s β

theorem d029320 (e a α s : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1550.d005474 (fun z => _root_.GD.N0106.N0428.N0765.N1586.d022740 e (_root_.GD.N0106.N0428.N0765.N1537.d021524 a α) z) s =
      fun y => _root_.GD.N0106.N0428.N0765.N1537.d021532 e α s (a,y) := by
  funext y
  exact _root_.GD.N0106.N0428.N0765.N1586.d022745 e a y α s


theorem d029321 {e dA dB β : ℝ} (he : 0 ≤ e)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ)/2)*(dA+dB) < Real.pi) (hβ : |β| ≤ dB) (b xi : ℝ) :
    ‖𝓕 (fun x => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 β (x,b)) xi‖ ≤
      Real.exp (-2*Real.pi*dA*|xi|) *
        ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e (if 0 ≤ xi then -dA else dA) β (x,b)‖ := by
  obtain ⟨K, _, hK⟩ := _root_.GD.N0106.N0428.N0765.N1602.d029274 hdA hdB hd
  have hphase : ∀ s : ℝ, |s| ≤ dA → ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 s β < Real.pi := by
    intro s hs; unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; nlinarith
  have hf : ∀ z : ℂ, |z.im| ≤ dA →
      DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1586.d022740 e q (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β)) z := by
    intro z hz
    exact _root_.GD.N0106.N0428.N0765.N1586.d022744 true he (by
      change ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 z.im (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β).im < Real.pi
      simpa only [_root_.GD.N0106.N0428.N0765.N1537.d021526] using hphase z.im hz)
  have hint : ∀ s : ℝ, |s| ≤ dA →
      Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (fun q => _root_.GD.N0106.N0428.N0765.N1586.d022740 e q (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β)) s) := by
    intro s hs; rw [_root_.GD.N0106.N0428.N0765.N1589.d029319]
    exact _root_.GD.N0106.N0428.N0765.N1602.d029277 he (hphase s hs) b
  have hbound : ∀ z : ℂ, |z.im| ≤ dA →
      ‖_root_.GD.N0106.N0428.N0765.N1586.d022740 e z (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β)‖ ≤ K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 z.re * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 b := by
    intro z hz
    have h := hK e he z.im β hz hβ z.re b
    rw [← _root_.GD.N0106.N0428.N0765.N1586.d022745, _root_.GD.N0106.N0428.N0765.N1589.d029318] at h
    exact h
  have h := _root_.GD.N0106.N0428.N0765.N1550.d005490 (f := fun z => _root_.GD.N0106.N0428.N0765.N1586.d022740 e z (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β))
    (AL := K * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 b) (AR := K * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 b)
    hdA hf (hint 0 (by simpa using hdA))
    (hint (-dA) (by simp only [abs_neg, abs_of_nonneg hdA, le_refl]))
    (hint dA (by simp only [abs_of_nonneg hdA, le_refl]))
    (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (0 : ℝ) < 10)
    (by
      intro z hz hx
      simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx, mul_assoc, mul_left_comm, mul_comm] using hbound z hz)
    (by
      intro z hz hx
      by_cases heq : z.re = 0
      · simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, heq, le_refl, if_true, mul_zero, Real.exp_zero, mul_one] using hbound z hz
      · have hp : ¬ z.re ≤ 0 := not_le.mpr (lt_of_le_of_ne hx (Ne.symm heq))
        simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg hp, mul_assoc, mul_left_comm, mul_comm] using hbound z hz) xi
  simpa only [_root_.GD.N0106.N0428.N0765.N1589.d029319] using h


theorem d029322 {e dA dB α : ℝ} (he : 0 ≤ e)
    (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ)/2)*(dA+dB) < Real.pi) (hα : |α| ≤ dA) (a xi : ℝ) :
    ‖𝓕 (fun y => _root_.GD.N0106.N0428.N0765.N1537.d021532 e α 0 (a,y)) xi‖ ≤
      Real.exp (-2*Real.pi*dB*|xi|) *
        ∫ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α (if 0 ≤ xi then -dB else dB) (a,y)‖ := by
  obtain ⟨K, _, hK⟩ := _root_.GD.N0106.N0428.N0765.N1602.d029274 hdA hdB hd
  have hphase : ∀ s : ℝ, |s| ≤ dB → ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 α s < Real.pi := by
    intro s hs; unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; nlinarith
  have hf : ∀ z : ℂ, |z.im| ≤ dB →
      DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1586.d022740 e (_root_.GD.N0106.N0428.N0765.N1537.d021524 a α) q) z := by
    intro z hz
    exact _root_.GD.N0106.N0428.N0765.N1586.d022744 false he (by
      change ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 (_root_.GD.N0106.N0428.N0765.N1537.d021524 a α).im z.im < Real.pi
      simpa only [_root_.GD.N0106.N0428.N0765.N1537.d021526] using hphase z.im hz)
  have hint : ∀ s : ℝ, |s| ≤ dB →
      Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (fun q => _root_.GD.N0106.N0428.N0765.N1586.d022740 e (_root_.GD.N0106.N0428.N0765.N1537.d021524 a α) q) s) := by
    intro s hs; rw [_root_.GD.N0106.N0428.N0765.N1589.d029320]
    exact _root_.GD.N0106.N0428.N0765.N1602.d029278 he (hphase s hs) a
  have hbound : ∀ z : ℂ, |z.im| ≤ dB →
      ‖_root_.GD.N0106.N0428.N0765.N1586.d022740 e (_root_.GD.N0106.N0428.N0765.N1537.d021524 a α) z‖ ≤ K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 a * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 z.re := by
    intro z hz
    have h := hK e he α z.im hα hz a z.re
    rw [← _root_.GD.N0106.N0428.N0765.N1586.d022745, _root_.GD.N0106.N0428.N0765.N1589.d029318] at h
    exact h
  have h := _root_.GD.N0106.N0428.N0765.N1550.d005490 (f := fun z => _root_.GD.N0106.N0428.N0765.N1586.d022740 e (_root_.GD.N0106.N0428.N0765.N1537.d021524 a α) z)
    (AL := K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 a) (AR := K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 a)
    hdB hf (hint 0 (by simpa using hdB))
    (hint (-dB) (by simp only [abs_neg, abs_of_nonneg hdB, le_refl]))
    (hint dB (by simp only [abs_of_nonneg hdB, le_refl]))
    (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 3)
    (by intro z hz hx; simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx] using hbound z hz)
    (by
      intro z hz hx
      by_cases heq : z.re = 0
      · simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, heq, le_refl, if_true, mul_zero, Real.exp_zero, mul_one] using hbound z hz
      · have hp : ¬ z.re ≤ 0 := not_le.mpr (lt_of_le_of_ne hx (Ne.symm heq))
        simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg hp] using hbound z hz) xi
  simpa only [_root_.GD.N0106.N0428.N0765.N1589.d029320] using h

end
end GD.N0106.N0428.N0765.N1589
#print axioms _root_.GD.N0106.N0428.N0765.N1589.d029321
#print axioms _root_.GD.N0106.N0428.N0765.N1589.d029322
