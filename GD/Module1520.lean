import GD.Module1376
import GD.Module0338
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set

namespace GD.N0062
noncomputable section
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441


theorem d023630 (S : Set ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f)
    (hi : Integrable f ((volume.restrict S).prod (volume.restrict (Ioi (0:ℝ))))) :
    Integrable (fun p : ℝ × ℝ => (2*p.2)*f (p.1,p.2^2))
      ((volume.restrict S).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hm : Measurable (fun p : ℝ × ℝ => (2*p.2)*f (p.1,p.2^2)) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hi.prod_right_ae] with u hu
    exact (_root_.GD.N0015.d005026 (fun s => f (u,s))).mpr hu
  · have heq (u : ℝ) :
        (∫ z in Ioi (0:ℝ), ‖(2*z)*f (u,z^2)‖) =
          ∫ s in Ioi (0:ℝ), ‖f (u,s)‖ := by
      conv_rhs => rw [_root_.GD.N0015.d005025]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hz)]
    simpa only [heq] using hi.integral_norm_prod_left


theorem d023631 (S : Set ℝ) (f : ℝ × ℝ → ℝ)
    (hf : Measurable f)
    (hi : Integrable f ((volume.restrict S).prod (volume.restrict (Ioi (0:ℝ))))) :
    (∫ p, f p ∂(volume.restrict S).prod (volume.restrict (Ioi (0:ℝ)))) =
      ∫ p : ℝ × ℝ, (2*p.2)*f (p.1,p.2^2)
        ∂(volume.restrict S).prod (volume.restrict (Ioi (0:ℝ))) := by
  rw [integral_prod _ hi,
    integral_prod _ (_root_.GD.N0062.d023630 S f hf hi)]
  exact _root_.GD.N0015.d005029 S (fun u s => f (u,s))

def d023632 (p : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1436.d013217 := (p.1,p.2^2)

def d023633 (t : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  30*p.2^2/(t*(1-t)*(p.2^2+_root_.GD.N0062.d022142 t p.1)^3*Real.sqrt (p.2^2+_root_.GD.N0062.d022142 t p.1))

theorem d023634 (t : ℝ) : Measurable (_root_.GD.N0062.d023633 t) := by
  unfold _root_.GD.N0062.d023633 _root_.GD.N0062.d022142
  fun_prop

private theorem d023635 : _root_.GD.N0232.N0720.N1436.d013288 =
    (volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ))) := by
  rw [Measure.prod_restrict]
  rfl


theorem d023636 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ p, |g p|≤B) (a : ℝ) :
    Integrable (fun p => _root_.GD.N0062.d023633 t p * (g (_root_.GD.N0062.d023632 p)-a)^2)
      _root_.GD.N0232.N0720.N1436.d013288 := by
  have hi := _root_.GD.N0045.d021928 3 3
    (by omega) (by omega) t g hg hB a
  rw [_root_.GD.N0062.d023635] at hi ⊢
  have htrans := _root_.GD.N0062.d023630 (Ioo (0:ℝ) 1)
    (fun p => _root_.GD.N0232.N0720.N1436.d013273 3 3 t p * (g p-a)^2)
    (by exact (_root_.GD.N0232.N0720.N1436.d013279 3 3 t).mul ((hg.sub measurable_const).pow_const 2)) hi
  apply htrans.congr
  rw [← _root_.GD.N0062.d023635]
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
  change p.1∈Ioo (0:ℝ) 1 ∧ 0<p.2 at hp
  rw [← mul_assoc, _root_.GD.N0062.d022146 t.property hp.1 hp.2]
  rfl


theorem d023637 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ p, |g p|≤B) (a : ℝ) :
    (∫ p, (g p-a)^2 ∂_root_.GD.N0232.N0720.N1441.d013678 3 3 t) =
      ∫ p, _root_.GD.N0062.d023633 t p * (g (_root_.GD.N0062.d023632 p)-a)^2
        ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  rw [_root_.GD.N0045.d021923 3 3 (by omega) (by omega)]
  have hi := _root_.GD.N0045.d021928 3 3
    (by omega) (by omega) t g hg hB a
  rw [_root_.GD.N0062.d023635] at hi ⊢
  rw [_root_.GD.N0062.d023631 _ _
    ((_root_.GD.N0232.N0720.N1436.d013279 3 3 t).mul ((hg.sub measurable_const).pow_const 2)) hi]
  apply integral_congr_ae
  rw [← _root_.GD.N0062.d023635]
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
  change p.1∈Ioo (0:ℝ) 1 ∧ 0<p.2 at hp
  rw [← mul_assoc, _root_.GD.N0062.d022146 t.property hp.1 hp.2]
  rfl

end
end GD.N0062

#print axioms _root_.GD.N0062.d023630
#print axioms _root_.GD.N0062.d023631
#print axioms _root_.GD.N0062.d023636
#print axioms _root_.GD.N0062.d023637
