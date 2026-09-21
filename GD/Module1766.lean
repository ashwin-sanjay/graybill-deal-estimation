import GD.Module0382
import GD.Module1765



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped FourierTransform
namespace GD.N0106.N0428.N0765.N1601
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1652 _root_.GD.N0106.N0428.N0765.N1613 _root_.GD.N0106.N0428.N0765.N1587


structure d029267 (g : ℝ → ℂ) : Prop where
  continuous : Continuous g
  bounds : ∃ a b k C D : ℝ, 0 < a ∧ 0 < b ∧ 0 < k ∧
    (∀ x : ℝ, ‖g x‖ ≤ C * _root_.GD.N0106.N0428.N0765.N1587.d029254 a b x) ∧
    (∀ xi : ℝ, ‖𝓕 g xi‖ ≤ D * Real.exp (-k*|xi|))

theorem d029268 {g : ℝ → ℂ} (hg : _root_.GD.N0106.N0428.N0765.N1601.d029267 g) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 g := by
  obtain ⟨a,b,k,C,D,ha,hb,hk,ht,hf⟩ := hg.bounds
  refine _root_.GD.N0106.N0428.N0765.N1652.d005814 (AL := C) (AR := C) hg.continuous ha hb hk ?_ ?_ (fun n => hf n)
  · intro x hx
    simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx] using ht x
  · intro x hx
    by_cases he : x = 0
    · simpa only [he, _root_.GD.N0106.N0428.N0765.N1587.d029254, le_refl, if_true, mul_zero, Real.exp_zero, mul_one] using ht x
    · have hp : ¬ x ≤ 0 := not_le.mpr (lt_of_le_of_ne hx (Ne.symm he))
      simpa only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg hp] using ht x

theorem d029269 {g : ℝ → ℂ} (hg : _root_.GD.N0106.N0428.N0765.N1601.d029267 g) {h : ℝ} (hh : 0 < h) :
    _root_.GD.N0106.N0428.N0765.N1601.d029267 (fun x : ℝ => g (h*x)) := by
  obtain ⟨a,b,k,C,D,ha,hb,hk,ht,hf⟩ := hg.bounds
  refine ⟨hg.continuous.comp (continuous_const.mul continuous_id),
    a*h,b*h,k/h,C,h⁻¹*D,mul_pos ha hh,mul_pos hb hh,div_pos hk hh,?_,?_⟩
  · intro x
    have he : _root_.GD.N0106.N0428.N0765.N1587.d029254 a b (h*x) = _root_.GD.N0106.N0428.N0765.N1587.d029254 (a*h) (b*h) x := by
      unfold _root_.GD.N0106.N0428.N0765.N1587.d029254
      have hsign : h*x ≤ 0 ↔ x ≤ 0 := by constructor <;> intro hx <;> nlinarith
      simp only [hsign]
      split <;> congr 1 <;> ring
    simpa only [he] using ht (h*x)
  · intro xi
    rw [_root_.GD.N0106.N0428.N0765.N1613.d005634 g hh, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    have he : -k*|xi/h| = -(k/h)*|xi| := by
      rw [abs_div, abs_of_pos hh]
      ring
    simpa only [he, mul_assoc] using
      mul_le_mul_of_nonneg_left (hf (xi/h)) (inv_pos.mpr hh).le

theorem d029270 {g : ℝ → ℂ} (hg : _root_.GD.N0106.N0428.N0765.N1601.d029267 g) (r : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1601.d029267 (fun x : ℝ => r • g x) := by
  obtain ⟨a,b,k,C,D,ha,hb,hk,ht,hf⟩ := hg.bounds
  refine ⟨continuous_const.smul hg.continuous,
    a,b,k,|r| *C,|r| *D,ha,hb,hk,?_,?_⟩
  · intro x
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (ht x) (abs_nonneg r)).trans_eq (mul_assoc _ _ _).symm
  · intro xi
    rw [_root_.GD.N0106.N0428.N0765.N1652.d005821, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hf xi) (abs_nonneg r)).trans_eq (mul_assoc _ _ _).symm

end
end GD.N0106.N0428.N0765.N1601
#print axioms _root_.GD.N0106.N0428.N0765.N1601.d029269
#print axioms _root_.GD.N0106.N0428.N0765.N1601.d029268
