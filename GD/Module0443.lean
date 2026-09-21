import GD.Module0442









set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1553
noncomputable section
open MeasureTheory Filter Set Complex ContinuousMap TopologicalSpace
open _root_.GD.N0106.N0428.N0765.N1551 _root_.GD.N0106.N0428.N0765.N1613
open scoped Topology FourierTransform


theorem d006797 {f : ℝ → ℂ} {Cpos Cneg k h : ℝ}
    (hc : Continuous f) (hk : 0 < k) (hh : 0 < h)
    (hnorm : ∀ K : Compacts ℝ, Summable fun n : ℤ =>
      ‖((⟨fun x : ℝ => f (h * x), hc.comp (continuous_const.mul continuous_id)⟩ :
        C(ℝ, ℂ)).comp (ContinuousMap.addRight n)).restrict K‖)
    (hpos : ∀ xi : ℝ, 0 < xi → ‖𝓕 f xi‖ ≤ Cpos * Real.exp (-k * xi))
    (hneg : ∀ xi : ℝ, 0 < xi → ‖𝓕 f (-xi)‖ ≤ Cneg * Real.exp (-k * xi))
    (offset : ℝ) :
    ‖(h : ℂ) * (∑' n : ℤ, f (offset + h * n)) - ∫ t : ℝ, f t‖ ≤
      (Cpos + Cneg) / (Real.exp (k / h) - 1) := by
  let g : ℝ → ℂ := fun x => f (h * x)
  have hg : Continuous g := hc.comp (continuous_const.mul continuous_id)
  have hp : ∀ n : ℕ, ‖𝓕 g ((n : ℝ) + 1)‖ ≤
      (h⁻¹ * Cpos) * Real.exp (-(k / h) * (n + 1)) := by
    intro n
    rw [show g = (fun x : ℝ => f (h*x)) from rfl, _root_.GD.N0106.N0428.N0765.N1613.d005634 f hh, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    have he : -k * (((n : ℝ) + 1) / h) = -(k / h) * (n + 1) := by ring
    simpa only [he, mul_assoc] using
      mul_le_mul_of_nonneg_left (hpos (((n : ℝ) + 1) / h) (by positivity))
        (inv_pos.mpr hh).le
  have hn : ∀ n : ℕ, ‖𝓕 g (-((n : ℝ) + 1))‖ ≤
      (h⁻¹ * Cneg) * Real.exp (-(k / h) * (n + 1)) := by
    intro n
    rw [show g = (fun x : ℝ => f (h*x)) from rfl, _root_.GD.N0106.N0428.N0765.N1613.d005634 f hh, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    have he : -k * (((n : ℝ) + 1) / h) = -(k / h) * (n + 1) := by ring
    simpa only [he, mul_assoc, neg_div] using
      mul_le_mul_of_nonneg_left (hneg (((n : ℝ) + 1) / h) (by positivity))
        (inv_pos.mpr hh).le
  have hu := _root_.GD.N0106.N0428.N0765.N1551.d006795 (f := (⟨g, hg⟩ : C(ℝ, ℂ)))
    (div_pos hk hh) hnorm hp hn (offset/h)
  have hsum : (∑' n : ℤ, g (offset/h+n)) = ∑' n : ℤ, f (offset+h*n) := by
    apply tsum_congr
    intro n
    change f (h * (offset/h + (n : ℝ))) = f (offset + h*n)
    congr 1
    field_simp [hh.ne'] <;> ring
  have hInt : (∫ x : ℝ, g x) = h⁻¹ • ∫ x : ℝ, f x := by
    simpa only [g, abs_of_pos (inv_pos.mpr hh)] using Measure.integral_comp_mul_left f h
  have hid : (h : ℂ) * (∑' n : ℤ, f (offset+h*n)) - ∫ x : ℝ, f x =
      h • ((∑' n : ℤ, g (offset/h+n)) - ∫ x : ℝ, g x) := by
    rw [hsum, hInt, smul_sub, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
    rfl
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ h * ((h⁻¹ * Cpos + h⁻¹ * Cneg) / (Real.exp (k/h)-1)) :=
      mul_le_mul_of_nonneg_left hu hh.le
    _ = (h*h⁻¹) * (Cpos + Cneg) / (Real.exp (k/h)-1) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hh.ne', one_mul]



theorem d006798 {error h d Bplus Bminus : ℝ}
    {r : ℕ → ℝ} (hh : 0 < h) (hd : 0 < d)
    (hr : Tendsto r atTop (𝓝 d))
    (hb : ∀ n : ℕ, error ≤ (Bplus + Bminus) /
      (Real.exp (2 * Real.pi * r n / h) - 1)) :
    error ≤ (Bplus + Bminus) / (Real.exp (2 * Real.pi * d / h) - 1) :=
  _root_.GD.N0106.N0428.N0765.N1551.d006796 hh hd hr tendsto_const_nhds tendsto_const_nhds hb

end
end GD.N0106.N0428.N0765.N1553
#print axioms _root_.GD.N0106.N0428.N0765.N1553.d006797
#print axioms _root_.GD.N0106.N0428.N0765.N1553.d006798
