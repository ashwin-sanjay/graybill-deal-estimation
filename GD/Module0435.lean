import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0377
noncomputable section



def d006739 (H R ε L : ℝ) : ℝ := H * ε / (R * Real.exp L)

theorem d006740 {H R ε L : ℝ}
    (hH : 0 < H) (hR : 0 < R) (he : 0 < ε) :
    0 < _root_.GD.N0101.N0377.d006739 H R ε L := by
  exact div_pos (mul_pos hH he) (mul_pos hR (Real.exp_pos L))

theorem d006741 {H R ε L : ℝ}
    (hH : 0 < H) (hHR : H ≤ R) (he : 0 < ε) (hL : 0 ≤ L) :
    _root_.GD.N0101.N0377.d006739 H R ε L ≤ ε := by
  have hR := hH.trans_le hHR
  have hexp : 1 ≤ Real.exp L := by simpa using Real.exp_le_exp.mpr hL
  apply (div_le_iff₀ (mul_pos hR (Real.exp_pos L))).mpr
  have hm : H ≤ R * Real.exp L := hHR.trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hR.le)
  nlinarith [mul_le_mul_of_nonneg_right hm he.le]

theorem d006742 {H R ε L : ℝ}
    (hH : 0 < H) (hR : 0 < R) (he : 0 < ε) :
    (H / _root_.GD.N0101.N0377.d006739 H R ε L) / (R / ε) = Real.exp L := by
  unfold _root_.GD.N0101.N0377.d006739
  field_simp [hH.ne', hR.ne', he.ne', Real.exp_ne_zero L]



theorem d006743 {H R ε L : ℝ}
    (hH : 0 < H) (hR : 0 < R) (he : 0 < ε) (hL : 0 ≤ L) :
    (∫ s in Ioo (R / ε) (H / _root_.GD.N0101.N0377.d006739 H R ε L), (1 : ℝ) / s) = L := by
  have ha := _root_.GD.N0101.N0377.d006740 (L := L) hH hR he
  have hlo := div_pos hR he
  have hhi := div_pos hH ha
  have hratio := _root_.GD.N0101.N0377.d006742 (L := L) hH hR he
  have hexp : 1 ≤ Real.exp L := by simpa using Real.exp_le_exp.mpr hL
  have horder : R / ε ≤ H / _root_.GD.N0101.N0377.d006739 H R ε L := by
    have h := hexp
    rw [← hratio, le_div_iff₀ hlo] at h
    simpa only [one_mul] using h
  have hint := integral_inv_of_pos hlo hhi
  rw [intervalIntegral.integral_of_le horder, integral_Ioc_eq_integral_Ioo,
    hratio, Real.log_exp] at hint
  simpa only [one_div] using hint



theorem d006744 {H R ε L : ℝ}
    (hH : 0 < H) (hR : 0 < R) (he : 0 < ε) :
    Real.log (ε / _root_.GD.N0101.N0377.d006739 H R ε L) = L + Real.log (R / H) := by
  have hid : ε / _root_.GD.N0101.N0377.d006739 H R ε L = (R / H) * Real.exp L := by
    unfold _root_.GD.N0101.N0377.d006739
    field_simp [hH.ne', hR.ne', he.ne', Real.exp_ne_zero L]
  rw [hid, Real.log_mul (div_pos hR hH).ne' (Real.exp_ne_zero L), Real.log_exp]
  ring




theorem d006745 {A q D E : ℝ}
    (h : ∀ L : ℝ, 0 ≤ L → A * L ≤ q * (L + D) + E) : A ≤ q := by
  by_contra hA
  have hd : 0 < A - q := sub_pos.mpr (lt_of_not_ge hA)
  let L := (|q * D + E| + 1) / (A - q)
  have hL : 0 ≤ L := (div_pos (by positivity) hd).le
  have heq : (A - q) * L = |q * D + E| + 1 := by
    dsimp only [L]
    field_simp [hd.ne']
  have hb := h L hL
  nlinarith [le_abs_self (q * D + E)]

end
end GD.N0101.N0377

#print axioms _root_.GD.N0101.N0377.d006740
#print axioms _root_.GD.N0101.N0377.d006741
#print axioms _root_.GD.N0101.N0377.d006742
#print axioms _root_.GD.N0101.N0377.d006743
#print axioms _root_.GD.N0101.N0377.d006744
#print axioms _root_.GD.N0101.N0377.d006745
