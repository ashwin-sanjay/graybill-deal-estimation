import GD.Module0545






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0101.N0392
noncomputable section

open _root_.GD.N0208.N0455
open _root_.GD.N0213.N0493
open _root_.GD.N0218



theorem d008129 (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, ENNReal.ofReal (1 / 2 : ℝ) * (H z + H z.swap)
      ∂(volume : Measure ℝ).prod volume) =
      ∫⁻ z, H z ∂(volume : Measure ℝ).prod volume := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left hH _, lintegral_prod_swap, ← two_mul, ← mul_assoc]
  have hc : ENNReal.ofReal (1 / 2 : ℝ) * (2 : ℝ≥0∞) = 1 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  rw [hc, one_mul]

theorem d008130 {F : ℝ} (hF : 0 ≤ F) (v w : ℝ) :
    0 ≤ _root_.GD.N0213.N0493.d007991 F v w := by
  unfold _root_.GD.N0213.N0493.d007991
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF)
    (_root_.GD.N0213.N0493.d007994 _).le) (add_pos (Real.exp_pos _) (Real.exp_pos _)).le




theorem d008131 (F : ℝ) (hF : 0 ≤ F)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫⁻ v : ℝ, ∫⁻ w : ℝ, ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 F v w) *
      ENNReal.ofReal ((f v - f w) ^ 2)) =
      ∫⁻ v : ℝ, ∫⁻ w : ℝ,
        ENNReal.ofReal (F / (2 * Real.pi * Real.cosh ((v + w) / 2))) *
          ENNReal.ofReal ((f v - f w) ^ 2) := by
  let H : ℝ × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 F z.1 z.2) * ENNReal.ofReal ((f z.1 - f z.2) ^ 2)
  have hH : Measurable H := by
    unfold H _root_.GD.N0213.N0493.d007991 _root_.GD.N0213.N0493.d007990
    fun_prop
  have hpoint (v w : ℝ) :
      ENNReal.ofReal (1 / 2 : ℝ) * (H (v, w) + H (w, v)) =
        ENNReal.ofReal (F / (2 * Real.pi * Real.cosh ((v + w) / 2))) *
          ENNReal.ofReal ((f v - f w) ^ 2) := by
    dsimp only [H]
    rw [sub_sq_comm (f w) (f v), ← add_mul,
      ← ENNReal.ofReal_add (_root_.GD.N0101.N0392.d008130 hF v w) (_root_.GD.N0101.N0392.d008130 hF w v),
      ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      show (1 / 2 : ℝ) * (_root_.GD.N0213.N0493.d007991 F v w + _root_.GD.N0213.N0493.d007991 F w v) =
        (_root_.GD.N0213.N0493.d007991 F v w + _root_.GD.N0213.N0493.d007991 F w v) / 2 by ring,
      _root_.GD.N0213.N0493.d007993]
  calc
    _ = ∫⁻ z, H z ∂(volume : Measure ℝ).prod volume :=
      (lintegral_prod H hH.aemeasurable).symm
    _ = ∫⁻ z, ENNReal.ofReal (1 / 2 : ℝ) * (H z + H z.swap)
        ∂(volume : Measure ℝ).prod volume := (_root_.GD.N0101.N0392.d008129 H hH).symm
    _ = ∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal (F / (2 * Real.pi * Real.cosh ((z.1 + z.2) / 2))) *
          ENNReal.ofReal ((f z.1 - f z.2) ^ 2)
        ∂(volume : Measure ℝ).prod volume :=
      lintegral_congr (fun z => hpoint z.1 z.2)
    _ = _ := lintegral_prod _ (by fun_prop)


theorem d008132 (K N : ℝ) :
    (∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 K s) v w) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) =
      ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
        ENNReal.ofReal (_root_.GD.N0218.d008118 K s /
          (2 * Real.pi * Real.cosh ((v + w) / 2))) *
          ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2) := by
  apply lintegral_congr
  intro s
  exact _root_.GD.N0101.N0392.d008131 (_root_.GD.N0218.d008118 K s)
    (_root_.GD.N0218.d008121 K s) (_root_.GD.N0208.N0455.d007937 N) (_root_.GD.N0208.N0455.d007938 N)

theorem d008133 (K N : ℝ) (hN : 0 < N) :
    (∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 K s) v w) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≤
      ENNReal.ofReal (256 / (Real.pi * N)) := by
  rw [_root_.GD.N0101.N0392.d008132]
  exact _root_.GD.N0218.d008124 K N hN

theorem d008134 (K N : ℝ) (hN : 0 < N) :
    (∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 K s) v w) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0101.N0392.d008133 K N hN)


theorem d008135 (K : ℝ → ℝ) :
    Tendsto (fun N : ℝ => ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 (K N) s) v w) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) atTop (𝓝 0) := by
  simp_rw [_root_.GD.N0101.N0392.d008132]
  exact _root_.GD.N0218.d008125 K

end
end GD.N0101.N0392

#print axioms _root_.GD.N0101.N0392.d008129
#print axioms _root_.GD.N0101.N0392.d008131
#print axioms _root_.GD.N0101.N0392.d008132
#print axioms _root_.GD.N0101.N0392.d008133
#print axioms _root_.GD.N0101.N0392.d008134
#print axioms _root_.GD.N0101.N0392.d008135
