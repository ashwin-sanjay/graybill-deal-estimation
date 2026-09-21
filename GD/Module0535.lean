import GD.Module0534

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0213.N0493
noncomputable section

theorem d007987 (v w : ℝ) :
    Real.exp v + Real.exp (-w) =
      Real.exp ((v - w) / 2) * (2 * Real.cosh ((v + w) / 2)) := by
  rw [Real.cosh_eq]
  have h₁ : (v - w) / 2 + (v + w) / 2 = v := by ring
  have h₂ : (v - w) / 2 + -((v + w) / 2) = -w := by ring
  calc
    _ = Real.exp ((v - w) / 2 + (v + w) / 2) +
        Real.exp ((v - w) / 2 + -((v + w) / 2)) := by rw [h₁, h₂]
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

theorem d007988 (v w : ℝ) :
    (Real.exp v + Real.exp (-w))⁻¹ =
      Real.exp (-((v - w) / 2)) / (2 * Real.cosh ((v + w) / 2)) := by
  rw [_root_.GD.N0213.N0493.d007987, mul_inv_rev, Real.exp_neg]
  ring

theorem d007989 (v w : ℝ) :
    (Real.exp v + Real.exp (-w))⁻¹ + (Real.exp w + Real.exp (-v))⁻¹ =
      Real.cosh ((v - w) / 2) / Real.cosh ((v + w) / 2) := by
  rw [_root_.GD.N0213.N0493.d007988, _root_.GD.N0213.N0493.d007988,
    show -((w - v) / 2) = (v - w) / 2 by ring,
    show (w + v) / 2 = (v + w) / 2 by ring,
    ← add_div]
  rw [Real.cosh_eq ((v - w) / 2)]
  ring

def d007990 (u : ℝ) : ℝ := (2 * Real.pi * Real.cosh (u / 2))⁻¹

def d007991 (F v w : ℝ) : ℝ :=
  2 * F * _root_.GD.N0213.N0493.d007990 (v - w) / (Real.exp v + Real.exp (-w))

theorem d007992 (u : ℝ) : _root_.GD.N0213.N0493.d007990 (-u) = _root_.GD.N0213.N0493.d007990 u := by
  unfold _root_.GD.N0213.N0493.d007990
  rw [neg_div, Real.cosh_neg]

theorem d007993 (F v w : ℝ) :
    (_root_.GD.N0213.N0493.d007991 F v w + _root_.GD.N0213.N0493.d007991 F w v) / 2 =
      F / (2 * Real.pi * Real.cosh ((v + w) / 2)) := by
  have hρ : _root_.GD.N0213.N0493.d007990 (w - v) = _root_.GD.N0213.N0493.d007990 (v - w) := by
    rw [show w - v = -(v - w) by ring, _root_.GD.N0213.N0493.d007992]
  unfold _root_.GD.N0213.N0493.d007991
  rw [hρ]
  calc
    _ = F * _root_.GD.N0213.N0493.d007990 (v - w) *
        ((Real.exp v + Real.exp (-w))⁻¹ + (Real.exp w + Real.exp (-v))⁻¹) := by ring
    _ = _ := by
      rw [_root_.GD.N0213.N0493.d007989]
      unfold _root_.GD.N0213.N0493.d007990
      field_simp [Real.pi_ne_zero, (Real.cosh_pos ((v - w) / 2)).ne',
        (Real.cosh_pos ((v + w) / 2)).ne']

theorem d007994 (u : ℝ) : 0 < _root_.GD.N0213.N0493.d007990 u := by
  unfold _root_.GD.N0213.N0493.d007990
  positivity

theorem d007995 (u : ℝ) :
    _root_.GD.N0213.N0493.d007990 u ≤ Real.pi⁻¹ * Real.exp (-|u| / 2) := by
  have hc : Real.exp (|u| / 2) ≤ 2 * Real.cosh (u / 2) := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu, Real.cosh_eq]
      linarith [Real.exp_pos (-(u / 2))]
    · rw [abs_of_neg (lt_of_not_ge hu), Real.cosh_eq]
      have he : -u / 2 = -(u / 2) := by ring
      rw [he]
      linarith [Real.exp_pos (u / 2)]
  have hden : Real.pi * Real.exp (|u| / 2) ≤
      2 * Real.pi * Real.cosh (u / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hc Real.pi_pos.le]
  have hi := (inv_le_inv₀
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) (Real.cosh_pos (u / 2)))
    (mul_pos Real.pi_pos (Real.exp_pos (|u| / 2)))).mpr hden
  simpa only [_root_.GD.N0213.N0493.d007990, mul_inv_rev, ← Real.exp_neg,
    show -(|u| / 2) = -|u| / 2 by ring, mul_comm] using hi

end
end GD.N0213.N0493

#print axioms _root_.GD.N0213.N0493.d007993
#print axioms _root_.GD.N0213.N0493.d007995
