import GD.Module0563




set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GD.N0106.N0428.N0770.N1702
noncomputable section


theorem d008348 {sigma t : ℝ}
    (hsigma : 0 < sigma) (ht : 0 ≤ t) :
    (∫ x : ℝ, Real.exp (-t * (2 / (sigma ^ 2 * x ^ 2))) ∂gaussianReal 0 1) =
      Real.exp (-(2 / sigma) * Real.sqrt t) := by
  have hq : 0 ≤ 2 * t / sigma ^ 2 := by positivity
  have harg : ∀ x : ℝ, -t * (2 / (sigma ^ 2 * x ^ 2)) =
      -(2 * t / sigma ^ 2 / x ^ 2) := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hsigma.ne', hx]
      <;> ring
  simp_rw [harg]
  rw [_root_.GD.N0106.N0428.N0770.N1702.d008347 hq]
  have hsqrt : Real.sqrt (2 * (2 * t / sigma ^ 2)) =
      (2 / sigma) * Real.sqrt t := by
    rw [show 2 * (2 * t / sigma ^ 2) = (4 * t) / sigma ^ 2 by ring,
      Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      Real.sqrt_sq_eq_abs, abs_of_pos hsigma]
    norm_num
    <;> ring
  rw [hsqrt]
  congr 1
  ring




theorem d008349 {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun u => ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 u x)
      (-(∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x)) b := by
  have he : (fun u => ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 u x) =ᶠ[𝓝 b]
      (fun u => Real.sqrt (Real.pi / 2) * Real.exp (-u)) :=
    (eventually_gt_nhds hb).mono fun u hu => _root_.GD.N0106.N0428.N0770.N1702.d006781 hu
  have hd := ((hasDerivAt_id b).neg.exp).const_mul (Real.sqrt (Real.pi / 2))
  simp only [Pi.neg_apply, id_eq] at hd
  have hd' : HasDerivAt (fun u => Real.sqrt (Real.pi / 2) * Real.exp (-u))
      (-(∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x)) b := by
    convert! hd using 1
    rw [_root_.GD.N0106.N0428.N0770.N1702.d006781 hb]
    ring
  exact hd'.congr_of_eventuallyEq he

end
end GD.N0106.N0428.N0770.N1702

#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008348
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008349
