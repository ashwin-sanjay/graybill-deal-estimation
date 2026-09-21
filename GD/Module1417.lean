import GD.Module1236
import GD.Module0980

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0207.N0451

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1332
open _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0107

theorem d022702 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1257.d015508 m n (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t) = t.1 * (1 - t.1) := by
  have ht : t.1 ≠ 0 := ne_of_gt t.2.1
  have ht' : 1 - t.1 ≠ 0 := ne_of_gt (sub_pos.mpr t.2.2)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold _root_.GD.N0232.N0720.N1257.d015508 _root_.GD.N0232.N0720.N1332.d020110 _root_.GD.N0232.N0720.N1424.d014846 _root_.GD.N0232.N0720.N1424.d014847
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr t.2.2.le)),
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) t.2.1.le)]
  have hsum : (m : ℝ) / (m * (1 - t.1)) + n / (n * t.1) =
      (t.1 * (1 - t.1))⁻¹ := by
    field_simp [ht, ht', hmR, hnR]
    ring
  rw [hsum, inv_inv]

theorem d022703
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta))
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ (C - 1) * t.1 * (1 - t.1) := by
  have h := hcap (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t)
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n _ (hrep _),
    _root_.GD.N0232.N0720.N1332.d020109 m n hm hn _ hg hb] at h
  have horacle := _root_.GD.N0232.N0720.N1396.d014795 m n hm hn
    (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t)
  unfold _root_.GD.N0232.N0720.N1396.d014778 at horacle
  rw [horacle, _root_.GD.N0232.N0720.N1332.d020111, _root_.GD.N0232.N0720.N1332.d020112,
    _root_.GD.N0207.N0451.d022702 hm hn t, one_mul, one_mul] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (mul_nonneg t.2.1.le (sub_nonneg.mpr t.2.2.le)))).mp h
  nlinarith

theorem d022704
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta))
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ (C - 1) * t.1 * (1 - t.1) :=
  _root_.GD.N0207.N0451.d022703 hm hn hg hb
    (fun _ => Filter.EventuallyEq.rfl) hC hcap t

end
end GD.N0207.N0451

#print axioms _root_.GD.N0207.N0451.d022703
#print axioms _root_.GD.N0207.N0451.d022704
