import GD.Module1236
import GD.Module0980

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0206.N0446

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1332
open _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0107

theorem d021608 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
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

theorem d021609
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
    _root_.GD.N0206.N0446.d021608 hm hn t, one_mul, one_mul] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (mul_nonneg t.2.1.le (sub_nonneg.mpr t.2.2.le)))).mp h
  nlinarith

theorem d021610
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta))
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ (C - 1) * t.1 * (1 - t.1) :=
  _root_.GD.N0206.N0446.d021609 hm hn hg hb
    (fun _ => Filter.EventuallyEq.rfl) hC hcap t

open _root_.GD.N0232.N0720.N1399 (d020100 d020102
  d020101 d020103)

theorem d021611
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hleft : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020100 k).1)
      atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, a ≤ g x) := by
  intro hfloor
  have hsmall := hleft.eventually_lt_const (sq_pos_of_pos (half_pos ha))
  have hfrac := _root_.GD.N0232.N0720.N1399.d020101.eventually_lt_const (half_pos ha)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020117 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020100 k)
    (a := a) (by linarith) hfloor
  have hgap : a / 2 < a - (_root_.GD.N0232.N0720.N1399.d020100 k).1 := by linarith
  have hsquare := (sq_lt_sq₀ (half_pos ha).le (by linarith)).2 hgap
  linarith

theorem d021612
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hright : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020102 k).1)
      atTop (𝓝 0)) {b : ℝ} (hbone : b < 1) :
    ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x ≤ b) := by
  intro hceiling
  have hgap : 0 < (1 - b) / 2 := half_pos (sub_pos.mpr hbone)
  have hsmall := hright.eventually_lt_const (sq_pos_of_pos hgap)
  have hfrac := _root_.GD.N0232.N0720.N1399.d020103.eventually_const_lt
    (show (1 + b) / 2 < 1 by linarith)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020118 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020102 k)
    (b := b) (by linarith) hceiling
  have hsquare := (sq_lt_sq₀ hgap.le
    (show 0 ≤ (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)).2
    (show (1 - b) / 2 < (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)
  linarith

theorem d021613
    {m n : ℕ} {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} {B : ℝ}
    (hbound : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ B * t.1 * (1 - t.1)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020100 k).1) atTop (𝓝 0) ∧
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020102 k).1) atTop (𝓝 0) := by
  constructor
  · apply squeeze_zero (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ hbound (_root_.GD.N0232.N0720.N1399.d020100 k))
    simpa using (_root_.GD.N0232.N0720.N1399.d020101.const_mul B).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub _root_.GD.N0232.N0720.N1399.d020101)
  · apply squeeze_zero (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ hbound (_root_.GD.N0232.N0720.N1399.d020102 k))
    simpa using (_root_.GD.N0232.N0720.N1399.d020103.const_mul B).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub _root_.GD.N0232.N0720.N1399.d020103)


end
end GD.N0206.N0446

#print axioms _root_.GD.N0206.N0446.d021609
#print axioms _root_.GD.N0206.N0446.d021610

#print axioms _root_.GD.N0206.N0446.d021608

#print axioms _root_.GD.N0206.N0446.d021611

#print axioms _root_.GD.N0206.N0446.d021612

#print axioms _root_.GD.N0206.N0446.d021613
