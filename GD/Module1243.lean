import GD.Module0938
import GD.Module1212











open MeasureTheory Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1401

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1372
open _root_.GD.N0232.N0720.N1388 _root_.GD.N0232.N0720.N1389 _root_.GD.N0232.N0720.N1387
open _root_.GD.N0232.N0720.N1381 _root_.GD.N0232.N0720.N1392
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1437 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556
open _root_.GD.N0107 _root_.GD.N0137

noncomputable section

def d020150 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  _root_.GD.N0232.N0720.N1437.d002998 (fun r s ↦ g (r, s)) (x 0) (x 2) (x 1 ^ 2) (x 3 ^ 2)

theorem d020151 {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) : Measurable (_root_.GD.N0232.N0720.N1401.d020150 g) := by
  unfold _root_.GD.N0232.N0720.N1401.d020150 _root_.GD.N0232.N0720.N1437.d002998
    _root_.GD.N0232.N0720.N1437.d002996 _root_.GD.N0232.N0720.N1437.d002997
  fun_prop

theorem d020152 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    _root_.GD.N0238.N0753.d004397 (_root_.GD.N0232.N0720.N1401.d020150 g) := by
  intro c hc x
  simpa only [_root_.GD.N0232.N0720.N1401.d020150, PiLp.smul_apply, smul_eq_mul, mul_pow, zero_add] using
    _root_.GD.N0232.N0720.N1437.d003003 (fun r s ↦ g (r, s)) 0 c (x 0) (x 2) (x 1 ^ 2) (x 3 ^ 2) hc

theorem d020153 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : ∀ p, g p ∈ Icc (0 : ℝ) 1) (u : _root_.GD.N0232.N0720.N1393.d004493) :
    ‖_root_.GD.N0232.N0720.N1401.d020150 g u‖ ≤ 3 := by
  have hu : ‖(u : _root_.GD.N0232.N0720.N1393.d004492)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp u.2
  have hX : ‖(u : _root_.GD.N0232.N0720.N1393.d004492) 0‖ ≤ 1 := by
    simpa only [hu] using PiLp.norm_apply_le (u : _root_.GD.N0232.N0720.N1393.d004492) 0
  have hY : ‖(u : _root_.GD.N0232.N0720.N1393.d004492) 2‖ ≤ 1 := by
    simpa only [hu] using PiLp.norm_apply_le (u : _root_.GD.N0232.N0720.N1393.d004492) 2
  let a := g (_root_.GD.N0232.N0720.N1437.d002996
    ((u : _root_.GD.N0232.N0720.N1393.d004492) 1 ^ 2)
    ((u : _root_.GD.N0232.N0720.N1393.d004492) 3 ^ 2),
    _root_.GD.N0232.N0720.N1437.d002997 ((u : _root_.GD.N0232.N0720.N1393.d004492) 0)
      ((u : _root_.GD.N0232.N0720.N1393.d004492) 2)
      ((u : _root_.GD.N0232.N0720.N1393.d004492) 1 ^ 2)
      ((u : _root_.GD.N0232.N0720.N1393.d004492) 3 ^ 2))
  have ha : ‖a‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg _).1]
    exact (hg _).2
  change ‖(u : _root_.GD.N0232.N0720.N1393.d004492) 2 +
    ((u : _root_.GD.N0232.N0720.N1393.d004492) 0 -
      (u : _root_.GD.N0232.N0720.N1393.d004492) 2) * a‖ ≤ 3
  calc
    _ ≤ ‖(u : _root_.GD.N0232.N0720.N1393.d004492) 2‖ +
      ‖((u : _root_.GD.N0232.N0720.N1393.d004492) 0 -
        (u : _root_.GD.N0232.N0720.N1393.d004492) 2) * a‖ := norm_add_le _ _
    _ = ‖(u : _root_.GD.N0232.N0720.N1393.d004492) 2‖ +
      ‖(u : _root_.GD.N0232.N0720.N1393.d004492) 0 -
        (u : _root_.GD.N0232.N0720.N1393.d004492) 2‖ * ‖a‖ := by rw [norm_mul]
    _ ≤ 1 + (1 + 1) * 1 := by
      apply add_le_add hY
      exact mul_le_mul ((norm_sub_le _ _).trans (add_le_add hX hY)) ha
        (norm_nonneg a) (by norm_num)
    _ = 3 := by norm_num

theorem d020154 (x : _root_.GD.N0137.d008894 2) :
    _root_.GD.N0107.d009084 x = (x 0 + x 1) / 2 := by
  simp [_root_.GD.N0107.d009084, _root_.GD.N0126.d006420,
    _root_.GD.N0126.d006419, Fin.sum_univ_succ]

theorem d020155 (x : _root_.GD.N0137.d008894 2) :
    _root_.GD.N0107.d009085 x / 2 = ((x 0 - x 1) / 2) ^ 2 := by
  norm_num [_root_.GD.N0107.d009085, _root_.GD.N0126.d006422,
    _root_.GD.N0126.d006421, _root_.GD.N0126.d006420,
    _root_.GD.N0126.d006419, Fin.sum_univ_succ]
  ring

theorem d020156 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (x : _root_.GD.N0232.N0720.N1387.d014681) :
    _root_.GD.N0232.N0720.N1401.d020150 g (_root_.GD.N0232.N0720.N1389.d012529 x) = _root_.GD.N0232.N0720.N1425.d014719 2 2 g x := by
  simp only [_root_.GD.N0232.N0720.N1401.d020150, _root_.GD.N0232.N0720.N1387.d014686, _root_.GD.N0232.N0720.N1425.d014719,
    _root_.GD.N0232.N0720.N1084.d014252,
    _root_.GD.N0232.N0720.N1084.d014253, Nat.cast_ofNat,
    _root_.GD.N0232.N0720.N1401.d020154, _root_.GD.N0232.N0720.N1401.d020155]
  rfl




theorem d020157 {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ∃ h : _root_.GD.N0232.N0720.N1393.d004495, _root_.GD.N0230.N0556.d000031 _root_.GD.N0232.N0720.N1372.d004546 h ∧
      ∀ θ : _root_.GD.N0232.N0720.N1387.d014682, _root_.GD.N0232.N0720.N1389.d012534 h =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 θ] d := by
  let g := _root_.GD.N0232.N0720.N1398.d019601 d
  let f := _root_.GD.N0232.N0720.N1401.d020150 g
  have hg : Measurable g := _root_.GD.N0232.N0720.N1398.d019602 hd.1
  have hf : Measurable f := _root_.GD.N0232.N0720.N1401.d020151 hg
  have hhom : _root_.GD.N0238.N0753.d004397 f := _root_.GD.N0232.N0720.N1401.d020152 g
  have hbound : ∀ u : _root_.GD.N0232.N0720.N1393.d004493, ‖f u‖ ≤ 3 :=
    _root_.GD.N0232.N0720.N1401.d020153 g (_root_.GD.N0232.N0720.N1398.d019603 d)
  have hrep : ∀ θ : _root_.GD.N0232.N0720.N1387.d014682,
      f ∘ _root_.GD.N0232.N0720.N1389.d012529 =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 θ] d := by
    intro θ
    have he := (_root_.GD.N0232.N0720.N1398.d019606 hd θ).symm
    simpa only [Function.comp_def, f, _root_.GD.N0232.N0720.N1401.d020156, g] using he
  refine ⟨_root_.GD.N0232.N0720.N1381.d014708 f hf 3 hbound, ?_, ?_⟩
  · exact _root_.GD.N0232.N0720.N1392.d014714 hd f hf hhom 3 hbound hrep
  · intro θ
    exact (_root_.GD.N0232.N0720.N1392.d014713 f hf hhom 3 hbound θ).trans (hrep θ)

end

end GD.N0232.N0720.N1401

#print axioms _root_.GD.N0232.N0720.N1401.d020156
#print axioms _root_.GD.N0232.N0720.N1401.d020157
