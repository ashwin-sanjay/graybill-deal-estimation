import GD.Module0775
import GD.Module0786
import GD.Module0752

















open Filter
open scoped BigOperators Topology

namespace GD
namespace N0232
namespace N0719
namespace N0834

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0719.N0865
open _root_.GD.N0232.N0719.N0830
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0835
open _root_.GD.N0230.N0655


def d011963 {k : ℕ} (sizes : Fin k → ℕ) : ℕ :=
  ∑ i, sizes i


def d011964
    {k : ℕ} {sizes : Fin k → ℕ}
    (b r : ℝ) (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  Finset.univ.sum fun i : Fin k ↦
    Finset.univ.sum fun j : Fin (sizes i) ↦
      (omega i j) ^ 2 / 2 - (r * omega i j + b) ^ 2 / 2


theorem d011965
    (b r x : ℝ) (hr : 0 < r) :
    _root_.GD.N0232.N0719.N0932.d009204 (-(b / r)) r⁻¹ x =
      r * Real.exp (x ^ 2 / 2 - (r * x + b) ^ 2 / 2) := by
  rw [_root_.GD.N0232.N0719.N1011.d011282 _ _ _ (inv_ne_zero hr.ne')]
  have hfront :
      (Real.sqrt (2 * Real.pi * (r⁻¹) ^ 2))⁻¹ /
          (Real.sqrt (2 * Real.pi))⁻¹ = r := by
    rw [show Real.sqrt (2 * Real.pi * (r⁻¹) ^ 2) =
        r⁻¹ * Real.sqrt (2 * Real.pi) by
      calc
        Real.sqrt (2 * Real.pi * (r⁻¹) ^ 2) =
            Real.sqrt ((r⁻¹) ^ 2 * (2 * Real.pi)) := by ring_nf
        _ = Real.sqrt ((r⁻¹) ^ 2) * Real.sqrt (2 * Real.pi) := by
          rw [Real.sqrt_mul (sq_nonneg (r⁻¹))]
        _ = r⁻¹ * Real.sqrt (2 * Real.pi) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hr)]]
    have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    field_simp [hr.ne', hsqrt]
  rw [hfront]
  congr 2
  field_simp [hr.ne']
  ring


theorem d011966
    (n : ℕ) (b r : ℝ) (hr : 0 < r)
    (x : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0719.N0932.d009213 n (-(b / r)) r⁻¹ x =
      r ^ n * Real.exp
        (Finset.univ.sum fun j : Fin n ↦
          (x j) ^ 2 / 2 - (r * x j + b) ^ 2 / 2) := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  simp_rw [_root_.GD.N0232.N0719.N0834.d011965 b r _ hr]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]


theorem d011967
    (k : ℕ) (sizes : Fin k → ℕ)
    (b r : ℝ) (hr : 0 < r)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0932.d009219 k sizes
        (-(b / r)) (fun _ ↦ r⁻¹) omega =
      r ^ _root_.GD.N0232.N0719.N0834.d011963 sizes *
        Real.exp (_root_.GD.N0232.N0719.N0834.d011964 b r omega) := by
  unfold _root_.GD.N0232.N0719.N0932.d009219 _root_.GD.N0232.N0719.N0932.d009190
    _root_.GD.N0232.N0719.N0834.d011963 _root_.GD.N0232.N0719.N0834.d011964
  simp_rw [_root_.GD.N0232.N0719.N0834.d011966
    _ b r hr]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [← Real.exp_sum]

@[simp] theorem d011968
    {k : ℕ} (g : _root_.GD.N0230.N0655.d000349) :
    (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g).location =
      -(g.1 / g.2.1) := by
  simp [_root_.GD.N0232.N0719.N0835.d011953, _root_.GD.N0232.N0719.N0842.d010906, _root_.GD.N0232.N0719.N0859.d010810,
    div_eq_mul_inv, mul_comm]

@[simp] theorem d011969
    {k : ℕ} (g : _root_.GD.N0230.N0655.d000349) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g).scale i = (g.2.1)⁻¹ := by
  simp [_root_.GD.N0232.N0719.N0835.d011953, _root_.GD.N0232.N0719.N0859.d010810]


theorem d011970
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) =
      (g.2.1)⁻¹ ^ 2 *
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) := by
  unfold _root_.GD.N0232.N0719.N0835.d011953
  exact _root_.GD.N0232.N0719.N0845.d010897 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0842.d010906 g.1 g.2.1) (g.2.1)⁻¹
    (inv_pos.mpr g.2.2) (_root_.GD.N0232.N0719.N0859.d010810 k)



theorem d011971
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : _root_.GD.N0230.N0655.d000349) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) g) omega =
      (g.2.1) ^ (_root_.GD.N0232.N0719.N0834.d011963 sizes + 2) /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) *
        Real.exp (_root_.GD.N0232.N0719.N0834.d011964 g.1 g.2.1 omega) := by
  unfold _root_.GD.N0232.N0719.N0830.d011754 _root_.GD.N0232.N0719.N0865.d011217
    _root_.GD.N0232.N0719.N0865.d011216 _root_.GD.N0232.N0719.N0865.d011214
  rw [_root_.GD.N0232.N0719.N0834.d011970,
    _root_.GD.N0232.N0719.N0834.d011968]
  simp only [_root_.GD.N0232.N0719.N0834.d011969]
  rw [_root_.GD.N0232.N0719.N0834.d011967
    k sizes g.1 g.2.1 g.2.2 omega]
  have hr : (g.2.1 : ℝ) ≠ 0 := g.2.2.ne'
  have hcap : _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ 0 :=
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)).ne'
  unfold _root_.GD.N0232.N0719.N0834.d011963
  field_simp [hr, hcap]
  ring




theorem d011972
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (g : ℕ → _root_.GD.N0230.N0655.d000349)
    (hdilation : Tendsto (fun n ↦ (g n).2.1) atTop (nhds 0))
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0835.d011953 (k := k) (g n)) omega)
      atTop (nhds 0) := by
  let C := _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
  let R : ℝ := Real.exp
    (∑ i : Fin k, ∑ j : Fin (sizes i), (omega i j) ^ 2 / 2)
  have hC : 0 < C := _root_.GD.N0232.N0719.N0858.d010853
    k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
  have hexponent : ∀ n,
      _root_.GD.N0232.N0719.N0834.d011964 (g n).1 (g n).2.1 omega ≤
        ∑ i : Fin k, ∑ j : Fin (sizes i),
          (omega i j) ^ 2 / 2 := by
    intro n
    unfold _root_.GD.N0232.N0719.N0834.d011964
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    nlinarith [sq_nonneg ((g n).2.1 * omega i j + (g n).1)]
  have hpow : Tendsto
      (fun n ↦ (g n).2.1 ^ (_root_.GD.N0232.N0719.N0834.d011963 sizes + 2))
      atTop (nhds 0) := by
    have h := hdilation.pow (_root_.GD.N0232.N0719.N0834.d011963 sizes + 2)
    simpa only [zero_pow (by omega : _root_.GD.N0232.N0719.N0834.d011963 sizes + 2 ≠ 0)] using h
  have hupper : Tendsto
      (fun n ↦ (g n).2.1 ^ (_root_.GD.N0232.N0719.N0834.d011963 sizes + 2) / C * R)
      atTop (nhds 0) := by
    have hdiv := hpow.div_const C
    simpa only [zero_div, zero_mul] using hdiv.mul_const R
  refine squeeze_zero'
    (f := fun n ↦ _root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0835.d011953 (k := k) (g n)) omega)
    (g := fun n ↦
      (g n).2.1 ^ (_root_.GD.N0232.N0719.N0834.d011963 sizes + 2) / C * R)
    (Eventually.of_forall fun n ↦
      _root_.GD.N0232.N0719.N0830.d011756
        k sizes hk hsizes _ omega)
    (Eventually.of_forall fun n ↦ ?_) ?_
  · rw [_root_.GD.N0232.N0719.N0834.d011971]
    apply mul_le_mul_of_nonneg_left
    · dsimp [R]
      exact Real.exp_le_exp.mpr (hexponent n)
    · exact div_nonneg (pow_nonneg (g n).2.2.le _) hC.le
  · exact hupper

end

end N0834
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0834.d011965
#print axioms _root_.GD.N0232.N0719.N0834.d011967
#print axioms _root_.GD.N0232.N0719.N0834.d011971
#print axioms _root_.GD.N0232.N0719.N0834.d011972
