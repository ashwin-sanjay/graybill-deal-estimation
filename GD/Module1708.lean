import GD.Module1681
import GD.Module1690
import GD.Module1653
import GD.Module1707

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0367
noncomputable section

open _root_.GD.N0101.N0414 _root_.GD.N0101.N0394
open _root_.GD.N0101.N0363 _root_.GD.N0101.N0362
open _root_.GD.N0220
open _root_.GD.N0219 _root_.GD.N0218
open _root_.GD.N0213.N0493
open _root_.GD.N0208.N0455

def d028640 (u : Fin 2 → ℝ) : ℝ := Real.log (u 0 / u 1)

theorem d028641 (β u : Fin 2 → ℝ)
    (hβ : ∀ i, 0 < β i) (hu : ∀ i, 0 < u i) :
    (β 0)⁻¹ * _root_.GD.N0101.N0394.d028503 (_root_.GD.N0101.N0414.d028419 β u) =
      (β 0 + β 1 * Real.exp (_root_.GD.N0101.N0367.d028640 u))⁻¹ := by
  rw [_root_.GD.N0101.N0367.d028640, Real.exp_log (div_pos (hu 0) (hu 1))]
  unfold _root_.GD.N0101.N0394.d028503 _root_.GD.N0101.N0414.d028419
  field_simp [(hβ 0).ne', (hβ 1).ne', (hu 1).ne',
    (add_pos (div_pos (hu 0) (hβ 0)) (div_pos (hu 1) (hβ 1))).ne',
    (add_pos (hβ 0) (mul_pos (hβ 1) (div_pos (hu 0) (hu 1)))).ne']
  rw [add_comm]

theorem d028642 (s v ell : ℝ) :
    _root_.GD.N0219.d008142 s * (Real.exp (s + v) + Real.exp (s - v) * Real.exp ell)⁻¹ =
      2 * _root_.GD.N0218.d008109 s / (Real.exp v + Real.exp (-(v - ell))) := by
  have he : Real.exp (-(v - ell)) = Real.exp ell / Real.exp v := by
    rw [neg_sub, Real.exp_sub]
  have hs : Real.exp (2 * s) = Real.exp s ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [_root_.GD.N0219.d008143, _root_.GD.N0218.d008109, Real.exp_add, Real.exp_sub, he, hs]
  field_simp



theorem d028643 (N s v : ℝ) (u : Fin 2 → ℝ)
    (hu : ∀ i, 0 < u i) :
    _root_.GD.N0219.d008142 s * ((_root_.GD.N0220.d028625 (s,v) 0)⁻¹ *
      _root_.GD.N0101.N0394.d028503 (_root_.GD.N0101.N0414.d028419 (_root_.GD.N0220.d028625 (s,v)) u)) *
      _root_.GD.N0213.N0493.d007990 (_root_.GD.N0101.N0367.d028640 u) * _root_.GD.N0208.N0455.d007937 N s ^ 2 =
    _root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 N s) v (v - _root_.GD.N0101.N0367.d028640 u) := by
  rw [_root_.GD.N0101.N0367.d028641 _ _ (_root_.GD.N0220.d028627 _) hu]
  change _root_.GD.N0219.d008142 s * (Real.exp (s+v) + Real.exp (s-v) *
    Real.exp (_root_.GD.N0101.N0367.d028640 u))⁻¹ * _root_.GD.N0213.N0493.d007990 (_root_.GD.N0101.N0367.d028640 u) * _root_.GD.N0208.N0455.d007937 N s ^ 2 = _
  rw [_root_.GD.N0101.N0367.d028642]
  unfold _root_.GD.N0213.N0493.d007991 _root_.GD.N0218.d008118
  rw [show v - (v - _root_.GD.N0101.N0367.d028640 u) = _root_.GD.N0101.N0367.d028640 u by ring]
  ring

theorem d028644 (N s v : ℝ) (u : Fin 2 → ℝ)
    (hu : ∀ i, 0 < u i) :
    (_root_.GD.N0101.N0362.d007947 N (_root_.GD.N0220.d028625 (s,v)) - _root_.GD.N0101.N0362.d007947 N
      (_root_.GD.N0101.N0394.d028504 (1/2) (_root_.GD.N0101.N0414.d028419 (_root_.GD.N0220.d028625 (s,v)) u)
        (_root_.GD.N0220.d028625 (s,v)))) ^ 2 =
      _root_.GD.N0208.N0455.d007937 N s ^ 2 * (_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N (v - _root_.GD.N0101.N0367.d028640 u)) ^ 2 := by
  have hβ := _root_.GD.N0220.d028627 (s,v)
  have ht : ∀ i, 0 < _root_.GD.N0101.N0414.d028419 (_root_.GD.N0220.d028625 (s,v)) u i :=
    fun i => div_pos (hu i) (hβ i)
  have hprod : _root_.GD.N0101.N0363.d028137 (_root_.GD.N0220.d028625 (s,v))
      (_root_.GD.N0101.N0414.d028419 (_root_.GD.N0220.d028625 (s,v)) u) = u := by
    funext i
    exact mul_div_cancel₀ (u i) (hβ i).ne'
  have h := _root_.GD.N0101.N0363.d028142 N (a := (1/2 : ℝ))
    (by norm_num) hβ ht
  rw [hprod, (_root_.GD.N0220.d028628 (s,v)).1,
    (_root_.GD.N0220.d028628 (s,v)).2] at h
  exact h



theorem d028645 (N s v : ℝ) (u : Fin 2 → ℝ)
    (hu : ∀ i, 0 < u i) :
    ENNReal.ofReal (_root_.GD.N0219.d008142 s) *
      _root_.GD.N0101.N0394.d028505 (1/2) (_root_.GD.N0101.N0362.d007947 N) (_root_.GD.N0220.d028625 (s,v))
        (_root_.GD.N0101.N0414.d028419 (_root_.GD.N0220.d028625 (s,v)) u) *
      ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 (_root_.GD.N0101.N0367.d028640 u)) =
    ENNReal.ofReal (_root_.GD.N0213.N0493.d007991 (_root_.GD.N0218.d008118 N s) v (v - _root_.GD.N0101.N0367.d028640 u)) *
      ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N (v - _root_.GD.N0101.N0367.d028640 u)) ^ 2) := by
  unfold _root_.GD.N0101.N0394.d028505
  rw [_root_.GD.N0101.N0367.d028644 N s v u hu,
    ← ENNReal.ofReal_mul (_root_.GD.N0219.d008144 s).1.le,
    ← ENNReal.ofReal_mul' (_root_.GD.N0213.N0493.d007994 _).le,
    ← ENNReal.ofReal_mul' (sq_nonneg _)]
  congr 1
  calc
    _ = (_root_.GD.N0219.d008142 s * ((_root_.GD.N0220.d028625 (s,v) 0)⁻¹ *
      _root_.GD.N0101.N0394.d028503 (_root_.GD.N0101.N0414.d028419 (_root_.GD.N0220.d028625 (s,v)) u)) *
      _root_.GD.N0213.N0493.d007990 (_root_.GD.N0101.N0367.d028640 u) * _root_.GD.N0208.N0455.d007937 N s ^ 2) *
      (_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N (v - _root_.GD.N0101.N0367.d028640 u)) ^ 2 := by ring
    _ = _ := by rw [_root_.GD.N0101.N0367.d028643 N s v u hu]

end
end GD.N0101.N0367

#print axioms _root_.GD.N0101.N0367.d028641
#print axioms _root_.GD.N0101.N0367.d028642
#print axioms _root_.GD.N0101.N0367.d028643
#print axioms _root_.GD.N0101.N0367.d028644
#print axioms _root_.GD.N0101.N0367.d028645
