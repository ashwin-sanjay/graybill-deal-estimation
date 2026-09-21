import GD.Module1816
import Mathlib.RingTheory.Algebraic.Basic

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0248

open Polynomial

noncomputable section

def d030113 (m n : ℕ) (a b x y : ℚ) : ℚ[X] :=
  C (m+n : ℚ) * X^3 - C ((m : ℚ)*(x+2*y)+(n : ℚ)*(y+2*x)) * X^2 +
    C ((m : ℚ)*(b+y^2+2*x*y)+(n : ℚ)*(a+x^2+2*x*y)) * X -
    C ((m : ℚ)*x*(b+y^2)+(n : ℚ)*y*(a+x^2))

theorem d030114 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (a b x y : ℚ) : _root_.GD.N0005.N0248.d030113 m n a b x y ≠ 0 := by
  intro hz
  have hc : (_root_.GD.N0005.N0248.d030113 m n a b x y).coeff 3 = (m+n : ℚ) := by
    simp only [_root_.GD.N0005.N0248.d030113, coeff_sub, coeff_add, coeff_C_mul,
      coeff_X_pow, coeff_X, coeff_C]
    norm_num
  rw [hz, coeff_zero] at hc
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  linarith

theorem d030115 (m n : ℕ) (a b x y : ℚ) (u : ℝ) :
    aeval u (_root_.GD.N0005.N0248.d030113 m n a b x y) =
      (_root_.GD.N0005.N0248.d030073 m n a b x y).eval u := by
  simp [_root_.GD.N0005.N0248.d030113, _root_.GD.N0005.N0248.d030073]

theorem d030116 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {a b x y : ℚ} (ha : 0 < a) (hb : 0 < b) {u : ℝ}
    (hu : deriv (_root_.GD.N0005.N0248.d030071 m n a b x y) u = 0) : IsAlgebraic ℚ u := by
  refine ⟨_root_.GD.N0005.N0248.d030113 m n a b x y,
    _root_.GD.N0005.N0248.d030114 hm hn a b x y, ?_⟩
  rw [_root_.GD.N0005.N0248.d030115]
  exact (_root_.GD.N0005.N0248.d030080 (by exact_mod_cast ha) (by exact_mod_cast hb)).1 hu

theorem d030117 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {a b x y : ℚ} (ha : 0 < a) (hb : 0 < b) {u : ℝ}
    (hu : ∀ v : ℝ, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u) :
    IsAlgebraic ℚ u :=
  _root_.GD.N0005.N0248.d030116 hm hn ha hb (_root_.GD.N0005.N0248.d030086 hu)

end
end GD.N0005.N0248

#print axioms _root_.GD.N0005.N0248.d030116
#print axioms _root_.GD.N0005.N0248.d030117
