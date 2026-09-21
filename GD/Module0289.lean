import GD.Module0003
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Ring


















namespace GD
namespace N0237
namespace N0747


def d004276
    {Ω : Type*}
    (ε : ℝ) (residual correction : Ω → ℝ) : Ω → ℝ :=
  fun ω ↦
    (residual ω - ε * correction ω) ^ 2 -
      (residual ω) ^ 2


theorem d004277
    {Ω : Type*}
    (ε : ℝ) (residual correction : Ω → ℝ) (ω : Ω) :
    _root_.GD.N0237.N0747.d004276 ε residual correction ω =
      ε ^ 2 * (correction ω) ^ 2 -
        2 * ε * (residual ω * correction ω) := by
  simp only [_root_.GD.N0237.N0747.d004276]
  ring





theorem d004278
    {Ω : Type*}
    (expect : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (ε : ℝ) (residual correction : Ω → ℝ) :
    expect (_root_.GD.N0237.N0747.d004276 ε residual correction) =
      ε ^ 2 * expect (fun ω ↦ (correction ω) ^ 2) -
        2 * ε * expect (fun ω ↦ residual ω * correction ω) := by
  have hfun :
      _root_.GD.N0237.N0747.d004276 ε residual correction =
        ε ^ 2 • (fun ω ↦ (correction ω) ^ 2) -
          (2 * ε) • (fun ω ↦ residual ω * correction ω) := by
    funext ω
    change
      (residual ω - ε * correction ω) ^ 2 - (residual ω) ^ 2 =
        ε ^ 2 * (correction ω) ^ 2 -
          (2 * ε) * (residual ω * correction ω)
    ring
  rw [hfun, map_sub, map_smul, map_smul]
  simp only [smul_eq_mul]





theorem d004279
    {ι Ω : Type*}
    (expect : ι → (Ω → ℝ) →ₗ[ℝ] ℝ)
    (residual correction : ι → Ω → ℝ)
    (δ M ε : ℝ)
    (hε : 0 < ε)
    (hgain :
      ∀ i, δ ≤
        expect i (fun ω ↦ residual i ω * correction i ω))
    (henergy :
      ∀ i, expect i (fun ω ↦ (correction i ω) ^ 2) ≤ M)
    (hstep : ε * M < 2 * δ) :
    ∀ i,
      expect i
        (_root_.GD.N0237.N0747.d004276 ε (residual i) (correction i)) < 0 := by
  intro i
  rw [_root_.GD.N0237.N0747.d004278]
  exact
    _root_.GD.N0229.N0552.d000025
      ε
      (expect i (fun ω ↦ (correction i ω) ^ 2))
      (expect i (fun ω ↦ residual i ω * correction i ω))
      δ M hε (hgain i) (henergy i) hstep

end N0747
end N0237
end GD
