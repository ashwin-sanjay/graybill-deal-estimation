import GD.Module0371
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory TopologicalSpace
open scoped FourierTransform Topology BigOperators

namespace GD.N0106.N0428.N0765.N1652
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1613


structure d005813 (g : ℝ → ℂ) : Prop where
  continuous : Continuous g
  translatedNorm : ∀ K : Compacts ℝ, Summable fun n : ℤ =>
    ‖((⟨g, continuous⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight n)).restrict K‖
  fourierSummable : Summable fun n : ℤ => 𝓕 g n


theorem d005814 {g : ℝ → ℂ} {AL AR a b C k : ℝ}
    (hg : Continuous g) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hleft : ∀ x : ℝ, x ≤ 0 → ‖g x‖ ≤ AL * Real.exp (a * x))
    (hright : ∀ x : ℝ, 0 ≤ x → ‖g x‖ ≤ AR * Real.exp (-b * x))
    (hfourier : ∀ n : ℤ, ‖𝓕 g n‖ ≤ C * Real.exp (-k * |(n : ℝ)|)) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 g :=
  ⟨hg, _root_.GD.N0106.N0428.N0765.N1613.d005626 hg ha hb hleft hright,
    _root_.GD.N0106.N0428.N0765.N1613.d005630 hk hfourier⟩

theorem d005813.d005815 {g : ℝ → ℂ} (hg : _root_.GD.N0106.N0428.N0765.N1652.d005813 g) (x : ℝ) :
    (∑' n : ℤ, g (x + n)) =
      ∑' n : ℤ, 𝓕 g n * fourier n (x : UnitAddCircle) := by
  exact Real.tsum_eq_tsum_fourier (f := (⟨g, hg.continuous⟩ : C(ℝ, ℂ)))
    hg.translatedNorm hg.fourierSummable x


def d005816 (f : ℝ × ℝ → ℂ) (eta a : ℝ) : ℂ :=
  𝓕 (fun b : ℝ => f (a, b)) eta


def d005817 (f : ℝ × ℝ → ℂ) (xi eta : ℝ) : ℂ :=
  𝓕 (_root_.GD.N0106.N0428.N0765.N1652.d005816 f eta) xi

theorem d005818 (f : ℝ × ℝ → ℂ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 f 0 0 = ∫ a : ℝ, ∫ b : ℝ, f (a, b) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1652.d005817, _root_.GD.N0106.N0428.N0765.N1652.d005816, _root_.GD.N0106.N0428.N0765.N1613.d005632]


theorem d005819 {s : ℤ × ℤ → ℂ} {u v : ℤ → ℝ}
    (hu : Summable u) (hv : Summable v) (hu0 : ∀ m, 0 ≤ u m) (hv0 : ∀ n, 0 ≤ v n)
    (hbound : ∀ p : ℤ × ℤ, ‖s p‖ ≤ u p.1 * v p.2) : Summable s := by
  have huv : Summable (fun p : ℤ × ℤ => u p.1 * v p.2) :=
    hu.mul_of_nonneg hv (fun m => hu0 m) (fun n => hv0 n)
  exact Summable.of_norm_bounded huv hbound



theorem d005820 {f : ℝ × ℝ → ℂ}
    (hrows : ∀ a : ℝ, _root_.GD.N0106.N0428.N0765.N1652.d005813 (fun b : ℝ => f (a, b)))
    (hcolumns : ∀ n : ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005813 (_root_.GD.N0106.N0428.N0765.N1652.d005816 f n))
    (x y : ℝ)
    (hsamples : Summable (fun p : ℤ × ℤ => f (x + p.1, y + p.2)))
    (hcross : Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005816 f p.2 (x + p.1)))
    (hcoeff : Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005817 f p.1 p.2)) :
    (∑' p : ℤ × ℤ, f (x + p.1, y + p.2)) =
      ∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005817 f p.1 p.2 *
        fourier p.1 (x : UnitAddCircle) * fourier p.2 (y : UnitAddCircle) := by
  have hphaseX (m : ℤ) : ‖fourier m (x : UnitAddCircle)‖ = 1 := Circle.norm_coe _
  have hphaseY (n : ℤ) : ‖fourier n (y : UnitAddCircle)‖ = 1 := Circle.norm_coe _
  let cross (p : ℤ × ℤ) : ℂ :=
    _root_.GD.N0106.N0428.N0765.N1652.d005816 f p.2 (x + p.1) * fourier p.2 (y : UnitAddCircle)
  have hcross' : Summable cross := by
    apply Summable.of_norm
    simpa only [cross, norm_mul, hphaseY, mul_one] using hcross.norm
  let mode (p : ℤ × ℤ) : ℂ := _root_.GD.N0106.N0428.N0765.N1652.d005817 f p.1 p.2 *
    fourier p.1 (x : UnitAddCircle) * fourier p.2 (y : UnitAddCircle)
  have hmode : Summable mode := by
    apply Summable.of_norm
    simpa only [mode, norm_mul, hphaseX, hphaseY, mul_one] using hcoeff.norm
  calc (∑' p : ℤ × ℤ, f (x + p.1, y + p.2))
      = ∑' m : ℤ, ∑' n : ℤ, f (x + m, y + n) := hsamples.tsum_prod
    _ = ∑' m : ℤ, ∑' n : ℤ,
        _root_.GD.N0106.N0428.N0765.N1652.d005816 f n (x + m) * fourier n (y : UnitAddCircle) := by
      apply tsum_congr
      intro m
      exact (hrows (x + m)).d005815 y
    _ = ∑' n : ℤ, ∑' m : ℤ,
        _root_.GD.N0106.N0428.N0765.N1652.d005816 f n (x + m) * fourier n (y : UnitAddCircle) := by
      exact (Summable.tsum_comm (f := fun m n : ℤ =>
        _root_.GD.N0106.N0428.N0765.N1652.d005816 f n (x + m) * fourier n (y : UnitAddCircle)) hcross').symm
    _ = ∑' n : ℤ, (∑' m : ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005816 f n (x + m)) *
        fourier n (y : UnitAddCircle) := by simp_rw [tsum_mul_right]
    _ = ∑' n : ℤ, (∑' m : ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005817 f m n *
        fourier m (x : UnitAddCircle)) * fourier n (y : UnitAddCircle) := by
      apply tsum_congr
      intro n
      exact congrArg (fun z : ℂ => z * fourier n (y : UnitAddCircle))
        ((hcolumns n).d005815 x)
    _ = ∑' n : ℤ, ∑' m : ℤ, mode (m, n) := by
      simp only [mode, tsum_mul_right]
    _ = ∑' m : ℤ, ∑' n : ℤ, mode (m, n) :=
      Summable.tsum_comm (f := fun m n : ℤ => mode (m, n)) hmode
    _ = ∑' p : ℤ × ℤ, mode p := hmode.tsum_prod.symm


theorem d005821 (g : ℝ → ℂ) (r xi : ℝ) :
    𝓕 (fun x : ℝ => r • g x) xi = r • 𝓕 g xi := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_comm _ r]
  exact integral_smul r (fun x : ℝ =>
    Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I) • g x)


def d005822 (f : ℝ × ℝ → ℂ) (h : ℝ) (p : ℝ × ℝ) : ℂ := f (h * p.1, h * p.2)

theorem d005823 (f : ℝ × ℝ → ℂ) {h : ℝ} (hh : 0 < h) (eta a : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 f h) eta a = h⁻¹ • _root_.GD.N0106.N0428.N0765.N1652.d005816 f (eta / h) (h * a) := by
  exact _root_.GD.N0106.N0428.N0765.N1613.d005634 (fun b : ℝ => f (h * a, b)) hh eta


theorem d005824 (f : ℝ × ℝ → ℂ) {h : ℝ} (hh : 0 < h) (xi eta : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1652.d005822 f h) xi eta =
      (h⁻¹ * h⁻¹) • _root_.GD.N0106.N0428.N0765.N1652.d005817 f (xi / h) (eta / h) := by
  have he : _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 f h) eta =
      fun a : ℝ => h⁻¹ • _root_.GD.N0106.N0428.N0765.N1652.d005816 f (eta / h) (h * a) := by
    funext a
    exact _root_.GD.N0106.N0428.N0765.N1652.d005823 f hh eta a
  rw [_root_.GD.N0106.N0428.N0765.N1652.d005817, he, _root_.GD.N0106.N0428.N0765.N1652.d005821, _root_.GD.N0106.N0428.N0765.N1613.d005634 _ hh, smul_smul]
  rfl


theorem d005825 (f : ℝ × ℝ → ℂ) {h : ℝ} (hh : 0 < h) (xi eta : ℝ) :
    h ^ 2 • _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1652.d005822 f h) xi eta = _root_.GD.N0106.N0428.N0765.N1652.d005817 f (xi / h) (eta / h) := by
  rw [_root_.GD.N0106.N0428.N0765.N1652.d005824 f hh, smul_smul]
  have hcancel : h ^ 2 * (h⁻¹ * h⁻¹) = 1 := by
    field_simp [hh.ne']
    <;> ring
  rw [hcancel, one_smul]



theorem d005826 {f : ℝ × ℝ → ℂ} {h : ℝ} (hh : 0 < h)
    (hrows : ∀ a : ℝ, _root_.GD.N0106.N0428.N0765.N1652.d005813 (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1652.d005822 f h (a, b)))
    (hcolumns : ∀ n : ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005813 (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 f h) n))
    (x y : ℝ)
    (hsamples : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005822 f h (x / h + p.1, y / h + p.2)))
    (hcross : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1652.d005822 f h) p.2 (x / h + p.1)))
    (hcoeff : Summable (fun p : ℤ × ℤ => _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1652.d005822 f h) p.1 p.2)) :
    h ^ 2 • (∑' p : ℤ × ℤ, f (x + h * p.1, y + h * p.2)) =
      ∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005817 f (p.1 / h) (p.2 / h) *
        fourier p.1 ((x / h : ℝ) : UnitAddCircle) *
        fourier p.2 ((y / h : ℝ) : UnitAddCircle) := by
  have hp := _root_.GD.N0106.N0428.N0765.N1652.d005820 hrows hcolumns (x / h) (y / h) hsamples hcross hcoeff
  have hpoint (p : ℤ × ℤ) : _root_.GD.N0106.N0428.N0765.N1652.d005822 f h (x / h + p.1, y / h + p.2) =
      f (x + h * p.1, y + h * p.2) := by
    unfold _root_.GD.N0106.N0428.N0765.N1652.d005822
    apply congrArg f
    apply Prod.ext <;> dsimp <;> field_simp [hh.ne'] <;> ring
  simp_rw [hpoint] at hp
  rw [hp, ← tsum_const_smul'']
  apply tsum_congr
  intro p
  rw [← smul_mul_assoc, ← smul_mul_assoc, _root_.GD.N0106.N0428.N0765.N1652.d005825 f hh]

end
end GD.N0106.N0428.N0765.N1652

#print axioms _root_.GD.N0106.N0428.N0765.N1652.d005814
#print axioms _root_.GD.N0106.N0428.N0765.N1652.d005813.d005815
#print axioms _root_.GD.N0106.N0428.N0765.N1652.d005818
#print axioms _root_.GD.N0106.N0428.N0765.N1652.d005819
#print axioms _root_.GD.N0106.N0428.N0765.N1652.d005820
#print axioms _root_.GD.N0106.N0428.N0765.N1652.d005824
#print axioms _root_.GD.N0106.N0428.N0765.N1652.d005825
#print axioms _root_.GD.N0106.N0428.N0765.N1652.d005826
