import GD.Module0294
import Mathlib.Analysis.Normed.Module.FiniteDimension


























open Set
open scoped BigOperators

namespace GD
namespace N0233
namespace N0723

noncomputable section

open _root_.GD.N0238.N0751

variable {E Θ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]


def d004309
    (a : Θ → E →L[ℝ] ℝ) (θ : Θ) (x : E) : ℝ :=
  (a θ x) ^ 2


def d004310
    (a : Θ → E →L[ℝ] ℝ) (u : Finset Θ) (x : E) : ℝ :=
  ∑ θ ∈ u, (a θ x) ^ 2

theorem d004311
    (a : Θ → E →L[ℝ] ℝ) (u : Finset Θ) (x : E) :
    _root_.GD.N0233.N0723.d004310 a u x =
      _root_.GD.N0238.N0751.d004301 u (_root_.GD.N0233.N0723.d004309 a) x :=
  rfl


theorem d004312
    (a : Θ → E →L[ℝ] ℝ) (θ : Θ) :
    Continuous (_root_.GD.N0233.N0723.d004309 a θ) := by
  unfold _root_.GD.N0233.N0723.d004309
  fun_prop


theorem d004313
    (a : Θ → E →L[ℝ] ℝ) (θ : Θ) (x : E) :
    0 ≤ _root_.GD.N0233.N0723.d004309 a θ x :=
  sq_nonneg _





theorem d004314
    (a : Θ → E →L[ℝ] ℝ)
    (hfaithful : ∀ x : E, (∀ θ, a θ x = 0) → x = 0) :
    ¬ ∃ x, x ∈ Metric.sphere (0 : E) 1 ∧
      ∀ θ, _root_.GD.N0233.N0723.d004309 a θ x = 0 := by
  rintro ⟨x, hx, hzero⟩
  have hall : ∀ θ, a θ x = 0 := by
    intro θ
    exact sq_eq_zero_iff.mp (hzero θ)
  have hxzero : x = 0 := hfaithful x hall
  subst x
  simp at hx





theorem d004315
    (a : Θ → E →L[ℝ] ℝ)
    (hfaithful : ∀ x : E, (∀ θ, a θ x = 0) → x = 0) :
    ∃ u : Finset Θ, ∃ δ : ℝ,
      0 < δ ∧
      ∀ x ∈ Metric.sphere (0 : E) 1,
        δ ≤ _root_.GD.N0233.N0723.d004310 a u x := by
  obtain ⟨u, δ, hδ, hmargin⟩ :=
    _root_.GD.N0238.N0751.d004305
      (Metric.sphere (0 : E) 1)
      (isCompact_sphere (0 : E) 1)
      (_root_.GD.N0233.N0723.d004309 a)
      (_root_.GD.N0233.N0723.d004312 a)
      (fun θ x _ ↦ _root_.GD.N0233.N0723.d004313 a θ x)
      (_root_.GD.N0233.N0723.d004314 a hfaithful)
  exact
    ⟨u, δ, hδ, fun x hx ↦ by
      simpa [_root_.GD.N0233.N0723.d004311] using hmargin x hx⟩


theorem d004316
    (a : Θ → E →L[ℝ] ℝ) (u : Finset Θ)
    (r : ℝ) (x : E) :
    _root_.GD.N0233.N0723.d004310 a u (r • x) =
      r ^ 2 * _root_.GD.N0233.N0723.d004310 a u x := by
  unfold _root_.GD.N0233.N0723.d004310
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ hθ
  simp
  ring








theorem d004317
    (a : Θ → E →L[ℝ] ℝ)
    (hfaithful : ∀ x : E, (∀ θ, a θ x = 0) → x = 0) :
    ∃ u : Finset Θ, ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : E,
        δ * ‖x‖ ^ 2 ≤ _root_.GD.N0233.N0723.d004310 a u x := by
  obtain ⟨u, δ, hδ, hunit⟩ :=
    _root_.GD.N0233.N0723.d004315
      a hfaithful
  refine ⟨u, δ, hδ, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [_root_.GD.N0233.N0723.d004310]
  · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let y : E := ‖x‖⁻¹ • x
    have hy_norm : ‖y‖ = 1 := by
      simp [y, norm_smul, hnorm]
    have hy_sphere : y ∈ Metric.sphere (0 : E) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hy_norm
    have hmargin : δ ≤ _root_.GD.N0233.N0723.d004310 a u y :=
      hunit y hy_sphere
    have hscale :
        _root_.GD.N0233.N0723.d004310 a u y =
          ‖x‖⁻¹ ^ 2 * _root_.GD.N0233.N0723.d004310 a u x := by
      simpa [y] using _root_.GD.N0233.N0723.d004316 a u ‖x‖⁻¹ x
    rw [hscale] at hmargin
    have hnorm_sq_pos : 0 < ‖x‖ ^ 2 :=
      sq_pos_of_ne_zero hnorm
    have hmul :=
      mul_le_mul_of_nonneg_right hmargin (le_of_lt hnorm_sq_pos)
    calc
      δ * ‖x‖ ^ 2 ≤
          (‖x‖⁻¹ ^ 2 * _root_.GD.N0233.N0723.d004310 a u x) *
            ‖x‖ ^ 2 := hmul
      _ = _root_.GD.N0233.N0723.d004310 a u x := by
        field_simp



theorem d004318
    (a : Θ → E →L[ℝ] ℝ)
    (u : Finset Θ) (δ : ℝ) (hδ : 0 < δ)
    (hcoercive :
      ∀ x : E,
        δ * ‖x‖ ^ 2 ≤ _root_.GD.N0233.N0723.d004310 a u x) :
    ∀ x : E, (∀ θ, a θ x = 0) → x = 0 := by
  intro x hzero
  have henergy_zero : _root_.GD.N0233.N0723.d004310 a u x = 0 := by
    simp [_root_.GD.N0233.N0723.d004310, hzero]
  have hlower := hcoercive x
  rw [henergy_zero] at hlower
  have hnorm_zero : ‖x‖ = 0 := by
    by_contra hne
    have hsq_pos : 0 < ‖x‖ ^ 2 :=
      sq_pos_of_ne_zero hne
    have hproduct_pos : 0 < δ * ‖x‖ ^ 2 :=
      mul_pos hδ hsq_pos
    linarith
  exact norm_eq_zero.mp hnorm_zero





theorem d004319
    (a : Θ → E →L[ℝ] ℝ) :
    (∀ x : E, (∀ θ, a θ x = 0) → x = 0) ↔
      ∃ u : Finset Θ, ∃ δ : ℝ,
        0 < δ ∧
        ∀ x : E,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0233.N0723.d004310 a u x := by
  constructor
  · exact _root_.GD.N0233.N0723.d004317 a
  · rintro ⟨u, δ, hδ, hcoercive⟩
    exact
      _root_.GD.N0233.N0723.d004318
        a u δ hδ hcoercive







theorem d004320
    (a : Θ → E →L[ℝ] ℝ) :
    (∃ x : E, x ≠ 0 ∧ ∀ θ, a θ x = 0) ∨
      ∃ u : Finset Θ, ∃ δ : ℝ,
        0 < δ ∧
        ∀ x : E,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0233.N0723.d004310 a u x := by
  classical
  by_cases hfaithful :
      ∀ x : E, (∀ θ, a θ x = 0) → x = 0
  · exact Or.inr <|
      _root_.GD.N0233.N0723.d004317
        a hfaithful
  · left
    push Not at hfaithful
    obtain ⟨x, hall, hx⟩ := hfaithful
    exact ⟨x, hx, hall⟩

end

end N0723
end N0233
end GD
