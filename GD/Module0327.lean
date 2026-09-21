import GD.Module0305
import Mathlib.Analysis.Normed.Module.FiniteDimension
























open Set

namespace GD
namespace N0238
namespace N0758

noncomputable section

variable {Θ E : Type*}
variable [TopologicalSpace Θ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]


def d004889 (K : Set Θ) : Set (Θ × E) :=
  K ×ˢ Metric.sphere (0 : E) 1


theorem d004890
    (K : Set Θ) (hK : IsCompact K) :
    IsCompact (_root_.GD.N0238.N0758.d004889 (E := E) K) := by
  exact hK.prod (isCompact_sphere (0 : E) 1)





theorem d004891
    (K : Set Θ)
    (energy : Θ × E → ℝ)
    (hzero :
      ∀ θ ∈ K, ∀ x : E, energy (θ, x) = 0 → x = 0) :
    ¬ ∃ z, z ∈ _root_.GD.N0238.N0758.d004889 (E := E) K ∧ energy z = 0 := by
  rintro ⟨⟨θ, x⟩, hz, henergy⟩
  have hxzero : x = 0 := hzero θ hz.1 x henergy
  subst x
  simpa [_root_.GD.N0238.N0758.d004889, Metric.mem_sphere] using hz.2








theorem d004892
    (K : Set Θ) (hK : IsCompact K)
    (energy : Θ × E → ℝ) (henergy : Continuous energy)
    (hnonneg :
      ∀ θ ∈ K, ∀ x : E, 0 ≤ energy (θ, x))
    (hzero :
      ∀ θ ∈ K, ∀ x : E, energy (θ, x) = 0 → x = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ θ ∈ K, ∀ x ∈ Metric.sphere (0 : E) 1,
        δ ≤ energy (θ, x) := by
  have hcompact :
      IsCompact (_root_.GD.N0238.N0758.d004889 (E := E) K) :=
    _root_.GD.N0238.N0758.d004890 K hK
  have hnonneg_relation :
      ∀ z ∈ _root_.GD.N0238.N0758.d004889 (E := E) K, 0 ≤ energy z := by
    rintro ⟨θ, x⟩ hz
    exact hnonneg θ hz.1 x
  have hdisc :
      _root_.GD.N0238.N0752.d004388
          (_root_.GD.N0238.N0758.d004889 (E := E) K) energy = ∅ := by
    rw [_root_.GD.N0238.N0752.d004393]
    exact _root_.GD.N0238.N0758.d004891 K energy hzero
  obtain ⟨δ, hδ, hmargin⟩ :=
    (_root_.GD.N0238.N0752.d004394
        (_root_.GD.N0238.N0758.d004889 (E := E) K) hcompact
        energy henergy hnonneg_relation).mp hdisc
  exact
    ⟨δ, hδ, fun θ hθ x hx ↦
      hmargin (θ, x) ⟨hθ, hx⟩⟩








theorem d004893
    (K : Set Θ) (hK : IsCompact K)
    (energy : Θ × E → ℝ) (henergy : Continuous energy)
    (hnonneg :
      ∀ θ ∈ K, ∀ x : E, 0 ≤ energy (θ, x))
    (hhom :
      ∀ θ ∈ K, ∀ r : ℝ, ∀ x : E,
        energy (θ, r • x) = r ^ 2 * energy (θ, x))
    (hzero :
      ∀ θ ∈ K, ∀ x : E, energy (θ, x) = 0 → x = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ θ ∈ K, ∀ x : E,
        δ * ‖x‖ ^ 2 ≤ energy (θ, x) := by
  obtain ⟨δ, hδ, hunit⟩ :=
    _root_.GD.N0238.N0758.d004892 K hK energy henergy hnonneg hzero
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ x
  by_cases hx : x = 0
  · subst x
    have henergy_zero : energy (θ, (0 : E)) = 0 := by
      have hscale := hhom θ hθ 0 (0 : E)
      simpa using hscale
    simp [henergy_zero]
  · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let y : E := ‖x‖⁻¹ • x
    have hy_norm : ‖y‖ = 1 := by
      simp [y, norm_smul, hnorm]
    have hy_sphere : y ∈ Metric.sphere (0 : E) 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hy_norm
    have hmargin : δ ≤ energy (θ, y) :=
      hunit θ hθ y hy_sphere
    have hscale :
        energy (θ, y) = ‖x‖⁻¹ ^ 2 * energy (θ, x) := by
      simpa [y] using hhom θ hθ ‖x‖⁻¹ x
    rw [hscale] at hmargin
    have hnorm_sq_pos : 0 < ‖x‖ ^ 2 :=
      sq_pos_of_ne_zero hnorm
    have hmul :=
      mul_le_mul_of_nonneg_right hmargin (le_of_lt hnorm_sq_pos)
    calc
      δ * ‖x‖ ^ 2 ≤
          (‖x‖⁻¹ ^ 2 * energy (θ, x)) * ‖x‖ ^ 2 := hmul
      _ = energy (θ, x) := by
        field_simp





theorem d004894
    (K : Set Θ) (energy : Θ × E → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hcoercive :
      ∀ θ ∈ K, ∀ x : E,
        δ * ‖x‖ ^ 2 ≤ energy (θ, x)) :
    ∀ θ ∈ K, ∀ x : E, energy (θ, x) = 0 → x = 0 := by
  intro θ hθ x henergy
  have hlower := hcoercive θ hθ x
  rw [henergy] at hlower
  have hnorm_zero : ‖x‖ = 0 := by
    by_contra hne
    have hsq_pos : 0 < ‖x‖ ^ 2 :=
      sq_pos_of_ne_zero hne
    have : 0 < δ * ‖x‖ ^ 2 := mul_pos hδ hsq_pos
    linarith
  exact norm_eq_zero.mp hnorm_zero





theorem d004895
    (K : Set Θ) (hK : IsCompact K)
    (energy : Θ × E → ℝ) (henergy : Continuous energy)
    (hnonneg :
      ∀ θ ∈ K, ∀ x : E, 0 ≤ energy (θ, x))
    (hhom :
      ∀ θ ∈ K, ∀ r : ℝ, ∀ x : E,
        energy (θ, r • x) = r ^ 2 * energy (θ, x)) :
    (∀ θ ∈ K, ∀ x : E, energy (θ, x) = 0 → x = 0) ↔
      ∃ δ : ℝ, 0 < δ ∧
        ∀ θ ∈ K, ∀ x : E,
          δ * ‖x‖ ^ 2 ≤ energy (θ, x) := by
  constructor
  · exact
      _root_.GD.N0238.N0758.d004893
        K hK energy henergy hnonneg hhom
  · rintro ⟨δ, hδ, hcoercive⟩
    exact
      _root_.GD.N0238.N0758.d004894
        K energy δ hδ hcoercive








theorem d004896
    (K : Set Θ) (hK : IsCompact K)
    (energy : Θ × E → ℝ) (henergy : Continuous energy)
    (hnonneg :
      ∀ θ ∈ K, ∀ x : E, 0 ≤ energy (θ, x))
    (hhom :
      ∀ θ ∈ K, ∀ r : ℝ, ∀ x : E,
        energy (θ, r • x) = r ^ 2 * energy (θ, x)) :
    (∃ θ ∈ K, ∃ x : E, x ≠ 0 ∧ energy (θ, x) = 0) ∨
      ∃ δ : ℝ, 0 < δ ∧
        ∀ θ ∈ K, ∀ x : E,
          δ * ‖x‖ ^ 2 ≤ energy (θ, x) := by
  classical
  by_cases hzero :
      ∀ θ ∈ K, ∀ x : E, energy (θ, x) = 0 → x = 0
  · exact Or.inr <|
      _root_.GD.N0238.N0758.d004893
        K hK energy henergy hnonneg hhom hzero
  · left
    push Not at hzero
    obtain ⟨θ, hθ, x, henergy_zero, hx⟩ := hzero
    exact ⟨θ, hθ, x, hx, henergy_zero⟩

end

end N0758
end N0238
end GD
