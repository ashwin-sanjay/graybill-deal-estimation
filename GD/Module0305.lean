import GD.Module0291























open Set

namespace GD
namespace N0238
namespace N0752

noncomputable section

variable {Θ X : Type*}
  [TopologicalSpace Θ] [TopologicalSpace X]


def d004387
    (physical : Set (Θ × X)) (energy : Θ × X → ℝ) :
    Set (Θ × X) :=
  physical ∩ {z | energy z = 0}


def d004388
    (physical : Set (Θ × X)) (energy : Θ × X → ℝ) :
    Set Θ :=
  Prod.fst '' _root_.GD.N0238.N0752.d004387 physical energy

@[simp]
theorem d004389
    (physical : Set (Θ × X)) (energy : Θ × X → ℝ)
    (z : Θ × X) :
    z ∈ _root_.GD.N0238.N0752.d004387 physical energy ↔
      z ∈ physical ∧ energy z = 0 :=
  Iff.rfl


theorem d004390
    (physical : Set (Θ × X)) (energy : Θ × X → ℝ)
    (θ : Θ) :
    θ ∈ _root_.GD.N0238.N0752.d004388 physical energy ↔
      ∃ x : X, (θ, x) ∈ physical ∧ energy (θ, x) = 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz.1, hz.2⟩
  · rintro ⟨x, hx, hzero⟩
    exact ⟨(θ, x), ⟨hx, hzero⟩, rfl⟩



theorem d004391
    (physical : Set (Θ × X)) (hphysical : IsCompact physical)
    (energy : Θ × X → ℝ) (henergy : Continuous energy) :
    IsCompact (_root_.GD.N0238.N0752.d004387 physical energy) := by
  apply hphysical.inter_right
  exact isClosed_eq henergy continuous_const


theorem d004392
    (physical : Set (Θ × X)) (hphysical : IsCompact physical)
    (energy : Θ × X → ℝ) (henergy : Continuous energy) :
    IsCompact (_root_.GD.N0238.N0752.d004388 physical energy) := by
  exact
    (_root_.GD.N0238.N0752.d004391
      physical hphysical energy henergy).image continuous_fst



theorem d004393
    (physical : Set (Θ × X)) (energy : Θ × X → ℝ) :
    _root_.GD.N0238.N0752.d004388 physical energy = ∅ ↔
      ¬ ∃ z, z ∈ physical ∧ energy z = 0 := by
  constructor
  · intro hempty
    rintro ⟨z, hz, hzero⟩
    have : z.1 ∈ _root_.GD.N0238.N0752.d004388 physical energy := by
      rw [_root_.GD.N0238.N0752.d004390]
      exact ⟨z.2, hz, hzero⟩
    simpa [hempty] using this
  · intro hno
    ext θ
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hθ
    obtain ⟨x, hx, hzero⟩ :=
      (_root_.GD.N0238.N0752.d004390 physical energy θ).mp hθ
    exact hno ⟨(θ, x), hx, hzero⟩







theorem d004394
    (physical : Set (Θ × X)) (hphysical : IsCompact physical)
    (energy : Θ × X → ℝ) (henergy : Continuous energy)
    (henergy_nonneg : ∀ z ∈ physical, 0 ≤ energy z) :
    _root_.GD.N0238.N0752.d004388 physical energy = ∅ ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ physical, δ ≤ energy z := by
  rw [_root_.GD.N0238.N0752.d004393]
  simpa using
    (_root_.GD.N0238.N0748.d004289
        physical hphysical
        (fun z : Θ × X ↦ energy z) ({0} : Set ℝ)
        energy henergy henergy_nonneg
        (fun z _ ↦ by simp))





theorem d004395
    (physical : Set (Θ × X)) (hphysical : IsCompact physical)
    (energy : Θ × X → ℝ) (henergy : Continuous energy)
    (henergy_nonneg : ∀ z ∈ physical, 0 ≤ energy z) :
    (∃ θ : Θ, ∃ x : X,
        (θ, x) ∈ physical ∧ energy (θ, x) = 0) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ physical, δ ≤ energy z := by
  by_cases hdisc : _root_.GD.N0238.N0752.d004388 physical energy = ∅
  · exact Or.inr <|
      (_root_.GD.N0238.N0752.d004394
        physical hphysical energy henergy henergy_nonneg).mp hdisc
  · left
    have hnonempty :
        (_root_.GD.N0238.N0752.d004388 physical energy).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hdisc
    obtain ⟨θ, hθ⟩ := hnonempty
    obtain ⟨x, hx, hzero⟩ :=
      (_root_.GD.N0238.N0752.d004390 physical energy θ).mp hθ
    exact ⟨θ, x, hx, hzero⟩









theorem d004396
    (physical : Set (Θ × X)) (hphysical : IsCompact physical)
    (cell : Set Θ) (hcell : IsClosed cell)
    (energy : Θ × X → ℝ) (henergy : Continuous energy)
    (henergy_nonneg : ∀ z ∈ physical, 0 ≤ energy z)
    (havoid :
      Disjoint cell (_root_.GD.N0238.N0752.d004388 physical energy)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ physical, z.1 ∈ cell → δ ≤ energy z := by
  let restricted : Set (Θ × X) :=
    physical ∩ Prod.fst ⁻¹' cell
  have hrestricted : IsCompact restricted := by
    exact hphysical.inter_right (hcell.preimage continuous_fst)
  have hnonneg :
      ∀ z ∈ restricted, 0 ≤ energy z := by
    intro z hz
    exact henergy_nonneg z hz.1
  have hnozero :
      ¬ ∃ z, z ∈ restricted ∧ energy z = 0 := by
    rintro ⟨z, hz, hzero⟩
    have hzdisc :
        z.1 ∈ _root_.GD.N0238.N0752.d004388 physical energy := by
      rw [_root_.GD.N0238.N0752.d004390]
      exact ⟨z.2, hz.1, hzero⟩
    exact Set.disjoint_left.mp havoid hz.2 hzdisc
  obtain ⟨δ, hδ, hmargin⟩ :=
    (_root_.GD.N0238.N0748.d004289
      restricted hrestricted
      (fun z : Θ × X ↦ energy z) ({0} : Set ℝ)
      energy henergy hnonneg
      (fun z _ ↦ by simp)).mp hnozero
  refine ⟨δ, hδ, ?_⟩
  intro z hzphysical hzcell
  exact hmargin z ⟨hzphysical, hzcell⟩

end

end N0752
end N0238
end GD
