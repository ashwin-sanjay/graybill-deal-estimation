import GD.Module0100
import GD.Module0059
import GD.Module0041
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuity.Basic






















open MeasureTheory Set Topology

namespace GD
namespace N0230
namespace N0585

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0659

variable {G Theta D : Type*}


def d001305
    (risk : Theta → D → ENNReal) (objective : D → ℝ) : Prop :=
  ∀ ⦃e d : D⦄, _root_.GD.N0230.N0608.d000672 risk e d → objective e ≤ objective d



def d001306 (objective : D → ℝ) (C : Set D) : Prop :=
  ∀ ⦃p q : D⦄, p ∈ C → q ∈ C →
    IsMinOn objective C p → IsMinOn objective C q → p = q



def d001307
    [Group G] [MulAction G D]
    (objective : D → ℝ) (C : Set D) (weight : G → ℝ) : Prop :=
  ∀ g d, d ∈ C → objective (g • d) = weight g * objective d




def d001308
    [Group G] [MulAction G D]
    (objective : D → ℝ) (C : Set D)
    (weight offset : G → ℝ) : Prop :=
  (∀ g, 0 < weight g) ∧
    ∀ g d, d ∈ C →
      objective (g • d) = weight g * objective d + offset g


theorem d001309
    [AddCommMonoid D] [Module ℝ D]
    (objective : D → ℝ) (C : Set D)
    (hstrict : StrictConvexOn ℝ C objective) :
    _root_.GD.N0230.N0585.d001306 objective C := by
  intro p q hpC hqC hp hq
  exact hstrict.eq_of_isMinOn hp hq hpC hqC

variable [TopologicalSpace D]
variable [Group G] [MulAction G D]







theorem d001310
    (risk : Theta → D → ENNReal)
    (objective : D → ℝ) (C : Set D) (weight : G → ℝ)
    (hCnonempty : C.Nonempty)
    (hCcompact : IsCompact C)
    (hlsc : LowerSemicontinuousOn objective C)
    (hCinv : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hweight : ∀ g, 0 < weight g)
    (hrelative : _root_.GD.N0230.N0585.d001307
      (G := G) objective C weight)
    (hrigid : _root_.GD.N0230.N0585.d001306 objective C)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0585.d001305 risk objective) :
    ∃ p, p ∈ C ∧ IsMinOn objective C p ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  obtain ⟨p, hpC, hpMin⟩ :=
    hlsc.exists_isMinOn hCnonempty hCcompact
  have hfixed : ∀ g : G, g • p = p := by
    intro g
    have hgpC : g • p ∈ C := hCinv g hpC
    have hgpMin : IsMinOn objective C (g • p) := by
      intro d hdC
      have hpreC : g⁻¹ • d ∈ C := hCinv g⁻¹ hdC
      have hle := hpMin hpreC
      calc
        objective (g • p) = weight g * objective p :=
          hrelative g p hpC
        _ ≤ weight g * objective (g⁻¹ • d) := by
          exact mul_le_mul_of_nonneg_left hle (le_of_lt (hweight g))
        _ = objective d := by
          rw [← hrelative g (g⁻¹ • d) hpreC]
          simp
    exact (hrigid (p := p) (q := g • p) hpC hgpC hpMin hgpMin).symm
  have hterminal : _root_.GD.N0230.N0608.d000674 risk p := by
    intro e hep
    have heC : e ∈ C := hhereditary hpC hep
    have hepObj : objective e ≤ objective p := hmono hep
    have hpeObj : objective p ≤ objective e := hpMin heC
    have heMin : IsMinOn objective C e := by
      intro d hdC
      calc
        objective e = objective p := le_antisymm hepObj hpeObj
        _ ≤ objective d := hpMin hdC
    exact (hrigid (p := p) (q := e) hpC heC hpMin heMin).symm
  exact ⟨p, hpC, hpMin, hfixed, hterminal⟩








theorem d001311
    (risk : Theta → D → ENNReal)
    (objective : D → ℝ) (C : Set D) (weight offset : G → ℝ)
    (hCnonempty : C.Nonempty)
    (hCcompact : IsCompact C)
    (hlsc : LowerSemicontinuousOn objective C)
    (hCinv : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (haffine : _root_.GD.N0230.N0585.d001308
      (G := G) objective C weight offset)
    (hrigid : _root_.GD.N0230.N0585.d001306 objective C)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0585.d001305 risk objective) :
    ∃ p, p ∈ C ∧ IsMinOn objective C p ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  obtain ⟨p, hpC, hpMin⟩ :=
    hlsc.exists_isMinOn hCnonempty hCcompact
  have hpStrict : ∀ a ∈ C, p ≠ a → objective p < objective a := by
    intro a haC hpa
    have hle : objective p ≤ objective a := hpMin haC
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply hpa
      apply hrigid hpC haC hpMin
      intro d hdC
      rw [← heq]
      exact hpMin hdC
  have hfixed : ∀ g : G, g • p = p := by
    intro g
    exact
      _root_.GD.N0230.N0685.d000526
        (K := C) (ρ := objective) (T := fun d ↦ g • d)
        (cw := weight g) (offset := offset g)
        (haffine.1 g)
        (fun a ha ↦ hCinv g ha)
        (by
          intro b hb
          exact ⟨g⁻¹ • b, hCinv g⁻¹ hb, by simp⟩)
        (fun a ha ↦ haffine.2 g a ha)
        hpC hpStrict
  have hterminal : _root_.GD.N0230.N0608.d000674 risk p := by
    intro e hep
    have heC : e ∈ C := hhereditary hpC hep
    have hepObj : objective e ≤ objective p := hmono hep
    have hpeObj : objective p ≤ objective e := hpMin heC
    have heMin : IsMinOn objective C e := by
      intro d hdC
      calc
        objective e = objective p := le_antisymm hepObj hpeObj
        _ ≤ objective d := hpMin hdC
    exact (hrigid (p := p) (q := e) hpC heC hpMin heMin).symm
  exact ⟨p, hpC, hpMin, hfixed, hterminal⟩


theorem d001312
    (risk : Theta → D → ENNReal)
    (objective : D → ℝ) (C : Set D)
    (hCnonempty : C.Nonempty)
    (hCcompact : IsCompact C)
    (hlsc : LowerSemicontinuousOn objective C)
    (hCinv : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hinvariant : ∀ (g : G) (d : D),
      d ∈ C → objective (g • d) = objective d)
    (hrigid : _root_.GD.N0230.N0585.d001306 objective C)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0585.d001305 risk objective) :
    ∃ p, p ∈ C ∧ IsMinOn objective C p ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  apply _root_.GD.N0230.N0585.d001310
    risk objective C (fun _ ↦ 1) hCnonempty hCcompact hlsc hCinv
      (fun _ ↦ by norm_num)
  · intro g d hd
    simpa using hinvariant g d hd
  · exact hrigid
  · exact hhereditary
  · exact hmono

variable [AddCommMonoid D] [Module ℝ D]


theorem d001313
    (risk : Theta → D → ENNReal)
    (objective : D → ℝ) (C : Set D) (weight : G → ℝ)
    (hCnonempty : C.Nonempty)
    (hCcompact : IsCompact C)
    (hlsc : LowerSemicontinuousOn objective C)
    (hCinv : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hweight : ∀ g, 0 < weight g)
    (hrelative : _root_.GD.N0230.N0585.d001307
      (G := G) objective C weight)
    (hstrict : StrictConvexOn ℝ C objective)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0585.d001305 risk objective) :
    ∃ p, p ∈ C ∧ IsMinOn objective C p ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact _root_.GD.N0230.N0585.d001310
    risk objective C weight hCnonempty hCcompact hlsc hCinv hweight
      hrelative (_root_.GD.N0230.N0585.d001309 objective C hstrict)
      hhereditary hmono



variable {I Omega : Type*} [MeasurableSpace Omega]







theorem d001314
    (mu : I → Measure Omega)
    [MulAction G
      (∀ i : I, WeakSpace ℝ (Lp ℝ 2 (mu i)))]
    (cap : ∀ i, Set (Lp ℝ 2 (mu i)))
    (risk : Theta →
      (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) → ENNReal)
    (objective :
      (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) → ℝ)
    (weight : G → ℝ)
    (hcapCompact : ∀ i,
      IsCompact (toWeakSpace ℝ (Lp ℝ 2 (mu i)) '' cap i))
    (hCnonempty : (_root_.GD.N0230.N0659.d001299 mu cap).Nonempty)
    (hlsc : LowerSemicontinuousOn objective
      (_root_.GD.N0230.N0659.d001299 mu cap))
    (hCinv : _root_.GD.N0230.N0616.d000726 (G := G) (_root_.GD.N0230.N0659.d001299 mu cap))
    (hweight : ∀ g, 0 < weight g)
    (hrelative : _root_.GD.N0230.N0585.d001307
      (G := G) objective (_root_.GD.N0230.N0659.d001299 mu cap) weight)
    (hrigid : _root_.GD.N0230.N0585.d001306 objective (_root_.GD.N0230.N0659.d001299 mu cap))
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk (_root_.GD.N0230.N0659.d001299 mu cap))
    (hmono : _root_.GD.N0230.N0585.d001305 risk objective) :
    ∃ p, p ∈ _root_.GD.N0230.N0659.d001299 mu cap ∧
      IsMinOn objective (_root_.GD.N0230.N0659.d001299 mu cap) p ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  apply _root_.GD.N0230.N0585.d001310
    risk objective (_root_.GD.N0230.N0659.d001299 mu cap) weight hCnonempty
  · exact _root_.GD.N0230.N0659.d001301 mu cap hcapCompact
  · exact hlsc
  · exact hCinv
  · exact hweight
  · exact hrelative
  · exact hrigid
  · exact hhereditary
  · exact hmono


theorem d001315
    (mu : I → Measure Omega)
    [MulAction G
      (∀ i : I, WeakSpace ℝ (Lp ℝ 2 (mu i)))]
    (cap : ∀ i, Set (Lp ℝ 2 (mu i)))
    (risk : Theta →
      (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) → ENNReal)
    (objective :
      (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) → ℝ)
    (weight : G → ℝ)
    (hcapCompact : ∀ i,
      IsCompact (toWeakSpace ℝ (Lp ℝ 2 (mu i)) '' cap i))
    (hCnonempty : (_root_.GD.N0230.N0659.d001299 mu cap).Nonempty)
    (hlsc : LowerSemicontinuousOn objective
      (_root_.GD.N0230.N0659.d001299 mu cap))
    (hCinv : _root_.GD.N0230.N0616.d000726 (G := G) (_root_.GD.N0230.N0659.d001299 mu cap))
    (hweight : ∀ g, 0 < weight g)
    (hrelative : _root_.GD.N0230.N0585.d001307
      (G := G) objective (_root_.GD.N0230.N0659.d001299 mu cap) weight)
    (hstrict : StrictConvexOn ℝ (_root_.GD.N0230.N0659.d001299 mu cap) objective)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk (_root_.GD.N0230.N0659.d001299 mu cap))
    (hmono : _root_.GD.N0230.N0585.d001305 risk objective) :
    ∃ p, p ∈ _root_.GD.N0230.N0659.d001299 mu cap ∧
      IsMinOn objective (_root_.GD.N0230.N0659.d001299 mu cap) p ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    _root_.GD.N0230.N0585.d001314
      mu cap risk objective weight hcapCompact hCnonempty hlsc hCinv
      hweight hrelative
      (_root_.GD.N0230.N0585.d001309 objective
        (_root_.GD.N0230.N0659.d001299 mu cap) hstrict)
      hhereditary hmono

end

end N0585
end N0230
end GD

#print axioms _root_.GD.N0230.N0585.d001310
#print axioms _root_.GD.N0230.N0585.d001311
#print axioms _root_.GD.N0230.N0585.d001313
#print axioms _root_.GD.N0230.N0585.d001314
#print axioms _root_.GD.N0230.N0585.d001315
