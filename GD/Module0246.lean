import GD.Module0242
import Mathlib.Topology.Instances.EReal.Lemmas






set_option autoImplicit false
set_option warningAsError true
open scoped ENNReal
namespace GD.N0230.N0686
noncomputable section
open _root_.GD.N0230.N0611
variable {Theta E : Type*} [Nonempty Theta]
variable (r : Theta → E → ℝ≥0∞)

def d003544 (d : E) : EReal := ⨅ theta, (1 : EReal) - (r theta d : EReal)
def d003545 (C : Set E) : EReal := ⨆ d ∈ C, _root_.GD.N0230.N0686.d003544 r d

theorem d003546 {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    (x : EReal) = (x.toReal : EReal) := by
  calc
    _ = (ENNReal.ofReal x.toReal : EReal) :=
      congrArg (fun x : ℝ≥0∞ => (x : EReal)) (ENNReal.ofReal_toReal hx).symm
    _ = _ := by simp only [EReal.coe_ennreal_ofReal,
      max_eq_left ENNReal.toReal_nonneg]

theorem d003547 (d : E) (c : ℝ≥0∞)
    (hc : c ≠ ⊤) (hpoint : ∀ theta, r theta d ≠ ⊤)
    (hlower : c ≤ _root_.GD.N0230.N0611.d003516 r d) :
    _root_.GD.N0230.N0686.d003544 r d ≤ ((1 - c.toReal : ℝ) : EReal) := by
  by_contra h
  obtain ⟨epsilon, heps0, heps⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hepsR : 1 - c.toReal < epsilon := by exact_mod_cast heps0
  have hpt : ∀ theta, (r theta d).toReal ≤ 1 - epsilon := by
    intro theta
    have h := (le_of_lt heps).trans (iInf_le
      (fun theta => (1 : EReal) - (r theta d : EReal)) theta)
    rw [_root_.GD.N0230.N0686.d003546 (hpoint theta), ← EReal.coe_one, ← EReal.coe_sub] at h
    have : epsilon ≤ 1 - (r theta d).toReal := by exact_mod_cast h
    linarith
  have hb : 0 ≤ 1 - epsilon :=
    ENNReal.toReal_nonneg.trans (hpt (Classical.arbitrary Theta))
  have hw : _root_.GD.N0230.N0611.d003516 r d ≤ ENNReal.ofReal (1 - epsilon) := by
    apply iSup_le
    intro theta
    rw [← ENNReal.ofReal_toReal (hpoint theta)]
    exact ENNReal.ofReal_le_ofReal (hpt theta)
  have hcl := (ENNReal.toReal_le_toReal hc ENNReal.ofReal_ne_top).2 (hlower.trans hw)
  rw [ENNReal.toReal_ofReal hb] at hcl
  linarith

theorem d003548 (d : E)
    (hfinite : _root_.GD.N0230.N0611.d003516 r d ≠ ⊤) :
    _root_.GD.N0230.N0686.d003544 r d = ((1 - (_root_.GD.N0230.N0611.d003516 r d).toReal : ℝ) : EReal) := by
  have hp : ∀ theta, r theta d ≠ ⊤ := fun theta =>
    ne_top_of_le_ne_top hfinite (le_iSup (fun theta => r theta d) theta)
  apply le_antisymm
    (_root_.GD.N0230.N0686.d003547 r d _ hfinite hp le_rfl)
  apply le_iInf
  intro theta
  have hle : (r theta d).toReal ≤ (_root_.GD.N0230.N0611.d003516 r d).toReal :=
    (ENNReal.toReal_le_toReal (hp theta) hfinite).2
      (le_iSup (fun theta => r theta d) theta)
  rw [_root_.GD.N0230.N0686.d003546 (hp theta), ← EReal.coe_one, ← EReal.coe_sub]
  exact_mod_cast (sub_le_sub_left hle 1)


theorem d003549 (C : Set E)
    (hpoint : ∀ d ∈ C, ∀ theta, r theta d ≠ ⊤)
    (d : E) (hd : d ∈ C)
    (hattain : _root_.GD.N0230.N0611.d003516 r d = _root_.GD.N0230.N0611.d003517 r C)
    (hfinite : _root_.GD.N0230.N0611.d003517 r C ≠ ⊤) :
    _root_.GD.N0230.N0686.d003545 r C = ((1 - (_root_.GD.N0230.N0611.d003517 r C).toReal : ℝ) : EReal) ∧
      _root_.GD.N0230.N0686.d003544 r d = _root_.GD.N0230.N0686.d003545 r C := by
  have hdval : _root_.GD.N0230.N0686.d003544 r d =
      ((1 - (_root_.GD.N0230.N0611.d003517 r C).toReal : ℝ) : EReal) := by
    rw [_root_.GD.N0230.N0686.d003548 r d (hattain ▸ hfinite), hattain]
  have hv : _root_.GD.N0230.N0686.d003545 r C = ((1 - (_root_.GD.N0230.N0611.d003517 r C).toReal : ℝ) : EReal) := by
    apply le_antisymm
    · exact iSup_le fun e => iSup_le fun he =>
        _root_.GD.N0230.N0686.d003547 r e _ hfinite (hpoint e he)
          (_root_.GD.N0230.N0611.d003520 r he)
    · rw [← hdval]
      exact le_iSup_of_le d (le_iSup_of_le hd le_rfl)
  exact ⟨hv, hdval.trans hv.symm⟩
end
end GD.N0230.N0686
#print axioms _root_.GD.N0230.N0686.d003549

