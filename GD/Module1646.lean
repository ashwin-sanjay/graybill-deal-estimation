import GD.Module1639
import GD.Module1644
import GD.Module1640
import GD.Module1645
import GD.Module1641

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0078.N0316

noncomputable section

open _root_.GD.N0074
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0079
open _root_.GD.N0079.N0319 _root_.GD.N0079.N0322
open _root_.GD.N0230.N0642
open _root_.GD.N0230.N0642.d001800

variable (k : ℕ) (sizes : Fin k → ℕ)

def d028047 (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) : Prop :=
  ∃ f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ, Measurable f ∧
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ B θ

def d028048 (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) : Prop :=
  ∃ h : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable h ∧
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (h ∘ _root_.GD.N0074.N0308.d022071 k sizes) ≤ B θ

def d028049 (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) : Prop :=
  ∃ κ : Kernel (_root_.GD.N0232.N0719.N0900.d009094 k sizes) ℝ, IsMarkovKernel κ ∧
    ∀ θ, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≤ B θ

theorem d028050
    (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) (hB : B (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ ∞) :
    _root_.GD.N0078.N0316.d028047 k sizes B ↔ _root_.GD.N0078.N0316.d028049 k sizes B := by
  constructor
  · rintro ⟨f, hf, hcap⟩
    refine ⟨Kernel.deterministic f hf, inferInstance, ?_⟩
    intro θ
    simpa only [_root_.GD.N0079.N0322.d028033] using hcap θ
  · rintro ⟨κ, hκ, hcap⟩
    letI : IsMarkovKernel κ := hκ
    have hfin : _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 ≠ ∞ :=
      ne_top_of_le_ne_top hB (hcap (_root_.GD.N0232.N0719.N0859.d010810 k))
    have hgood0 := _root_.GD.N0230.N0642.d001800.d001830 κ
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 hfin
    refine ⟨(_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802,
      (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001808, ?_⟩
    intro θ
    have hgood := (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hgood0
    have hr : (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001818 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location =
        _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location := by
      rw [(_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001829]
      exact _root_.GD.N0230.N0642.d001800.d001836 κ _ θ.location 0 hgood
    apply le_trans _ (hcap θ)
    change _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 ≤ _
    rw [← hr, (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001821]
    exact le_self_add

theorem d028051
    (hsizes : ∀ i, 2 ≤ sizes i)
    (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) (hB : ∀ θ, B θ ≠ ∞) :
    _root_.GD.N0078.N0316.d028049 k sizes B ↔ _root_.GD.N0078.N0316.d028048 k sizes B := by
  constructor
  · rintro ⟨κ, hκ, hcap⟩
    letI : IsMarkovKernel κ := hκ
    have hfin : ∀ θ, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞ :=
      fun θ => ne_top_of_le_ne_top (hB θ) (hcap θ)
    obtain ⟨h, hh, _, hdecomp⟩ :=
      _root_.GD.N0079.N0321.d028009 k sizes hsizes κ hfin
    refine ⟨h, hh, fun θ => le_trans ?_ (hcap θ)⟩
    rw [hdecomp θ]
    exact le_trans le_self_add le_self_add
  · rintro ⟨h, hh, hcap⟩
    apply (_root_.GD.N0078.N0316.d028050 k sizes B (hB (_root_.GD.N0232.N0719.N0859.d010810 k))).mp
    exact ⟨h ∘ _root_.GD.N0074.N0308.d022071 k sizes,
      hh.comp (_root_.GD.N0074.N0308.d022072 k sizes), hcap⟩

theorem d028052
    (hsizes : ∀ i, 2 ≤ sizes i)
    (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) (hB : ∀ θ, B θ ≠ ∞) :
    (_root_.GD.N0078.N0316.d028047 k sizes B ↔ _root_.GD.N0078.N0316.d028048 k sizes B) ∧
    (_root_.GD.N0078.N0316.d028047 k sizes B ↔ _root_.GD.N0078.N0316.d028049 k sizes B) := by
  have hr := _root_.GD.N0078.N0316.d028050 k sizes B (hB (_root_.GD.N0232.N0719.N0859.d010810 k))
  exact ⟨hr.trans (_root_.GD.N0078.N0316.d028051 k sizes hsizes B hB), hr⟩

theorem d028053
    (hsizes : ∀ i, 2 ≤ sizes i)
    (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) (hB : B (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ ∞) :
    _root_.GD.N0078.N0316.d028047 k sizes B ↔ _root_.GD.N0078.N0316.d028048 k sizes B := by
  constructor
  · rintro ⟨f, hf, hcap⟩
    have hf2 : MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) :=
      _root_.GD.N0079.N0321.d028003 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)
        f hf (ne_top_of_le_ne_top hB (hcap (_root_.GD.N0232.N0719.N0859.d010810 k)))
    let d : _root_.GD.N0074.d023610 k sizes := hf2.toLp f
    obtain ⟨g, hg, hpg⟩ := _root_.GD.N0074.N0308.d022075 k sizes d
    refine ⟨g, hg, fun θ => ?_⟩
    calc
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (g ∘ _root_.GD.N0074.N0308.d022071 k sizes) =
          _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N1012.d011399 k sizes d) :=
        (_root_.GD.N0079.N0319.d027979 k sizes θ _ _ (hpg θ)).symm
      _ ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d :=
        _root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ d
      _ = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f :=
        (_root_.GD.N0232.N0719.N0859.d010841 k sizes θ f hf2).symm
      _ ≤ B θ := hcap θ
  · rintro ⟨g, hg, hcap⟩
    exact ⟨g ∘ _root_.GD.N0074.N0308.d022071 k sizes,
      hg.comp (_root_.GD.N0074.N0308.d022072 k sizes), hcap⟩

theorem d028054
    (hsizes : ∀ i, 2 ≤ sizes i)
    (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) (hB : B (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ ∞) :
    (_root_.GD.N0078.N0316.d028047 k sizes B ↔ _root_.GD.N0078.N0316.d028048 k sizes B) ∧
    (_root_.GD.N0078.N0316.d028047 k sizes B ↔ _root_.GD.N0078.N0316.d028049 k sizes B) :=
  ⟨_root_.GD.N0078.N0316.d028053 k sizes hsizes B hB,
    _root_.GD.N0078.N0316.d028050 k sizes B hB⟩

theorem d028055
    (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023612 k sizes) :
    (_root_.GD.N0079.N0319.d027977 k sizes d.val ↔ _root_.GD.N0079.N0319.d027994 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027977 k sizes d.val ↔ _root_.GD.N0079.N0322.d028031 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027977 k sizes d.val ↔ _root_.GD.N0079.N0319.d027989 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027977 k sizes d.val → _root_.GD.N0079.N0319.d027973 k sizes d.val) := by
  obtain ⟨hs, _, hf, _, hp⟩ := _root_.GD.N0079.N0319.d028001 k sizes hsizes d
  exact ⟨hs.symm, (_root_.GD.N0079.N0322.d028036 k sizes d.val).symm, hf.symm, hp⟩

theorem d028056
    (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023612 k sizes) :
    (_root_.GD.N0079.N0319.d027978 k sizes d.val ↔ _root_.GD.N0079.N0319.d027995 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027978 k sizes d.val ↔ _root_.GD.N0079.N0322.d028032 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027978 k sizes d.val ↔ _root_.GD.N0079.N0319.d027990 k sizes d.val) := by
  obtain ⟨_, hs, _, hf, _⟩ := _root_.GD.N0079.N0319.d028001 k sizes hsizes d
  exact ⟨hs.symm, (_root_.GD.N0079.N0322.d028037 k sizes d.val).symm, hf.symm⟩

theorem d028057
    (hsizes : ∀ i, 2 ≤ sizes i)
    {I : Type*} [Nonempty I] (B : I → _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞)
    (hB : ∀ i θ, B i θ ≠ ∞) :
    (∃ f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ, Measurable f ∧
      ∀ i θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ B i θ) ↔
    (∃ h : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable h ∧
      ∀ i θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (h ∘ _root_.GD.N0074.N0308.d022071 k sizes) ≤ B i θ) := by
  have hfin : ∀ θ, (⨅ i, B i θ) ≠ ∞ := by
    intro θ
    let i : I := Classical.arbitrary I
    exact ne_top_of_le_ne_top (hB i θ) (iInf_le _ i)
  have h := (_root_.GD.N0078.N0316.d028052 k sizes hsizes (fun θ => ⨅ i, B i θ) hfin).1
  simpa only [_root_.GD.N0078.N0316.d028047, _root_.GD.N0078.N0316.d028048, le_iInf_iff, forall_comm (α := _root_.GD.N0232.N0719.N0859.d010809 k)] using h

theorem d028058
    (hsizes : ∀ i, 2 ≤ sizes i)
    {I : Type*} (B : I → _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞)
    (hB : ∃ i, B i (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ ∞) :
    (∃ f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ, Measurable f ∧
      ∀ i θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ B i θ) ↔
    (∃ h : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable h ∧
      ∀ i θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (h ∘ _root_.GD.N0074.N0308.d022071 k sizes) ≤ B i θ) := by
  obtain ⟨i, hi⟩ := hB
  have hfin : (⨅ j, B j (_root_.GD.N0232.N0719.N0859.d010810 k)) ≠ ∞ :=
    ne_top_of_le_ne_top hi (iInf_le _ i)
  have h := _root_.GD.N0078.N0316.d028053 k sizes hsizes (fun θ => ⨅ j, B j θ) hfin
  simpa only [_root_.GD.N0078.N0316.d028047, _root_.GD.N0078.N0316.d028048, le_iInf_iff, forall_comm (α := _root_.GD.N0232.N0719.N0859.d010809 k)] using h

end
end GD.N0078.N0316

#print axioms _root_.GD.N0078.N0316.d028050
#print axioms _root_.GD.N0078.N0316.d028051
#print axioms _root_.GD.N0078.N0316.d028052
#print axioms _root_.GD.N0078.N0316.d028053
#print axioms _root_.GD.N0078.N0316.d028054
#print axioms _root_.GD.N0078.N0316.d028055
#print axioms _root_.GD.N0078.N0316.d028056
#print axioms _root_.GD.N0078.N0316.d028057
#print axioms _root_.GD.N0078.N0316.d028058
