import GD.Module1638
import GD.Module0160

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0079.N0322

noncomputable section

open _root_.GD.N0074
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0230.N0642
open _root_.GD.N0230.N0642.d001800
open _root_.GD.N0079.N0319

variable (k : ℕ) (sizes : Fin k → ℕ)

abbrev d028030 := _root_.GD.N0232.N0719.N0900.d009094 k sizes

def d028031 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ κ : Kernel (_root_.GD.N0079.N0322.d028030 k sizes) ℝ, IsMarkovKernel κ →
    (∀ θ, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) →
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d ≤ _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location

def d028032 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ κ : Kernel (_root_.GD.N0079.N0322.d028030 k sizes) ℝ, IsMarkovKernel κ →
    (∀ θ, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) →
    ∀ θ, ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, κ x = Measure.dirac (d x)

theorem d028033 (f : _root_.GD.N0079.N0322.d028030 k sizes → ℝ) (hf : Measurable f) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0230.N0642.d001800.d001823 (Kernel.deterministic f hf) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  unfold _root_.GD.N0230.N0642.d001800.d001823 _root_.GD.N0230.N0642.d001800.d001822 _root_.GD.N0232.N0719.N0859.d010840
  simp only [Kernel.deterministic_apply, lintegral_dirac]

theorem d028034 (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d ≠ ∞ := by
  rw [_root_.GD.N0232.N0719.N0859.d010829]
  exact ENNReal.ofReal_ne_top

theorem d028035
    (d : _root_.GD.N0074.d023610 k sizes) (κ : Kernel (_root_.GD.N0079.N0322.d028030 k sizes) ℝ) [IsMarkovKernel κ]
    (hdom : ∀ θ, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) :
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 ≤
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location := by
  have hfin : _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 ≠ ∞ :=
    ne_top_of_le_ne_top (_root_.GD.N0079.N0322.d028034 k sizes d) (hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
  have hgood0 := _root_.GD.N0230.N0642.d001800.d001830 κ
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 hfin
  intro θ
  have hgood := (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hgood0
  have hr : (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001818 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location =
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location := by
    rw [(_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001829]
    exact _root_.GD.N0230.N0642.d001800.d001836 κ _ θ.location 0 hgood
  change _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 ≤ _
  rw [← hr, (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001821]
  exact le_self_add

theorem d028036 (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0322.d028031 k sizes d ↔ _root_.GD.N0079.N0319.d027977 k sizes d := by
  constructor
  · intro h f hf hdom θ
    have hd : ∀ η, _root_.GD.N0230.N0642.d001800.d001823 (Kernel.deterministic f hf) (_root_.GD.N0232.N0719.N0859.d010812 k sizes η)
        η.location ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes η d := by
      intro η
      rw [_root_.GD.N0079.N0322.d028033]
      exact hdom η
    simpa only [_root_.GD.N0079.N0322.d028033] using h (Kernel.deterministic f hf) inferInstance hd θ
  · intro h κ hκ hdom θ
    letI : IsMarkovKernel κ := hκ
    have hb := _root_.GD.N0079.N0322.d028035 k sizes d κ hdom
    exact (h (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001808
      (fun η => (hb η).trans (hdom η)) θ).trans (hb θ)

theorem d028037 (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0322.d028032 k sizes d ↔ _root_.GD.N0079.N0319.d027978 k sizes d := by
  constructor
  · intro h f hf hdom θ
    have hd : ∀ η, _root_.GD.N0230.N0642.d001800.d001823 (Kernel.deterministic f hf) (_root_.GD.N0232.N0719.N0859.d010812 k sizes η)
        η.location ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes η d := by
      intro η
      rw [_root_.GD.N0079.N0322.d028033]
      exact hdom η
    have he := h (Kernel.deterministic f hf) inferInstance hd θ
    filter_upwards [he] with x hx
    rw [Kernel.deterministic_apply] at hx
    exact MeasureTheory.injective_dirac hx
  · intro h κ hκ hdom θ
    letI : IsMarkovKernel κ := hκ
    exact _root_.GD.N0230.N0642.d001800.d001839
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes) _root_.GD.N0232.N0719.N0859.d010809.location (d : _root_.GD.N0079.N0322.d028030 k sizes → ℝ) κ (_root_.GD.N0232.N0719.N0859.d010810 k)
      h (_root_.GD.N0079.N0322.d028034 k sizes d) hdom
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes) θ

theorem d028038 (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023610 k sizes) :
    (_root_.GD.N0079.N0322.d028031 k sizes d ↔ _root_.GD.N0079.N0319.d027975 k sizes d) ∧
    (_root_.GD.N0079.N0322.d028032 k sizes d ↔ _root_.GD.N0079.N0319.d027976 k sizes d) :=
  ⟨(_root_.GD.N0079.N0322.d028036 k sizes d).trans
      (_root_.GD.N0079.N0319.d027987 k sizes hsizes d).1.symm,
    (_root_.GD.N0079.N0322.d028037 k sizes d).trans
      (_root_.GD.N0079.N0319.d027987 k sizes hsizes d).2.symm⟩

#print axioms _root_.GD.N0079.N0322.d028033
#print axioms _root_.GD.N0079.N0322.d028034
#print axioms _root_.GD.N0079.N0322.d028035
#print axioms _root_.GD.N0079.N0322.d028036
#print axioms _root_.GD.N0079.N0322.d028037
#print axioms _root_.GD.N0079.N0322.d028038

end
end GD.N0079.N0322
