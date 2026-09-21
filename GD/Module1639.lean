import GD.Module1638

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0079.N0319

noncomputable section

open _root_.GD.N0074
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N1012
open _root_.GD.N0230.N0608

variable (k : ℕ) (sizes : Fin k → ℕ)


def d027994 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ g : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable g →
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (g ∘ _root_.GD.N0074.N0308.d022071 k sizes) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) →
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (g ∘ _root_.GD.N0074.N0308.d022071 k sizes)

def d027995 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ g : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable g →
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (g ∘ _root_.GD.N0074.N0308.d022071 k sizes) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) →
    ∀ θ, (g ∘ _root_.GD.N0074.N0308.d022071 k sizes) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
      (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)

theorem d027996 (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0319.d027994 k sizes d ↔ _root_.GD.N0079.N0319.d027977 k sizes d := by
  rw [_root_.GD.N0079.N0319.d027981]
  constructor
  · intro h e he θ
    obtain ⟨g, hg, hpg⟩ := _root_.GD.N0074.N0308.d022075 k sizes e
    have hr : ∀ η, _root_.GD.N0232.N0719.N0859.d010821 k sizes η (_root_.GD.N0232.N0719.N1012.d011399 k sizes e) =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes η (g ∘ _root_.GD.N0074.N0308.d022071 k sizes) :=
      fun η => _root_.GD.N0079.N0319.d027979 k sizes η _ _ (hpg η)
    have hdom : ∀ η, _root_.GD.N0232.N0719.N0859.d010840 k sizes η (g ∘ _root_.GD.N0074.N0308.d022071 k sizes) ≤
        _root_.GD.N0232.N0719.N0859.d010821 k sizes η d := by
      intro η
      rw [← hr η]
      exact le_trans (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes η e) (he η)
    have hle := h g hg hdom θ
    rw [← hr θ] at hle
    exact le_trans hle (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ e)
  · intro h g hg hdom
    exact (_root_.GD.N0079.N0319.d027981 k sizes d).mpr h
      (g ∘ _root_.GD.N0074.N0308.d022071 k sizes)
      (hg.comp (_root_.GD.N0074.N0308.d022072 k sizes)) hdom

theorem d027997 (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0319.d027995 k sizes d ↔ _root_.GD.N0079.N0319.d027978 k sizes d := by
  rw [_root_.GD.N0079.N0319.d027982]
  constructor
  · intro h e he
    obtain ⟨g, hg, hpg⟩ := _root_.GD.N0074.N0308.d022075 k sizes e
    have hdom : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (g ∘ _root_.GD.N0074.N0308.d022071 k sizes) ≤
        _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d := by
      intro θ
      rw [← _root_.GD.N0079.N0319.d027979 k sizes θ _ _ (hpg θ)]
      exact le_trans (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ e) (he θ)
    apply _root_.GD.N0079.N0319.d027984 k sizes d e he
    apply Lp.ext
    exact (hpg (_root_.GD.N0232.N0719.N0859.d010810 k)).trans (h g hg hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
  · intro h g hg hdom
    exact (_root_.GD.N0079.N0319.d027982 k sizes d).mpr h
      (g ∘ _root_.GD.N0074.N0308.d022071 k sizes)
      (hg.comp (_root_.GD.N0074.N0308.d022072 k sizes)) hdom


theorem d027998 (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023610 k sizes)
    (hd : _root_.GD.N0079.N0319.d027974 k sizes d) : _root_.GD.N0079.N0319.d027973 k sizes d := by
  have hpd : _root_.GD.N0230.N0608.d000672
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N1012.d011399 k sizes d) d :=
    fun θ => _root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ d
  have hnorm := hd _ hpd (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829, _root_.GD.N0232.N0719.N0859.d010829] at hnorm
  simp only [zero_sub, norm_neg] at hnorm
  have hsquare : ‖d‖ ^ 2 ≤ ‖_root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖_root_.GD.N0232.N0719.N1012.d011399 k sizes d‖)).mp hnorm
  have htax := _root_.GD.N0232.N0719.N1012.d011402 k sizes d
  have hzero : ‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ = 0 := by
    nlinarith [sq_nonneg ‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖,
      norm_nonneg (d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm


theorem d027999 (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0074.d023610 k sizes) (hd : _root_.GD.N0079.N0319.d027977 k sizes d) :
    ∃ g : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable g ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
          g ∘ _root_.GD.N0074.N0308.d022071 k sizes := by
  have hp := _root_.GD.N0079.N0319.d027998 k sizes hsizes d ((_root_.GD.N0079.N0319.d027981 k sizes d).mp hd)
  obtain ⟨g, hg, hproj⟩ := _root_.GD.N0074.N0308.d022075 k sizes d
  exact ⟨g, hg, fun θ => hp ▸ hproj θ⟩


theorem d028000 (d : _root_.GD.N0074.d023610 k sizes)
    (hd : ¬ _root_.GD.N0079.N0319.d027973 k sizes d) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) (_root_.GD.N0232.N0719.N1012.d011399 k sizes d) <
      _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d := by
  have hne : d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d ≠ 0 := by
    intro h
    exact hd (sub_eq_zero.mp h).symm
  have hpos : 0 < ‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hne)
  rw [_root_.GD.N0232.N0719.N0859.d010829, _root_.GD.N0232.N0719.N0859.d010829]
  simp only [zero_sub, norm_neg]
  have htax := _root_.GD.N0232.N0719.N1012.d011402 k sizes d
  have hsquare : ‖_root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ ^ 2 < ‖d‖ ^ 2 := by linarith
  exact (ENNReal.ofReal_lt_ofReal_iff
    (lt_of_le_of_lt (sq_nonneg _) hsquare)).2 hsquare


theorem d028001 (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0074.d023612 k sizes) :
    (_root_.GD.N0079.N0319.d027994 k sizes d.val ↔ _root_.GD.N0079.N0319.d027977 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027995 k sizes d.val ↔ _root_.GD.N0079.N0319.d027978 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027989 k sizes d.val ↔ _root_.GD.N0079.N0319.d027977 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027990 k sizes d.val ↔ _root_.GD.N0079.N0319.d027978 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027977 k sizes d.val → _root_.GD.N0079.N0319.d027973 k sizes d.val) := by
  refine ⟨_root_.GD.N0079.N0319.d027996 k sizes hsizes d.val,
    _root_.GD.N0079.N0319.d027997 k sizes hsizes d.val,
    (_root_.GD.N0079.N0319.d027992 k sizes d).trans (_root_.GD.N0079.N0319.d027981 k sizes d.val).symm,
    (_root_.GD.N0079.N0319.d027993 k sizes d).trans (_root_.GD.N0079.N0319.d027982 k sizes d.val).symm, ?_⟩
  intro hd
  exact _root_.GD.N0079.N0319.d027998 k sizes hsizes d.val ((_root_.GD.N0079.N0319.d027981 k sizes d.val).mp hd)

#print axioms _root_.GD.N0079.N0319.d027996
#print axioms _root_.GD.N0079.N0319.d027997
#print axioms _root_.GD.N0079.N0319.d027998
#print axioms _root_.GD.N0079.N0319.d027999
#print axioms _root_.GD.N0079.N0319.d028000
#print axioms _root_.GD.N0079.N0319.d028001

end
end GD.N0079.N0319
