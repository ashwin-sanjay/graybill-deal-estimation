import GD.Module1637

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0079.N0319

noncomputable section

open _root_.GD.N0074
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N1012
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

variable (k : ℕ) (sizes : Fin k → ℕ)

abbrev d027973 (d : _root_.GD.N0074.d023610 k sizes) : Prop := _root_.GD.N0232.N0719.N1012.d011399 k sizes d = d


def d027974 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ e, _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) e d → _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d e

def d027975 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ e, _root_.GD.N0079.N0319.d027973 k sizes e →
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) e d → _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d e

def d027976 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ e, _root_.GD.N0079.N0319.d027973 k sizes e → _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) e d → e = d


def d027977 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ, Measurable f →
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) →
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f


def d027978 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ, Measurable f →
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) →
    ∀ θ, f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)

theorem d027979 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0074.d023610 k sizes)
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (h : (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]


theorem d027980 (d : _root_.GD.N0074.d023610 k sizes)
    (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) (hf : Measurable f)
    (hdom : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) :
    MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  have hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) f ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
    rw [_root_.GD.N0232.N0719.N0859.d010829]
    exact ENNReal.ofReal_ne_top
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  have hlin :
      (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) ≠ ⊤ := by
    simpa [_root_.GD.N0232.N0719.N0859.d010840, _root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.d009182] using hfinite
  have hint := integrable_toReal_of_lintegral_ne_top
    ((hf.pow_const 2).ennreal_ofReal.aemeasurable) hlin
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint

theorem d027981 (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0319.d027977 k sizes d ↔ _root_.GD.N0079.N0319.d027974 k sizes d := by
  constructor
  · intro h e he
    obtain ⟨f, hf, hef⟩ := _root_.GD.N0074.N0308.d022077 k sizes e
    have hr : ∀ θ, _root_.GD.N0232.N0719.N0859.d010821 k sizes θ e = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f :=
      fun θ => _root_.GD.N0079.N0319.d027979 k sizes θ e f (hef θ)
    intro θ
    rw [hr θ]
    exact h f hf (fun η => (hr η).symm ▸ he η) θ
  · intro h f hf hdom
    have hf2 := _root_.GD.N0079.N0319.d027980 k sizes d f hf hdom
    have he := h (hf2.toLp f) (fun θ =>
      (_root_.GD.N0232.N0719.N0859.d010841 k sizes θ f hf2) ▸ hdom θ)
    intro θ
    simpa only [← _root_.GD.N0232.N0719.N0859.d010841 k sizes θ f hf2] using he θ

theorem d027982 (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0319.d027978 k sizes d ↔ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d := by
  constructor
  · intro h e he
    obtain ⟨f, hf, hef⟩ := _root_.GD.N0074.N0308.d022077 k sizes e
    have hdom : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d := by
      intro θ
      rw [← _root_.GD.N0079.N0319.d027979 k sizes θ e f (hef θ)]
      exact he θ
    apply Lp.ext
    exact (hef (_root_.GD.N0232.N0719.N0859.d010810 k)).trans (h f hf hdom (_root_.GD.N0232.N0719.N0859.d010810 k))
  · intro h f hf hdom
    have hf2 := _root_.GD.N0079.N0319.d027980 k sizes d f hf hdom
    have he := h (hf2.toLp f) (fun θ =>
      (_root_.GD.N0232.N0719.N0859.d010841 k sizes θ f hf2) ▸ hdom θ)
    intro θ
    have hae := (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hf2.coeFn_toLp
    filter_upwards [hae] with ω hω
    simpa only [he] using hω.symm

theorem d027983 (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0319.d027973 k sizes (_root_.GD.N0232.N0719.N1012.d011399 k sizes d) :=
  (_root_.GD.N0232.N0719.N1012.d011405 k sizes _).mpr
    (_root_.GD.N0232.N0719.N1012.d011401 k sizes d)


theorem d027984 (d e : _root_.GD.N0074.d023610 k sizes)
    (he : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) e d)
    (hp : _root_.GD.N0232.N0719.N1012.d011399 k sizes e = d) : e = d := by
  have hnorm := he (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829, _root_.GD.N0232.N0719.N0859.d010829] at hnorm
  simp only [zero_sub, norm_neg] at hnorm
  have hsquare : ‖e‖ ^ 2 ≤ ‖d‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖d‖)).mp hnorm
  have htax := _root_.GD.N0232.N0719.N1012.d011402 k sizes e
  rw [hp] at htax
  have hzero : ‖e - d‖ = 0 := by
    nlinarith [sq_nonneg ‖e - d‖, norm_nonneg (e - d)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem d027985 (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0319.d027975 k sizes d ↔ _root_.GD.N0079.N0319.d027974 k sizes d := by
  constructor
  · intro h e he θ
    have hpd : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N1012.d011399 k sizes e) d :=
      fun η => le_trans (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes η e) (he η)
    exact le_trans (h _ (_root_.GD.N0079.N0319.d027983 k sizes e) hpd θ)
      (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ e)
  · intro h e _ he
    exact h e he

theorem d027986 (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023610 k sizes) :
    _root_.GD.N0079.N0319.d027976 k sizes d ↔ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d := by
  constructor
  · intro h e he
    apply _root_.GD.N0079.N0319.d027984 k sizes d e he
    apply h _ (_root_.GD.N0079.N0319.d027983 k sizes e)
    exact fun θ => le_trans (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ e) (he θ)
  · intro h e _ he
    exact h e he

theorem d027987 (hsizes : ∀ i, 2 ≤ sizes i) (d : _root_.GD.N0074.d023610 k sizes) :
    (_root_.GD.N0079.N0319.d027975 k sizes d ↔ _root_.GD.N0079.N0319.d027977 k sizes d) ∧
    (_root_.GD.N0079.N0319.d027976 k sizes d ↔ _root_.GD.N0079.N0319.d027978 k sizes d) :=
  ⟨(_root_.GD.N0079.N0319.d027985 k sizes hsizes d).trans (_root_.GD.N0079.N0319.d027981 k sizes d).symm,
   (_root_.GD.N0079.N0319.d027986 k sizes hsizes d).trans (_root_.GD.N0079.N0319.d027982 k sizes d).symm⟩


theorem d027988 (hsizes : ∀ i, 2 ≤ sizes i)
    (d e : _root_.GD.N0074.d023610 k sizes) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (h : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ e < _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N1012.d011399 k sizes e) < _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d :=
  lt_of_le_of_lt (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ e) h

def d027989 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ e : _root_.GD.N0074.d023612 k sizes, _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) e.val d →
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d e.val

def d027990 (d : _root_.GD.N0074.d023610 k sizes) : Prop :=
  ∀ e : _root_.GD.N0074.d023612 k sizes, _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) e.val d → e.val = d

theorem d027991 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d e : _root_.GD.N0074.d023610 k sizes)
    (hd : MemLp (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ))
    (h : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ e ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d) :
    MemLp (e : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    unfold _root_.GD.N0232.N0719.N0859.d010812
    infer_instance
  have hdm := hd.sub (memLp_const θ.location)
  have hem : AEStronglyMeasurable (fun ω => e ω - θ.location) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) :=
    ((Lp.memLp e).aestronglyMeasurable.mono_ac
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ)).sub aestronglyMeasurable_const
  have hdRisk : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hdm.integrable_sq.aestronglyMeasurable
      (ae_of_all _ fun _ => sq_nonneg _)).2 hdm.integrable_sq
  have heRisk := ne_top_of_le_ne_top hdRisk h
  have he2 : MemLp (fun ω => e ω - θ.location) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    apply (memLp_two_iff_integrable_sq hem).2
    exact (lintegral_ofReal_ne_top_iff_integrable (hem.pow 2)
      (ae_of_all _ fun _ => sq_nonneg _)).1 heRisk
  refine MemLp.ae_eq (ae_of_all _ fun ω => ?_) (he2.add (memLp_const θ.location))
  simp only [Pi.add_apply, sub_add_cancel]

theorem d027992 (d : _root_.GD.N0074.d023612 k sizes) :
    _root_.GD.N0079.N0319.d027989 k sizes d.val ↔ _root_.GD.N0079.N0319.d027974 k sizes d.val := by
  constructor
  · intro h e he
    exact h ⟨e, fun θ => _root_.GD.N0079.N0319.d027991 k sizes θ d.val e (d.property θ) (he θ)⟩ he
  · intro h e he
    exact h e.val he

theorem d027993 (d : _root_.GD.N0074.d023612 k sizes) :
    _root_.GD.N0079.N0319.d027990 k sizes d.val ↔ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d.val := by
  constructor
  · intro h e he
    exact h ⟨e, fun θ => _root_.GD.N0079.N0319.d027991 k sizes θ d.val e (d.property θ) (he θ)⟩ he
  · intro h e he
    exact h e.val he

#print axioms _root_.GD.N0079.N0319.d027979
#print axioms _root_.GD.N0079.N0319.d027980
#print axioms _root_.GD.N0079.N0319.d027981
#print axioms _root_.GD.N0079.N0319.d027982
#print axioms _root_.GD.N0079.N0319.d027983
#print axioms _root_.GD.N0079.N0319.d027984
#print axioms _root_.GD.N0079.N0319.d027985
#print axioms _root_.GD.N0079.N0319.d027986
#print axioms _root_.GD.N0079.N0319.d027987
#print axioms _root_.GD.N0079.N0319.d027988
#print axioms _root_.GD.N0079.N0319.d027991
#print axioms _root_.GD.N0079.N0319.d027992
#print axioms _root_.GD.N0079.N0319.d027993

end
end GD.N0079.N0319
