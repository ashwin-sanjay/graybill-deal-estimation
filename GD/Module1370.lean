import GD.Module0758
import GD.Module0625

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0074.N0308

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N1012
open _root_.GD.N0228.N0548
open _root_.GD.N0230.N0602

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d022064 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = Measure.pi (fun i : Fin k ↦
      Measure.pi (fun _ : Fin (sizes i) ↦
        gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale i)))) := by
  unfold _root_.GD.N0232.N0719.N0859.d010812 _root_.GD.N0232.N0719.d009176
  congr 1
  funext i
  exact _root_.GD.N0232.N0719.N0932.d009211 _ _ _

theorem d022065 (θ η : _root_.GD.N0232.N0719.N0859.d010809 k)
    (f g : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) :
    f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] g ↔ f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes η] g := by
  exact (_root_.GD.N0232.N0719.d009184 k sizes
    θ.location θ.scale θ.scale_pos).trans
      (_root_.GD.N0232.N0719.d009184 k sizes
        η.location η.scale η.scale_pos).symm

theorem d022066
    (hsizes : ∀ i, 0 < sizes i) (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) :
    AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes] f
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes) ↔
      ∃ g : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ, Measurable g ∧
        f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          g ∘ _root_.GD.N0228.N0548.d009155 k sizes := by
  constructor
  · intro hf
    obtain ⟨g, hg, hfactor⟩ := hf.stronglyMeasurable_mk.exists_eq_measurable_comp
    refine ⟨g ∘ _root_.GD.N0228.N0548.d009149 sizes,
      hg.measurable.comp (_root_.GD.N0228.N0548.d009151 sizes), ?_⟩
    filter_upwards [hf.ae_eq_mk] with ω hω
    calc
      f ω = hf.mk f ω := hω
      _ = g (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) := congrFun hfactor ω
      _ = ((g ∘ _root_.GD.N0228.N0548.d009149 sizes) ∘ _root_.GD.N0228.N0548.d009155 k sizes) ω := rfl
  · rintro ⟨g, hg, hfg⟩
    have hm : Measurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
        (g ∘ _root_.GD.N0228.N0548.d009155 k sizes) := by
      have heq : g ∘ _root_.GD.N0228.N0548.d009155 k sizes =
          (g ∘ _root_.GD.N0228.N0548.d009148 sizes) ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes := by
        funext ω
        exact congrArg g (_root_.GD.N0228.N0548.d009156 k sizes hsizes ω).symm
      rw [heq]
      exact (hg.comp (_root_.GD.N0228.N0548.d009150 sizes)).comp
        (comap_measurable (_root_.GD.N0232.N0719.N0900.d009104 k sizes))
    exact hm.stronglyMeasurable.aestronglyMeasurable.congr hfg.symm

theorem d022067
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ∃ g : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ, Measurable g ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        (fun ω ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d ω) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
          g ∘ _root_.GD.N0228.N0548.d009155 k sizes := by
  let p : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := fun ω ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d ω
  have hp : AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes] p
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    _root_.GD.N0232.N0719.N1012.d011401 k sizes d
  obtain ⟨g, hg, hfactor⟩ := hp.stronglyMeasurable_mk.exists_eq_measurable_comp
  refine ⟨g ∘ _root_.GD.N0228.N0548.d009149 sizes,
    hg.measurable.comp (_root_.GD.N0228.N0548.d009151 sizes), ?_⟩
  intro θ
  have hlive := (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hp.ae_eq_mk
  filter_upwards [hlive] with ω hω
  calc
    _root_.GD.N0232.N0719.N1012.d011399 k sizes d ω = hp.mk p ω := hω
    _ = g (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) := congrFun hfactor ω
    _ = ((g ∘ _root_.GD.N0228.N0548.d009149 sizes) ∘ _root_.GD.N0228.N0548.d009155 k sizes) ω := rfl

theorem d022068
    (hsizes : ∀ i, 0 < sizes i)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N1012.d011399 k sizes d = d ↔
      ∃ g : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ, Measurable g ∧
        (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          g ∘ _root_.GD.N0228.N0548.d009155 k sizes := by
  rw [_root_.GD.N0232.N0719.N1012.d011405,
    _root_.GD.N0074.N0308.d022066 k sizes hsizes]

abbrev d022069 (k : ℕ) :=
  {s : _root_.GD.N0232.N0719.N0900.d009096 k // ∀ i, 0 ≤ s.meanVariance i}

theorem d022070 (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) (i : Fin k) :
    0 ≤ (_root_.GD.N0228.N0548.d009155 k sizes ω).meanVariance i := by
  change 0 ≤ _root_.GD.N0107.d009085 (ω i)
  unfold _root_.GD.N0107.d009085 _root_.GD.N0126.d006422
  positivity

def d022071 (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : _root_.GD.N0074.N0308.d022069 k :=
  ⟨_root_.GD.N0228.N0548.d009155 k sizes ω, _root_.GD.N0074.N0308.d022070 k sizes ω⟩

theorem d022072 : Measurable (_root_.GD.N0074.N0308.d022071 k sizes) :=
  (_root_.GD.N0228.N0548.d009158 k sizes).subtype_mk

theorem d022073 (hsizes : ∀ i, 0 < sizes i) :
    Measurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes] (_root_.GD.N0074.N0308.d022071 k sizes) := by
  apply Measurable.subtype_mk
  have heq : _root_.GD.N0228.N0548.d009155 k sizes =
      _root_.GD.N0228.N0548.d009148 sizes ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes := by
    funext ω
    exact (_root_.GD.N0228.N0548.d009156 k sizes hsizes ω).symm
  rw [heq]
  exact (_root_.GD.N0228.N0548.d009150 sizes).comp
    (comap_measurable (_root_.GD.N0232.N0719.N0900.d009104 k sizes))

theorem d022074
    (hsizes : ∀ i, 0 < sizes i) (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) :
    AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes] f
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes) ↔
      ∃ g : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable g ∧
        f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          g ∘ _root_.GD.N0074.N0308.d022071 k sizes := by
  constructor
  · intro hf
    obtain ⟨g, hg, hfg⟩ :=
      (_root_.GD.N0074.N0308.d022066 k sizes hsizes f).mp hf
    exact ⟨g ∘ Subtype.val, hg.comp measurable_subtype_coe, hfg⟩
  · rintro ⟨g, hg, hfg⟩
    exact (hg.comp (_root_.GD.N0074.N0308.d022073 k sizes hsizes)).stronglyMeasurable
      |>.aestronglyMeasurable.congr hfg.symm

theorem d022075
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ∃ g : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable g ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        (fun ω ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d ω) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
          g ∘ _root_.GD.N0074.N0308.d022071 k sizes := by
  obtain ⟨g, hg, hfg⟩ := _root_.GD.N0074.N0308.d022067 k sizes d
  exact ⟨g ∘ Subtype.val, hg.comp measurable_subtype_coe, hfg⟩

theorem d022076
    (hsizes : ∀ i, 0 < sizes i)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N1012.d011399 k sizes d = d ↔
      ∃ g : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable g ∧
        (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          g ∘ _root_.GD.N0074.N0308.d022071 k sizes := by
  rw [_root_.GD.N0232.N0719.N1012.d011405,
    _root_.GD.N0074.N0308.d022074 k sizes hsizes]

theorem d022077
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ∃ f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ, Measurable f ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  have hd := (Lp.memLp d).aestronglyMeasurable
  refine ⟨hd.mk d, hd.stronglyMeasurable_mk.measurable, ?_⟩
  intro θ
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hd.ae_eq_mk

#print axioms _root_.GD.N0074.N0308.d022077

#print axioms _root_.GD.N0074.N0308.d022074
#print axioms _root_.GD.N0074.N0308.d022075
#print axioms _root_.GD.N0074.N0308.d022076

#print axioms _root_.GD.N0074.N0308.d022064
#print axioms _root_.GD.N0074.N0308.d022065
#print axioms _root_.GD.N0074.N0308.d022066
#print axioms _root_.GD.N0074.N0308.d022067
#print axioms _root_.GD.N0074.N0308.d022068

end
end GD.N0074.N0308
