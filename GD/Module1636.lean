import GD.Module1635
import GD.Module1370

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0074

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859

variable (k : ℕ) (sizes : Fin k → ℕ)

def d027958 (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) : _root_.GD.N0074.d023612 k sizes :=
  ⟨(_root_.GD.N0074.d027954 k sizes f hf).toLp f, fun θ =>
    (memLp_congr_ae ((_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le
      (_root_.GD.N0074.d027954 k sizes f hf).coeFn_toLp)).mpr (hf θ)⟩

theorem d027959 (f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ((_root_.GD.N0074.d027958 k sizes f hf).val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
      =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f :=
  (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le
    (_root_.GD.N0074.d027954 k sizes f hf).coeFn_toLp

theorem d027960 (f g : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ))
    (hg : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp g 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) :
    _root_.GD.N0074.d027958 k sizes f hf = _root_.GD.N0074.d027958 k sizes g hg ↔
      f =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] g := by
  constructor
  · intro h
    have he : (_root_.GD.N0074.d027958 k sizes f hf).val = (_root_.GD.N0074.d027958 k sizes g hg).val :=
      congrArg Subtype.val h
    exact (_root_.GD.N0074.d027959 k sizes f hf (_root_.GD.N0232.N0719.N0859.d010810 k)).symm.trans
      ((Lp.ext_iff.mp he).trans (_root_.GD.N0074.d027959 k sizes g hg (_root_.GD.N0232.N0719.N0859.d010810 k)))
  · intro h
    apply Subtype.ext
    apply Lp.ext
    exact (_root_.GD.N0074.d027959 k sizes f hf (_root_.GD.N0232.N0719.N0859.d010810 k)).trans
      (h.trans (_root_.GD.N0074.d027959 k sizes g hg (_root_.GD.N0232.N0719.N0859.d010810 k)).symm)

theorem d027961 (d : _root_.GD.N0074.d023612 k sizes) :
    ∃ f : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ, Measurable f ∧
      ∃ hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ),
        _root_.GD.N0074.d027958 k sizes f hf = d := by
  obtain ⟨f, hfm, hfd⟩ := _root_.GD.N0074.N0308.d022077 k sizes d.val
  let hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) :=
    fun θ => (memLp_congr_ae (hfd θ)).mp (d.property θ)
  refine ⟨f, hfm, hf, ?_⟩
  apply Subtype.ext
  apply Lp.ext
  exact (_root_.GD.N0074.d027959 k sizes f hf (_root_.GD.N0232.N0719.N0859.d010810 k)).trans
    (hfd (_root_.GD.N0232.N0719.N0859.d010810 k)).symm

end
end GD.N0074

#print axioms _root_.GD.N0074.d027959
#print axioms _root_.GD.N0074.d027960
#print axioms _root_.GD.N0074.d027961
