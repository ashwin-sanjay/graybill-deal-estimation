import GD.Module1518
import GD.Module1444
import GD.Module1370

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0074

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N1012

variable (k : ℕ) (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)

def d023620 (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0074.d023612 k sizes →ₗ[ℝ] _root_.GD.N0074.d023614 k sizes where
  toFun d := ⟨⟨_root_.GD.N0232.N0719.N1012.d011399 k sizes d.val,
    fun θ => _root_.GD.N0074.d022924 k sizes hsizes θ d.val (d.property θ)⟩,
    (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mpr
      (_root_.GD.N0232.N0719.N1012.d011401 k sizes d.val)⟩
  map_add' d e := by
    apply Subtype.ext
    apply Subtype.ext
    exact (_root_.GD.N0232.N0719.N1012.d011399 k sizes).map_add d.val e.val
  map_smul' c d := by
    apply Subtype.ext
    apply Subtype.ext
    exact (_root_.GD.N0232.N0719.N1012.d011399 k sizes).map_smul c d.val

@[simp] theorem d023621 (d : _root_.GD.N0074.d023612 k sizes) :
    (_root_.GD.N0074.d023620 k sizes hsizes d).val.val = _root_.GD.N0232.N0719.N1012.d011399 k sizes d.val := rfl

theorem d023622 (d : _root_.GD.N0074.d023614 k sizes) :
    _root_.GD.N0074.d023620 k sizes hsizes d.val = d := by
  apply Subtype.ext
  apply Subtype.ext
  exact (_root_.GD.N0232.N0719.N1012.d011405 k sizes d.val.val).mpr
    ((_root_.GD.N0074.d023615 k sizes d.val).mp d.property)

theorem d023623 (d : _root_.GD.N0074.d023612 k sizes) :
    _root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0074.d023620 k sizes hsizes d).val =
      _root_.GD.N0074.d023620 k sizes hsizes d := _root_.GD.N0074.d023622 k sizes hsizes _

theorem d023624 (d : _root_.GD.N0074.d023612 k sizes) :
    _root_.GD.N0074.d023620 k sizes hsizes (d - (_root_.GD.N0074.d023620 k sizes hsizes d).val) = 0 := by
  rw [map_sub, _root_.GD.N0074.d023623, sub_self]

theorem d023625 (d : _root_.GD.N0074.d023612 k sizes) :
    d = (_root_.GD.N0074.d023620 k sizes hsizes d).val + (d - (_root_.GD.N0074.d023620 k sizes hsizes d).val) := by
  abel

theorem d023626 (d : _root_.GD.N0074.d023612 k sizes)
    (h : _root_.GD.N0074.N0308.d022069 k → ℝ) (hh : Measurable h)
    (C : ℝ) (hC : ∀ s, ‖h s‖ ≤ C) :
    (∫ x, h (_root_.GD.N0074.N0308.d022071 k sizes x) *
      (d.val x - (_root_.GD.N0074.d023620 k sizes hsizes d).val.val x)
      ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) = 0 := by
  exact _root_.GD.N0074.d022923 k sizes d.val
    (h ∘ _root_.GD.N0074.N0308.d022071 k sizes)
    (hh.comp (_root_.GD.N0074.N0308.d022073 k sizes
      (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hsizes i)))).stronglyMeasurable
    C (Filter.Eventually.of_forall (fun x => hC _))

theorem d023627 (d : _root_.GD.N0074.d023612 k sizes) :
    ‖d.val‖ ^ 2 = ‖(_root_.GD.N0074.d023620 k sizes hsizes d).val.val‖ ^ 2 +
      ‖d.val - (_root_.GD.N0074.d023620 k sizes hsizes d).val.val‖ ^ 2 :=
  _root_.GD.N0232.N0719.N1012.d011402 k sizes d.val

theorem d023628 (d : _root_.GD.N0074.d023612 k sizes) :
    ∃ h : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable h ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        ((_root_.GD.N0074.d023620 k sizes hsizes d).val.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
          =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] h ∘ _root_.GD.N0074.N0308.d022071 k sizes :=
  _root_.GD.N0074.N0308.d022075 k sizes d.val

def d023629 : _root_.GD.N0074.d023618 := fun n => _root_.GD.N0074.d023620 n.groups n.sizes n.sizes_ge

end
end GD.N0074

#print axioms _root_.GD.N0074.d023622
#print axioms _root_.GD.N0074.d023623
#print axioms _root_.GD.N0074.d023624
#print axioms _root_.GD.N0074.d023625
#print axioms _root_.GD.N0074.d023626
#print axioms _root_.GD.N0074.d023627
#print axioms _root_.GD.N0074.d023628
