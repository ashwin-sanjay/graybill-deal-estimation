import GD.Module0758
import GD.Module0727

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0074

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N1012

variable (k : ℕ) (sizes : Fin k → ℕ)

abbrev d023610 := Lp ℝ 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)

def d023611 : Submodule ℝ (_root_.GD.N0074.d023610 k sizes) where
  carrier := {d | ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
    MemLp (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)}
  zero_mem' := by
    intro θ
    exact (memLp_congr_ae
      ((_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le
        (Lp.coeFn_zero ℝ 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)))).mpr MemLp.zero
  add_mem' := by
    intro d e hd he θ
    exact (memLp_congr_ae
      ((_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le (Lp.coeFn_add d e))).mpr
      ((hd θ).add (he θ))
  smul_mem' := by
    intro c d hd θ
    exact (memLp_congr_ae
      ((_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le (Lp.coeFn_smul c d))).mpr
      ((hd θ).const_smul c)

abbrev d023612 := _root_.GD.N0074.d023611 k sizes

def d023613 : Submodule ℝ (_root_.GD.N0074.d023612 k sizes) :=
  (lpMeas ℝ ℝ (_root_.GD.N0232.N0719.N1012.d011397 k sizes) 2
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)).comap (_root_.GD.N0074.d023611 k sizes).subtype

abbrev d023614 := _root_.GD.N0074.d023613 k sizes

theorem d023615 (d : _root_.GD.N0074.d023612 k sizes) :
    d ∈ _root_.GD.N0074.d023613 k sizes ↔
      AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
        (d.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)

theorem d023616 (d : _root_.GD.N0074.d023612 k sizes) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp (d.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := d.property θ

structure d023617 where
  groups : ℕ
  groups_ge : 2 ≤ groups
  sizes : Fin groups → ℕ
  sizes_ge : ∀ i, 2 ≤ sizes i

abbrev d023618 := ∀ n : _root_.GD.N0074.d023617,
  _root_.GD.N0074.d023612 n.groups n.sizes →ₗ[ℝ] _root_.GD.N0074.d023614 n.groups n.sizes

theorem d023619 {α : Sort*} (C : α → Prop) :
    (∃ p, C p) ↔ ¬ (∀ p, ¬ C p) := by
  classical
  simp only [not_forall, not_not]

end
end GD.N0074

#print axioms _root_.GD.N0074.d023615
#print axioms _root_.GD.N0074.d023616
#print axioms _root_.GD.N0074.d023619
