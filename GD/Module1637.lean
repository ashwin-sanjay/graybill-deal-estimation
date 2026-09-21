import GD.Module1519
import GD.Module1635
import GD.Module1445
import GD.Module1446
import GD.Module1636

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0074

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N1012

def d027962 (P : _root_.GD.N0074.d023618) : Prop :=
  ∀ (n : _root_.GD.N0074.d023617) (d : _root_.GD.N0074.d023612 n.groups n.sizes),
    (∀ (h : _root_.GD.N0074.N0308.d022069 n.groups → ℝ), Measurable h →
      ∀ C : ℝ, (∀ s, ‖h s‖ ≤ C) →
        (∫ x, h (_root_.GD.N0074.N0308.d022071 n.groups n.sizes x) *
          (d.val x - (P n d).val.val x)
          ∂_root_.GD.N0232.N0719.N0859.d010813 n.groups n.sizes) = 0) ∧
    (∀ (a : ℝ) (ha : 0 < a) (b : ℝ),
      (P n (_root_.GD.N0074.d027955 n.groups n.sizes b a ha d)).val =
        _root_.GD.N0074.d027955 n.groups n.sizes b a ha (P n d).val)

def d027963 : Prop := ∀ P : _root_.GD.N0074.d023618, ¬ _root_.GD.N0074.d027962 P

theorem d027964 (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (a : ℝ) (ha : 0 < a) (b : ℝ)
    (d : _root_.GD.N0074.d023612 k sizes) :
    (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0074.d027955 k sizes b a ha d)).val =
      _root_.GD.N0074.d027955 k sizes b a ha (_root_.GD.N0074.d023620 k sizes hsizes d).val := by
  apply Subtype.ext
  apply Lp.ext
  exact (_root_.GD.N0074.d022933 k sizes hsizes b a ha d.val
    (_root_.GD.N0074.d027955 k sizes b a ha d).val d.property
    (_root_.GD.N0074.d027956 k sizes b a ha d (_root_.GD.N0232.N0719.N0859.d010810 k))).trans
      (_root_.GD.N0074.d027956 k sizes b a ha (_root_.GD.N0074.d023620 k sizes hsizes d).val
        (_root_.GD.N0232.N0719.N0859.d010810 k)).symm

theorem d027965 : _root_.GD.N0074.d027962 _root_.GD.N0074.d023629 := by
  intro n d
  constructor
  · intro h hh C hC
    exact _root_.GD.N0074.d023626 n.groups n.sizes n.sizes_ge d h hh C hC
  · intro a ha b
    exact _root_.GD.N0074.d027964 n.groups n.sizes n.sizes_ge a ha b d

theorem d027966 : ∃ P : _root_.GD.N0074.d023618, _root_.GD.N0074.d027962 P :=
  ⟨_root_.GD.N0074.d023629, _root_.GD.N0074.d027965⟩

theorem d027967 {P : _root_.GD.N0074.d023618} (hP : _root_.GD.N0074.d027962 P) : P = _root_.GD.N0074.d023629 := by
  funext n
  apply LinearMap.ext
  intro d
  apply Subtype.ext
  apply Subtype.ext
  exact _root_.GD.N0074.d022936 n.groups n.sizes
    (fun i => lt_of_lt_of_le (by decide : 0 < 2) (n.sizes_ge i))
    d.val (P n d).val.val
    ((_root_.GD.N0074.d023615 n.groups n.sizes (P n d).val).mp (P n d).property)
    (fun h hh hb => (hP n d).1 h hh 1 hb)

theorem d027968 : ∃! P : _root_.GD.N0074.d023618, _root_.GD.N0074.d027962 P :=
  ⟨_root_.GD.N0074.d023629, _root_.GD.N0074.d027965, fun _ h => _root_.GD.N0074.d027967 h⟩

theorem d027969 {P : _root_.GD.N0074.d023618} (hP : _root_.GD.N0074.d027962 P)
    (n : _root_.GD.N0074.d023617) (d : _root_.GD.N0074.d023612 n.groups n.sizes)
    (a : ℝ) (ha : 0 < a) (b : ℝ)
    (hd : _root_.GD.N0074.d027955 n.groups n.sizes b a ha d = d) :
    _root_.GD.N0074.d027955 n.groups n.sizes b a ha (P n d).val = (P n d).val := by
  rw [← (hP n d).2 a ha b, hd]

theorem d027970 : ¬ _root_.GD.N0074.d027963 := fun h => h _root_.GD.N0074.d023629 _root_.GD.N0074.d027965

theorem d027971 : (∃ P : _root_.GD.N0074.d023618, _root_.GD.N0074.d027962 P) ↔ ¬ _root_.GD.N0074.d027963 :=
  _root_.GD.N0074.d023619 _root_.GD.N0074.d027962

theorem d027972 :
    (∃! P : _root_.GD.N0074.d023618, _root_.GD.N0074.d027962 P) ∧ ¬ _root_.GD.N0074.d027963 ∧
      ((∃ P : _root_.GD.N0074.d023618, _root_.GD.N0074.d027962 P) ↔ ¬ _root_.GD.N0074.d027963) :=
  ⟨_root_.GD.N0074.d027968, _root_.GD.N0074.d027970, _root_.GD.N0074.d027971⟩

end
end GD.N0074

#print axioms _root_.GD.N0074.d027964
#print axioms _root_.GD.N0074.d027965
#print axioms _root_.GD.N0074.d027966
#print axioms _root_.GD.N0074.d027967
#print axioms _root_.GD.N0074.d027968
#print axioms _root_.GD.N0074.d027969
#print axioms _root_.GD.N0074.d027970
#print axioms _root_.GD.N0074.d027971
#print axioms _root_.GD.N0074.d027972
