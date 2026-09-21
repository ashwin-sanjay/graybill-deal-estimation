import GD.Module1346











set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0106.N0428.N0761
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859



theorem d021789 {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 k sizes theta) := by
  have herror : MemLp
      (fun omega : _root_.GD.N0232.N0719.d009173 k sizes => _root_.GD.N0232.N0719.N0859.d010815 k sizes omega - theta.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
    _root_.GD.N0232.N0719.N0910.d010294 sizes hk hn theta.location theta.scale
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0232.N0719.N0972.d012340 _root_.GD.N0141.d006684
  exact (ofReal_integral_eq_lintegral_ofReal herror.integrable_sq
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm


theorem d021790 {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  rw [_root_.GD.N0106.N0428.N0761.d021789 hk sizes hn theta, ENNReal.ofReal_pos]
  exact _root_.GD.N0106.N0428.N0762.d021788 hk sizes hn theta


theorem d021791 {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) ≠ ∞ := by
  rw [_root_.GD.N0106.N0428.N0761.d021789 hk sizes hn theta]
  exact ENNReal.ofReal_ne_top


theorem d021792 {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) ∧
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) < ∞ := by
  exact ⟨_root_.GD.N0106.N0428.N0761.d021790 hk sizes hn theta,
    lt_top_iff_ne_top.mpr (_root_.GD.N0106.N0428.N0761.d021791 hk sizes hn theta)⟩

end
end GD.N0106.N0428.N0761

#print axioms _root_.GD.N0106.N0428.N0761.d021789
#print axioms _root_.GD.N0106.N0428.N0761.d021790
#print axioms _root_.GD.N0106.N0428.N0761.d021791
#print axioms _root_.GD.N0106.N0428.N0761.d021792
