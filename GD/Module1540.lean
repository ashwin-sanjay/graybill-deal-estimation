import GD.Module1537
import GD.Module1534

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0032
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0051 _root_.GD.N0069 _root_.GD.N0031

variable {k : ℕ}


theorem d023887
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i j : Fin k) (hij : i ≠ j)
    (hab : _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j = 1) :
    Measurable (_root_.GD.N0069.d023854 sizes i j (_root_.GD.N0051.d023841 (_root_.GD.N0069.d022756 sizes i) 1)) ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
          (_root_.GD.N0069.d023854 sizes i j (_root_.GD.N0051.d023841 (_root_.GD.N0069.d022756 sizes i) 1)) ≤
        ENNReal.ofReal (_root_.GD.N0031.d023872 (_root_.GD.N0069.d022756 sizes i) (_root_.GD.N0069.d022756 sizes j) (_root_.GD.N0069.d022756 sizes i) 1 *
          min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
  have hf : Measurable (_root_.GD.N0051.d023841 (_root_.GD.N0069.d022756 sizes i) 1) := _root_.GD.N0051.d022771 _ _
  refine ⟨_root_.GD.N0069.d023855 sizes i j _ hf, ?_⟩
  intro θ
  rw [_root_.GD.N0069.d023856 sizes hn i j hij θ _ hf]
  have hb := _root_.GD.N0031.d023875 (m := θ.location)
    (_root_.GD.N0069.d022757 sizes hn i) (_root_.GD.N0069.d022757 sizes hn j) hab
    (_root_.GD.N0069.d023851 sizes hn θ i) (_root_.GD.N0069.d023851 sizes hn θ j)
  rw [← ofReal_integral_eq_lintegral_ofReal hb.1 (ae_of_all _ fun _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hb.2


theorem d023888
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i j : Fin k) (hij : i ≠ j)
    (hab : 1 ≤ _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤
        ENNReal.ofReal (C * min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
  rcases hab.eq_or_lt with hab | hab
  · have hh := _root_.GD.N0032.d023887 sizes hn i j hij hab.symm
    exact ⟨_root_.GD.N0031.d023872 (_root_.GD.N0069.d022756 sizes i) (_root_.GD.N0069.d022756 sizes j) (_root_.GD.N0069.d022756 sizes i) 1,
      (_root_.GD.N0031.d023873 (_root_.GD.N0069.d022757 sizes hn j) (_root_.GD.N0069.d022757 sizes hn i) (by norm_num)).le,
      _, hh⟩
  · obtain ⟨r, hr, hrb, hra⟩ := (_root_.GD.N0051.d022772 (_root_.GD.N0069.d022757 sizes hn i)).mpr hab
    have hqr : r / 1 < _root_.GD.N0069.d022756 sizes j := by simpa using hrb
    have hh := _root_.GD.N0069.d023857 sizes hn i j hij
      (by norm_num : (0 : ℝ) < 1) hr hra hqr
    exact ⟨_root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes i) (_root_.GD.N0069.d022756 sizes j) 1 r,
      (_root_.GD.N0051.d023843 (_root_.GD.N0069.d022757 sizes hn i) (_root_.GD.N0069.d022757 sizes hn j) hra hqr).le, _, hh⟩

end
end GD.N0032

#print axioms _root_.GD.N0032.d023887
#print axioms _root_.GD.N0032.d023888
