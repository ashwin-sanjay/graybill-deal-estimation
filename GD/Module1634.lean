import GD.Module1533
import GD.Module1368

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0090
noncomputable section
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962
open _root_.GD.N0069 _root_.GD.N0051 _root_.GD.N0052

private theorem d027945 (sizes : Fin 3 → ℕ) (i : Fin 3)
    {n : ℕ} (hn : 1 ≤ n) (h : n ≤ sizes i) :
    ((n - 1 : ℕ) : ℝ) / 2 ≤ _root_.GD.N0069.d022756 sizes i := by
  unfold _root_.GD.N0069.d022756
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (by omega)) (by norm_num)


def d027946 (sizes : Fin 3 → ℕ) : _root_.GD.N0232.N0719.N0859.d010811 3 sizes → ℝ :=
  _root_.GD.N0052.d007226
    (_root_.GD.N0069.d023854 sizes 0 1 (_root_.GD.N0051.d023841 1 (9 / 4)))
    (_root_.GD.N0069.d023854 sizes 0 2 (_root_.GD.N0051.d023841 1 (9 / 4)))
    (_root_.GD.N0069.d023854 sizes 1 2 (_root_.GD.N0051.d023841 1 1))

def d027947 (sizes : Fin 3 → ℕ) : ℝ :=
  max (_root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes 0) (_root_.GD.N0069.d022756 sizes 1) 1 (9 / 4))
    (max (_root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes 0) (_root_.GD.N0069.d022756 sizes 2) 1 (9 / 4))
      (_root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes 1) (_root_.GD.N0069.d022756 sizes 2) 1 1))



theorem d027948 (sizes : Fin 3 → ℕ)
    (h0 : 2 ≤ sizes 0) (h1 : 6 ≤ sizes 1) (h2 : 6 ≤ sizes 2) :
    0 < _root_.GD.N0090.d027947 sizes ∧ Measurable (_root_.GD.N0090.d027946 sizes) ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 3, _root_.GD.N0232.N0719.N0962.d012186 3 sizes θ (_root_.GD.N0090.d027946 sizes) ≤
        ENNReal.ofReal (6 * _root_.GD.N0090.d027947 sizes) := by
  have hn : ∀ i, 2 ≤ sizes i := by
    intro i
    fin_cases i
    · exact h0
    · exact (by decide : 2 ≤ 6).trans h1
    · exact (by decide : 2 ≤ 6).trans h2
  have hn' : ∀ i, 0 < sizes i := fun i => by have := hn i; omega
  have s0 : (1 : ℝ) / 2 ≤ _root_.GD.N0069.d022756 sizes 0 := by
    simpa using _root_.GD.N0090.d027945 sizes 0 (by decide : 1 ≤ 2) h0
  have s1 : (5 : ℝ) / 2 ≤ _root_.GD.N0069.d022756 sizes 1 := by
    simpa using _root_.GD.N0090.d027945 sizes 1 (by decide : 1 ≤ 6) h1
  have s2 : (5 : ℝ) / 2 ≤ _root_.GD.N0069.d022756 sizes 2 := by
    simpa using _root_.GD.N0090.d027945 sizes 2 (by decide : 1 ≤ 6) h2
  have a0 : (1 : ℝ) / (9 / 4) < _root_.GD.N0069.d022756 sizes 0 := by linarith
  have a1 : (9 / 4 : ℝ) / 1 < _root_.GD.N0069.d022756 sizes 1 := by linarith
  have a2 : (9 / 4 : ℝ) / 1 < _root_.GD.N0069.d022756 sizes 2 := by linarith
  have b1 : (1 : ℝ) / 1 < _root_.GD.N0069.d022756 sizes 1 := by linarith
  have b2 : (1 : ℝ) / 1 < _root_.GD.N0069.d022756 sizes 2 := by linarith
  have r01 := _root_.GD.N0069.d023857 sizes hn 0 1 (by decide)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 9 / 4) a0 a1
  have r02 := _root_.GD.N0069.d023857 sizes hn 0 2 (by decide)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 9 / 4) a0 a2
  have r12 := _root_.GD.N0069.d023857 sizes hn 1 2 (by decide)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) b1 b2
  have c01 : _root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes 0) (_root_.GD.N0069.d022756 sizes 1) 1 (9 / 4) ≤ _root_.GD.N0090.d027947 sizes :=
    le_max_left _ _
  have c02 : _root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes 0) (_root_.GD.N0069.d022756 sizes 2) 1 (9 / 4) ≤ _root_.GD.N0090.d027947 sizes :=
    (le_max_left _ _).trans (le_max_right _ _)
  have c12 : _root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes 1) (_root_.GD.N0069.d022756 sizes 2) 1 1 ≤ _root_.GD.N0090.d027947 sizes :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hC : 0 < _root_.GD.N0090.d027947 sizes :=
    (_root_.GD.N0051.d023843 (_root_.GD.N0069.d022757 sizes hn 0) (_root_.GD.N0069.d022757 sizes hn 1) a0 a1).trans_le c01
  refine ⟨hC, ?_⟩
  apply _root_.GD.N0052.d022049 sizes hn' _ _ _ r01.1 r02.1 r12.1 hC.le
  · intro θ
    exact (r01.2 θ).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right c01 (le_of_lt (lt_min
        (_root_.GD.N0069.d023851 sizes hn θ 0) (_root_.GD.N0069.d023851 sizes hn θ 1)))))
  · intro θ
    exact (r02.2 θ).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right c02 (le_of_lt (lt_min
        (_root_.GD.N0069.d023851 sizes hn θ 0) (_root_.GD.N0069.d023851 sizes hn θ 2)))))
  · intro θ
    exact (r12.2 θ).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right c12 (le_of_lt (lt_min
        (_root_.GD.N0069.d023851 sizes hn θ 1) (_root_.GD.N0069.d023851 sizes hn θ 2)))))

theorem d027949 (sizes : Fin 3 → ℕ)
    (h0 : 2 ≤ sizes 0) (h1 : 6 ≤ sizes 1) (h2 : 6 ≤ sizes 2) :
    _root_.GD.N0232.N0719.N0962.d012187 3 sizes (_root_.GD.N0090.d027946 sizes) ≤ ENNReal.ofReal (6 * _root_.GD.N0090.d027947 sizes) := by
  exact iSup_le (_root_.GD.N0090.d027948 sizes h0 h1 h2).2.2


theorem d027950 (sizes : Fin 3 → ℕ)
    (h0 : 2 ≤ sizes 0) (h1 : 6 ≤ sizes 1) (h2 : 6 ≤ sizes 2) :
    _root_.GD.N0232.N0719.N0962.d012188 3 sizes ≤ ENNReal.ofReal (6 * _root_.GD.N0090.d027947 sizes) := by
  exact (_root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0719.N0962.d012186 3 sizes) (_root_.GD.N0090.d027948 sizes h0 h1 h2).2.1).trans
    (_root_.GD.N0090.d027949 sizes h0 h1 h2)

theorem d027951 (sizes : Fin 3 → ℕ)
    (h0 : 2 ≤ sizes 0) (h1 : 6 ≤ sizes 1) (h2 : 6 ≤ sizes 2) :
    _root_.GD.N0232.N0719.N0962.d012188 3 sizes ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0090.d027950 sizes h0 h1 h2)

end
end GD.N0090

#print axioms _root_.GD.N0090.d027948
#print axioms _root_.GD.N0090.d027949
#print axioms _root_.GD.N0090.d027950
#print axioms _root_.GD.N0090.d027951
