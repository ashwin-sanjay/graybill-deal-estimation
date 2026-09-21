import GD.Module1456
import GD.Module0491

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0068
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0038

variable {k : ℕ}

def d023031 (sizes : Fin k → ℕ)
    (d : ∀ i j, _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (i j : Fin k) : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  if i < j then _root_.GD.N0068.d023024 sizes i j (d i j) else _root_.GD.N0068.d023024 sizes j i (d j i)

theorem d023032 (sizes : Fin k → ℕ)
    (d : ∀ i j, _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (hd : ∀ i j, Measurable (d i j)) (i j : Fin k) : Measurable (_root_.GD.N0068.d023031 sizes d i j) := by
  unfold _root_.GD.N0068.d023031
  split_ifs
  · exact _root_.GD.N0068.d023025 sizes i j (d i j) (hd i j)
  · exact _root_.GD.N0068.d023025 sizes j i (d j i) (hd j i)

theorem d023033 (sizes : Fin k → ℕ)
    (d : ∀ i j, _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (i j : Fin k) (ω : _root_.GD.N0232.N0719.N0859.d010811 k sizes) : _root_.GD.N0068.d023031 sizes d i j ω = _root_.GD.N0068.d023031 sizes d j i ω := by
  by_cases h : i = j
  · subst j
    rfl
  rcases lt_or_gt_of_ne h with h | h
  · simp [_root_.GD.N0068.d023031, h, not_lt_of_ge h.le]
  · simp [_root_.GD.N0068.d023031, h, not_lt_of_ge h.le]

def d023034 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (d : ∀ i j, _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ) :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ := _root_.GD.N0038.d007546 hk (_root_.GD.N0068.d023031 sizes d)



theorem d023035 (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (d : ∀ i j, _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (hd : ∀ i j, Measurable (d i j)) (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ i j, i ≠ j → ∀ θ,
      _root_.GD.N0232.N0720.N1080.d014197 (sizes i) (sizes j) θ (d i j) ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 (sizes i) (sizes j) θ)) :
    Measurable (_root_.GD.N0068.d023034 hk sizes d) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0068.d023034 hk sizes d) ≤
        ENNReal.ofReal ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * C *
          _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
  have he := _root_.GD.N0068.d023032 sizes d hd
  refine ⟨_root_.GD.N0038.d007547 hk _ he, ?_⟩
  intro θ
  have hb (i j : Fin k) (hij : i ≠ j) :
      _root_.GD.N0038.d007554 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location (_root_.GD.N0068.d023031 sizes d i j) ≤
        ENNReal.ofReal (C * min (_root_.GD.N0068.d023027 sizes θ i) (_root_.GD.N0068.d023027 sizes θ j)) := by
    change _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0068.d023031 sizes d i j) ≤ _
    unfold _root_.GD.N0068.d023031
    split_ifs
    · rw [_root_.GD.N0068.d023026 sizes i j hij (d i j) (hd i j)]
      exact (hcap i j hij (_root_.GD.N0068.d023020 θ i j)).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (_root_.GD.N0068.d023029 sizes hn θ i j) hC))
    · rw [_root_.GD.N0068.d023026 sizes j i hij.symm (d j i) (hd j i)]
      have hh := (hcap j i hij.symm (_root_.GD.N0068.d023020 θ j i)).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (_root_.GD.N0068.d023029 sizes hn θ j i) hC))
      simpa only [min_comm] using hh
  simpa only [_root_.GD.N0068.d023034, _root_.GD.N0068.d023030, _root_.GD.N0038.d007554, _root_.GD.N0232.N0719.N0859.d010840] using
    _root_.GD.N0038.d007559 hk (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location (_root_.GD.N0068.d023031 sizes d) he
      (_root_.GD.N0068.d023033 sizes d) (_root_.GD.N0068.d023027 sizes θ) (_root_.GD.N0068.d023028 sizes hn θ) hC hb

theorem d023036 (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (d : ∀ i j, _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (hd : ∀ i j, Measurable (d i j)) (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ i j, i ≠ j → ∀ θ,
      _root_.GD.N0232.N0720.N1080.d014197 (sizes i) (sizes j) θ (d i j) ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 (sizes i) (sizes j) θ)) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ ENNReal.ofReal ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * C) := by
  obtain ⟨hd', hb⟩ := _root_.GD.N0068.d023035 hk sizes hn d hd C hC hcap
  apply (_root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd').trans
  apply iSup_le
  intro θ
  exact (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) (fun i => by have := hn i; omega)
    _ (by positivity) θ _).mpr (hb θ)

end
end GD.N0068

#print axioms _root_.GD.N0068.d023035
#print axioms _root_.GD.N0068.d023036
