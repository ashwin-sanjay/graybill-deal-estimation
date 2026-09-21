import GD.Module0623













open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0107

noncomputable section

open _root_.GD.N0137

theorem d012721
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    1 - _root_.GD.N0107.d009046 m n σ τ =
      _root_.GD.N0107.d009043 m σ / _root_.GD.N0107.d009045 m n σ τ := by
  apply _root_.GD.N0144.d006708
  exact (_root_.GD.N0107.d009049 hm hn hσ hτ).ne'



theorem d012722
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    Real.sqrt (_root_.GD.N0107.d009045 m n σ τ) *
        Real.sqrt (1 - _root_.GD.N0107.d009046 m n σ τ) *
        Real.sqrt m / σ = 1 := by
  let S := _root_.GD.N0107.d009045 m n σ τ
  let e := _root_.GD.N0107.d009046 m n σ τ
  have hS : 0 < S := _root_.GD.N0107.d009049 hm hn hσ hτ
  have he1 : e < 1 := _root_.GD.N0107.d009051 hm hn hσ hτ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnonneg :
      0 ≤ Real.sqrt S * Real.sqrt (1 - e) * Real.sqrt m / σ := by
    positivity
  have hsquare :
      (Real.sqrt S * Real.sqrt (1 - e) * Real.sqrt m / σ) ^ 2 = 1 := by
    calc
      (Real.sqrt S * Real.sqrt (1 - e) * Real.sqrt m / σ) ^ 2 =
          (Real.sqrt S) ^ 2 * (Real.sqrt (1 - e)) ^ 2 *
            (Real.sqrt m) ^ 2 / σ ^ 2 := by ring
      _ = S * (1 - e) * m / σ ^ 2 := by
        rw [Real.sq_sqrt hS.le,
          Real.sq_sqrt (sub_nonneg.mpr he1.le),
          Real.sq_sqrt hmR.le]
      _ = 1 := by
        dsimp [S, e]
        rw [_root_.GD.N0107.d012721 hm hn hσ hτ]
        unfold _root_.GD.N0107.d009043
        have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
        have hS0 :
            _root_.GD.N0107.d009045 m n σ τ ≠ 0 :=
          (_root_.GD.N0107.d009049 hm hn hσ hτ).ne'
        field_simp [hm0, hS0, hσ.ne']
  nlinarith



theorem d012723
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    Real.sqrt (_root_.GD.N0107.d009045 m n σ τ) *
        Real.sqrt (_root_.GD.N0107.d009046 m n σ τ) *
        Real.sqrt n / τ = 1 := by
  let S := _root_.GD.N0107.d009045 m n σ τ
  let e := _root_.GD.N0107.d009046 m n σ τ
  have hS : 0 < S := _root_.GD.N0107.d009049 hm hn hσ hτ
  have he0 : 0 < e := _root_.GD.N0107.d009050 hm hn hσ hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg :
      0 ≤ Real.sqrt S * Real.sqrt e * Real.sqrt n / τ := by
    positivity
  have hsquare :
      (Real.sqrt S * Real.sqrt e * Real.sqrt n / τ) ^ 2 = 1 := by
    calc
      (Real.sqrt S * Real.sqrt e * Real.sqrt n / τ) ^ 2 =
          (Real.sqrt S) ^ 2 * (Real.sqrt e) ^ 2 *
            (Real.sqrt n) ^ 2 / τ ^ 2 := by ring
      _ = S * e * n / τ ^ 2 := by
        rw [Real.sq_sqrt hS.le, Real.sq_sqrt he0.le,
          Real.sq_sqrt hnR.le]
      _ = 1 := by
        dsimp [S, e]
        unfold _root_.GD.N0107.d009046 _root_.GD.N0107.d009044
        have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
        have hS0 :
            _root_.GD.N0107.d009045 m n σ τ ≠ 0 :=
          (_root_.GD.N0107.d009049 hm hn hσ hτ).ne'
        field_simp [hn0, hS0, hτ.ne']
  nlinarith



theorem d012724
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009038 m n μ σ τ
        (_root_.GD.N0107.d009046 m n σ τ)
        (_root_.GD.N0107.d009045 m n σ τ) ω =
      _root_.GD.N0107.d009090 m n ω := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold _root_.GD.N0107.d009038 _root_.GD.N0137.d008942
    _root_.GD.N0137.d008932 _root_.GD.N0137.d008919 _root_.GD.N0137.d008896
    _root_.GD.N0107.d009025 _root_.GD.N0107.d009090 _root_.GD.N0107.d009084
  simp only [Function.comp_apply]
  rw [_root_.GD.N0107.d009087 (by omega) μ σ ω.1,
    _root_.GD.N0107.d009087 (by omega) μ τ ω.2]
  have hfirst :=
    _root_.GD.N0107.d012722
      (m := m) (n := n) (by omega) (by omega) hσ hτ
  have hsecond :=
    _root_.GD.N0107.d012723
      (m := m) (n := n) (by omega) (by omega) hσ hτ
  calc
    Real.sqrt (_root_.GD.N0107.d009045 m n σ τ) *
        (Real.sqrt (1 - _root_.GD.N0107.d009046 m n σ τ) *
            (Real.sqrt ↑m *
              ((_root_.GD.N0126.d006420 ω.1 - μ) / σ)) -
          Real.sqrt (_root_.GD.N0107.d009046 m n σ τ) *
            (Real.sqrt ↑n *
              ((_root_.GD.N0126.d006420 ω.2 - μ) / τ))) =
      (Real.sqrt (_root_.GD.N0107.d009045 m n σ τ) *
          Real.sqrt (1 - _root_.GD.N0107.d009046 m n σ τ) *
          Real.sqrt m / σ) *
            (_root_.GD.N0126.d006420 ω.1 - μ) -
        (Real.sqrt (_root_.GD.N0107.d009045 m n σ τ) *
          Real.sqrt (_root_.GD.N0107.d009046 m n σ τ) *
          Real.sqrt n / τ) *
            (_root_.GD.N0126.d006420 ω.2 - μ) := by ring
    _ = _ := by rw [hfirst, hsecond]; ring

end

end GD.N0107
