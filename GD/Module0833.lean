import GD.Module0832










open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0107

noncomputable section

open _root_.GD.N0137


def d012738
    (m n : ℕ) (μ σ τ e Sigma : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ :=
  _root_.GD.N0137.d008945 m n e Sigma ∘ _root_.GD.N0107.d009025 m n μ σ τ

@[fun_prop] theorem d012739
    (m n : ℕ) (μ σ τ e Sigma : ℝ) :
    Measurable (_root_.GD.N0107.d012738 m n μ σ τ e Sigma) := by
  unfold _root_.GD.N0107.d012738 _root_.GD.N0137.d008945
  exact measurable_const.mul
    ((_root_.GD.N0137.d008936 m n e).comp
      (_root_.GD.N0107.d009027 m n μ σ τ))




theorem d012740
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d012738 m n μ σ τ
        (_root_.GD.N0107.d009046 m n σ τ)
        (_root_.GD.N0107.d009045 m n σ τ) ω =
      _root_.GD.N0107.d012732 m n μ
        (_root_.GD.N0107.d009046 m n σ τ) ω := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let S := _root_.GD.N0107.d009045 m n σ τ
  let e := _root_.GD.N0107.d009046 m n σ τ
  have hS : 0 < S :=
    _root_.GD.N0107.d009049 (by omega) (by omega) hσ hτ
  have he0 : 0 < e :=
    _root_.GD.N0107.d009050 (by omega) (by omega) hσ hτ
  have he1 : e < 1 :=
    _root_.GD.N0107.d009051 (by omega) (by omega) hσ hτ
  have hfirst :=
    _root_.GD.N0107.d012722
      (m := m) (n := n) (by omega) (by omega) hσ hτ
  have hsecond :=
    _root_.GD.N0107.d012723
      (m := m) (n := n) (by omega) (by omega) hσ hτ
  change Real.sqrt S * Real.sqrt (1 - e) * Real.sqrt m / σ = 1
    at hfirst
  change Real.sqrt S * Real.sqrt e * Real.sqrt n / τ = 1
    at hsecond
  unfold _root_.GD.N0107.d012738 _root_.GD.N0137.d008945 _root_.GD.N0137.d008931
    _root_.GD.N0137.d008918 _root_.GD.N0137.d008896 _root_.GD.N0107.d009025
    _root_.GD.N0107.d012732 _root_.GD.N0107.d009090 _root_.GD.N0107.d009084
  simp only [Function.comp_apply]
  rw [_root_.GD.N0107.d009087 (by omega) μ σ ω.1,
    _root_.GD.N0107.d009087 (by omega) μ τ ω.2]
  change
    Real.sqrt (S * e * (1 - e)) *
        (Real.sqrt e *
            (Real.sqrt ↑m *
              ((_root_.GD.N0126.d006420 ω.1 - μ) / σ)) +
          Real.sqrt (1 - e) *
            (Real.sqrt ↑n *
              ((_root_.GD.N0126.d006420 ω.2 - μ) / τ))) =
      _root_.GD.N0126.d006420 ω.2 +
        e * (_root_.GD.N0126.d006420 ω.1 -
          _root_.GD.N0126.d006420 ω.2) - μ
  rw [Real.sqrt_mul (mul_nonneg hS.le he0.le),
    Real.sqrt_mul hS.le]
  calc
    Real.sqrt S * Real.sqrt e * Real.sqrt (1 - e) *
        (Real.sqrt e *
            (Real.sqrt ↑m *
              ((_root_.GD.N0126.d006420 ω.1 - μ) / σ)) +
          Real.sqrt (1 - e) *
            (Real.sqrt ↑n *
              ((_root_.GD.N0126.d006420 ω.2 - μ) / τ))) =
      (Real.sqrt S * Real.sqrt (1 - e) * Real.sqrt m / σ) *
          (Real.sqrt e) ^ 2 *
            (_root_.GD.N0126.d006420 ω.1 - μ) +
        (Real.sqrt S * Real.sqrt e * Real.sqrt n / τ) *
          (Real.sqrt (1 - e)) ^ 2 *
            (_root_.GD.N0126.d006420 ω.2 - μ) := by ring
    _ = e * (_root_.GD.N0126.d006420 ω.1 - μ) +
        (1 - e) * (_root_.GD.N0126.d006420 ω.2 - μ) := by
      rw [Real.sq_sqrt he0.le,
        Real.sq_sqrt (sub_nonneg.mpr he1.le), hfirst, hsecond]
      ring
    _ = _ := by ring

end

end GD.N0107
