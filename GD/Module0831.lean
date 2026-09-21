import GD.Module0830











open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0107

noncomputable section

open _root_.GD.N0137

theorem d012725
    (m n : ℕ) (hm : 2 ≤ m)
    (μ σ τ : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009033 m n μ σ τ ω =
      _root_.GD.N0107.d009085 ω.1 / σ ^ 2 := by
  unfold _root_.GD.N0107.d009033 _root_.GD.N0137.d008933 _root_.GD.N0137.d008897
    _root_.GD.N0107.d009025 _root_.GD.N0107.d009085
  simp only [Function.comp_apply]
  rw [_root_.GD.N0107.d009089 (by omega) μ σ ω.1]
  ring

theorem d012726
    (m n : ℕ) (hn : 2 ≤ n)
    (μ σ τ : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009034 m n μ σ τ ω =
      _root_.GD.N0107.d009085 ω.2 / τ ^ 2 := by
  unfold _root_.GD.N0107.d009034 _root_.GD.N0137.d008934 _root_.GD.N0137.d008897
    _root_.GD.N0107.d009025 _root_.GD.N0107.d009085
  simp only [Function.comp_apply]
  rw [_root_.GD.N0107.d009089 (by omega) μ τ ω.2]
  ring



theorem d012727
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009045 m n σ τ *
        ((1 - _root_.GD.N0107.d009046 m n σ τ) *
            _root_.GD.N0107.d009033 m n μ σ τ ω +
          _root_.GD.N0107.d009046 m n σ τ *
            _root_.GD.N0107.d009034 m n μ σ τ ω) =
      _root_.GD.N0107.d009092 m n ω := by
  rw [_root_.GD.N0107.d012725 m n hm μ σ τ ω,
    _root_.GD.N0107.d012726 m n hn μ σ τ ω,
    _root_.GD.N0107.d012721 (by omega) (by omega) hσ hτ]
  unfold _root_.GD.N0107.d009046 _root_.GD.N0107.d009045 _root_.GD.N0107.d009043
    _root_.GD.N0107.d009044 _root_.GD.N0107.d009092
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS :
      0 < σ ^ 2 / (m : ℝ) + τ ^ 2 / (n : ℝ) := by
    positivity
  field_simp [hmR.ne', hnR.ne', hσ.ne', hτ.ne', hS.ne']



theorem d012728
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009045 m n σ τ *
        (_root_.GD.N0107.d009046 m n σ τ *
          _root_.GD.N0107.d009034 m n μ σ τ ω) =
      _root_.GD.N0107.d009085 ω.2 / n := by
  rw [_root_.GD.N0107.d012726 m n hn μ σ τ ω]
  unfold _root_.GD.N0107.d009046 _root_.GD.N0107.d009044
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS :=
    _root_.GD.N0107.d009049 (show 0 < m by omega)
      (show 0 < n by omega) hσ hτ
  field_simp [hnR.ne', hτ.ne', hS.ne']



theorem d012729
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009039 m n μ σ τ
        (_root_.GD.N0107.d009046 m n σ τ) ω =
      _root_.GD.N0107.d009091 m n
        (_root_.GD.N0107.d009085 ω.1)
        (_root_.GD.N0107.d009085 ω.2) := by
  let S := _root_.GD.N0107.d009045 m n σ τ
  have hS : S ≠ 0 :=
    (_root_.GD.N0107.d009049 (by omega) (by omega) hσ hτ).ne'
  have hden :=
    _root_.GD.N0107.d012727
      m n hm hn μ σ τ hσ hτ ω
  have hnum :=
    _root_.GD.N0107.d012728
      m n hm hn μ σ τ hσ hτ ω
  unfold _root_.GD.N0107.d009039 _root_.GD.N0137.d008943
    _root_.GD.N0107.d009091 at *
  simp only [_root_.GD.N0107.d009025, Function.comp_apply]
  change
    _root_.GD.N0107.d009046 m n σ τ *
          _root_.GD.N0107.d009034 m n μ σ τ ω /
        ((1 - _root_.GD.N0107.d009046 m n σ τ) *
            _root_.GD.N0107.d009033 m n μ σ τ ω +
          _root_.GD.N0107.d009046 m n σ τ *
            _root_.GD.N0107.d009034 m n μ σ τ ω) =
      (_root_.GD.N0107.d009085 ω.2 / ↑n) /
        (_root_.GD.N0107.d009085 ω.1 / ↑m +
          _root_.GD.N0107.d009085 ω.2 / ↑n)
  calc
    _ = (S *
          (_root_.GD.N0107.d009046 m n σ τ *
            _root_.GD.N0107.d009034 m n μ σ τ ω)) /
        (S * ((1 - _root_.GD.N0107.d009046 m n σ τ) *
            _root_.GD.N0107.d009033 m n μ σ τ ω +
          _root_.GD.N0107.d009046 m n σ τ *
            _root_.GD.N0107.d009034 m n μ σ τ ω)) := by
          field_simp [hS]
    _ = _ := by
      rw [hnum, hden]
      rfl



theorem d012730
    {m n : ℕ} {sx2 sy2 : ℝ}
    (hm : 0 < m) (hn : 0 < n)
    (hsx : sx2 ≠ 0) (hsy : sy2 ≠ 0) :
    _root_.GD.N0107.d009091 m n sx2 sy2 =
      _root_.GD.N0144.d006702 (m : ℝ) (n : ℝ) sx2 sy2 := by
  unfold _root_.GD.N0107.d009091 _root_.GD.N0144.d006702
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hmR, hnR, hsx, hsy]
  ring


theorem d012731
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009040 m n μ σ τ
        (_root_.GD.N0107.d009046 m n σ τ) ω =
      _root_.GD.N0107.d009093 m n ω := by
  let S := _root_.GD.N0107.d009045 m n σ τ
  have hSpos : 0 < S :=
    _root_.GD.N0107.d009049 (by omega) (by omega) hσ hτ
  have hD :=
    congrArg (fun x : ℝ => x ^ 2)
      (_root_.GD.N0107.d012724
        m n hm hn μ σ τ hσ hτ ω)
  have hnum :
      S *
          _root_.GD.N0107.d009032 m n μ σ τ
            (_root_.GD.N0107.d009046 m n σ τ) ω ^ 2 =
        _root_.GD.N0107.d009090 m n ω ^ 2 := by
    unfold _root_.GD.N0107.d009038 _root_.GD.N0137.d008942 at hD
    simp only [Function.comp_apply] at hD
    rw [mul_pow, Real.sq_sqrt hSpos.le] at hD
    simpa [S, _root_.GD.N0107.d009032, Function.comp_apply] using hD
  have hden :=
    _root_.GD.N0107.d012727
      m n hm hn μ σ τ hσ hτ ω
  unfold _root_.GD.N0107.d009040 _root_.GD.N0137.d008944 _root_.GD.N0107.d009093
  change
    _root_.GD.N0107.d009032 m n μ σ τ
          (_root_.GD.N0107.d009046 m n σ τ) ω ^ 2 /
        ((1 - _root_.GD.N0107.d009046 m n σ τ) *
            _root_.GD.N0107.d009033 m n μ σ τ ω +
          _root_.GD.N0107.d009046 m n σ τ *
            _root_.GD.N0107.d009034 m n μ σ τ ω) =
      _root_.GD.N0107.d009090 m n ω ^ 2 /
        _root_.GD.N0107.d009092 m n ω
  calc
    _ = (S *
          _root_.GD.N0107.d009032 m n μ σ τ
            (_root_.GD.N0107.d009046 m n σ τ) ω ^ 2) /
        (S * ((1 - _root_.GD.N0107.d009046 m n σ τ) *
            _root_.GD.N0107.d009033 m n μ σ τ ω +
          _root_.GD.N0107.d009046 m n σ τ *
            _root_.GD.N0107.d009034 m n μ σ τ ω)) := by
          field_simp [hSpos.ne']
    _ = _ := by rw [hnum, hden]

end

end GD.N0107
