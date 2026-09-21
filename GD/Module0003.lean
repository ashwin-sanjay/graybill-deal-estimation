import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

















namespace GD
namespace N0229
namespace N0552


def d000024 (ε energy gain : ℝ) : ℝ :=
  ε ^ 2 * energy - 2 * ε * gain


theorem d000025
    (ε energy gain δ M : ℝ)
    (hε : 0 < ε)
    (hgain : δ ≤ gain)
    (henergy : energy ≤ M)
    (hstep : ε * M < 2 * δ) :
    _root_.GD.N0229.N0552.d000024 ε energy gain < 0 := by
  have henergy_scaled :
      ε ^ 2 * energy ≤ ε ^ 2 * M :=
    mul_le_mul_of_nonneg_left henergy (sq_nonneg ε)
  have hgain_scaled :
      2 * ε * δ ≤ 2 * ε * gain :=
    mul_le_mul_of_nonneg_left hgain (by positivity)
  have hupper :
      _root_.GD.N0229.N0552.d000024 ε energy gain ≤
        ε ^ 2 * M - 2 * ε * δ := by
    exact sub_le_sub henergy_scaled hgain_scaled
  have hnegative : ε ^ 2 * M - 2 * ε * δ < 0 := by
    calc
      ε ^ 2 * M - 2 * ε * δ = ε * (ε * M - 2 * δ) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hε (sub_neg.mpr hstep)
  exact lt_of_le_of_lt hupper hnegative





theorem d000026
    {ι : Type*}
    (gain energy : ι → ℝ)
    (δ M ε : ℝ)
    (hε : 0 < ε)
    (hgain : ∀ i, δ ≤ gain i)
    (henergy : ∀ i, energy i ≤ M)
    (hstep : ε * M < 2 * δ) :
    ∀ i, _root_.GD.N0229.N0552.d000024 ε (energy i) (gain i) < 0 := by
  intro i
  exact _root_.GD.N0229.N0552.d000025 ε (energy i) (gain i) δ M
    hε (hgain i) (henergy i) hstep





theorem d000027
    {ι : Type*}
    (gain energy : ι → ℝ)
    (δ M ε : ℝ)
    (hδ : 0 < δ)
    (hε : 0 < ε)
    (hgain : ∀ i, δ ≤ gain i)
    (henergy : ∀ i, energy i ≤ M)
    (hstep : ε * M ≤ δ) :
    ∀ i, _root_.GD.N0229.N0552.d000024 ε (energy i) (gain i) < 0 := by
  apply _root_.GD.N0229.N0552.d000026 gain energy δ M ε hε hgain henergy
  linarith

end N0552
end N0229
end GD
