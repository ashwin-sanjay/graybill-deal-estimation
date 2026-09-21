import GD.Module0620









open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0107

noncomputable section

open _root_.GD.N0137



def d009084 {n : ℕ}
    (x : _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0126.d006420 x


def d009085 {n : ℕ}
    (x : _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0126.d006422 x / (n - 1 : ℕ)

theorem d009086
    {n : ℕ} (hn : 0 < n) (μ σ : ℝ)
    (z : _root_.GD.N0137.d008894 n) :
    @_root_.GD.N0126.d006420 (Fin n) _
        (_root_.GD.N0107.d009018 n μ σ z) =
      μ + σ *
        @_root_.GD.N0126.d006420 (Fin n) _ z := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold _root_.GD.N0126.d006420
    _root_.GD.N0126.d006419 _root_.GD.N0107.d009018
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hnR]

theorem d009087
    {n : ℕ} (hn : 0 < n) (μ σ : ℝ)
    (x : _root_.GD.N0137.d008894 n) :
    @_root_.GD.N0126.d006420 (Fin n) _
        (_root_.GD.N0107.d009019 n μ σ x) =
      (@_root_.GD.N0126.d006420 (Fin n) _ x - μ)
        / σ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold _root_.GD.N0126.d006420
    _root_.GD.N0126.d006419 _root_.GD.N0107.d009019
  rw [← Finset.sum_div]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hnR]

theorem d009088
    {n : ℕ} (hn : 0 < n) (μ σ : ℝ)
    (z : _root_.GD.N0137.d008894 n) :
    @_root_.GD.N0126.d006422 (Fin n) _
        (_root_.GD.N0107.d009018 n μ σ z) =
      σ ^ 2 *
        @_root_.GD.N0126.d006422 (Fin n) _ z := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
  rw [_root_.GD.N0107.d009086 hn μ σ z]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold _root_.GD.N0107.d009018
  ring

theorem d009089
    {n : ℕ} (hn : 0 < n) (μ σ : ℝ)
    (x : _root_.GD.N0137.d008894 n) :
    @_root_.GD.N0126.d006422 (Fin n) _
        (_root_.GD.N0107.d009019 n μ σ x) =
      @_root_.GD.N0126.d006422 (Fin n) _ x
        / σ ^ 2 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
  rw [_root_.GD.N0107.d009087 hn μ σ x]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold _root_.GD.N0107.d009019
  ring


def d009090
    (m n : ℕ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0107.d009084 ω.1 - _root_.GD.N0107.d009084 ω.2



def d009091 (m n : ℕ) (sx2 sy2 : ℝ) : ℝ :=
  (sy2 / n) / (sx2 / m + sy2 / n)



def d009092
    (m n : ℕ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0107.d009085 ω.1 / m +
    _root_.GD.N0107.d009085 ω.2 / n


def d009093
    (m n : ℕ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0107.d009090 m n ω ^ 2 /
    _root_.GD.N0107.d009092 m n ω

end

end GD.N0107
