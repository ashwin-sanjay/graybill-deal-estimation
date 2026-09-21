import Mathlib.Tactic














namespace GD.N0232.N0720.N1251


structure d002231 (K : ℝ → ℝ) (a b : ℝ) where
  lower : ℝ
  ordered : a ≤ b
  lower_pos : 0 < lower
  enclosure : ∀ e ∈ Set.Icc a b, lower ≤ K e



inductive d002232 (K : ℝ → ℝ) : ℝ → ℝ → Type
  | single {a b : ℝ} (cell : _root_.GD.N0232.N0720.N1251.d002231 K a b) : d002232 K a b
  | cons {a b c : ℝ} (cell : _root_.GD.N0232.N0720.N1251.d002231 K a b)
      (tail : d002232 K b c) : d002232 K a c

namespace d002232


def d002233 {K : ℝ → ℝ} {a b : ℝ} : _root_.GD.N0232.N0720.N1251.d002232 K a b → ℝ
  | .single cell => cell.lower
  | .cons cell tail => min cell.lower tail.d002233


theorem d002234 {K : ℝ → ℝ} {a b : ℝ} (chain : _root_.GD.N0232.N0720.N1251.d002232 K a b) :
    0 < chain.d002233 := by
  induction chain with
  | single cell => exact cell.lower_pos
  | cons cell tail ih =>
      simpa [_root_.GD.N0232.N0720.N1251.d002232.d002233] using (lt_min cell.lower_pos ih)



theorem d002235 {K : ℝ → ℝ} {a b : ℝ} (chain : _root_.GD.N0232.N0720.N1251.d002232 K a b)
    {e : ℝ} (he : e ∈ Set.Icc a b) :
    chain.d002233 ≤ K e := by
  induction chain with
  | single cell =>
      simpa [_root_.GD.N0232.N0720.N1251.d002232.d002233] using cell.enclosure e he
  | @cons a middle b cell tail ih =>
      simp only [_root_.GD.N0232.N0720.N1251.d002232.d002233]
      by_cases hleft : e ≤ middle
      · exact (min_le_left cell.lower tail.d002233).trans
          (cell.enclosure e ⟨he.1, hleft⟩)
      · have hmiddle : middle ≤ e := (lt_of_not_ge hleft).le
        exact (min_le_right cell.lower tail.d002233).trans
          (ih ⟨hmiddle, he.2⟩)



theorem d002236 {K : ℝ → ℝ} {a b : ℝ} (chain : _root_.GD.N0232.N0720.N1251.d002232 K a b)
    {e : ℝ} (he : e ∈ Set.Icc a b) :
    0 < K e :=
  chain.d002234.trans_le (chain.d002235 he)

end d002232



theorem d002237 (K : ℝ → ℝ) (chain : _root_.GD.N0232.N0720.N1251.d002232 K 0 (1 / 50))
    {e : ℝ} (he0 : 0 ≤ e) (he50 : e ≤ 1 / 50) :
    0 < K e :=
  chain.d002236 ⟨he0, he50⟩



theorem d002238 (K : ℝ → ℝ)
    (chain : _root_.GD.N0232.N0720.N1251.d002232 K 0 (1 / 50)) :
    0 < chain.d002233 ∧
      ∀ e ∈ Set.Icc (0 : ℝ) (1 / 50), chain.d002233 ≤ K e := by
  exact ⟨chain.d002234, fun e he ↦ chain.d002235 he⟩

end GD.N0232.N0720.N1251
