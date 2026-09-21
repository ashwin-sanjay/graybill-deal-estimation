import GD.Module0149

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0046.N0303

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0675
open _root_.GD.N0230.N0718

variable {Ω : Type*} [MeasurableSpace Ω]

theorem d030187
    {μ₀ μ : Measure Ω} (hμ : μ ≪ μ₀) (target : ℝ)
    {p q : _root_.GD.N0230.N0602.d000116 μ₀} {c : ℝ≥0∞}
    (hp : _root_.GD.N0230.N0602.d000117 μ target p ≤ c)
    (hq : _root_.GD.N0230.N0602.d000117 μ target q ≤ c) :
    _root_.GD.N0230.N0602.d000117 μ target (_root_.GD.N0230.N0718.d001528 p q) ≤ c := by
  have h := _root_.GD.N0230.N0602.d000121 hμ target p q
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  apply h.trans
  calc
    ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0230.N0602.d000117 μ target p +
        ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0230.N0602.d000117 μ target q ≤
      ENNReal.ofReal (1 / 2 : ℝ) * c + ENNReal.ofReal (1 / 2 : ℝ) * c :=
      add_le_add (mul_le_mul_right hp _) (mul_le_mul_right hq _)
    _ = c := by
      rw [← add_mul, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num

theorem d030188
    {μ₀ μ : Measure Ω} (hμ : μ ≪ μ₀) (hμ₀ : μ₀ ≪ μ) (target : ℝ)
    {p q : _root_.GD.N0230.N0602.d000116 μ₀} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hp : _root_.GD.N0230.N0602.d000117 μ target p ≤ c)
    (hq : _root_.GD.N0230.N0602.d000117 μ target q ≤ c) (hpq : p ≠ q) :
    _root_.GD.N0230.N0602.d000117 μ target (_root_.GD.N0230.N0718.d001528 p q) < c := by
  have hpfin := ne_top_of_le_ne_top hc hp
  have hqfin := ne_top_of_le_ne_top hc hq
  have hmfin := ne_top_of_le_ne_top hc
    (_root_.GD.N0046.N0303.d030187 hμ target hp hq)
  have hidentity := _root_.GD.N0230.N0670.d001649
    hμ target p q hpfin hqfin
  have htax := _root_.GD.N0230.N0675.d001656
    hμ hμ₀ target hpfin hqfin hpq
  have hpR := ENNReal.toReal_mono hc hp
  have hqR := ENNReal.toReal_mono hc hq
  apply (ENNReal.toReal_lt_toReal hmfin hc).mp
  unfold _root_.GD.N0230.N0675.d001653 at htax
  linarith

end
end GD.N0046.N0303

#print axioms _root_.GD.N0046.N0303.d030188
