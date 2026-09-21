import GD.Module1337
import GD.Module1872

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0373
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0101.N0387 _root_.GD.N0101.N0369 _root_.GD.N0101.N0370
open _root_.GD.N0101.N0382 _root_.GD.N0101.N0381 _root_.GD.N0101.N0379
open _root_.GD.N0101.N0377

def d030657 (ε c η : ℝ) : ℝ :=
  ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) * (1 - η) * (1 - 2 * ε) ^ 2

theorem d030658 {ε c η : ℝ} (hc : 1 ≤ c) (hη1 : η ≤ 1) :
    0 ≤ _root_.GD.N0101.N0373.d030657 ε c η :=
  mul_nonneg (mul_nonneg
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hc) _))
    (sub_nonneg.mpr hη1)) (sq_nonneg _)



theorem d030659
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {δ ε c η H R a : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (he : ε ≤ 1 / 2) (hc : 1 ≤ c)
    (hec : ε ≤ δ * (c - 1)) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hH : 0 < H) (hHR : H ≤ R) (ha : 0 < a)
    (hwindow : R / ε ≤ H / a)
    (herr : (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) + 1 / R ≤
      (2 / 3 : ℝ) * η) :
    ENNReal.ofReal (_root_.GD.N0101.N0369.d006733 δ * _root_.GD.N0101.N0373.d030657 ε c η *
      Real.log ((H / a) / (R / ε))) ≤
      _root_.GD.N0101.N0379.d030644 (fun t => ∫⁻ z, ENNReal.ofReal ((g z - t) ^ 2)
        ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) a ε := by
  have hR := hH.trans_le hHR
  have he1 : ε < 1 := by linarith
  rw [_root_.GD.N0101.N0381.d030654 g hg a ε]
  apply _root_.GD.N0101.N0370.d021722 _ hδ (div_pos hR hε) hwindow
    (_root_.GD.N0101.N0373.d030658 hc hη1)
  intro z hz
  have hu : z.1 ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans hz.1.1, by linarith [hz.1.2]⟩
  have hs : 0 < z.2 := (div_pos hR hε).trans hz.2.1
  have haH : z.2 * a ≤ H := ((lt_div_iff₀ ha).mp hz.2.2).le
  have hRs : R ≤ z.2 * ε := ((div_lt_iff₀ hε).mp hz.2.1).le
  have hpoint := _root_.GD.N0101.N0382.d021732 (g z) hu hs hH hHR ha.le hδ
    hz.1.1.le hz.1.2.le he hc hec haH hRs hη hη1 herr
  rw [_root_.GD.N0101.N0381.d030656 g a ε z ⟨hu, hs⟩ ha.le he1]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hs).mpr
  calc
    _ ≤ z.2 * (_root_.GD.N0101.N0382.d021727 (g z) z.1 z.2 a ε +
        _root_.GD.N0101.N0382.d021727 (1 - g z) (1 - z.1) z.2 a ε) := by
      simpa only [_root_.GD.N0101.N0373.d030657, mul_assoc] using hpoint
    _ = _ := mul_comm _ _



theorem d030660
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {δ ε c η H R L : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (he : ε ≤ 1 / 2) (hc : 1 ≤ c)
    (hec : ε ≤ δ * (c - 1)) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hH : 0 < H) (hHR : H ≤ R) (hL : 0 ≤ L)
    (herr : (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) + 1 / R ≤
      (2 / 3 : ℝ) * η) :
    ENNReal.ofReal (_root_.GD.N0101.N0369.d006733 δ * _root_.GD.N0101.N0373.d030657 ε c η * L) ≤
      _root_.GD.N0101.N0379.d030644 (fun t => ∫⁻ z, ENNReal.ofReal ((g z - t) ^ 2)
        ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) (_root_.GD.N0101.N0377.d006739 H R ε L) ε := by
  have hR := hH.trans_le hHR
  have ha := _root_.GD.N0101.N0377.d006740 (L := L) hH hR hε
  have hratio := _root_.GD.N0101.N0377.d006742 (L := L) hH hR hε
  have hexp : 1 ≤ Real.exp L := by simpa using Real.exp_le_exp.mpr hL
  have hwindow : R / ε ≤ H / _root_.GD.N0101.N0377.d006739 H R ε L := by
    rw [← hratio, le_div_iff₀ (div_pos hR hε)] at hexp
    simpa only [one_mul] using hexp
  have h := _root_.GD.N0101.N0373.d030659 g hg hδ hε he hc hec hη hη1 hH hHR ha hwindow herr
  simpa only [hratio, Real.log_exp] using h

end
end GD.N0101.N0373

#print axioms _root_.GD.N0101.N0373.d030658
#print axioms _root_.GD.N0101.N0373.d030659
#print axioms _root_.GD.N0101.N0373.d030660
