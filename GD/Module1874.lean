import GD.Module1873
import GD.Module0436

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0378
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0101.N0368 _root_.GD.N0101.N0369 _root_.GD.N0101.N0383
open _root_.GD.N0101.N0373 _root_.GD.N0101.N0379
open _root_.GD.N0101.N0371 _root_.GD.N0101.N0377



theorem d030661
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgb : ∀ z, g z ∈ Icc (0 : ℝ) 1) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    ¬ (∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) ≤
        q * _root_.GD.N0101.N0368.d021679 t.1) := by
  intro hcap
  obtain ⟨δ, ε, c, η, H, R, hδ, _, hε, he, hc, hec, hη, hη1, hH, hHR, herr, hgain⟩ :=
    _root_.GD.N0101.N0383.d006755 hq1
  let A := _root_.GD.N0101.N0369.d006733 δ * _root_.GD.N0101.N0373.d030657 ε c η
  have hqA : q < A := by simpa only [A, _root_.GD.N0101.N0373.d030657, mul_assoc] using hgain
  have hR := hH.trans_le hHR
  have he1 : ε < 1 := by linarith
  have hAq : A ≤ q := by
    apply _root_.GD.N0101.N0377.d006745 (D := Real.log (R / H) + 2 * ε) (E := 0)
    intro L hL
    have ha := _root_.GD.N0101.N0377.d006740 (L := L) hH hR hε
    have hae := _root_.GD.N0101.N0377.d006741 hH hHR hε hL
    have hlower := _root_.GD.N0101.N0373.d030660 g hg hδ hε he hc hec
      hη.le hη1.le hH hHR hL herr
    have hupper := _root_.GD.N0101.N0379.d030646 g hg hgb hq ha hae he1 hcap
    have hlog : 0 ≤ Real.log (ε / _root_.GD.N0101.N0377.d006739 H R ε L) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hae)
    have hnon : 0 ≤ q * (Real.log (ε / _root_.GD.N0101.N0377.d006739 H R ε L) +
        2 * (ε - _root_.GD.N0101.N0377.d006739 H R ε L)) :=
      mul_nonneg hq (add_nonneg hlog
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hae)))
    have hreal := (ENNReal.ofReal_le_ofReal_iff hnon).mp (hlower.trans hupper)
    change A * L ≤ _ at hreal
    apply hreal.trans
    rw [_root_.GD.N0101.N0377.d006744 hH hR hε]
    nlinarith [mul_nonneg hq ha.le]
  exact (not_le_of_gt hqA) hAq




theorem d030662
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ) (hd : Measurable d)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    ¬ (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 2 θ d ≤
      ENNReal.ofReal (q * _root_.GD.N0076.N0313.d030565
        2 2 (by decide) (by decide) θ)) := by
  intro hbound
  obtain ⟨g, hg, hgb, hcap⟩ := _root_.GD.N0101.N0371.d030643
    q hq hq1.le d hd hbound
  exact _root_.GD.N0101.N0378.d030661 g hg hgb hq hq1 hcap

end
end GD.N0101.N0378

#print axioms _root_.GD.N0101.N0378.d030661
#print axioms _root_.GD.N0101.N0378.d030662
