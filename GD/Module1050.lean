import GD.Module0945
import GD.Module1034
import Mathlib.Tactic










open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD.N0232.N0720.N1281

noncomputable section

open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1283
open _root_.GD.N0232.N0720.N1397


def d016761 (e : ℝ) : ℝ :=
  Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 e)

theorem d016762 {e : ℝ} (he1 : e < 1) :
    0 < _root_.GD.N0232.N0720.N1283.d003854 e := by
  unfold _root_.GD.N0232.N0720.N1283.d003854
  linarith

theorem d016763 {e : ℝ} (he1 : e < 1) :
    0 < _root_.GD.N0232.N0720.N1281.d016761 e := by
  exact Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1281.d016762 he1)

theorem d016764 {e : ℝ} (he1 : e < 1) :
    _root_.GD.N0232.N0720.N1281.d016761 e ^ 2 = _root_.GD.N0232.N0720.N1283.d003854 e := by
  unfold _root_.GD.N0232.N0720.N1281.d016761
  exact Real.sq_sqrt (_root_.GD.N0232.N0720.N1281.d016762 he1).le


theorem d016765
    {e x : ℝ} (he1 : e < 1) :
    x ^ 2 / 2 - x ^ 2 / (2 * _root_.GD.N0232.N0720.N1281.d016761 e ^ 2) =
      -(e / _root_.GD.N0232.N0720.N1283.d003854 e) * x ^ 2 / 2 := by
  rw [_root_.GD.N0232.N0720.N1281.d016764 he1]
  have ht := _root_.GD.N0232.N0720.N1281.d016762 he1
  unfold _root_.GD.N0232.N0720.N1283.d003854 at ht ⊢
  field_simp [ht.ne']
  ring



theorem d016766
    {e : ℝ} (he1 : e < 1) (x : ℝ) :
    _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1281.d016761 e) x =
      (Real.sqrt (_root_.GD.N0232.N0720.N1283.d003854 e))⁻¹ *
        _root_.GD.N0232.N0720.N1283.d003851 (e / _root_.GD.N0232.N0720.N1283.d003854 e) x := by
  rw [_root_.GD.N0232.N0720.N1124.d016497
      0 (_root_.GD.N0232.N0720.N1281.d016761 e) x
      (_root_.GD.N0232.N0720.N1281.d016763 he1)]
  simp only [sub_zero]
  rw [_root_.GD.N0232.N0720.N1281.d016765 he1]
  unfold _root_.GD.N0232.N0720.N1281.d016761 _root_.GD.N0232.N0720.N1283.d003851
  rfl


def d016767
    (e : ℝ) (r : ℝ × (ℝ × ℝ)) : ℝ :=
  _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.1 *
    (_root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.2.1 *
      _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.2.2)


theorem d016768
    {e : ℝ} (he1 : e < 1) (r : ℝ × (ℝ × ℝ)) :
    _root_.GD.N0232.N0720.N1281.d016767 e r =
      _root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2 := by
  unfold _root_.GD.N0232.N0720.N1281.d016767 _root_.GD.N0232.N0720.N1283.d003859
  rw [_root_.GD.N0232.N0720.N1281.d016766 he1,
    _root_.GD.N0232.N0720.N1281.d016766 he1,
    _root_.GD.N0232.N0720.N1281.d016766 he1]
  ring

theorem d016769 (e : ℝ) :
    Measurable (fun r : ℝ × (ℝ × ℝ) ↦
      _root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2) := by
  unfold _root_.GD.N0232.N0720.N1283.d003859 _root_.GD.N0232.N0720.N1283.d003851
  fun_prop



theorem d016770
    {e : ℝ} (he1 : e < 1) (r : ℝ × (ℝ × ℝ)) :
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2) =
      _root_.GD.N0232.N0719.N0932.d009197 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.1 *
        (_root_.GD.N0232.N0719.N0932.d009197 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.2.1 *
          _root_.GD.N0232.N0719.N0932.d009197 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.2.2) := by
  let a := _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.1
  let b := _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.2.1
  let c := _root_.GD.N0232.N0719.N0932.d009204 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.2.2
  have ha : 0 ≤ a := _root_.GD.N0232.N0719.N0932.d009205 _ _ _
  have hb : 0 ≤ b := _root_.GD.N0232.N0719.N0932.d009205 _ _ _
  rw [← _root_.GD.N0232.N0719.N0932.d009207 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.1,
    ← _root_.GD.N0232.N0719.N0932.d009207 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.2.1,
    ← _root_.GD.N0232.N0719.N0932.d009207 0 (_root_.GD.N0232.N0720.N1281.d016761 e) r.2.2]
  change ENNReal.ofReal (_root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2) =
    ENNReal.ofReal a * (ENNReal.ofReal b * ENNReal.ofReal c)
  rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul ha]
  congr 1
  exact (_root_.GD.N0232.N0720.N1281.d016768 he1 r).symm


def d016771 (e : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1281.d016761 e))).prod
    ((gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1281.d016761 e))).prod
      (gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1281.d016761 e))))

instance d016772 (e : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1281.d016771 e) := by
  unfold _root_.GD.N0232.N0720.N1281.d016771
  infer_instance




theorem d016773
    {e : ℝ} (he1 : e < 1) :
    _root_.GD.N0232.N0720.N1281.d016771 e =
      _root_.GD.N0232.N0720.N1397.d014799.withDensity (fun r ↦
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2)) := by
  let g : Measure ℝ := gaussianReal 0 1
  let ell : ℝ → ℝ≥0∞ := _root_.GD.N0232.N0719.N0932.d009197 0 (_root_.GD.N0232.N0720.N1281.d016761 e)
  have hs : _root_.GD.N0232.N0720.N1281.d016761 e ≠ 0 := (_root_.GD.N0232.N0720.N1281.d016763 he1).ne'
  have hell : Measurable ell := _root_.GD.N0232.N0719.N0932.d009198 _ _
  have hpair : Measurable (fun z : ℝ × ℝ ↦ ell z.1 * ell z.2) :=
    (hell.comp measurable_fst).mul (hell.comp measurable_snd)
  have hgauss : gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1281.d016761 e)) =
      g.withDensity ell := by
    exact _root_.GD.N0232.N0719.N0932.d009201 0 (_root_.GD.N0232.N0720.N1281.d016761 e) hs
  calc
    _root_.GD.N0232.N0720.N1281.d016771 e =
        (g.withDensity ell).prod
          ((g.withDensity ell).prod (g.withDensity ell)) := by
      unfold _root_.GD.N0232.N0720.N1281.d016771
      rw [hgauss]
    _ = (g.withDensity ell).prod
          ((g.prod g).withDensity (fun z ↦ ell z.1 * ell z.2)) := by
      rw [prod_withDensity hell hell]
    _ = (g.prod (g.prod g)).withDensity
          (fun r ↦ ell r.1 * (ell r.2.1 * ell r.2.2)) := by
      rw [prod_withDensity hell hpair]
    _ = _root_.GD.N0232.N0720.N1397.d014799.withDensity (fun r ↦
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2)) := by
      unfold _root_.GD.N0232.N0720.N1397.d014799 g ell
      congr 1
      funext r
      exact (_root_.GD.N0232.N0720.N1281.d016770
        he1 r).symm



def d016774
    (mu e : ℝ) (z : _root_.GD.N0232.N0720.N1397.d014798) : ℝ≥0∞ :=
  gaussianPDF mu (_root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1281.d016761 e / 2)) z.1 *
    ENNReal.ofReal
      (_root_.GD.N0232.N0720.N1283.d003859 e z.2.1 z.2.2.1 z.2.2.2)

theorem d016775 (mu e : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1281.d016774 mu e) := by
  unfold _root_.GD.N0232.N0720.N1281.d016774
  exact ((measurable_gaussianPDF _ _).comp measurable_fst).mul
    (((_root_.GD.N0232.N0720.N1281.d016769 e).ennreal_ofReal).comp measurable_snd)


theorem d016776
    (mu : ℝ) {e : ℝ} (he1 : e < 1) :
    _root_.GD.N0232.N0720.N1397.d014809 mu (_root_.GD.N0232.N0720.N1281.d016761 e) =
      (volume.prod _root_.GD.N0232.N0720.N1397.d014799).withDensity
        (_root_.GD.N0232.N0720.N1281.d016774 mu e) := by
  have hs : _root_.GD.N0232.N0720.N1281.d016761 e ≠ 0 := (_root_.GD.N0232.N0720.N1281.d016763 he1).ne'
  have hhalf : _root_.GD.N0232.N0720.N1281.d016761 e / 2 ≠ 0 := div_ne_zero hs (by norm_num)
  have hloc : Measurable
      (gaussianPDF mu (_root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1281.d016761 e / 2))) :=
    measurable_gaussianPDF _ _
  have hanc : Measurable (fun r : ℝ × (ℝ × ℝ) ↦
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1283.d003859 e r.1 r.2.1 r.2.2)) :=
    (_root_.GD.N0232.N0720.N1281.d016769 e).ennreal_ofReal
  change
    (gaussianReal mu (_root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1281.d016761 e / 2))).prod
        (_root_.GD.N0232.N0720.N1281.d016771 e) = _
  rw [gaussianReal_of_var_ne_zero mu (_root_.GD.N0232.N0719.N0932.d009196 hhalf),
    _root_.GD.N0232.N0720.N1281.d016773 he1,
    prod_withDensity hloc hanc]
  rfl


theorem d016777
    (mu : ℝ) {e : ℝ} (he1 : e < 1) :
    _root_.GD.N0232.N0720.N1397.d014809 mu (Real.sqrt (1 - e)) =
      (volume.prod _root_.GD.N0232.N0720.N1397.d014799).withDensity
        (_root_.GD.N0232.N0720.N1281.d016774 mu e) := by
  simpa [_root_.GD.N0232.N0720.N1281.d016761, _root_.GD.N0232.N0720.N1283.d003854] using
    _root_.GD.N0232.N0720.N1281.d016776 mu he1



theorem d016778
    (mu : ℝ) {e : ℝ} (he1 : e < 1) :
    (_root_.GD.N0107.d009030 2 2 mu
        (Real.sqrt (1 - e)) (Real.sqrt (1 - e))).map
          _root_.GD.N0232.N0720.N1397.d014815 =
      (volume.prod _root_.GD.N0232.N0720.N1397.d014799).withDensity
        (_root_.GD.N0232.N0720.N1281.d016774 mu e) := by
  have hs : Real.sqrt (1 - e) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  rw [_root_.GD.N0232.N0720.N1397.d014819 mu
      (Real.sqrt (1 - e)) hs]
  exact _root_.GD.N0232.N0720.N1281.d016777 mu he1

end

end GD.N0232.N0720.N1281

#print axioms _root_.GD.N0232.N0720.N1281.d016766
#print axioms _root_.GD.N0232.N0720.N1281.d016768
#print axioms _root_.GD.N0232.N0720.N1281.d016773
#print axioms _root_.GD.N0232.N0720.N1281.d016776
#print axioms _root_.GD.N0232.N0720.N1281.d016778
