import GD.Module0269
import GD.Module0945















open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Real

namespace GD.N0232.N0720.N1282

noncomputable section

open _root_.GD.N0232.N0720.N1280
open _root_.GD.N0232.N0720.N1397

abbrev d014821 :=
  _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2
abbrev d014822 := _root_.GD.N0232.N0720.N1397.d014798


def d014823 (N : ℝ) (z : _root_.GD.N0232.N0720.N1282.d014822) : ℝ :=
  _root_.GD.N0232.N0720.N1280.d003939 N z / _root_.GD.N0232.N0720.N1280.d003886 z.1


def d014824 (N : ℝ) (z : _root_.GD.N0232.N0720.N1282.d014822) : ℝ :=
  _root_.GD.N0232.N0720.N1280.d003940 N z / _root_.GD.N0232.N0720.N1280.d003886 z.1


def d014825 (N : ℝ) (z : _root_.GD.N0232.N0720.N1282.d014822) : ℝ :=
  _root_.GD.N0232.N0720.N1282.d014824 N z ^ 2 / _root_.GD.N0232.N0720.N1282.d014823 N z



def d014826 (N : ℝ) (omega : _root_.GD.N0232.N0720.N1282.d014821) : ℝ :=
  _root_.GD.N0232.N0720.N1282.d014823 N (_root_.GD.N0232.N0720.N1397.d014815 omega)



def d014827 (N : ℝ) (omega : _root_.GD.N0232.N0720.N1282.d014821) : ℝ :=
  _root_.GD.N0232.N0720.N1282.d014824 N (_root_.GD.N0232.N0720.N1397.d014815 omega)


def d014828 (N : ℝ) : ℝ :=
  ∫ omega : _root_.GD.N0232.N0720.N1282.d014821,
    _root_.GD.N0232.N0720.N1282.d014827 N omega ^ 2 / _root_.GD.N0232.N0720.N1282.d014826 N omega
      ∂_root_.GD.N0107.d009030 2 2 0 1 1

theorem d014829 :
    _root_.GD.N0232.N0720.N1397.d014799 =
      _root_.GD.N0232.N0720.N1280.d003880 := by
  unfold _root_.GD.N0232.N0720.N1397.d014799
    _root_.GD.N0232.N0720.N1280.d003880
    _root_.GD.N0232.N0720.N1283.d003842
  rfl

theorem d014830 :
    gaussianReal 0 (1 / 4 : ℝ≥0) =
      volume.withDensity
        (fun x : ℝ => ENNReal.ofReal (_root_.GD.N0232.N0720.N1280.d003886 x)) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 4 : ℝ≥0) ≠ 0)]
  congr 1
  funext x
  unfold _root_.GD.N0232.N0720.N1280.d003886
    _root_.GD.N0232.N0720.N1277.d002621 _root_.GD.N0232.N0720.N1280.d003878
    ProbabilityTheory.gaussianPDF
  have hquarter : (1 / 4 : ℝ≥0) = (1 / 4 : ℝ).toNNReal := by
    apply NNReal.eq
    norm_num
  rw [hquarter]

theorem d014831 :
    Measurable _root_.GD.N0232.N0720.N1280.d003886 := by
  unfold _root_.GD.N0232.N0720.N1280.d003886
    _root_.GD.N0232.N0720.N1277.d002621
  exact measurable_gaussianPDFReal 0 _root_.GD.N0232.N0720.N1280.d003878.toNNReal

theorem d014832 :
    (gaussianReal 0 (1 / 4 : ℝ≥0)).prod
        _root_.GD.N0232.N0720.N1397.d014799 =
      (volume.prod _root_.GD.N0232.N0720.N1280.d003880).withDensity
        (fun z : _root_.GD.N0232.N0720.N1282.d014822 =>
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1280.d003886 z.1)) := by
  rw [_root_.GD.N0232.N0720.N1282.d014830,
    _root_.GD.N0232.N0720.N1282.d014829,
    prod_withDensity_left]
  exact _root_.GD.N0232.N0720.N1282.d014831.ennreal_ofReal

theorem d014833
    {N : ℝ} (hN : 3 ≤ N) (z : _root_.GD.N0232.N0720.N1282.d014822) :
    0 < _root_.GD.N0232.N0720.N1280.d003939 N z := by
  have hfloor := _root_.GD.N0232.N0720.N1280.d003948 hN z
  have hpositive : 0 <
      _root_.GD.N0232.N0720.N1285.d002684 N *
        _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 *
        _root_.GD.N0232.N0720.N1280.d003887 N z.1 := by
    exact mul_pos
      (mul_pos (_root_.GD.N0232.N0720.N1280.d003942 hN)
        (_root_.GD.N0232.N0720.N1280.d003925 (show _root_.GD.N0232.N0720.N1285.d002679 N < 1 by
          linarith [_root_.GD.N0232.N0720.N1285.d002687 hN])
          z.2))
      (_root_.GD.N0232.N0720.N1280.d003894 hN z.1)
  exact hpositive.trans_le hfloor

theorem d014834 (N : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1282.d014825 N) := by
  unfold _root_.GD.N0232.N0720.N1282.d014825 _root_.GD.N0232.N0720.N1282.d014824
    _root_.GD.N0232.N0720.N1282.d014823
  exact (((_root_.GD.N0232.N0720.N1280.d003949 N).div
      (_root_.GD.N0232.N0720.N1282.d014831.comp measurable_fst)).pow_const 2).div
    ((_root_.GD.N0232.N0720.N1280.d003950 N).div
      (_root_.GD.N0232.N0720.N1282.d014831.comp measurable_fst))

theorem d014835
    {N : ℝ} (hN : 3 ≤ N) (z : _root_.GD.N0232.N0720.N1282.d014822) :
    _root_.GD.N0232.N0720.N1280.d003886 z.1 * _root_.GD.N0232.N0720.N1282.d014825 N z =
      _root_.GD.N0232.N0720.N1280.d003940 N z ^ 2 / _root_.GD.N0232.N0720.N1280.d003939 N z := by
  have hp := (_root_.GD.N0232.N0720.N1280.d003893 z.1).ne'
  have hD := (_root_.GD.N0232.N0720.N1282.d014833 hN z).ne'
  unfold _root_.GD.N0232.N0720.N1282.d014825 _root_.GD.N0232.N0720.N1282.d014824
    _root_.GD.N0232.N0720.N1282.d014823
  field_simp [hp, hD]




theorem d014836
    {N : ℝ} (hN : 3 ≤ N) :
    (∫ z : _root_.GD.N0232.N0720.N1282.d014822, _root_.GD.N0232.N0720.N1282.d014825 N z
      ∂((gaussianReal 0 (1 / 4 : ℝ≥0)).prod
        _root_.GD.N0232.N0720.N1397.d014799)) =
      _root_.GD.N0232.N0720.N1280.d003941 N := by
  rw [_root_.GD.N0232.N0720.N1282.d014832]
  have hdensity : Measurable (fun z : _root_.GD.N0232.N0720.N1282.d014822 =>
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1280.d003886 z.1)) :=
    (_root_.GD.N0232.N0720.N1282.d014831.comp measurable_fst).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hdensity
    (ae_of_all (volume.prod _root_.GD.N0232.N0720.N1280.d003880)
      fun _ => ENNReal.ofReal_lt_top)]
  unfold _root_.GD.N0232.N0720.N1280.d003941
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1280.d003893 z.1).le]
  simpa only [smul_eq_mul] using _root_.GD.N0232.N0720.N1282.d014835 hN z



theorem d014837
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1282.d014828 N = _root_.GD.N0232.N0720.N1280.d003941 N := by
  have hmap := integral_map
    (μ := _root_.GD.N0107.d009030 2 2 0 1 1)
    _root_.GD.N0232.N0720.N1397.d014816.aemeasurable
    (_root_.GD.N0232.N0720.N1282.d014834 N).aestronglyMeasurable
  calc
    _root_.GD.N0232.N0720.N1282.d014828 N =
        ∫ z : _root_.GD.N0232.N0720.N1282.d014822, _root_.GD.N0232.N0720.N1282.d014825 N z
          ∂((_root_.GD.N0107.d009030 2 2 0 1 1).map
            _root_.GD.N0232.N0720.N1397.d014815) := by
      rw [hmap]
      rfl
    _ = ∫ z : _root_.GD.N0232.N0720.N1282.d014822, _root_.GD.N0232.N0720.N1282.d014825 N z
          ∂((gaussianReal 0 (1 / 4 : ℝ≥0)).prod
            _root_.GD.N0232.N0720.N1397.d014799) := by
      rw [show (_root_.GD.N0107.d009030 2 2 0 1 1).map
            _root_.GD.N0232.N0720.N1397.d014815 =
          (gaussianReal 0 (1 / 4 : ℝ≥0)).prod
            _root_.GD.N0232.N0720.N1397.d014799 by
        exact _root_.GD.N0232.N0720.N1397.d014820]
    _ = _root_.GD.N0232.N0720.N1280.d003941 N :=
      _root_.GD.N0232.N0720.N1282.d014836 hN


theorem d014838
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1282.d014828 N ≤ 48 / N ^ 9 := by
  rw [_root_.GD.N0232.N0720.N1282.d014837 hN]
  exact _root_.GD.N0232.N0720.N1280.d003957 hN

#print axioms _root_.GD.N0232.N0720.N1282.d014837
#print axioms _root_.GD.N0232.N0720.N1282.d014838

end

end GD.N0232.N0720.N1282
