import GD.Module0940
import GD.Module0884















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1424

noncomputable section

open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1084
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441


def d014839 : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  fun x ↦ x.1



def d014840
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  fun x ↦ _root_.GD.N0232.N0720.N1084.d014254 U x.1 x.2


def d014841
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  fun x ↦ _root_.GD.N0230.N0637.d000240
    (_root_.GD.N0232.N0720.N1424.d014840 U x)

theorem d014842 : Measurable _root_.GD.N0232.N0720.N1424.d014839 := by
  exact measurable_fst

theorem d014843
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    Measurable (_root_.GD.N0232.N0720.N1424.d014840 U) := by
  unfold _root_.GD.N0232.N0720.N1424.d014840 _root_.GD.N0232.N0720.N1084.d014254
  exact measurable_fst.add
    (measurable_const.mul (_root_.GD.N0113.d008651.d008664 U.emitted.table))

theorem d014844
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    Measurable (_root_.GD.N0232.N0720.N1424.d014841 U) := by
  exact
    _root_.GD.N0230.N0660.d000890.measurable.comp
    (_root_.GD.N0232.N0720.N1424.d014843 U)

theorem d014845
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1424.d014841 U x ∈ Set.Icc (0 : ℝ) 1 := by
  exact _root_.GD.N0230.N0637.d000243 _




def d014846 (m : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt ((m : ℝ) * (1 - t))


def d014847 (n : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt ((n : ℝ) * t)

theorem d014848
    {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht1 : t < 1) :
    0 < _root_.GD.N0232.N0720.N1424.d014846 m t := by
  unfold _root_.GD.N0232.N0720.N1424.d014846
  apply Real.sqrt_pos.2
  have hm0 : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  exact mul_pos hm0 (sub_pos.mpr ht1)

theorem d014849
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 < t) :
    0 < _root_.GD.N0232.N0720.N1424.d014847 n t := by
  unfold _root_.GD.N0232.N0720.N1424.d014847
  apply Real.sqrt_pos.2
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  exact mul_pos hn0 ht0

theorem d014850
    {m : ℕ} (hm : 2 ≤ m) {t : ℝ} (ht1 : t < 1) :
    _root_.GD.N0107.d009043 m
        (_root_.GD.N0232.N0720.N1424.d014846 m t) = 1 - t := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hm))
  unfold _root_.GD.N0107.d009043 _root_.GD.N0232.N0720.N1424.d014846
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr ht1.le))]
  rw [div_eq_iff hm0]
  ring

theorem d014851
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 < t) :
    _root_.GD.N0107.d009044 n
        (_root_.GD.N0232.N0720.N1424.d014847 n t) = t := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hn))
  unfold _root_.GD.N0107.d009044 _root_.GD.N0232.N0720.N1424.d014847
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) ht0.le)]
  rw [div_eq_iff hn0]
  ring

theorem d014852
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0107.d009045 m n (_root_.GD.N0232.N0720.N1424.d014846 m t)
        (_root_.GD.N0232.N0720.N1424.d014847 n t) = 1 := by
  unfold _root_.GD.N0107.d009045
  rw [_root_.GD.N0232.N0720.N1424.d014850 hm ht1,
    _root_.GD.N0232.N0720.N1424.d014851 hn ht0]
  ring

theorem d014853
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0107.d009046 m n (_root_.GD.N0232.N0720.N1424.d014846 m t)
        (_root_.GD.N0232.N0720.N1424.d014847 n t) = t := by
  unfold _root_.GD.N0107.d009046
  rw [_root_.GD.N0232.N0720.N1424.d014851 hn ht0,
    _root_.GD.N0232.N0720.N1424.d014852 hm hn ht0 ht1]
  simp



theorem d014854
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1425.d014719 m n _root_.GD.N0232.N0720.N1424.d014839 omega =
      _root_.GD.N0107.d012733 m n omega := by
  rw [_root_.GD.N0232.N0720.N1425.d014720]
  unfold _root_.GD.N0232.N0720.N1424.d014839 _root_.GD.N0107.d012733
  ring

theorem d014855
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1424.d014840 U) omega =
      _root_.GD.N0107.d012734 m n (U.step : ℝ) (_root_.GD.N0232.N0720.d014159 U) omega := by
  simpa [_root_.GD.N0232.N0720.N1425.d014719, _root_.GD.N0232.N0720.N1424.d014840] using
    (_root_.GD.N0232.N0720.N1084.d014258 U omega).symm



private theorem d014856
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    0 ≤ _root_.GD.N0108.d008888
      U.emitted.table := by
  unfold _root_.GD.N0108.d008888
  positivity

private theorem d014857
    (m n : ℕ) (t : ℝ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1436.d013289 m n t, x ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  apply (_root_.GD.N0232.N0720.N1436.d013290 m n t).ae_le
  unfold _root_.GD.N0232.N0720.N1436.d013288
  exact ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219

private theorem d014858
    (m n : ℕ) (t : ℝ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1436.d013289 m n t,
      |_root_.GD.N0232.N0720.N1424.d014839 x| ≤ 1 := by
  filter_upwards [_root_.GD.N0232.N0720.N1424.d014857 m n t] with x hx
  unfold _root_.GD.N0232.N0720.N1424.d014839 _root_.GD.N0232.N0720.N1436.d013218 at *
  rw [abs_of_nonneg hx.1.1.le]
  exact hx.1.2.le

private theorem d014859
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (t : ℝ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1436.d013289 m n t,
      |_root_.GD.N0232.N0720.N1424.d014840 U x| ≤
        1 + |(U.step : ℝ)| *
          _root_.GD.N0108.d008888
            U.emitted.table := by
  filter_upwards [_root_.GD.N0232.N0720.N1424.d014857 m n t] with x hx
  have hxabs : |x.1| ≤ 1 := by
    rw [abs_of_nonneg hx.1.1.le]
    exact hx.1.2.le
  have hq := _root_.GD.N0108.d008891
    U.emitted.table x
  unfold _root_.GD.N0232.N0720.N1424.d014840 _root_.GD.N0232.N0720.N1084.d014254
  calc
    |x.1 + (U.step : ℝ) * _root_.GD.N0113.d008651.d008659 U.emitted.table x| ≤
        |x.1| + |(U.step : ℝ) * _root_.GD.N0113.d008651.d008659 U.emitted.table x| :=
      abs_add_le _ _
    _ ≤ 1 + |(U.step : ℝ)| *
        _root_.GD.N0108.d008888 U.emitted.table := by
      rw [abs_mul]
      exact add_le_add hxabs
        (mul_le_mul_of_nonneg_left hq (abs_nonneg _))

private theorem d014860
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t B : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hB : 0 ≤ B)
    (hgBound : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1436.d013289 m n t, |g x| ≤ B) :
    Integrable (fun x ↦ (g x - t) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 m n t) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1436.d013289 m n t) :=
    _root_.GD.N0232.N0720.N1434.d013564 hm hn ht0 ht1
  apply Integrable.of_bound
    ((hg.sub measurable_const).pow_const 2).aestronglyMeasurable
    ((B + |t|) ^ 2)
  filter_upwards [hgBound] with x hx
  rw [Real.norm_eq_abs, abs_sq]
  have hdiff : |g x - t| ≤ B + |t| := by
    exact (abs_sub (g x) t).trans (add_le_add hx le_rfl)
  have hsquare :=
    (sq_le_sq₀ (abs_nonneg _) (add_nonneg hB (abs_nonneg t))).2 hdiff
  simpa only [sq_abs] using hsquare

private theorem d014861
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Integrable (fun x ↦ (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 m n t.1) := by
  exact _root_.GD.N0232.N0720.N1424.d014860 hm hn t.property.1 t.property.2
    _root_.GD.N0232.N0720.N1424.d014839 _root_.GD.N0232.N0720.N1424.d014842 (by norm_num)
      (_root_.GD.N0232.N0720.N1424.d014858 m n t.1)

private theorem d014862
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Integrable (fun x ↦ (_root_.GD.N0232.N0720.N1424.d014840 U x - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 m n t.1) := by
  let C := _root_.GD.N0108.d008888 U.emitted.table
  have hC : 0 ≤ C := _root_.GD.N0232.N0720.N1424.d014856 U
  exact _root_.GD.N0232.N0720.N1424.d014860 hm hn t.property.1 t.property.2
    (_root_.GD.N0232.N0720.N1424.d014840 U) (_root_.GD.N0232.N0720.N1424.d014843 U)
    (B := 1 + |(U.step : ℝ)| * C) (by positivity)
    (by simpa only [C] using _root_.GD.N0232.N0720.N1424.d014859 U t.1)

private theorem d014863
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Integrable (fun x ↦ (_root_.GD.N0232.N0720.N1424.d014841 U x - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 m n t.1) := by
  apply _root_.GD.N0232.N0720.N1424.d014860 hm hn t.property.1 t.property.2
    (_root_.GD.N0232.N0720.N1424.d014841 U)
    (_root_.GD.N0232.N0720.N1424.d014844 U) (B := 1) (by norm_num)
  filter_upwards [] with x
  have hx := _root_.GD.N0232.N0720.N1424.d014845 U x
  rw [abs_of_nonneg hx.1]
  exact hx.2

private theorem d014864
    {m n : ℕ} (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : Integrable (fun x ↦ (g x - t.1) ^ 2)
      (_root_.GD.N0232.N0720.N1436.d013289 m n t.1)) :
    _root_.GD.N0232.N0720.N1441.d013705 m n t g =
      ENNReal.ofReal
        (∫ x, (g x - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1) := by
  unfold _root_.GD.N0232.N0720.N1441.d013705 _root_.GD.N0232.N0720.N1441.d013678
  exact (ofReal_integral_eq_lintegral_ofReal hg
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)).symm






theorem d014865
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    (∫ x, (_root_.GD.N0232.N0720.N1424.d014840 U x - t.1) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1) <
      ∫ x, (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by
  let sigma := _root_.GD.N0232.N0720.N1424.d014846 m t.1
  let tau := _root_.GD.N0232.N0720.N1424.d014847 n t.1
  have hsigma : 0 < sigma := _root_.GD.N0232.N0720.N1424.d014848 hm t.property.2
  have htau : 0 < tau := _root_.GD.N0232.N0720.N1424.d014849 hn t.property.1
  have hSigma : _root_.GD.N0107.d009045 m n sigma tau = 1 := by
    exact _root_.GD.N0232.N0720.N1424.d014852 hm hn t.property.1 t.property.2
  have hfrac : _root_.GD.N0107.d009046 m n sigma tau = t.1 := by
    exact _root_.GD.N0232.N0720.N1424.d014853 hm hn t.property.1 t.property.2
  let q : _root_.GD.N0232.N0720.N1436.d013217 → ℝ := _root_.GD.N0113.d008651.d008659 U.emitted.table
  have hq : Measurable q := _root_.GD.N0113.d008651.d008664 U.emitted.table
  let C := _root_.GD.N0108.d008888 U.emitted.table
  have hC : 0 ≤ C := _root_.GD.N0232.N0720.N1424.d014856 U
  have hqBound : ∀ x, |q x| ≤ C := by
    intro x
    exact _root_.GD.N0108.d008891
      U.emitted.table x
  have hinputs := _root_.GD.N0107.d012748
    m n hm hn 0 sigma tau hsigma htau q hq hC hqBound
  have hbaselineCarrier : MemLp
      (fun omega ↦
        _root_.GD.N0107.d009038 m n 0 sigma tau
            (_root_.GD.N0107.d009046 m n sigma tau)
            (_root_.GD.N0107.d009045 m n sigma tau) omega *
          (_root_.GD.N0232.N0720.N1424.d014839
              (_root_.GD.N0107.d009039 m n 0 sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega,
                _root_.GD.N0107.d009040 m n 0 sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega) -
            _root_.GD.N0107.d009046 m n sigma tau))
      2 (_root_.GD.N0107.d009030 m n 0 sigma tau) := by
    simpa [_root_.GD.N0232.N0720.N1424.d014839] using hinputs.1
  have hrawCarrier : MemLp
      (fun omega ↦
        _root_.GD.N0107.d009038 m n 0 sigma tau
            (_root_.GD.N0107.d009046 m n sigma tau)
            (_root_.GD.N0107.d009045 m n sigma tau) omega *
          (_root_.GD.N0232.N0720.N1424.d014840 U
              (_root_.GD.N0107.d009039 m n 0 sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega,
                _root_.GD.N0107.d009040 m n 0 sigma tau
                  (_root_.GD.N0107.d009046 m n sigma tau) omega) -
            _root_.GD.N0107.d009046 m n sigma tau))
      2 (_root_.GD.N0107.d009030 m n 0 sigma tau) := by
    have hadd := hinputs.1.add
      (hinputs.2.const_mul (U.step : ℝ))
    apply (memLp_congr_ae ?_).2 hadd
    filter_upwards [] with omega
    simp only [Pi.add_apply]
    unfold _root_.GD.N0232.N0720.N1424.d014840 _root_.GD.N0232.N0720.N1084.d014254 q
    ring
  have hrawBridge :=
    _root_.GD.N0232.N0720.N1425.d014725
      m n hm hn 0 sigma tau hsigma htau
      (_root_.GD.N0232.N0720.N1424.d014840 U) (_root_.GD.N0232.N0720.N1424.d014843 U)
      hrawCarrier
  have hbaselineBridge :=
    _root_.GD.N0232.N0720.N1425.d014725
      m n hm hn 0 sigma tau hsigma htau
      _root_.GD.N0232.N0720.N1424.d014839 _root_.GD.N0232.N0720.N1424.d014842 hbaselineCarrier
  have hrawBridge' :
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 sigma tau)
          (_root_.GD.N0107.d012734 m n (U.step : ℝ) (_root_.GD.N0232.N0720.d014159 U)) =
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 sigma tau)
            (_root_.GD.N0107.d012732 m n 0 t.1) +
          ∫ x, (_root_.GD.N0232.N0720.N1424.d014840 U x - t.1) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by
    simpa only [sub_zero, _root_.GD.N0232.N0720.N1424.d014855,
      hSigma, hfrac, one_mul] using hrawBridge
  have hbaselineBridge' :
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 sigma tau)
          (_root_.GD.N0107.d012733 m n) =
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 sigma tau)
            (_root_.GD.N0107.d012732 m n 0 t.1) +
          ∫ x, (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by
    simpa only [sub_zero, _root_.GD.N0232.N0720.N1424.d014854,
      hSigma, hfrac, one_mul] using hbaselineBridge
  have hphysical :=
    (_root_.GD.N0232.N0720.d014166 U 0 sigma tau hsigma htau).2
  simp only [sub_zero] at hphysical
  rw [hrawBridge', hbaselineBridge'] at hphysical
  linarith




theorem d014866
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013705 m n t (_root_.GD.N0232.N0720.N1424.d014841 U) <
      _root_.GD.N0232.N0720.N1441.d013705 m n t _root_.GD.N0232.N0720.N1424.d014839 := by
  have hrawInt := _root_.GD.N0232.N0720.N1424.d014862 U t
  have hclipInt := _root_.GD.N0232.N0720.N1424.d014863 U t
  have hbaselineInt := _root_.GD.N0232.N0720.N1424.d014861 hm hn t
  have hclipLe :
      (∫ x, (_root_.GD.N0232.N0720.N1424.d014841 U x - t.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1) ≤
        ∫ x, (_root_.GD.N0232.N0720.N1424.d014840 U x - t.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by
    apply integral_mono hclipInt hrawInt
    intro x
    exact _root_.GD.N0230.N0637.d000246
      ⟨t.property.1.le, t.property.2.le⟩
  have hstrict :
      (∫ x, (_root_.GD.N0232.N0720.N1424.d014841 U x - t.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1) <
        ∫ x, (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 :=
    lt_of_le_of_lt hclipLe
      (_root_.GD.N0232.N0720.N1424.d014865 U t)
  have hbaselinePos :
      0 < ∫ x, (_root_.GD.N0232.N0720.N1424.d014839 x - t.1) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by
    exact lt_of_le_of_lt (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0720.N1424.d014864 t
      (_root_.GD.N0232.N0720.N1424.d014841 U) hclipInt,
    _root_.GD.N0232.N0720.N1424.d014864 t _root_.GD.N0232.N0720.N1424.d014839 hbaselineInt]
  exact (ENNReal.ofReal_lt_ofReal_iff hbaselinePos).2 hstrict


theorem d014867
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    Measurable (_root_.GD.N0232.N0720.N1424.d014841 U) ∧
      (∀ x, _root_.GD.N0232.N0720.N1424.d014841 U x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        _root_.GD.N0232.N0720.N1441.d013705 m n t (_root_.GD.N0232.N0720.N1424.d014841 U) <
          _root_.GD.N0232.N0720.N1441.d013705 m n t _root_.GD.N0232.N0720.N1424.d014839 := by
  exact ⟨_root_.GD.N0232.N0720.N1424.d014844 U,
    _root_.GD.N0232.N0720.N1424.d014845 U,
    _root_.GD.N0232.N0720.N1424.d014866 U⟩







theorem d014868
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ selected : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable selected ∧
      (∀ x, selected x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        _root_.GD.N0232.N0720.N1441.d013705 m n t selected <
          _root_.GD.N0232.N0720.N1441.d013705 m n t _root_.GD.N0232.N0720.N1424.d014839) ∧
      (∀ competitor : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
        Measurable competitor →
        (∀ x, competitor x ∈ Set.Icc (0 : ℝ) 1) →
        (∀ t : _root_.GD.N0232.N0720.N1441.d013676,
          _root_.GD.N0232.N0720.N1441.d013705 m n t competitor ≤ _root_.GD.N0232.N0720.N1441.d013705 m n t selected) →
        competitor =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] selected) := by
  rcases _root_.GD.N0232.N0720.d014167 m n hm hn with
    ⟨U, -, -, -⟩
  have hseed := _root_.GD.N0232.N0720.N1424.d014867 U
  exact _root_.GD.N0232.N0720.N1441.d013711 hm hn
    (_root_.GD.N0232.N0720.N1424.d014841 U) _root_.GD.N0232.N0720.N1424.d014839
    hseed.1 hseed.2.1 hseed.2.2

end

end N1424
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1424.d014866
#print axioms _root_.GD.N0232.N0720.N1424.d014867
#print axioms _root_.GD.N0232.N0720.N1424.d014868
