import GD.Module1043

























open Filter MeasureTheory
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1444

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1499

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false


def d017041 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) : Unit ⊕ ι → _root_.GD.N0232.N0720.N1080.d014168
  | Sum.inl _ => _root_.GD.N0232.N0720.N1080.d014169
  | Sum.inr i => packet i



def d017042 (t : ℝ) (weight : ι → ℝ) : Unit ⊕ ι → ℝ
  | Sum.inl _ => t - 1
  | Sum.inr i => t * weight i



theorem d017043
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1499.d015001 m n _root_.GD.N0232.N0720.N1080.d014169 omega = 1 := by
  have h :=
    _root_.GD.N0232.N0720.N1124.d016500
      (m := m) (n := n)
      (g := (1 :
        _root_.GD.N0232.N0719.N0946.d009229))
      _root_.GD.N0232.N0720.N1080.d014169 omega
  simp only [_root_.GD.N0232.N0720.N1215.d014276,
    one_smul] at h
  have hpos := _root_.GD.N0232.N0720.N1499.d015005 m n _root_.GD.N0232.N0720.N1080.d014169 omega
  nlinarith



theorem d017044
    (t : ℝ) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1444.d017041 packet)
        (_root_.GD.N0232.N0720.N1444.d017042 t weight) omega =
      t * _root_.GD.N0232.N0720.N1126.d016415 packet weight omega := by
  classical
  simp only [_root_.GD.N0232.N0720.N1126.d016415, _root_.GD.N0230.N0617.d000163, _root_.GD.N0232.N0720.N1126.d016413,
    _root_.GD.N0232.N0720.N1444.d017041, _root_.GD.N0232.N0720.N1444.d017042,
    Fintype.sum_sum_type, Fintype.sum_unique, _root_.GD.N0232.N0720.N1126.d016413]
  rw [_root_.GD.N0232.N0720.N1444.d017043]
  have hsum :
      (∑ x, t * weight x * _root_.GD.N0232.N0720.N1499.d015001 m n (packet x) omega) =
        t * ∑ x, weight x * _root_.GD.N0232.N0720.N1499.d015001 m n (packet x) omega := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring



theorem d017045
    (t : ℝ) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1444.d017042 t weight)
        (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1444.d017041 packet))
        (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1444.d017041 packet)) omega =
      t * _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) omega := by
  classical
  simp only [_root_.GD.N0230.N0617.d000164, _root_.GD.N0232.N0720.N1126.d016413, _root_.GD.N0232.N0720.N1126.d016414,
    _root_.GD.N0232.N0720.N1444.d017041, _root_.GD.N0232.N0720.N1444.d017042,
    Fintype.sum_sum_type, Fintype.sum_unique, _root_.GD.N0232.N0720.N1080.d014169,
    mul_zero, zero_add]
  have hsum :
      (∑ x,
          t * weight x * _root_.GD.N0232.N0720.N1499.d015001 m n (packet x) omega *
            (packet x).location) =
        t * ∑ x,
          weight x * _root_.GD.N0232.N0720.N1499.d015001 m n (packet x) omega *
            (packet x).location := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  exact hsum



theorem d017046
    {t : ℝ} (ht : t ≠ 0)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016416 (_root_.GD.N0232.N0720.N1444.d017041 packet)
        (_root_.GD.N0232.N0720.N1444.d017042 t weight) omega =
      _root_.GD.N0232.N0720.N1126.d016416 packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1126.d016416 _root_.GD.N0230.N0617.d000166
  change
    _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1444.d017042 t weight)
          (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1444.d017041 packet))
          (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1444.d017041 packet)) omega /
        _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1444.d017041 packet)
          (_root_.GD.N0232.N0720.N1444.d017042 t weight) omega =
      _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
          omega /
        _root_.GD.N0232.N0720.N1126.d016415 packet weight omega
  rw [_root_.GD.N0232.N0720.N1444.d017045,
    _root_.GD.N0232.N0720.N1444.d017044]
  field_simp [ht]



theorem d017047
    {t : ℝ} (ht : 1 ≤ t) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1444.d017042 t weight i := by
  rintro (u | i)
  · simp [_root_.GD.N0232.N0720.N1444.d017042, sub_nonneg.mpr ht]
  · exact mul_nonneg (le_trans zero_le_one ht) (hweight i)



theorem d017048
    {t : ℝ} (ht : t ≠ 0)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000167 (_root_.GD.N0232.N0720.N1444.d017042 t weight)
        (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1444.d017041 packet))
        (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1444.d017041 packet)) omega =
      t * _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) omega := by
  unfold _root_.GD.N0230.N0617.d000167
  change
    _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1444.d017042 t weight)
          (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1444.d017041 packet))
          (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1444.d017041 packet)) omega ^ 2 /
        _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1444.d017041 packet)
          (_root_.GD.N0232.N0720.N1444.d017042 t weight) omega =
      t * (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
          (_root_.GD.N0232.N0720.N1126.d016414 packet) omega ^ 2 /
        _root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
  rw [_root_.GD.N0232.N0720.N1444.d017045,
    _root_.GD.N0232.N0720.N1444.d017044]
  field_simp [ht]



theorem d017049
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1126.d016431 s (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014169) () = ‖s.value‖ ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1126.d016431
  rw [_root_.GD.N0232.N0720.N1080.d014190]
  simp only [zero_sub, norm_neg]
  rw [ENNReal.toReal_ofReal (sq_nonneg ‖s.value‖)]


theorem d017050
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {t : ℝ} (ht : t ≠ 0)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1126.d016432 s (_root_.GD.N0232.N0720.N1444.d017041 packet)
        (_root_.GD.N0232.N0720.N1444.d017042 t weight) =
      t * _root_.GD.N0232.N0720.N1126.d016432 s packet weight -
        (t - 1) * ‖s.value‖ ^ 2 := by
  classical
  unfold _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0230.N0617.d000186
  simp only [_root_.GD.N0232.N0720.N1444.d017041, _root_.GD.N0232.N0720.N1444.d017042,
    _root_.GD.N0232.N0720.N1126.d016414, _root_.GD.N0232.N0720.N1126.d016431, Fintype.sum_sum_type, Fintype.sum_unique]
  have hsum :
      (∑ x,
          t * weight x *
            ((packet x).location ^ 2 -
              (_root_.GD.N0232.N0720.N1080.d014182 m n (packet x) s.value).toReal)) =
        t * ∑ x,
          weight x *
            ((packet x).location ^ 2 -
              (_root_.GD.N0232.N0720.N1080.d014182 m n (packet x) s.value).toReal) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcorrection :
      (∫ omega,
          _root_.GD.N0230.N0617.d000167 (_root_.GD.N0232.N0720.N1444.d017042 t weight)
            (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1444.d017041 packet))
            (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1444.d017041 packet)) omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        t * ∫ omega,
          _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
            (_root_.GD.N0232.N0720.N1126.d016414 packet) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [integral_congr_ae (ae_of_all _ fun omega ↦
      _root_.GD.N0232.N0720.N1444.d017048 ht packet weight omega)]
    exact integral_const_mul t _
  rw [hcorrection]
  have href :
      (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 s.value).toReal = ‖s.value‖ ^ 2 := by
    rw [_root_.GD.N0232.N0720.N1080.d014190]
    simp only [zero_sub, norm_neg]
    rw [ENNReal.toReal_ofReal (sq_nonneg ‖s.value‖)]
  rw [href, hsum]
  simp only [_root_.GD.N0232.N0720.N1080.d014169]
  ring



theorem d017051
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {t : ℝ} (ht : t ≠ 0)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (_root_.GD.N0232.N0720.N1444.d017041 packet)
          (_root_.GD.N0232.N0720.N1444.d017042 t weight) =
      t * (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s packet weight) +
        (t - 1) * (‖s.value‖ ^ 2 -
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1444.d017050 s ht packet weight]
  ring






theorem d017052
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (scale : ℕ → ℝ)
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hscaleOne : ∀ j, 1 ≤ scale j)
    (hscale : Tendsto scale atTop atTop)
    (hbaseGap : ∀ j,
      0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
    (hreplicatedTight : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s
            (_root_.GD.N0232.N0720.N1444.d017041 (packet j))
            (_root_.GD.N0232.N0720.N1444.d017042 (scale j) (weight j)))
      atTop (nhds 0)) :
    ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 = 0 := by
  let delta :=
    ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2
  have hdeltaNonneg : 0 ≤ delta := by
    have href :=
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1 _root_.GD.N0232.N0720.N1080.d014169
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
    simp only [zero_sub, norm_neg] at href
    have hnorm :
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ ‖s.value‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
    exact sub_nonneg.mpr hnorm
  have hdeltaZero : delta = 0 := by
    by_contra hne
    have hdeltaPos : 0 < delta :=
      lt_of_le_of_ne hdeltaNonneg (fun h ↦ hne h.symm)
    have hthreshold : ∀ᶠ j in atTop,
        1 + 1 / delta ≤ scale j :=
      (tendsto_atTop.1 hscale) (1 + 1 / delta)
    have hreplicatedLarge : ∀ᶠ j in atTop,
        1 ≤
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
            _root_.GD.N0232.N0720.N1126.d016432 s
              (_root_.GD.N0232.N0720.N1444.d017041 (packet j))
              (_root_.GD.N0232.N0720.N1444.d017042 (scale j) (weight j)) := by
      filter_upwards [hthreshold] with j hj
      have hscalePos : 0 < scale j :=
        lt_of_lt_of_le zero_lt_one (hscaleOne j)
      rw [_root_.GD.N0232.N0720.N1444.d017051
        s hscalePos.ne' (packet j) (weight j)]
      have hfirst :
          0 ≤ scale j *
            (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
              _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j)) :=
        mul_nonneg hscalePos.le (hbaseGap j)
      have hinv : (1 / delta) * delta = 1 := by
        field_simp [hdeltaPos.ne']
      have hfactor : 1 ≤ (scale j - 1) * delta := by
        have hquotient : 1 / delta ≤ scale j - 1 := by
          linarith
        have hmul := mul_le_mul_of_nonneg_right hquotient hdeltaNonneg
        linarith
      change 1 ≤
        scale j *
            (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
              _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j)) +
          (scale j - 1) * delta
      linarith
    have hreplicatedSmall : ∀ᶠ j in atTop,
        |‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
            _root_.GD.N0232.N0720.N1126.d016432 s
              (_root_.GD.N0232.N0720.N1444.d017041 (packet j))
              (_root_.GD.N0232.N0720.N1444.d017042 (scale j) (weight j))| < 1 := by
      obtain ⟨N, hN⟩ :=
        (Metric.tendsto_atTop.1 hreplicatedTight) 1 zero_lt_one
      filter_upwards [eventually_ge_atTop N] with j hj
      have hjMetric := hN j hj
      simpa only [Real.dist_eq, sub_zero] using hjMetric
    obtain ⟨j, hlarge, hsmall⟩ :=
      (hreplicatedLarge.and hreplicatedSmall).exists
    have hleAbs :
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
              _root_.GD.N0232.N0720.N1126.d016432 s
                (_root_.GD.N0232.N0720.N1444.d017041 (packet j))
                (_root_.GD.N0232.N0720.N1444.d017042 (scale j) (weight j)) ≤
            |‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
              _root_.GD.N0232.N0720.N1126.d016432 s
                (_root_.GD.N0232.N0720.N1444.d017041 (packet j))
                (_root_.GD.N0232.N0720.N1444.d017042 (scale j) (weight j))| :=
      le_abs_self _
    linarith
  simpa only [delta] using hdeltaZero


theorem d017053
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (scale : ℕ → ℝ)
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hscaleOne : ∀ j, 1 ≤ scale j)
    (hscale : Tendsto scale atTop atTop)
    (hbaseGap : ∀ j,
      0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
    (hreplicatedTight : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s
            (_root_.GD.N0232.N0720.N1444.d017041 (packet j))
            (_root_.GD.N0232.N0720.N1444.d017042 (scale j) (weight j)))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  have hgap :=
    _root_.GD.N0232.N0720.N1444.d017052
      s scale packet weight hscaleOne hscale hbaseGap hreplicatedTight
  have htax := _root_.GD.N0232.N0720.N1159.d014648
    m n s.value s.value (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
  have hsq :
      ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ 0 :=
    htax.trans_eq hgap
  have hnorm :
      ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ = 0 := by
    nlinarith [norm_nonneg
      (s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm



theorem d017054
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (scale : ℕ → ℝ)
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hscaleOne : ∀ j, 1 ≤ scale j)
    (hscale : Tendsto scale atTop atTop)
    (hbaseGap : ∀ j,
      0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
    (hreplicatedTight : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s
            (_root_.GD.N0232.N0720.N1444.d017041 (packet j))
            (_root_.GD.N0232.N0720.N1444.d017042 (scale j) (weight j)))
      atTop (nhds 0)) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  apply (_root_.GD.N0232.N0720.N1159.d014635 m n s.value).1
  exact _root_.GD.N0232.N0720.N1444.d017053
    s scale packet weight hscaleOne hscale hbaseGap hreplicatedTight

end

end N1444
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1444.d017046
#print axioms _root_.GD.N0232.N0720.N1444.d017050
#print axioms _root_.GD.N0232.N0720.N1444.d017051
#print axioms _root_.GD.N0232.N0720.N1444.d017052
#print axioms _root_.GD.N0232.N0720.N1444.d017053
