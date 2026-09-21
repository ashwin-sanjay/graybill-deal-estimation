import GD.Module0677














open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0232.N0719.N0923

noncomputable section

open _root_.GD.N0232.N0719.N0922


abbrev d009974 := ℝ × (ℝ × ℝ)


noncomputable def d009975 : Measure _root_.GD.N0232.N0719.N0923.d009974 :=
  (gaussianReal 0 1).prod
    ((gaussianReal 0 1).prod (gaussianReal 0 1))


noncomputable def d009976 : Measure _root_.GD.N0232.N0719.N0923.d009974 :=
  (gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).prod
    ((gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)).prod
      (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)))


noncomputable def d009977 : Measure (_root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974) :=
  _root_.GD.N0232.N0719.N0923.d009975.prod _root_.GD.N0232.N0719.N0923.d009976


def d009978 : Set _root_.GD.N0232.N0719.N0923.d009974 :=
  Icc (0 : ℝ) (1 / 4) ×ˢ
    (Icc (5 / 4 : ℝ) (3 / 2) ×ˢ Icc (5 / 4 : ℝ) (3 / 2))


def d009979 : Set _root_.GD.N0232.N0719.N0923.d009974 :=
  Icc (1 : ℝ) 2 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2)


def d009980 : Set (_root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974) :=
  _root_.GD.N0232.N0719.N0923.d009978 ×ˢ _root_.GD.N0232.N0719.N0923.d009979


def d009981 (ε : ℝ) (z : _root_.GD.N0232.N0719.N0923.d009974) : Fin 3 → ℝ :=
  ![Real.sqrt ε * z.1, z.2.1, z.2.2]


def d009982 (ε : ℝ) (q : _root_.GD.N0232.N0719.N0923.d009974) : Fin 3 → ℝ :=
  ![ε * q.1, q.2.1, q.2.2]




theorem d009983 {a b : ℝ} (hab : a < b) :
    0 < gaussianReal 0 1 (Icc a b) := by
  have hvolPos : 0 < (volume : Measure ℝ) (Icc a b) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 hab)
  have hvol : (volume : Measure ℝ) (Icc a b) ≠ 0 := hvolPos.ne'
  have hac : (volume : Measure ℝ) ≪ gaussianReal 0 1 :=
    gaussianReal_absolutelyContinuous' 0 one_ne_zero
  exact pos_iff_ne_zero.mpr (fun hzero => hvol (hac hzero))



theorem d009984
    {a r u v : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hu : 0 < u) (huv : u < v) :
    0 < gammaMeasure a r (Icc u v) := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Icc]
  change 0 < ∫⁻ x in Icc u v, ENNReal.ofReal (gammaPDFReal a r x) ∂volume
  rw [setLIntegral_pos_iff
    ((measurable_gammaPDFReal a r).ennreal_ofReal)]
  have hsubset :
      Icc u v ⊆ Function.support (gammaPDF a r) ∩ Icc u v := by
    intro x hx
    refine ⟨?_, hx⟩
    have hxpos : 0 < x := lt_of_lt_of_le hu hx.1
    exact ne_of_gt (ENNReal.ofReal_pos.2 (gammaPDFReal_pos ha hr hxpos))
  have hvol : 0 < (volume : Measure ℝ) (Icc u v) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 huv)
  exact hvol.trans_le (measure_mono hsubset)




noncomputable instance d009985 :
    IsProbabilityMeasure _root_.GD.N0232.N0719.N0923.d009977 := by
  unfold _root_.GD.N0232.N0719.N0923.d009977 _root_.GD.N0232.N0719.N0923.d009975
    _root_.GD.N0232.N0719.N0923.d009976
  letI : IsProbabilityMeasure
      (gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure
      (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  infer_instance



theorem d009986 :
    0 < _root_.GD.N0232.N0719.N0923.d009977 _root_.GD.N0232.N0719.N0923.d009980 := by
  have hg0 : 0 < gaussianReal 0 1 (Icc (0 : ℝ) (1 / 4)) :=
    _root_.GD.N0232.N0719.N0923.d009983 (by norm_num)
  have hg1 : 0 < gaussianReal 0 1 (Icc (5 / 4 : ℝ) (3 / 2)) :=
    _root_.GD.N0232.N0719.N0923.d009983 (by norm_num)
  have hq0 :
      0 < gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ) (Icc (1 : ℝ) 2) :=
    _root_.GD.N0232.N0719.N0923.d009984 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hq1 :
      0 < gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ) (Icc (1 : ℝ) 2) :=
    _root_.GD.N0232.N0719.N0923.d009984 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold _root_.GD.N0232.N0719.N0923.d009977 _root_.GD.N0232.N0719.N0923.d009975
    _root_.GD.N0232.N0719.N0923.d009976 _root_.GD.N0232.N0719.N0923.d009980 _root_.GD.N0232.N0719.N0923.d009978
    _root_.GD.N0232.N0719.N0923.d009979
  simp only [Measure.prod_prod]
  positivity



theorem d009987
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {z q : _root_.GD.N0232.N0719.N0923.d009974}
    (hbox : (z, q) ∈ _root_.GD.N0232.N0719.N0923.d009980) :
    _root_.GD.N0232.N0719.N0922.d009928 ε (_root_.GD.N0232.N0719.N0923.d009981 ε z) (_root_.GD.N0232.N0719.N0923.d009982 ε q) := by
  rcases hbox with ⟨hz, hq⟩
  rcases hz with ⟨hz0, hz12⟩
  rcases hz12 with ⟨hz1, hz2⟩
  rcases hq with ⟨hq0, hq12⟩
  rcases hq12 with ⟨hq1, hq2⟩
  have hsqrt_nonneg : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hsqrt_le_one : Real.sqrt ε ≤ 1 := by
    nlinarith [Real.sq_sqrt hε.le]
  have hy0_nonneg : 0 ≤ Real.sqrt ε * z.1 :=
    mul_nonneg hsqrt_nonneg hz0.1
  have hy0_le : Real.sqrt ε * z.1 ≤ 1 / 4 := by
    calc
      Real.sqrt ε * z.1 ≤ 1 * z.1 :=
        mul_le_mul_of_nonneg_right hsqrt_le_one hz0.1
      _ = z.1 := one_mul _
      _ ≤ 1 / 4 := hz0.2
  have ht0l : ε ≤ ε * q.1 := by
    calc
      ε = ε * 1 := by ring
      _ ≤ ε * q.1 := mul_le_mul_of_nonneg_left hq0.1 hε.le
  have ht0u : ε * q.1 ≤ 2 * ε := by
    calc
      ε * q.1 ≤ ε * 2 := mul_le_mul_of_nonneg_left hq0.2 hε.le
      _ = 2 * ε := by ring
  have hy1l : 1 ≤ z.2.1 - Real.sqrt ε * z.1 := by
    linarith [hz1.1]
  have hy1u : z.2.1 - Real.sqrt ε * z.1 ≤ 2 := by
    linarith [hz1.2]
  have hy2l : 1 ≤ z.2.2 - Real.sqrt ε * z.1 := by
    linarith [hz2.1]
  have hy2u : z.2.2 - Real.sqrt ε * z.1 ≤ 2 := by
    linarith [hz2.2]
  refine ⟨hε, hε1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [_root_.GD.N0232.N0719.N0923.d009982] using ht0l
  · simpa [_root_.GD.N0232.N0719.N0923.d009982] using ht0u
  · simpa [_root_.GD.N0232.N0719.N0923.d009982] using hq1.1
  · simpa [_root_.GD.N0232.N0719.N0923.d009982] using hq1.2
  · simpa [_root_.GD.N0232.N0719.N0923.d009982] using hq2.1
  · simpa [_root_.GD.N0232.N0719.N0923.d009982] using hq2.2
  · simpa [_root_.GD.N0232.N0719.N0923.d009981] using hy1l
  · simpa [_root_.GD.N0232.N0719.N0923.d009981] using hy1u
  · simpa [_root_.GD.N0232.N0719.N0923.d009981] using hy2l
  · simpa [_root_.GD.N0232.N0719.N0923.d009981] using hy2u



theorem d009988
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < _root_.GD.N0232.N0719.N0923.d009977
      {w | _root_.GD.N0232.N0719.N0922.d009928 ε (_root_.GD.N0232.N0719.N0923.d009981 ε w.1)
        (_root_.GD.N0232.N0719.N0923.d009982 ε w.2)} := by
  refine _root_.GD.N0232.N0719.N0923.d009986.trans_le (measure_mono ?_)
  intro w hw
  exact _root_.GD.N0232.N0719.N0923.d009987 hε hε1 hw

end

end GD.N0232.N0719.N0923

#print axioms _root_.GD.N0232.N0719.N0923.d009986
#print axioms _root_.GD.N0232.N0719.N0923.d009987
#print axioms _root_.GD.N0232.N0719.N0923.d009988
