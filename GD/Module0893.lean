import GD.Module0883

































open Filter MeasureTheory ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1442

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1421
open _root_.GD.N0232.N0720.N1426
open _root_.GD.N0232.N0720.N1428
open _root_.GD.N0232.N0720.N1431
open _root_.GD.N0232.N0720.N1439



def d013866 (p : ℝ) : ℝ :=
  p * (1 - p)


def d013867 (alpha beta p : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1442.d013866 p + _root_.GD.N0232.N0720.N1091.d012790 alpha beta p



def d013868 (alpha beta p : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1091.d012790 alpha beta p /
    _root_.GD.N0232.N0720.N1442.d013867 alpha beta p


def d013869 (alpha beta p : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1442.d013866 p / _root_.GD.N0232.N0720.N1442.d013867 alpha beta p

theorem d013870 (alpha beta p : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1091.d012790 alpha beta p := by
  unfold _root_.GD.N0232.N0720.N1091.d012790
  exact integral_nonneg fun _ => sq_nonneg _

theorem d013871
    {alpha beta p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < _root_.GD.N0232.N0720.N1442.d013867 alpha beta p := by
  unfold _root_.GD.N0232.N0720.N1442.d013867 _root_.GD.N0232.N0720.N1442.d013866
  exact add_pos_of_pos_of_nonneg
    (mul_pos hp0 (sub_pos.mpr hp1))
    (_root_.GD.N0232.N0720.N1442.d013870 alpha beta p)


theorem d013872
    {alpha beta p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1442.d013869 alpha beta p +
        _root_.GD.N0232.N0720.N1442.d013868 alpha beta p = 1 := by
  have htotal := _root_.GD.N0232.N0720.N1442.d013871
    (alpha := alpha) (beta := beta) hp0 hp1
  unfold _root_.GD.N0232.N0720.N1442.d013869 _root_.GD.N0232.N0720.N1442.d013868
    _root_.GD.N0232.N0720.N1442.d013867
  rw [← add_div]
  exact div_self htotal.ne'

theorem d013873
    {alpha beta p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1442.d013869 alpha beta p =
      1 - _root_.GD.N0232.N0720.N1442.d013868 alpha beta p := by
  linarith [_root_.GD.N0232.N0720.N1442.d013872
    (alpha := alpha) (beta := beta) hp0 hp1]






theorem d013874
    {alpha beta : ℝ} {p scale : ℕ → ℝ}
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1)
    (hscale : ∀ k, scale k ≠ 0)
    {O R : ℝ}
    (hOracle : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013866 (p k) / scale k)
      atTop (nhds O))
    (hRegret : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / scale k)
      atTop (nhds R))
    (hOR : O + R ≠ 0) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013868 alpha beta (p k))
      atTop (nhds (R / (O + R))) := by
  have hquot := hRegret.div (hOracle.add hRegret) hOR
  apply hquot.congr'
  exact Filter.Eventually.of_forall fun k => by
    have htotal := _root_.GD.N0232.N0720.N1442.d013871
      (alpha := alpha) (beta := beta) (hp0 k) (hp1 k)
    change
      (_root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / scale k) /
          (_root_.GD.N0232.N0720.N1442.d013866 (p k) / scale k +
            _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / scale k) =
        _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) /
          _root_.GD.N0232.N0720.N1442.d013867 alpha beta (p k)
    unfold _root_.GD.N0232.N0720.N1442.d013867
    field_simp [hscale k, htotal.ne']



theorem d013875
    {alpha beta L : ℝ} {p : ℕ → ℝ}
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1)
    (hExcess : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013868 alpha beta (p k))
      atTop (nhds L)) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013869 alpha beta (p k))
      atTop (nhds (1 - L)) := by
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h := hconst.sub hExcess
  apply h.congr'
  exact Filter.Eventually.of_forall fun k =>
    (_root_.GD.N0232.N0720.N1442.d013873
      (alpha := alpha) (beta := beta) (hp0 k) (hp1 k)).symm






theorem d013876
    {alpha beta : ℝ} (halphaOne : 1 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / p k)
      atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halphaOne
  have hhorn := _root_.GD.N0232.N0720.N1439.d013670
    halpha0 halphaTwo hbeta hp hp0 hp1
  have hpow : Tendsto (fun k => p k ^ (alpha - 1)) atTop (nhds 0) :=
    _root_.GD.N0232.N0720.N1428.d013152 hp (sub_pos.mpr halphaOne)
  have hproduct := hhorn.mul hpow
  simpa only [mul_zero] using hproduct.congr' (Filter.Eventually.of_forall
    fun k => by
      rw [Real.rpow_sub (hp0 k) alpha 1, Real.rpow_one]
      field_simp [(hp0 k).ne',
        (Real.rpow_pos_of_pos (hp0 k) alpha).ne'])



theorem d013877
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 2 beta (p k) / p k)
      atTop (nhds 0) := by
  have hcritical := _root_.GD.N0232.N0720.N1426.d013206
    hbeta hp hp0 hp1
  have hmulLogRaw : Tendsto (fun k => p k * Real.log (p k))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.continuous_mul_log.continuousAt.tendsto.comp hp
  have hmulLog : Tendsto (fun k => p k * Real.log (1 / p k))
      atTop (nhds 0) := by
    have hneg := hmulLogRaw.neg
    have heq : (fun k => -(p k * Real.log (p k))) =ᶠ[atTop]
        (fun k => p k * Real.log (1 / p k)) :=
      Filter.Eventually.of_forall fun k => by
      change -(p k * Real.log (p k)) = p k * Real.log (1 / p k)
      rw [one_div, Real.log_inv]
      ring
    simpa only [neg_zero] using hneg.congr' heq
  have hproduct := hcritical.mul hmulLog
  simpa only [mul_zero] using hproduct.congr' (Filter.Eventually.of_forall
    fun k => by
      have hratio : 1 < 1 / p k :=
        (lt_div_iff₀ (hp0 k)).2 (by simpa using hp1 k)
      have hlog : Real.log (1 / p k) ≠ 0 :=
        (Real.log_pos hratio).ne'
      field_simp [(hp0 k).ne', hlog])


theorem d013878
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / p k)
      atTop (nhds 0) := by
  have hregular := _root_.GD.N0232.N0720.N1421.d013121
    halpha hbeta hp hp0 hp1
  have hproduct := hregular.mul hp
  simpa only [mul_zero] using hproduct.congr' (Filter.Eventually.of_forall
    fun k => by
      field_simp [(hp0 k).ne'])





theorem d013879
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k =>
        (_root_.GD.N0232.N0720.N1442.d013869 alpha beta (p k),
          _root_.GD.N0232.N0720.N1442.d013868 alpha beta (p k)))
      atTop (nhds (0, 1)) := by
  let C := _root_.GD.N0232.N0720.N1431.d013671 alpha beta
  have hC : 0 < C := by
    unfold C _root_.GD.N0232.N0720.N1431.d013671
    exact div_pos
      (mul_pos
        (mul_pos (Real.rpow_pos_of_pos (div_pos halpha hbeta) _)
          (Real.Gamma_pos_of_pos (add_pos halpha hbeta)))
        (Real.Gamma_pos_of_pos (by linarith)))
      (Real.Gamma_pos_of_pos hbeta)
  have hregret : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / p k ^ alpha)
      atTop (nhds C) := by
    exact _root_.GD.N0232.N0720.N1439.d013670
      halpha (lt_trans halphaOne one_lt_two) hbeta hp hp0 hp1
  have hpow : Tendsto (fun k => p k ^ (1 - alpha)) atTop (nhds 0) :=
    _root_.GD.N0232.N0720.N1428.d013152 hp (sub_pos.mpr halphaOne)
  have honeSub : Tendsto (fun k => 1 - p k) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hp using 1 <;> ring
  have hOracle : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013866 (p k) / p k ^ alpha)
      atTop (nhds 0) := by
    have hproduct := hpow.mul honeSub
    simpa only [zero_mul] using hproduct.congr' (Filter.Eventually.of_forall
      fun k => by
        unfold _root_.GD.N0232.N0720.N1442.d013866
        rw [Real.rpow_sub (hp0 k) 1 alpha, Real.rpow_one]
        field_simp [(Real.rpow_pos_of_pos (hp0 k) alpha).ne'])
  have hExcess :=
    _root_.GD.N0232.N0720.N1442.d013874
      hp0 hp1
      (fun k => (Real.rpow_pos_of_pos (hp0 k) alpha).ne')
      hOracle hregret (by simpa using hC.ne')
  have hExcess' : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013868 alpha beta (p k))
      atTop (nhds 1) := by
    simpa [hC.ne'] using hExcess
  have hOracle' := _root_.GD.N0232.N0720.N1442.d013875
    hp0 hp1 hExcess'
  simpa using hOracle'.prodMk_nhds hExcess'



theorem d013880
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k =>
        (_root_.GD.N0232.N0720.N1442.d013869 1 beta (p k),
          _root_.GD.N0232.N0720.N1442.d013868 1 beta (p k)))
      atTop (nhds (1 / 2, 1 / 2)) := by
  have hregretRaw := _root_.GD.N0232.N0720.N1439.d013670
    (alpha := (1 : ℝ)) zero_lt_one one_lt_two hbeta hp hp0 hp1
  have hconstant :
      (1 / beta) ^ (1 : ℝ) * Real.Gamma (1 + beta) *
          Real.Gamma (2 - 1) / Real.Gamma beta = 1 := by
    change _root_.GD.N0232.N0720.N1431.d013671 1 beta = 1
    exact _root_.GD.N0232.N0720.N1431.d013673 hbeta
  have hregret : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 1 beta (p k) / p k)
      atTop (nhds 1) := by
    rw [hconstant] at hregretRaw
    simpa only [Real.rpow_one] using hregretRaw
  have honeSub : Tendsto (fun k => 1 - p k) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hp using 1 <;> ring
  have hOracle : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013866 (p k) / p k)
      atTop (nhds 1) := by
    apply honeSub.congr'
    exact Filter.Eventually.of_forall fun k => by
      unfold _root_.GD.N0232.N0720.N1442.d013866
      field_simp [(hp0 k).ne']
  have hExcess := _root_.GD.N0232.N0720.N1442.d013874
    hp0 hp1 (fun k => (hp0 k).ne') hOracle hregret (by norm_num)
  have hExcess' : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013868 1 beta (p k))
      atTop (nhds (1 / 2)) := by
    norm_num at hExcess ⊢
    exact hExcess
  have hOracle' := _root_.GD.N0232.N0720.N1442.d013875
    hp0 hp1 hExcess'
  convert hOracle'.prodMk_nhds hExcess' using 1 <;> norm_num



theorem d013881
    {alpha beta : ℝ} {p : ℕ → ℝ}
    (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1)
    (hregret : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / p k)
      atTop (nhds 0)) :
    Tendsto
      (fun k =>
        (_root_.GD.N0232.N0720.N1442.d013869 alpha beta (p k),
          _root_.GD.N0232.N0720.N1442.d013868 alpha beta (p k)))
      atTop (nhds (1, 0)) := by
  have honeSub : Tendsto (fun k => 1 - p k) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hp using 1 <;> ring
  have hOracle : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013866 (p k) / p k)
      atTop (nhds 1) := by
    apply honeSub.congr'
    exact Filter.Eventually.of_forall fun k => by
      unfold _root_.GD.N0232.N0720.N1442.d013866
      field_simp [(hp0 k).ne']
  have hExcess := _root_.GD.N0232.N0720.N1442.d013874
    hp0 hp1 (fun k => (hp0 k).ne') hOracle hregret (by norm_num)
  have hExcess' : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013868 alpha beta (p k))
      atTop (nhds 0) := by
    simpa using hExcess
  have hOracle' := _root_.GD.N0232.N0720.N1442.d013875
    hp0 hp1 hExcess'
  simpa using hOracle'.prodMk_nhds hExcess'

theorem d013882
    {alpha beta : ℝ} (halphaOne : 1 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k =>
        (_root_.GD.N0232.N0720.N1442.d013869 alpha beta (p k),
          _root_.GD.N0232.N0720.N1442.d013868 alpha beta (p k)))
      atTop (nhds (1, 0)) := by
  exact _root_.GD.N0232.N0720.N1442.d013881
    hp hp0 hp1
      (_root_.GD.N0232.N0720.N1442.d013876
        halphaOne halphaTwo hbeta hp hp0 hp1)

theorem d013883
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k =>
        (_root_.GD.N0232.N0720.N1442.d013869 2 beta (p k),
          _root_.GD.N0232.N0720.N1442.d013868 2 beta (p k)))
      atTop (nhds (1, 0)) := by
  exact _root_.GD.N0232.N0720.N1442.d013881
    hp hp0 hp1
      (_root_.GD.N0232.N0720.N1442.d013877
        hbeta hp hp0 hp1)

theorem d013884
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k =>
        (_root_.GD.N0232.N0720.N1442.d013869 alpha beta (p k),
          _root_.GD.N0232.N0720.N1442.d013868 alpha beta (p k)))
      atTop (nhds (1, 0)) := by
  exact _root_.GD.N0232.N0720.N1442.d013881
    hp hp0 hp1
      (_root_.GD.N0232.N0720.N1442.d013878
        halpha hbeta hp hp0 hp1)

end

end N1442
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1442.d013876
#print axioms _root_.GD.N0232.N0720.N1442.d013877
#print axioms _root_.GD.N0232.N0720.N1442.d013878
#print axioms _root_.GD.N0232.N0720.N1442.d013879
#print axioms _root_.GD.N0232.N0720.N1442.d013880
#print axioms _root_.GD.N0232.N0720.N1442.d013882
#print axioms _root_.GD.N0232.N0720.N1442.d013883
#print axioms _root_.GD.N0232.N0720.N1442.d013884
