import GD.Module0857






















open MeasureTheory Filter Set

namespace GD
namespace N0232
namespace N0720
namespace N1429

noncomputable section

open _root_.GD.N0232.N0720.N1421
open _root_.GD.N0232.N0720.N1428
open _root_.GD.N0232.N0720.N1427


noncomputable def d013173 (beta t : ℝ) : ℝ :=
  ∫ X : ℝ in t..1, _root_.GD.N0232.N0720.N1427.d013155 beta t X



noncomputable def d013174 (beta t : ℝ) : ℝ :=
  ∫ X : ℝ in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1427.d013155 beta t X



noncomputable def d013175 (beta t : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1427.d013156 beta t + _root_.GD.N0232.N0720.N1429.d013173 beta t +
    _root_.GD.N0232.N0720.N1427.d013157 beta t

theorem d013176
    {t : ℝ} (ht : 0 < t) :
    Continuous (_root_.GD.N0232.N0720.N1421.d013128 t) := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (_root_.GD.N0232.N0720.N1421.d013131 (u := u) ht).continuousAt


theorem d013177
    {beta t : ℝ} (hbeta : 0 < beta) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1429.d013173 beta t =
      _root_.GD.N0232.N0720.N1428.d013133 beta * Real.log (1 / t) *
        ∫ u : ℝ in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1428.d013140 beta t u := by
  let f : ℝ → ℝ := _root_.GD.N0232.N0720.N1421.d013128 t
  let f' : ℝ → ℝ := fun u =>
    -Real.log t * _root_.GD.N0232.N0720.N1421.d013128 t u
  let g : ℝ → ℝ := _root_.GD.N0232.N0720.N1427.d013155 beta t
  have hderiv : ∀ u ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt f (f' u) u := by
    intro u _hu
    exact _root_.GD.N0232.N0720.N1421.d013131 ht0
  have hderivNonneg : ∀ u ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      0 ≤ f' u := by
    intro u _hu
    dsimp [f']
    exact mul_nonneg (neg_nonneg.mpr (Real.log_nonpos ht0.le ht1.le))
      (Real.rpow_nonneg ht0.le _)
  have hcov := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := f) (f' := f') (g := g)
    (_root_.GD.N0232.N0720.N1429.d013176 ht0).continuousOn hderiv hderivNonneg
  have hf0 : f 0 = t := _root_.GD.N0232.N0720.N1421.d013129 t
  have hf1 : f 1 = 1 := _root_.GD.N0232.N0720.N1421.d013130 t
  have hcov' :
      (∫ u : ℝ in (0 : ℝ)..1, g (f u) * f' u) =
        ∫ X : ℝ in t..1, g X := by
    simpa [hf0, hf1] using hcov
  unfold _root_.GD.N0232.N0720.N1429.d013173
  rw [← hcov']
  calc
    (∫ u : ℝ in (0 : ℝ)..1, g (f u) * f' u) =
        ∫ u : ℝ in (0 : ℝ)..1,
          _root_.GD.N0232.N0720.N1428.d013133 beta * Real.log (1 / t) *
            _root_.GD.N0232.N0720.N1428.d013140 beta t u := by
      apply intervalIntegral.integral_congr
      intro u _hu
      have hjac := _root_.GD.N0232.N0720.N1428.d013146
        (beta := beta) (t := t) (u := u) hbeta ht0 ht1
      have hf'nonneg : 0 ≤ f' u := by
        dsimp [f']
        exact mul_nonneg (neg_nonneg.mpr (Real.log_nonpos ht0.le ht1.le))
          (Real.rpow_nonneg ht0.le _)
      rw [abs_of_nonneg hf'nonneg] at hjac
      simpa [g, f, f', _root_.GD.N0232.N0720.N1427.d013155, mul_assoc] using hjac
    _ = _root_.GD.N0232.N0720.N1428.d013133 beta * Real.log (1 / t) *
          ∫ u : ℝ in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1428.d013140 beta t u := by
      rw [intervalIntegral.integral_const_mul]

theorem d013178
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < Real.log (1 / t) := by
  apply Real.log_pos
  rw [one_lt_div ht0]
  exact ht1



theorem d013179
    {beta t : ℝ} (hbeta : 0 < beta) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1429.d013173 beta t / Real.log (1 / t) =
      _root_.GD.N0232.N0720.N1428.d013133 beta *
        ∫ u : ℝ in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1428.d013140 beta t u := by
  rw [_root_.GD.N0232.N0720.N1429.d013177 hbeta ht0 ht1]
  apply (div_eq_iff (_root_.GD.N0232.N0720.N1429.d013178 ht0 ht1).ne').2
  ring


theorem d013180
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1429.d013173 beta (p n) /
        Real.log (1 / p n))
      atTop (nhds (_root_.GD.N0232.N0720.N1428.d013133 beta)) := by
  have hw := _root_.GD.N0232.N0720.N1428.d013154 hbeta hp hp0 hp1
  have hw' : Tendsto
      (fun n => ∫ u : ℝ in (0 : ℝ)..1,
        _root_.GD.N0232.N0720.N1428.d013140 beta (p n) u)
      atTop (nhds 1) := by
    simpa [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hw
  have hmul := hw'.const_mul (_root_.GD.N0232.N0720.N1428.d013133 beta)
  convert hmul using 1
  · funext n
    exact _root_.GD.N0232.N0720.N1429.d013179 hbeta (hp0 n) (hp1 n)
  · simp

theorem d013181
    {beta t : ℝ} (hbeta : 0 < beta) (ht0 : 0 < t) :
    0 ≤ _root_.GD.N0232.N0720.N1427.d013156 beta t := by
  unfold _root_.GD.N0232.N0720.N1427.d013156
  apply intervalIntegral.integral_nonneg ht0.le
  intro X hX
  exact _root_.GD.N0232.N0720.N1427.d013160 hbeta hX.1

theorem d013182
    {beta t : ℝ} (hbeta : 0 < beta) :
    0 ≤ _root_.GD.N0232.N0720.N1427.d013157 beta t := by
  unfold _root_.GD.N0232.N0720.N1427.d013157
  apply setIntegral_nonneg measurableSet_Ioi
  intro X hX
  exact _root_.GD.N0232.N0720.N1427.d013160 hbeta (zero_le_one.trans hX.le)

theorem d013183
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) :
    Tendsto (fun n => Real.log (1 / p n)) atTop atTop := by
  have hpGT : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hp, Eventually.of_forall fun n => hp0 n⟩
  have hinv : Tendsto (fun n => (p n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hpGT
  have hlog := Real.tendsto_log_atTop.comp hinv
  apply hlog.congr'
  exact Eventually.of_forall fun n => by
    simp only [Function.comp_apply, one_div]

theorem d013184
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1427.d013156 beta (p n) /
        Real.log (1 / p n))
      atTop (nhds 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero
    (b := (0 : ℝ))
    (B := _root_.GD.N0232.N0720.N1428.d013133 beta / 2)
  · exact Eventually.of_forall fun n =>
      _root_.GD.N0232.N0720.N1429.d013181 hbeta (hp0 n)
  · exact Eventually.of_forall fun n =>
      _root_.GD.N0232.N0720.N1427.d013164 hbeta (hp0 n) (hp1 n)
  · exact _root_.GD.N0232.N0720.N1429.d013183 hp hp0

theorem d013185
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1427.d013157 beta (p n) /
        Real.log (1 / p n))
      atTop (nhds 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero
    (b := (0 : ℝ))
    (B := _root_.GD.N0232.N0720.N1428.d013133 beta * beta ^ (beta + 2) / beta)
  · exact Eventually.of_forall fun _ => _root_.GD.N0232.N0720.N1429.d013182 hbeta
  · exact Eventually.of_forall fun n =>
      _root_.GD.N0232.N0720.N1427.d013172 hbeta (hp0 n) (hp1 n)
  · exact _root_.GD.N0232.N0720.N1429.d013183 hp hp0



theorem d013186
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1429.d013175 beta (p n) /
        Real.log (1 / p n))
      atTop (nhds (_root_.GD.N0232.N0720.N1428.d013133 beta)) := by
  have hleft := _root_.GD.N0232.N0720.N1429.d013184 hbeta hp hp0 hp1
  have hmiddle := _root_.GD.N0232.N0720.N1429.d013180 hbeta hp hp0 hp1
  have hright := _root_.GD.N0232.N0720.N1429.d013185 hbeta hp hp0 hp1
  have hsum := (hleft.add hmiddle).add hright
  convert hsum using 1
  · funext n
    unfold _root_.GD.N0232.N0720.N1429.d013175
    ring_nf
  · simp

end

end N1429
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1429.d013177
#print axioms _root_.GD.N0232.N0720.N1429.d013180
#print axioms _root_.GD.N0232.N0720.N1429.d013184
#print axioms _root_.GD.N0232.N0720.N1429.d013185
#print axioms _root_.GD.N0232.N0720.N1429.d013186
