import GD.Module0199
import GD.Module1105
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

















open Filter Topology
open scoped Topology

namespace GD.N0232.N0720.N1300

noncomputable section

open _root_.GD.N0232.N0720.N1350
open _root_.GD.N0232.N0720.N1416


def d017771 (rho : ℝ) (n : ℕ) (s : ℤ) : ℝ :=
  rho ^ ((n : ℝ) + (s : ℝ))









def d017772
    (rho e c : ℝ) (n : ℕ) (s : ℤ) : ℝ :=
  let p := _root_.GD.N0232.N0720.N1300.d017771 rho n s
  e * (1 - p) + (1 - e) * p + c * rho ^ (s : ℝ) * (1 - p)



def d017773
    (rho beta e c : ℝ) (n : ℕ) (s : ℤ) : ℝ :=
  if (1 : ℤ) ≤ (n : ℤ) + s then
    rho ^ (beta * (s : ℝ)) /
      _root_.GD.N0232.N0720.N1300.d017772 rho e c n s ^ (5 / 2 : ℝ)
  else 0




def d017774
    (rho beta e c : ℝ) (n : ℕ) : ℝ :=
  ∑' s : ℤ, _root_.GD.N0232.N0720.N1300.d017773 rho beta e c n s


def d017775
    (rho beta e c : ℝ) (s : ℤ) : ℝ :=
  rho ^ (beta * (s : ℝ)) /
    (e + c * rho ^ (s : ℝ)) ^ (5 / 2 : ℝ)


theorem d017776
    {rho e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (s : ℤ) :
    Tendsto (fun n : ℕ ↦ _root_.GD.N0232.N0720.N1300.d017772 rho e c n s)
      atTop (nhds (e + c * rho ^ (s : ℝ))) := by
  have hrhoNonneg : 0 ≤ rho := hrho.le
  have hpow : Tendsto (fun n : ℕ ↦ rho ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrhoNonneg hrhoOne
  have hspos : 0 < rho ^ (s : ℝ) := Real.rpow_pos_of_pos hrho _
  have hshell : Tendsto (fun n : ℕ ↦ _root_.GD.N0232.N0720.N1300.d017771 rho n s)
      atTop (nhds 0) := by
    have heq : (fun n : ℕ ↦ _root_.GD.N0232.N0720.N1300.d017771 rho n s) =
        fun n : ℕ ↦ (rho ^ n) * rho ^ (s : ℝ) := by
      funext n
      unfold _root_.GD.N0232.N0720.N1300.d017771
      rw [Real.rpow_add hrho]
      rw [Real.rpow_natCast]
    rw [heq]
    simpa using hpow.mul_const (rho ^ (s : ℝ))
  unfold _root_.GD.N0232.N0720.N1300.d017772
  dsimp only
  convert
    ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hshell)).add
      ((tendsto_const_nhds.sub tendsto_const_nhds).mul hshell)).add
      ((tendsto_const_nhds.mul tendsto_const_nhds).mul
        (tendsto_const_nhds.sub hshell)) using 1 <;> ring_nf


theorem d017777 (s : ℤ) :
    ∀ᶠ n : ℕ in atTop, (1 : ℤ) ≤ (n : ℤ) + s := by
  rw [eventually_atTop]
  refine ⟨Int.toNat (1 - s), fun n hn ↦ ?_⟩
  have hcast : (Int.toNat (1 - s) : ℤ) ≥ 1 - s := Int.self_le_toNat _
  have hncast : (Int.toNat (1 - s) : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hn
  omega


theorem d017778
    {rho beta e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (he : 0 < e) (hc : 0 < c) (s : ℤ) :
    Tendsto (fun n : ℕ ↦ _root_.GD.N0232.N0720.N1300.d017773 rho beta e c n s)
      atTop (nhds (_root_.GD.N0232.N0720.N1300.d017775 rho beta e c s)) := by
  have hden := _root_.GD.N0232.N0720.N1300.d017776 hrho hrhoOne (e := e) (c := c) s
  have hlimden : 0 < e + c * rho ^ (s : ℝ) := by positivity
  have hpowden := hden.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 5 / 2))
  have hquot : Tendsto
      (fun n : ℕ ↦ rho ^ (beta * (s : ℝ)) /
        _root_.GD.N0232.N0720.N1300.d017772 rho e c n s ^ (5 / 2 : ℝ))
      atTop
      (nhds (rho ^ (beta * (s : ℝ)) /
        (e + c * rho ^ (s : ℝ)) ^ (5 / 2 : ℝ))) := by
    exact tendsto_const_nhds.div hpowden (by positivity)
  apply hquot.congr'
  filter_upwards [_root_.GD.N0232.N0720.N1300.d017777 s] with n hn
  simp [_root_.GD.N0232.N0720.N1300.d017773, hn]




theorem d017779
    {rho e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (he : 0 ≤ e) (heOne : e ≤ 1) (hc : 0 ≤ c)
    {n : ℕ} {s : ℤ} (hactive : (1 : ℤ) ≤ (n : ℤ) + s) :
    (1 - rho) * (e + c * rho ^ (s : ℝ)) ≤
      _root_.GD.N0232.N0720.N1300.d017772 rho e c n s := by
  have hexp : (1 : ℝ) ≤ (n : ℝ) + (s : ℝ) := by
    exact_mod_cast hactive
  have hp0 : 0 ≤ _root_.GD.N0232.N0720.N1300.d017771 rho n s := by
    unfold _root_.GD.N0232.N0720.N1300.d017771
    positivity
  have hpLe : _root_.GD.N0232.N0720.N1300.d017771 rho n s ≤ rho := by
    unfold _root_.GD.N0232.N0720.N1300.d017771
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne.le hexp
  have hp1 : _root_.GD.N0232.N0720.N1300.d017771 rho n s ≤ 1 := hpLe.trans hrhoOne.le
  have hrhos : 0 ≤ rho ^ (s : ℝ) := Real.rpow_nonneg hrho.le _
  unfold _root_.GD.N0232.N0720.N1300.d017772
  dsimp only
  nlinarith [mul_nonneg (sub_nonneg.mpr heOne) hp0,
    mul_nonneg hc hrhos, mul_nonneg (mul_nonneg hc hrhos) (sub_nonneg.mpr hp1)]


theorem d017780
    {rho beta e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (he : 0 < e) (heOne : e < 1) (hc : 0 < c)
    (n : ℕ) (s : ℤ) :
    ‖_root_.GD.N0232.N0720.N1300.d017773 rho beta e c n s‖ ≤
      (1 / (1 - rho) ^ (5 / 2 : ℝ)) *
        _root_.GD.N0232.N0720.N1300.d017775 rho beta e c s := by
  by_cases hactive : (1 : ℤ) ≤ (n : ℤ) + s
  · have hlow := _root_.GD.N0232.N0720.N1300.d017779
      hrho hrhoOne he.le heOne.le hc.le hactive
    have hleft : 0 < 1 - rho := sub_pos.mpr hrhoOne
    have hlim : 0 < e + c * rho ^ (s : ℝ) := by positivity
    have hfinite : 0 < _root_.GD.N0232.N0720.N1300.d017772 rho e c n s :=
      lt_of_lt_of_le (mul_pos hleft hlim) hlow
    have hpowLow :
        ((1 - rho) * (e + c * rho ^ (s : ℝ))) ^ (5 / 2 : ℝ) ≤
          _root_.GD.N0232.N0720.N1300.d017772 rho e c n s ^ (5 / 2 : ℝ) := by
      exact Real.rpow_le_rpow (mul_nonneg hleft.le hlim.le) hlow (by norm_num)
    have hnum : 0 ≤ rho ^ (beta * (s : ℝ)) :=
      Real.rpow_nonneg hrho.le _
    rw [_root_.GD.N0232.N0720.N1300.d017773, if_pos hactive, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hnum (Real.rpow_nonneg hfinite.le _))]
    unfold _root_.GD.N0232.N0720.N1300.d017775
    calc
      rho ^ (beta * (s : ℝ)) /
          _root_.GD.N0232.N0720.N1300.d017772 rho e c n s ^ (5 / 2 : ℝ) ≤
        rho ^ (beta * (s : ℝ)) /
          (((1 - rho) * (e + c * rho ^ (s : ℝ))) ^ (5 / 2 : ℝ)) :=
            div_le_div_of_nonneg_left hnum (by positivity) hpowLow
      _ = (1 / (1 - rho) ^ (5 / 2 : ℝ)) *
          (rho ^ (beta * (s : ℝ)) /
            (e + c * rho ^ (s : ℝ)) ^ (5 / 2 : ℝ)) := by
        rw [Real.mul_rpow hleft.le hlim.le]
        field_simp
  · rw [_root_.GD.N0232.N0720.N1300.d017773, if_neg hactive, norm_zero]
    exact mul_nonneg (by positivity)
      (div_nonneg (Real.rpow_nonneg hrho.le _)
        (Real.rpow_nonneg (by positivity) _))


theorem d017781
    {rho beta e c : ℝ} (hrho : 0 < rho) (he : 0 < e) (hc : 0 < c) (s : ℤ) :
    _root_.GD.N0232.N0720.N1300.d017775 rho beta e c s =
      (1 / c ^ (5 / 2 : ℝ)) *
        _root_.GD.N0232.N0720.N1350.d002722 rho beta (e / c) s := by
  have hc0 : c ≠ 0 := hc.ne'
  have hbase : 0 ≤ e / c + rho ^ (s : ℝ) := by positivity
  have harg : e + c * rho ^ (s : ℝ) =
      c * (e / c + rho ^ (s : ℝ)) := by field_simp
  unfold _root_.GD.N0232.N0720.N1300.d017775 _root_.GD.N0232.N0720.N1350.d002722
  rw [harg, Real.mul_rpow hc.le hbase]
  field_simp



theorem d017782
    {rho beta e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (he : 0 < e) (heOne : e < 1) (hc : 0 < c) :
    Tendsto (_root_.GD.N0232.N0720.N1300.d017774 rho beta e c)
      atTop
      (nhds ((1 / c ^ (5 / 2 : ℝ)) *
        _root_.GD.N0232.N0720.N1350.d002729 rho beta (e / c))) := by
  have hx : 0 < e / c := div_pos he hc
  have hsumLimit : Summable (_root_.GD.N0232.N0720.N1300.d017775 rho beta e c) := by
    rw [show _root_.GD.N0232.N0720.N1300.d017775 rho beta e c =
        fun s ↦ (1 / c ^ (5 / 2 : ℝ)) *
          _root_.GD.N0232.N0720.N1350.d002722 rho beta (e / c) s by
      funext s
      exact _root_.GD.N0232.N0720.N1300.d017781 hrho he hc s]
    exact (_root_.GD.N0232.N0720.N1350.d002727 hrho hrhoOne hbeta hbetaTop hx).mul_left _
  have hbound : Summable
      (fun s : ℤ ↦ (1 / (1 - rho) ^ (5 / 2 : ℝ)) *
        _root_.GD.N0232.N0720.N1300.d017775 rho beta e c s) :=
    hsumLimit.mul_left _
  have htendsto := tendsto_tsum_of_dominated_convergence hbound
    (fun s ↦ _root_.GD.N0232.N0720.N1300.d017778 hrho hrhoOne he hc s)
    (Filter.Eventually.of_forall fun n s ↦
      _root_.GD.N0232.N0720.N1300.d017780 hrho hrhoOne he heOne hc n s)
  unfold _root_.GD.N0232.N0720.N1300.d017774
  convert htendsto using 1
  rw [show _root_.GD.N0232.N0720.N1300.d017775 rho beta e c =
      fun s ↦ (1 / c ^ (5 / 2 : ℝ)) *
        _root_.GD.N0232.N0720.N1350.d002722 rho beta (e / c) s by
    funext s
    exact _root_.GD.N0232.N0720.N1300.d017781 hrho he hc s]
  rw [tsum_mul_left]
  rfl





def d017783
    (rho beta e c : ℝ) (n : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1300.d017774 rho beta (1 - e) c n /
    (_root_.GD.N0232.N0720.N1300.d017774 rho beta e c n +
      _root_.GD.N0232.N0720.N1300.d017774 rho beta (1 - e) c n)





theorem d017784
    {rho beta e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (he : 0 < e) (heOne : e < 1) (hc : 0 < c) :
    Tendsto (_root_.GD.N0232.N0720.N1300.d017783 rho beta e c)
      atTop (nhds (_root_.GD.N0232.N0720.N1350.d002732 rho beta 1 e c)) := by
  have hleftE : 0 < 1 - e := sub_pos.mpr heOne
  have hright := _root_.GD.N0232.N0720.N1300.d017782
    hrho hrhoOne hbeta hbetaTop he heOne hc
  have hleft := _root_.GD.N0232.N0720.N1300.d017782
    hrho hrhoOne hbeta hbetaTop hleftE (by linarith) hc
  have hxRight : 0 < e / c := div_pos he hc
  have hxLeft : 0 < (1 - e) / c := div_pos hleftE hc
  have hDRight := _root_.GD.N0232.N0720.N1350.d002731
    hrho hrhoOne hbeta hbetaTop hxRight
  have hDLeft := _root_.GD.N0232.N0720.N1350.d002731
    hrho hrhoOne hbeta hbetaTop hxLeft
  have hscale : 0 < 1 / c ^ (5 / 2 : ℝ) := by positivity
  have hden :
      (1 / c ^ (5 / 2 : ℝ)) * _root_.GD.N0232.N0720.N1350.d002729 rho beta (e / c) +
        (1 / c ^ (5 / 2 : ℝ)) *
          _root_.GD.N0232.N0720.N1350.d002729 rho beta ((1 - e) / c) ≠ 0 := by
    positivity
  have hquot := hleft.div (hright.add hleft) hden
  have hlimit :
      (1 / c ^ (5 / 2 : ℝ)) *
            _root_.GD.N0232.N0720.N1350.d002729 rho beta ((1 - e) / c) /
          ((1 / c ^ (5 / 2 : ℝ)) *
              _root_.GD.N0232.N0720.N1350.d002729 rho beta (e / c) +
            (1 / c ^ (5 / 2 : ℝ)) *
              _root_.GD.N0232.N0720.N1350.d002729 rho beta ((1 - e) / c)) =
        _root_.GD.N0232.N0720.N1350.d002732 rho beta 1 e c := by
    unfold _root_.GD.N0232.N0720.N1350.d002732
    dsimp only
    have hargR : e * 1 / c = e / c := by ring
    have hargL : (1 - e) * 1 / c = (1 - e) / c := by ring
    rw [hargR, hargL]
    field_simp [ne_of_gt hscale, ne_of_gt hDRight, ne_of_gt hDLeft]
  rw [hlimit] at hquot
  change Tendsto
    (fun n : ℕ ↦ _root_.GD.N0232.N0720.N1300.d017774 rho beta (1 - e) c n /
      (_root_.GD.N0232.N0720.N1300.d017774 rho beta e c n +
        _root_.GD.N0232.N0720.N1300.d017774 rho beta (1 - e) c n))
    atTop (nhds (_root_.GD.N0232.N0720.N1350.d002732 rho beta 1 e c))
  exact hquot






theorem d017785
    {rho beta e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (he : 0 < e) (heOne : e < 1) (hc : 0 < c)
    (target : ℕ → ℝ) (htarget : Tendsto target atTop (nhds e))
    (hne : _root_.GD.N0232.N0720.N1350.d002732 rho beta 1 e c ≠ e) :
    ¬ Tendsto
      (fun n ↦ _root_.GD.N0232.N0720.N1300.d017783 rho beta e c n - target n)
      atTop (nhds 0) := by
  intro hzero
  have hfinite := _root_.GD.N0232.N0720.N1300.d017784
    hrho hrhoOne hbeta hbetaTop he heOne hc
  have hdiff := hfinite.sub htarget
  have heq : _root_.GD.N0232.N0720.N1350.d002732 rho beta 1 e c - e = 0 :=
    tendsto_nhds_unique hdiff hzero
  exact hne (sub_eq_zero.mp heq)




theorem d017786
    {rho beta c : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (hbetaNe : beta ≠ 3 / 2) (hc : 0 < c)
    (target : ℕ → ℝ)
    (htarget : Tendsto target atTop (nhds (1 / (1 + rho)))) :
    ¬ Tendsto
      (fun n ↦ _root_.GD.N0232.N0720.N1300.d017783 rho beta
        (1 / (1 + rho)) c n - target n)
      atTop (nhds 0) := by
  have hden : 0 < 1 + rho := by linarith
  have he : 0 < 1 / (1 + rho) := by positivity
  have heOne : 1 / (1 + rho) < 1 := by
    rw [div_lt_one hden]
    linarith
  apply
    _root_.GD.N0232.N0720.N1300.d017785
      hrho hrhoOne hbeta hbetaTop he heOne hc target htarget
  exact _root_.GD.N0232.N0720.N1350.d002738
    hrho hrhoOne hbeta hbetaTop hbetaNe hc






theorem d017787
    {q : (ℝ × ℝ) → ℝ} (hq : HasCompactSupport q)
    (e : ℝ) {F : ℕ → ℝ} (hF : Tendsto F atTop atTop) :
    ∀ᶠ n : ℕ in atTop, q (e, F n) = 0 := by
  rcases hq.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ) with ⟨R, hR⟩
  filter_upwards [hF.eventually_gt_atTop R] with n hn
  by_contra hne
  have hsupp : (e, F n) ∈ Function.support q := by
    simpa [Function.mem_support] using hne
  have hball := hR (subset_tsupport q hsupp)
  have hdist : dist (e, F n) (0 : ℝ × ℝ) ≤ R := by
    simpa only [Metric.mem_closedBall] using hball
  rw [Prod.dist_eq] at hdist
  have hsecond : dist (F n) 0 ≤ R :=
    (le_max_right (dist e 0) (dist (F n) 0)).trans hdist
  have hFn : F n ≤ dist (F n) 0 := by
    simpa [Real.dist_eq] using (le_abs_self (F n))
  linarith


theorem d017788
    {rho c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ c / rho ^ n) atTop atTop := by
  have hinv : 1 < rho⁻¹ := (one_lt_inv₀ hrho).2 hrhoOne
  have hpow : Tendsto (fun n : ℕ ↦ rho⁻¹ ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hinv
  have hmul := Tendsto.const_mul_atTop hc hpow
  simpa only [inv_pow, div_eq_mul_inv] using hmul





def d017789
    (rho e c : ℝ) (n : ℕ) : ℝ :=
  e + (5 / 4 : ℝ) * (_root_.GD.N0232.N0720.N1416.d017756.step : ℝ) *
    _root_.GD.N0232.N0720.N1416.d017756.emitted.table.d008659 (e, c / rho ^ n)



theorem d017790
    {rho e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, _root_.GD.N0232.N0720.N1300.d017789 rho e c n = e := by
  have hzero := _root_.GD.N0232.N0720.N1300.d017787
    _root_.GD.N0232.N0720.N1416.d017756.emitted.table.d008666 e
    (_root_.GD.N0232.N0720.N1300.d017788 hrho hrhoOne hc)
  filter_upwards [hzero] with n hn
  change e + (5 / 4 : ℝ) * (_root_.GD.N0232.N0720.N1416.d017756.step : ℝ) *
      _root_.GD.N0232.N0720.N1416.d017756.emitted.table.d008659 (e, c / rho ^ n) = e
  rw [hn]
  ring



theorem d017791
    {rho e c : ℝ} (hrho : 0 < rho) (hrhoOne : rho < 1) (hc : 0 < c) :
    Tendsto (_root_.GD.N0232.N0720.N1300.d017789 rho e c) atTop (nhds e) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [_root_.GD.N0232.N0720.N1300.d017790 hrho hrhoOne hc]
    with n hn
  exact hn.symm





theorem d017792
    {rho beta c : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hbeta : 0 < beta) (hbetaTop : beta < 5 / 2)
    (hbetaNe : beta ≠ 3 / 2) (hc : 0 < c) :
    ¬ Tendsto
      (fun n ↦ _root_.GD.N0232.N0720.N1300.d017783 rho beta
          (1 / (1 + rho)) c n -
        _root_.GD.N0232.N0720.N1300.d017789 rho (1 / (1 + rho)) c n)
      atTop (nhds 0) := by
  apply _root_.GD.N0232.N0720.N1300.d017786
    hrho hrhoOne hbeta hbetaTop hbetaNe hc
  exact _root_.GD.N0232.N0720.N1300.d017791 hrho hrhoOne hc

end

end GD.N0232.N0720.N1300

#print axioms _root_.GD.N0232.N0720.N1300.d017782
#print axioms _root_.GD.N0232.N0720.N1300.d017784
#print axioms _root_.GD.N0232.N0720.N1300.d017786
#print axioms _root_.GD.N0232.N0720.N1300.d017792
