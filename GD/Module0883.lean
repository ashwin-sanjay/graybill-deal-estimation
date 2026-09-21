import GD.Module0882
import GD.Module0855
import GD.Module0856
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv




















open Filter

namespace GD
namespace N0232
namespace N0720
namespace N1431

noncomputable section

open _root_.GD.N0232.N0720.N1428


def d013671 (alpha beta : ℝ) : ℝ :=
  (alpha / beta) ^ alpha * Real.Gamma (alpha + beta) *
      Real.Gamma (2 - alpha) / Real.Gamma beta


def d013672 (alpha beta : ℝ) : ℝ :=
  (alpha ^ 2 + alpha * beta + 2 * beta) /
    (beta * (alpha - 1) * (alpha - 2))




theorem d013673 {beta : ℝ} (hbeta : 0 < beta) :
    _root_.GD.N0232.N0720.N1431.d013671 1 beta = 1 := by
  have hgammaBeta : Real.Gamma beta ≠ 0 :=
    (Real.Gamma_pos_of_pos hbeta).ne'
  have hstep := Real.Gamma_add_one (s := beta) hbeta.ne'
  unfold _root_.GD.N0232.N0720.N1431.d013671
  norm_num only [one_div, Real.rpow_one, one_add_one_eq_two, sub_self,
    Real.Gamma_one]
  rw [show 1 + beta = beta + 1 by ring, hstep]
  field_simp [hbeta.ne', hgammaBeta]



theorem d013674
    {beta : ℝ} (hbeta : 0 < beta)
    {alpha : ℕ → ℝ} (halpha : Tendsto alpha atTop (nhds 2))
    (halphaTwo : ∀ n, 2 < alpha n) :
    Tendsto
      (fun n => (alpha n - 2) * _root_.GD.N0232.N0720.N1431.d013672 (alpha n) beta)
      atTop (nhds (_root_.GD.N0232.N0720.N1428.d013133 beta)) := by
  let reduced : ℝ → ℝ := fun a =>
    (a ^ 2 + a * beta + 2 * beta) / (beta * (a - 1))
  have hreduced : Tendsto (fun n => reduced (alpha n)) atTop (nhds (reduced 2)) := by
    have hcontinuous : ContinuousAt reduced 2 := by
      unfold reduced
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num [hbeta.ne']
    exact hcontinuous.tendsto.comp halpha
  have heq : ∀ n,
      (alpha n - 2) * _root_.GD.N0232.N0720.N1431.d013672 (alpha n) beta =
        reduced (alpha n) := by
    intro n
    unfold _root_.GD.N0232.N0720.N1431.d013672 reduced
    field_simp [hbeta.ne', (sub_pos.mpr (halphaTwo n)).ne']
  rw [show reduced 2 = _root_.GD.N0232.N0720.N1428.d013133 beta by
    unfold reduced _root_.GD.N0232.N0720.N1428.d013133
    field_simp [hbeta.ne']
    ring] at hreduced
  exact hreduced.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)



theorem d013675
    {beta : ℝ} (hbeta : 0 < beta)
    {alpha : ℕ → ℝ} (halpha : Tendsto alpha atTop (nhds 2))
    (halpha0 : ∀ n, 0 < alpha n) (halphaTwo : ∀ n, alpha n < 2) :
    Tendsto
      (fun n => (2 - alpha n) * _root_.GD.N0232.N0720.N1431.d013671 (alpha n) beta)
      atTop (nhds (_root_.GD.N0232.N0720.N1428.d013133 beta)) := by
  let reduced : ℝ → ℝ := fun a =>
    (a / beta) ^ a * Real.Gamma (a + beta) * Real.Gamma (3 - a) /
      Real.Gamma beta
  have hbase : Tendsto (fun n => alpha n / beta) atTop (nhds (2 / beta)) :=
    halpha.div_const beta
  have hbase0 : ∀ n, 0 < alpha n / beta := fun n => div_pos (halpha0 n) hbeta
  have hlimitBase0 : 0 < (2 : ℝ) / beta := div_pos (by norm_num) hbeta
  have hpow : Tendsto (fun n => (alpha n / beta) ^ alpha n)
      atTop (nhds ((2 / beta) ^ (2 : ℝ))) := by
    have hlog : Tendsto (fun n => Real.log (alpha n / beta))
        atTop (nhds (Real.log (2 / beta))) :=
      (Real.continuousAt_log hlimitBase0.ne').tendsto.comp hbase
    have hexponent := hlog.mul halpha
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp hexponent
    change Tendsto
        (fun n => Real.exp (Real.log (alpha n / beta) * alpha n))
        atTop (nhds (Real.exp (Real.log (2 / beta) * 2))) at hexp
    have hfun : (fun n => (alpha n / beta) ^ alpha n) =
        (fun n => Real.exp (Real.log (alpha n / beta) * alpha n)) := by
      funext n
      rw [Real.rpow_def_of_pos (hbase0 n)]
    rw [hfun, Real.rpow_def_of_pos hlimitBase0]
    exact hexp
  have hgammaSum : Tendsto (fun n => Real.Gamma (alpha n + beta))
      atTop (nhds (Real.Gamma (2 + beta))) := by
    have harg : Tendsto (fun n => alpha n + beta) atTop (nhds (2 + beta)) :=
      halpha.add_const beta
    exact ((Real.differentiableAt_Gamma (s := 2 + beta) (by
      intro m
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)).continuousAt.tendsto).comp harg
  have hgammaWall : Tendsto (fun n => Real.Gamma (3 - alpha n))
      atTop (nhds (Real.Gamma 1)) := by
    have harg : Tendsto (fun n => 3 - alpha n) atTop (nhds 1) := by
      have hconst : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) :=
        tendsto_const_nhds
      simpa only [show (3 : ℝ) - 2 = 1 by norm_num] using
        (hconst.sub halpha)
    exact ((Real.differentiableAt_Gamma (s := 1) (by
      intro m
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)).continuousAt.tendsto).comp harg
  have hreduced : Tendsto (fun n => reduced (alpha n)) atTop (nhds (reduced 2)) := by
    unfold reduced
    simpa only [show (3 : ℝ) - 2 = 1 by norm_num] using
      ((hpow.mul hgammaSum).mul hgammaWall).div_const (Real.Gamma beta)
  have heq : ∀ n,
      (2 - alpha n) * _root_.GD.N0232.N0720.N1431.d013671 (alpha n) beta =
        reduced (alpha n) := by
    intro n
    have hwall : 2 - alpha n ≠ 0 := (sub_pos.mpr (halphaTwo n)).ne'
    have hstep := Real.Gamma_add_one (s := 2 - alpha n) hwall
    unfold _root_.GD.N0232.N0720.N1431.d013671 reduced
    rw [show 2 - alpha n + 1 = 3 - alpha n by ring] at hstep
    rw [hstep]
    ring
  have hgammaBeta : Real.Gamma beta ≠ 0 :=
    (Real.Gamma_pos_of_pos hbeta).ne'
  have hvalue : reduced 2 = _root_.GD.N0232.N0720.N1428.d013133 beta := by
    unfold reduced _root_.GD.N0232.N0720.N1428.d013133
    norm_num only [sub_self, Nat.cast_ofNat]
    rw [Real.Gamma_one]
    rw [show Real.Gamma (2 + beta) = (1 + beta) * beta * Real.Gamma beta by
      have h1 := Real.Gamma_add_one (s := beta) hbeta.ne'
      have h2 := Real.Gamma_add_one (s := beta + 1) (by linarith)
      rw [show beta + 1 + 1 = 2 + beta by ring] at h2
      rw [h2, h1]
      ring]
    rw [Real.rpow_two]
    field_simp [hbeta.ne', hgammaBeta]
    ring
  rw [hvalue] at hreduced
  exact hreduced.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)

end

end N1431
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1431.d013674
#print axioms _root_.GD.N0232.N0720.N1431.d013675
#print axioms _root_.GD.N0232.N0720.N1431.d013673
