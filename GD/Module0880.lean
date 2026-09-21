import GD.Module0859



















open Filter MeasureTheory ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1438

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1421
open _root_.GD.N0232.N0720.N1426
open _root_.GD.N0232.N0720.N1428





def d013596 : ℝ ≃ᵐ ℝ where
  toFun u := 1 - u
  invFun u := 1 - u
  left_inv u := by ring
  right_inv u := by ring
  measurable_toFun := measurable_const.sub measurable_id
  measurable_invFun := measurable_const.sub measurable_id

@[simp]
theorem d013597 (u : ℝ) :
    _root_.GD.N0232.N0720.N1438.d013596 u = 1 - u := rfl


theorem d013598 (alpha beta : ℝ) :
    ProbabilityTheory.beta alpha beta =
      ProbabilityTheory.beta beta alpha := by
  unfold ProbabilityTheory.beta
  rw [mul_comm, add_comm]


theorem d013599 (alpha beta u : ℝ) :
    betaPDFReal alpha beta (1 - u) = betaPDFReal beta alpha u := by
  by_cases hu : 0 < u ∧ u < 1
  · have hreflect : 0 < 1 - u ∧ 1 - u < 1 := by
      constructor <;> linarith [hu.1, hu.2]
    rw [betaPDFReal, if_pos hreflect, betaPDFReal, if_pos hu]
    rw [_root_.GD.N0232.N0720.N1438.d013598 alpha beta]
    have hone : 1 - (1 - u) = u := by ring
    rw [hone]
    ring
  · have hreflect : ¬(0 < 1 - u ∧ 1 - u < 1) := by
      intro h
      apply hu
      constructor <;> linarith [h.1, h.2]
    rw [betaPDFReal, if_neg hreflect, betaPDFReal, if_neg hu]





theorem d013600
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (g : ℝ → ℝ) :
    (∫ u, g (1 - u) ∂betaMeasure alpha beta) =
      ∫ u, g u ∂betaMeasure beta alpha := by
  rw [_root_.GD.N0235.d004041
      halpha hbeta,
    _root_.GD.N0235.d004041
      hbeta halpha]
  have hpres : MeasurePreserving (fun u : ℝ => 1 - u) volume volume :=
    volume.measurePreserving_sub_left 1
  have hemb : MeasurableEmbedding (fun u : ℝ => 1 - u) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      ((measurableEmbedding_addLeft (1 : ℝ)).comp measurableEmbedding_neg)
  have hchange := hpres.integral_comp hemb
    (fun u : ℝ => betaPDFReal alpha beta u * g (1 - u))
  calc
    (∫ u, betaPDFReal alpha beta u * g (1 - u)) =
        ∫ u, betaPDFReal alpha beta (1 - u) * g u := by
      convert hchange.symm using 1
      simp
    _ = ∫ u, betaPDFReal beta alpha u * g u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [_root_.GD.N0232.N0720.N1438.d013599]






theorem d013601
    (alpha beta p u : ℝ) :
    p ^ 2 * (1 - p) ^ 2 *
          (_root_.GD.N0232.N0720.N1091.d012765 alpha beta u) ^ 2 /
            (_root_.GD.N0232.N0720.N1091.d012764 alpha beta p u) ^ 2 =
      (1 - p) ^ 2 * (1 - (1 - p)) ^ 2 *
          (_root_.GD.N0232.N0720.N1091.d012765 beta alpha (1 - u)) ^ 2 /
            (_root_.GD.N0232.N0720.N1091.d012764 beta alpha (1 - p) (1 - u)) ^ 2 := by
  have hscore : _root_.GD.N0232.N0720.N1091.d012765 beta alpha (1 - u) =
      -_root_.GD.N0232.N0720.N1091.d012765 alpha beta u := by
    unfold _root_.GD.N0232.N0720.N1091.d012765
    ring
  have hden : _root_.GD.N0232.N0720.N1091.d012764 beta alpha (1 - p) (1 - u) =
      _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u := by
    unfold _root_.GD.N0232.N0720.N1091.d012764
    ring
  rw [hscore, hden]
  ring


theorem d013602
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (p : ℝ) :
    _root_.GD.N0232.N0720.N1091.d012791 alpha beta p =
      _root_.GD.N0232.N0720.N1091.d012791 beta alpha (1 - p) := by
  unfold _root_.GD.N0232.N0720.N1091.d012791
  calc
    (∫ u,
        p ^ 2 * (1 - p) ^ 2 *
          (_root_.GD.N0232.N0720.N1091.d012765 alpha beta u) ^ 2 /
            (_root_.GD.N0232.N0720.N1091.d012764 alpha beta p u) ^ 2
        ∂betaMeasure alpha beta) =
        ∫ u,
          ((1 - p) ^ 2 * (1 - (1 - p)) ^ 2 *
            (_root_.GD.N0232.N0720.N1091.d012765 beta alpha (1 - u)) ^ 2 /
              (_root_.GD.N0232.N0720.N1091.d012764 beta alpha (1 - p) (1 - u)) ^ 2)
          ∂betaMeasure alpha beta := by
      apply integral_congr_ae
      filter_upwards with u
      exact _root_.GD.N0232.N0720.N1438.d013601 alpha beta p u
    _ = ∫ u,
          ((1 - p) ^ 2 * (1 - (1 - p)) ^ 2 *
            (_root_.GD.N0232.N0720.N1091.d012765 beta alpha u) ^ 2 /
              (_root_.GD.N0232.N0720.N1091.d012764 beta alpha (1 - p) u) ^ 2)
          ∂betaMeasure beta alpha := by
      exact _root_.GD.N0232.N0720.N1438.d013600 halpha hbeta
        (fun u =>
          (1 - p) ^ 2 * (1 - (1 - p)) ^ 2 *
            (_root_.GD.N0232.N0720.N1091.d012765 beta alpha u) ^ 2 /
              (_root_.GD.N0232.N0720.N1091.d012764 beta alpha (1 - p) u) ^ 2)




theorem d013603
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 alpha beta p =
      _root_.GD.N0232.N0720.N1091.d012790 beta alpha (1 - p) := by
  have hq0 : 0 < 1 - p := sub_pos.mpr hp1
  have hq1 : 1 - p < 1 := by linarith
  rw [_root_.GD.N0232.N0720.N1091.d012800 halpha hbeta hp0 hp1,
    _root_.GD.N0232.N0720.N1091.d012800 hbeta halpha hq0 hq1]
  exact _root_.GD.N0232.N0720.N1438.d013602 halpha hbeta p






theorem d013604
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 2 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 1))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n) / (1 - p n) ^ 2)
      atTop
      (nhds ((beta ^ 2 + beta * alpha + 2 * alpha) /
        (alpha * (beta - 1) * (beta - 2)))) := by
  let q : ℕ → ℝ := fun n => 1 - p n
  have hq : Tendsto q atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hp
  have hq0 : ∀ n, 0 < q n := fun n => sub_pos.mpr (hp1 n)
  have hq1 : ∀ n, q n < 1 := by
    intro n
    dsimp [q]
    linarith [hp0 n]
  have hleft := _root_.GD.N0232.N0720.N1421.d013121
    hbeta halpha hq hq0 hq1
  convert hleft using 1
  funext n
  rw [_root_.GD.N0232.N0720.N1438.d013603 halpha (lt_trans (by norm_num) hbeta)
    (hp0 n) (hp1 n)]




theorem d013605
    {alpha : ℝ} (halpha : 0 < alpha)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 1))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1091.d012790 alpha 2 (p n) /
        ((1 - p n) ^ 2 * Real.log (1 / (1 - p n))))
      atTop (nhds (_root_.GD.N0232.N0720.N1428.d013133 alpha)) := by
  let q : ℕ → ℝ := fun n => 1 - p n
  have hq : Tendsto q atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hp
  have hq0 : ∀ n, 0 < q n := fun n => sub_pos.mpr (hp1 n)
  have hq1 : ∀ n, q n < 1 := by
    intro n
    dsimp [q]
    linarith [hp0 n]
  have hleft := _root_.GD.N0232.N0720.N1426.d013206
    halpha hq hq0 hq1
  convert hleft using 1
  funext n
  rw [_root_.GD.N0232.N0720.N1438.d013603 halpha (by norm_num)
    (hp0 n) (hp1 n)]

end

end N1438
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1438.d013600
#print axioms _root_.GD.N0232.N0720.N1438.d013603
#print axioms _root_.GD.N0232.N0720.N1438.d013604
#print axioms _root_.GD.N0232.N0720.N1438.d013605
