import Mathlib.Analysis.InnerProductSpace.Basic
import GD.Module0103













































open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0673

noncomputable section

open _root_.GD.N0230.N0717

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} [MeasurableSpace Θ]





theorem d001332 (x y : H) (t : ℝ) :
    ‖t • x + (1 - t) • y‖ ^ 2 =
      t * ‖x‖ ^ 2 + (1 - t) * ‖y‖ ^ 2 -
        t * (1 - t) * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
    norm_smul, norm_smul, norm_sub_sq_real, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring


def d001333 (ψ base : Θ → H) (d : H) (θ : Θ) : ℝ :=
  ‖d - ψ θ‖ ^ 2 - ‖base θ - ψ θ‖ ^ 2



theorem d001334
    (ψ base : Θ → H) (d e : H) (t : ℝ) (θ : Θ) :
    _root_.GD.N0230.N0673.d001333 ψ base (t • d + (1 - t) • e) θ =
      t * _root_.GD.N0230.N0673.d001333 ψ base d θ +
        (1 - t) * _root_.GD.N0230.N0673.d001333 ψ base e θ -
        t * (1 - t) * ‖d - e‖ ^ 2 := by
  unfold _root_.GD.N0230.N0673.d001333
  have hcomb : t • d + (1 - t) • e - ψ θ =
      t • (d - ψ θ) + (1 - t) • (e - ψ θ) := by
    have h1 : t • (d - ψ θ) + (1 - t) • (e - ψ θ) =
        t • d + (1 - t) • e - (t • ψ θ + (1 - t) • ψ θ) := by
      rw [smul_sub, smul_sub]
      abel
    have h2 : t • ψ θ + (1 - t) • ψ θ = ψ θ := by
      rw [← add_smul]
      norm_num
    rw [h1, h2]
  have hdiff : d - ψ θ - (e - ψ θ) = d - e := by abel
  rw [hcomb, _root_.GD.N0230.N0673.d001332 (d - ψ θ) (e - ψ θ) t, hdiff]
  ring


theorem d001335
    (ψ base : Θ → H) (d e : H) (θ : Θ) :
    |_root_.GD.N0230.N0673.d001333 ψ base d θ -
        _root_.GD.N0230.N0673.d001333 ψ base e θ| ≤
      (‖d - ψ θ‖ + ‖e - ψ θ‖) * ‖d - e‖ := by
  unfold _root_.GD.N0230.N0673.d001333
  have hval : ‖d - ψ θ‖ ^ 2 - ‖base θ - ψ θ‖ ^ 2 -
      (‖e - ψ θ‖ ^ 2 - ‖base θ - ψ θ‖ ^ 2) =
      ‖d - ψ θ‖ ^ 2 - ‖e - ψ θ‖ ^ 2 := by ring
  rw [hval]
  have hpolar : ‖d - ψ θ‖ ^ 2 - ‖e - ψ θ‖ ^ 2 =
      ⟪d - ψ θ - (e - ψ θ), d - ψ θ + (e - ψ θ)⟫ := by
    rw [inner_sub_left, inner_add_right, inner_add_right,
      real_inner_comm (e - ψ θ) (d - ψ θ),
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  rw [hpolar, show d - ψ θ - (e - ψ θ) = d - e from by abel]
  calc
    |⟪d - e, d - ψ θ + (e - ψ θ)⟫| ≤
        ‖d - e‖ * ‖d - ψ θ + (e - ψ θ)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖d - e‖ * (‖d - ψ θ‖ + ‖e - ψ θ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = (‖d - ψ θ‖ + ‖e - ψ θ‖) * ‖d - e‖ := by ring


theorem d001336
    (ψ base : Θ → H) (d e : H) (θ : Θ) :
    |_root_.GD.N0230.N0673.d001333 ψ base d θ -
        _root_.GD.N0230.N0673.d001333 ψ base e θ| ≤
      (‖d‖ + ‖e‖ + 2 * ‖ψ θ‖) * ‖d - e‖ := by
  refine le_trans (_root_.GD.N0230.N0673.d001335 ψ base d e θ) ?_
  have h1 : ‖d - ψ θ‖ ≤ ‖d‖ + ‖ψ θ‖ := norm_sub_le _ _
  have h2 : ‖e - ψ θ‖ ≤ ‖e‖ + ‖ψ θ‖ := norm_sub_le _ _
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)





theorem d001337
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {ψ base : Θ → H}
    (d e : H) (t : ℝ) (n : ℕ)
    (hK : μ (K n) < ⊤)
    (hd : IntegrableOn (_root_.GD.N0230.N0673.d001333 ψ base d) (K n) μ)
    (he : IntegrableOn (_root_.GD.N0230.N0673.d001333 ψ base e) (K n) μ) :
    _root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n
        (t • d + (1 - t) • e) =
      t * _root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n d +
        (1 - t) * _root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n e -
        a n * (μ (K n)).toReal * (t * (1 - t) * ‖d - e‖ ^ 2) := by
  have hconst : IntegrableOn
      (fun _θ : Θ ↦ t * (1 - t) * ‖d - e‖ ^ 2) (K n) μ :=
    integrableOn_const hK.ne enorm_ne_top
  have hpt : ∀ θ : Θ,
      _root_.GD.N0230.N0673.d001333 ψ base (t • d + (1 - t) • e) θ =
        t * _root_.GD.N0230.N0673.d001333 ψ base d θ +
          ((1 - t) * _root_.GD.N0230.N0673.d001333 ψ base e θ -
            t * (1 - t) * ‖d - e‖ ^ 2) := by
    intro θ
    rw [_root_.GD.N0230.N0673.d001334]
    ring
  have hf1 : Integrable (fun θ : Θ ↦
      t * _root_.GD.N0230.N0673.d001333 ψ base d θ) (μ.restrict (K n)) :=
    hd.const_mul t
  have hf2 : Integrable (fun θ : Θ ↦
      (1 - t) * _root_.GD.N0230.N0673.d001333 ψ base e θ) (μ.restrict (K n)) :=
    he.const_mul (1 - t)
  have hcn : Integrable (fun _θ : Θ ↦
      t * (1 - t) * ‖d - e‖ ^ 2) (μ.restrict (K n)) := hconst
  have hg2 : Integrable (fun θ : Θ ↦
      (1 - t) * _root_.GD.N0230.N0673.d001333 ψ base e θ -
        t * (1 - t) * ‖d - e‖ ^ 2) (μ.restrict (K n)) := hf2.sub hcn
  unfold _root_.GD.N0230.N0717.d001329
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add hf1 hg2,
    integral_sub hf2 hcn, integral_const_mul, integral_const_mul,
    setIntegral_const, smul_eq_mul, measureReal_def]
  ring



theorem d001338
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {ψ base : Θ → H}
    (d e : H) (n : ℕ)
    (ha : 0 ≤ a n) (hK : μ (K n) < ⊤) (hKm : MeasurableSet (K n))
    (hd : IntegrableOn (_root_.GD.N0230.N0673.d001333 ψ base d) (K n) μ)
    (he : IntegrableOn (_root_.GD.N0230.N0673.d001333 ψ base e) (K n) μ)
    (hψ : IntegrableOn (fun θ ↦ ‖ψ θ‖) (K n) μ) :
    |_root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n d -
        _root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n e| ≤
      a n * ((‖d‖ + ‖e‖) * (μ (K n)).toReal +
        2 * ∫ θ in K n, ‖ψ θ‖ ∂μ) * ‖d - e‖ := by
  have hRHSint : IntegrableOn
      (fun θ ↦ (‖d‖ + ‖e‖ + 2 * ‖ψ θ‖) * ‖d - e‖) (K n) μ :=
    (((integrableOn_const hK.ne enorm_ne_top).add
      (hψ.const_mul 2))).mul_const _
  have habs : |∫ θ in K n,
      (_root_.GD.N0230.N0673.d001333 ψ base d θ -
        _root_.GD.N0230.N0673.d001333 ψ base e θ) ∂μ| ≤
      ∫ θ in K n, (‖d‖ + ‖e‖ + 2 * ‖ψ θ‖) * ‖d - e‖ ∂μ := by
    calc
      |∫ θ in K n, (_root_.GD.N0230.N0673.d001333 ψ base d θ -
          _root_.GD.N0230.N0673.d001333 ψ base e θ) ∂μ| ≤
          ∫ θ in K n, |_root_.GD.N0230.N0673.d001333 ψ base d θ -
            _root_.GD.N0230.N0673.d001333 ψ base e θ| ∂μ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (fun θ ↦ _root_.GD.N0230.N0673.d001333 ψ base d θ -
              _root_.GD.N0230.N0673.d001333 ψ base e θ)
            (μ := μ.restrict (K n))
      _ ≤ ∫ θ in K n, (‖d‖ + ‖e‖ + 2 * ‖ψ θ‖) * ‖d - e‖ ∂μ :=
        setIntegral_mono_on (hd.sub he).abs hRHSint hKm
          (fun θ _ ↦ _root_.GD.N0230.N0673.d001336 ψ base d e θ)
  have heval : (∫ θ in K n, (‖d‖ + ‖e‖ + 2 * ‖ψ θ‖) * ‖d - e‖ ∂μ) =
      ((‖d‖ + ‖e‖) * (μ (K n)).toReal +
        2 * ∫ θ in K n, ‖ψ θ‖ ∂μ) * ‖d - e‖ := by
    have hconst1 : Integrable (fun _θ : Θ ↦ ‖d‖ + ‖e‖)
        (μ.restrict (K n)) := integrableOn_const hK.ne enorm_ne_top
    have hψ2 : Integrable (fun θ : Θ ↦ 2 * ‖ψ θ‖)
        (μ.restrict (K n)) := hψ.const_mul 2
    rw [integral_mul_const, integral_add hconst1 hψ2,
      integral_const_mul, setIntegral_const, smul_eq_mul,
      measureReal_def]
    ring
  unfold _root_.GD.N0230.N0717.d001329
  rw [← mul_sub, abs_mul, abs_of_nonneg ha,
    ← integral_sub hd he]
  calc
    a n * |∫ θ in K n,
        (_root_.GD.N0230.N0673.d001333 ψ base d θ -
          _root_.GD.N0230.N0673.d001333 ψ base e θ) ∂μ| ≤
        a n * (((‖d‖ + ‖e‖) * (μ (K n)).toReal +
          2 * ∫ θ in K n, ‖ψ θ‖ ∂μ) * ‖d - e‖) := by
      exact mul_le_mul_of_nonneg_left (heval ▸ habs) ha
    _ = a n * ((‖d‖ + ‖e‖) * (μ (K n)).toReal +
          2 * ∫ θ in K n, ‖ψ θ‖ ∂μ) * ‖d - e‖ := by ring








theorem d001339
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {ψ base : Θ → H}
    {Q : H → ℝ} {v : ℝ}
    (hK : ∀ n, μ (K n) < ⊤)
    (hint : ∀ (x : H) (n : ℕ),
      IntegrableOn (_root_.GD.N0230.N0673.d001333 ψ base x) (K n) μ)
    (hvol : Tendsto (fun n ↦ a n * (μ (K n)).toReal) atTop (nhds v))
    (hlim : ∀ x, Tendsto
      (fun n ↦ _root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n x)
      atTop (nhds (Q x)))
    (d e : H) (t : ℝ) :
    Q (t • d + (1 - t) • e) =
      t * Q d + (1 - t) * Q e - v * (t * (1 - t) * ‖d - e‖ ^ 2) := by
  have hseq : (fun n ↦ _root_.GD.N0230.N0717.d001329 μ K a
      (_root_.GD.N0230.N0673.d001333 ψ base) n (t • d + (1 - t) • e)) =
      fun n ↦ t * _root_.GD.N0230.N0717.d001329 μ K a
          (_root_.GD.N0230.N0673.d001333 ψ base) n d +
        (1 - t) * _root_.GD.N0230.N0717.d001329 μ K a
          (_root_.GD.N0230.N0673.d001333 ψ base) n e -
        a n * (μ (K n)).toReal * (t * (1 - t) * ‖d - e‖ ^ 2) :=
    funext fun n ↦ _root_.GD.N0230.N0673.d001337 d e t n
      (hK n) (hint d n) (hint e n)
  have h1 := hlim (t • d + (1 - t) • e)
  rw [hseq] at h1
  have h2 : Tendsto (fun n ↦ t * _root_.GD.N0230.N0717.d001329 μ K a
      (_root_.GD.N0230.N0673.d001333 ψ base) n d +
        (1 - t) * _root_.GD.N0230.N0717.d001329 μ K a
          (_root_.GD.N0230.N0673.d001333 ψ base) n e -
        a n * (μ (K n)).toReal * (t * (1 - t) * ‖d - e‖ ^ 2))
      atTop (nhds (t * Q d + (1 - t) * Q e -
        v * (t * (1 - t) * ‖d - e‖ ^ 2))) :=
    (((hlim d).const_mul t).add
      ((hlim e).const_mul (1 - t))).sub (hvol.mul_const _)
  exact tendsto_nhds_unique h1 h2




theorem d001340
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {ψ base : Θ → H}
    {Q : H → ℝ} {v : ℝ}
    (hK : ∀ n, μ (K n) < ⊤)
    (hint : ∀ (x : H) (n : ℕ),
      IntegrableOn (_root_.GD.N0230.N0673.d001333 ψ base x) (K n) μ)
    (hvol : Tendsto (fun n ↦ a n * (μ (K n)).toReal) atTop (nhds v))
    (hlim : ∀ x, Tendsto
      (fun n ↦ _root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n x)
      atTop (nhds (Q x)))
    (d e : H) (t : ℝ) :
    Q (t • d + (1 - t) • e) - v * ‖t • d + (1 - t) • e‖ ^ 2 =
      t * (Q d - v * ‖d‖ ^ 2) + (1 - t) * (Q e - v * ‖e‖ ^ 2) := by
  rw [_root_.GD.N0230.N0673.d001339 hK hint hvol hlim d e t,
    _root_.GD.N0230.N0673.d001332]
  ring




theorem d001341
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {ψ base : Θ → H}
    {Q : H → ℝ}
    (hK : ∀ n, μ (K n) < ⊤)
    (hint : ∀ (x : H) (n : ℕ),
      IntegrableOn (_root_.GD.N0230.N0673.d001333 ψ base x) (K n) μ)
    (hvol : Tendsto (fun n ↦ a n * (μ (K n)).toReal) atTop (nhds 0))
    (hlim : ∀ x, Tendsto
      (fun n ↦ _root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n x)
      atTop (nhds (Q x)))
    (d e : H) (t : ℝ) :
    Q (t • d + (1 - t) • e) = t * Q d + (1 - t) * Q e := by
  have h := _root_.GD.N0230.N0673.d001339 hK hint hvol
    hlim d e t
  simpa using h





theorem d001342
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {ψ base : Θ → H}
    {Q : H → ℝ} {v : ℝ}
    (hK : ∀ n, μ (K n) < ⊤)
    (hint : ∀ (x : H) (n : ℕ),
      IntegrableOn (_root_.GD.N0230.N0673.d001333 ψ base x) (K n) μ)
    (hvol : Tendsto (fun n ↦ a n * (μ (K n)).toReal) atTop (nhds v))
    (hlim : ∀ x, Tendsto
      (fun n ↦ _root_.GD.N0230.N0717.d001329 μ K a (_root_.GD.N0230.N0673.d001333 ψ base) n x)
      atTop (nhds (Q x)))
    (hv : 0 ≤ v) (β : ℝ) :
    Convex ℝ {x : H | Q x ≤ β} := by
  intro x hx y hy s r hs hr hsr
  have hr' : r = 1 - s := by linarith
  subst hr'
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hid := _root_.GD.N0230.N0673.d001339 hK hint hvol
    hlim x y s
  have hquad : 0 ≤ v * (s * (1 - s) * ‖x - y‖ ^ 2) :=
    mul_nonneg hv (mul_nonneg (mul_nonneg hs (by linarith))
      (sq_nonneg _))
  have hxs := mul_le_mul_of_nonneg_left hx hs
  have hys := mul_le_mul_of_nonneg_left hy
    (by linarith : (0 : ℝ) ≤ 1 - s)
  calc
    Q (s • x + (1 - s) • y) =
        s * Q x + (1 - s) * Q y -
          v * (s * (1 - s) * ‖x - y‖ ^ 2) := hid
    _ ≤ s * β + (1 - s) * β := by linarith
    _ = β := by ring

end

end N0673
end N0230
end GD

#print axioms _root_.GD.N0230.N0673.d001332
#print axioms _root_.GD.N0230.N0673.d001334
#print axioms _root_.GD.N0230.N0673.d001337
#print axioms _root_.GD.N0230.N0673.d001338
#print axioms _root_.GD.N0230.N0673.d001339
#print axioms _root_.GD.N0230.N0673.d001341
#print axioms _root_.GD.N0230.N0673.d001342
