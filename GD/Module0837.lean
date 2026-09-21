import GD.Module0274
import GD.Module0640
import GD.Module0836
import GD.Module0612
import GD.Module0409



























open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1091

noncomputable section


def d012754 (alpha beta : ℝ) : Measure (ℝ × ℝ) :=
  (gammaMeasure alpha alpha).prod (gammaMeasure beta beta)


def d012755 (alpha beta : ℝ) : Measure (ℝ × ℝ) :=
  (gammaMeasure alpha 1).prod (gammaMeasure beta 1)


def d012756 (alpha beta : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (alpha * q.1, beta * q.2)


def d012757 (q : ℝ × ℝ) : ℝ :=
  q.1 / (q.1 + q.2)


def d012758 (alpha beta : ℝ) : Prop :=
  (_root_.GD.N0232.N0720.N1091.d012755 alpha beta).map _root_.GD.N0232.N0720.N1091.d012757 = betaMeasure alpha beta


def d012759 (p : ℝ) (q : ℝ × ℝ) : ℝ :=
  p * q.2 / ((1 - p) * q.1 + p * q.2)



def d012760 (alpha beta : ℝ) (q : ℝ × ℝ) : ℝ :=
  alpha * q.1 / (alpha * q.1 + beta * q.2)



def d012761 (alpha beta : ℝ) : Prop :=
  (_root_.GD.N0232.N0720.N1091.d012754 alpha beta).map (_root_.GD.N0232.N0720.N1091.d012760 alpha beta) =
    betaMeasure alpha beta


def d012762 (alpha beta p : ℝ) : ℝ :=
  alpha * p / (beta * (1 - p))


def d012763 (lambda u : ℝ) : ℝ :=
  lambda * (1 - u) / (u + lambda * (1 - u))


def d012764 (alpha beta p u : ℝ) : ℝ :=
  beta * (1 - p) * u + alpha * p * (1 - u)


def d012765 (alpha beta u : ℝ) : ℝ :=
  alpha - (alpha + beta) * u


def d012766 (alpha beta p t : ℝ) : ℝ :=
  alpha + (beta - (alpha + beta) * p) * t

theorem d012767 (p : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1091.d012759 p) := by
  unfold _root_.GD.N0232.N0720.N1091.d012759
  fun_prop

theorem d012768 (alpha beta : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1091.d012756 alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1091.d012756
  fun_prop

theorem d012769 : Measurable _root_.GD.N0232.N0720.N1091.d012757 := by
  unfold _root_.GD.N0232.N0720.N1091.d012757
  fun_prop

theorem d012770 (alpha beta : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1091.d012760 alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1091.d012760
  fun_prop

theorem d012771 (lambda : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1091.d012763 lambda) := by
  unfold _root_.GD.N0232.N0720.N1091.d012763
  fun_prop


theorem d012772
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Integrable (betaPDFReal alpha beta) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (stronglyMeasurable_betaPDFReal alpha beta).aestronglyMeasurable
    (ae_of_all volume fun u =>
      _root_.GD.N0235.d004040 halpha hbeta u)).1
  change (∫⁻ u, betaPDF alpha beta u) ≠ ⊤
  rw [lintegral_betaPDF_eq_one halpha hbeta]
  exact ENNReal.one_ne_top



theorem d012773
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [_root_.GD.N0125.d008871 ha hr]
  unfold _root_.GD.N0125.d008870
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ioi)


theorem d012774
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    ∀ᵐ q ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta, 0 < q.1 ∧ 0 < q.2 := by
  unfold _root_.GD.N0232.N0720.N1091.d012754
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd))).2
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012773 halpha halpha] with x hx
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012773 hbeta hbeta] with y hy
  exact ⟨hx, hy⟩



theorem d012775
    {alpha beta x y : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hx : 0 < x) (hy : 0 < y) :
    0 < alpha * x + beta * y := by
  positivity


theorem d012776
    {alpha beta : ℝ} {q : ℝ × ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hx : 0 < q.1) (hy : 0 < q.2) :
    _root_.GD.N0232.N0720.N1091.d012760 alpha beta q ∈ Set.Ioo (0 : ℝ) 1 := by
  have hden : 0 < alpha * q.1 + beta * q.2 :=
    _root_.GD.N0232.N0720.N1091.d012775 halpha hbeta hx hy
  constructor
  · exact div_pos (mul_pos halpha hx) hden
  · unfold _root_.GD.N0232.N0720.N1091.d012760
    rw [div_lt_one hden]
    nlinarith [mul_pos hbeta hy]



theorem d012777
    (alpha beta : ℝ) (q : ℝ × ℝ) :
    _root_.GD.N0232.N0720.N1091.d012760 alpha beta q =
      _root_.GD.N0232.N0720.N1091.d012757 (_root_.GD.N0232.N0720.N1091.d012756 alpha beta q) := by
  rfl


theorem d012778
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < _root_.GD.N0232.N0720.N1091.d012762 alpha beta p := by
  unfold _root_.GD.N0232.N0720.N1091.d012762
  positivity


theorem d012779
    {lambda u : ℝ} (hlambda : 0 < lambda)
    (hu0 : 0 < u) (hu1 : u < 1) :
    0 < u + lambda * (1 - u) := by
  positivity


theorem d012780
    {lambda u : ℝ} (hlambda : 0 < lambda)
    (hu0 : 0 < u) (hu1 : u < 1) :
    _root_.GD.N0232.N0720.N1091.d012763 lambda u ∈ Set.Ioo (0 : ℝ) 1 := by
  have hden := _root_.GD.N0232.N0720.N1091.d012779 hlambda hu0 hu1
  constructor
  · unfold _root_.GD.N0232.N0720.N1091.d012763
    exact div_pos (mul_pos hlambda (sub_pos.mpr hu1)) hden
  · unfold _root_.GD.N0232.N0720.N1091.d012763
    rw [div_lt_one hden]
    linarith



theorem d012781
    {alpha beta p : ℝ} {q : ℝ × ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < q.1) (hy : 0 < q.2) :
    _root_.GD.N0232.N0720.N1091.d012759 p q =
      _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p)
        (_root_.GD.N0232.N0720.N1091.d012760 alpha beta q) := by
  have hab : alpha * q.1 + beta * q.2 ≠ 0 :=
    (_root_.GD.N0232.N0720.N1091.d012775 halpha hbeta hx hy).ne'
  have hbeta0 : beta ≠ 0 := hbeta.ne'
  have h1p : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
  have hraw : (1 - p) * q.1 + p * q.2 ≠ 0 := by
    positivity
  have hcomp :
      1 - alpha * q.1 / (alpha * q.1 + beta * q.2) =
        beta * q.2 / (alpha * q.1 + beta * q.2) := by
    field_simp [hab]
    ring
  unfold _root_.GD.N0232.N0720.N1091.d012759 _root_.GD.N0232.N0720.N1091.d012763 _root_.GD.N0232.N0720.N1091.d012762 _root_.GD.N0232.N0720.N1091.d012760
  rw [hcomp]
  field_simp [hab, hbeta0, h1p, hraw]




theorem d012782
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᵐ q ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta,
      _root_.GD.N0232.N0720.N1091.d012759 p q =
        _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p)
          (_root_.GD.N0232.N0720.N1091.d012760 alpha beta q) := by
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012774 halpha hbeta]
    with q hq
  exact _root_.GD.N0232.N0720.N1091.d012781 halpha hbeta hp0 hp1 hq.1 hq.2



theorem d012783
    {alpha beta p u : ℝ}
    (hbeta : beta ≠ 0) (hp1 : p ≠ 1)
    (hden : _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u ≠ 0) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p =
      p * (1 - p) * _root_.GD.N0232.N0720.N1091.d012765 alpha beta u /
        _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u := by
  have hscale : beta * (1 - p) ≠ 0 :=
    mul_ne_zero hbeta (sub_ne_zero.mpr hp1.symm)
  have hinner :
      u + alpha * p / (beta * (1 - p)) * (1 - u) ≠ 0 := by
    intro hz
    apply hden
    unfold _root_.GD.N0232.N0720.N1091.d012764
    field_simp [hscale] at hz
    linarith
  have hweight :
      _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u =
        alpha * p * (1 - u) /
          _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u := by
    unfold _root_.GD.N0232.N0720.N1091.d012763 _root_.GD.N0232.N0720.N1091.d012762
    apply (div_eq_div_iff hinner hden).2
    unfold _root_.GD.N0232.N0720.N1091.d012764
    field_simp [hscale]
  rw [hweight]
  rw [div_sub' hden]
  unfold _root_.GD.N0232.N0720.N1091.d012765 _root_.GD.N0232.N0720.N1091.d012764
  congr 1
  ring


theorem d012784
    {alpha beta p u : ℝ}
    (hbeta : beta ≠ 0) (hp1 : p ≠ 1)
    (hden : _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u ≠ 0) :
    (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2 =
      p ^ 2 * (1 - p) ^ 2 *
        (_root_.GD.N0232.N0720.N1091.d012765 alpha beta u) ^ 2 /
          (_root_.GD.N0232.N0720.N1091.d012764 alpha beta p u) ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1091.d012783 hbeta hp1 hden]
  field_simp [hden]



theorem d012785
    {alpha beta p u : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu0 : 0 < u) (hu1 : u < 1) :
    0 < _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u := by
  unfold _root_.GD.N0232.N0720.N1091.d012764
  positivity



theorem d012786
    (alpha beta p t : ℝ) :
    _root_.GD.N0232.N0720.N1091.d012764 alpha beta p (p * t) =
      p * _root_.GD.N0232.N0720.N1091.d012766 alpha beta p t := by
  unfold _root_.GD.N0232.N0720.N1091.d012764 _root_.GD.N0232.N0720.N1091.d012766
  ring


theorem d012787
    (alpha beta p t : ℝ) :
    _root_.GD.N0232.N0720.N1091.d012765 alpha beta (p * t) =
      alpha - (alpha + beta) * p * t := by
  unfold _root_.GD.N0232.N0720.N1091.d012765
  ring




theorem d012788
    {alpha beta p t : ℝ}
    (hbeta : beta ≠ 0) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hlayer : _root_.GD.N0232.N0720.N1091.d012766 alpha beta p t ≠ 0) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) (p * t) - p =
      (1 - p) * (alpha - (alpha + beta) * p * t) /
        _root_.GD.N0232.N0720.N1091.d012766 alpha beta p t := by
  rw [_root_.GD.N0232.N0720.N1091.d012783 hbeta hp1]
  · rw [_root_.GD.N0232.N0720.N1091.d012786, _root_.GD.N0232.N0720.N1091.d012787]
    field_simp [hp0, hlayer]
  · rw [_root_.GD.N0232.N0720.N1091.d012786]
    exact mul_ne_zero hp0 hlayer


theorem d012789
    {alpha beta p t : ℝ}
    (hbeta : beta ≠ 0) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hlayer : _root_.GD.N0232.N0720.N1091.d012766 alpha beta p t ≠ 0) :
    (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) (p * t) - p) ^ 2 =
      (1 - p) ^ 2 *
        (alpha - (alpha + beta) * p * t) ^ 2 /
          (_root_.GD.N0232.N0720.N1091.d012766 alpha beta p t) ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1091.d012788 hbeta hp0 hp1 hlayer]
  field_simp [hlayer]



def d012790 (alpha beta p : ℝ) : ℝ :=
  ∫ u, (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2
    ∂betaMeasure alpha beta


def d012791 (alpha beta p : ℝ) : ℝ :=
  ∫ u,
    p ^ 2 * (1 - p) ^ 2 *
      (_root_.GD.N0232.N0720.N1091.d012765 alpha beta u) ^ 2 /
        (_root_.GD.N0232.N0720.N1091.d012764 alpha beta p u) ^ 2
    ∂betaMeasure alpha beta



theorem d012792
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (_root_.GD.N0232.N0720.N1091.d012754 alpha beta).map (_root_.GD.N0232.N0720.N1091.d012756 alpha beta) =
      _root_.GD.N0232.N0720.N1091.d012755 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1091.d012754 _root_.GD.N0232.N0720.N1091.d012755 _root_.GD.N0232.N0720.N1091.d012756
  change Measure.map (Prod.map (alpha * ·) (beta * ·))
      ((gammaMeasure alpha alpha).prod (gammaMeasure beta beta)) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [_root_.GD.N0232.N0719.N0954.d009354
      halpha halpha halpha,
    _root_.GD.N0232.N0719.N0954.d009354
      hbeta hbeta hbeta]
  simp only [div_self halpha.ne', div_self hbeta.ne']



theorem d012793
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hunit : _root_.GD.N0232.N0720.N1091.d012758 alpha beta) :
    _root_.GD.N0232.N0720.N1091.d012761 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1091.d012761
  have hfun : _root_.GD.N0232.N0720.N1091.d012760 alpha beta =
      _root_.GD.N0232.N0720.N1091.d012757 ∘ _root_.GD.N0232.N0720.N1091.d012756 alpha beta := by
    funext q
    exact _root_.GD.N0232.N0720.N1091.d012777 alpha beta q
  rw [hfun]
  rw [← Measure.map_map _root_.GD.N0232.N0720.N1091.d012769
    (_root_.GD.N0232.N0720.N1091.d012768 alpha beta)]
  rw [_root_.GD.N0232.N0720.N1091.d012792 halpha hbeta]
  exact hunit



def d012794 (p : _root_.GD.N0124.d006387) : ℝ × ℝ :=
  (p.1, p.2.1)

theorem d012795 : Measurable _root_.GD.N0232.N0720.N1091.d012794 := by
  unfold _root_.GD.N0232.N0720.N1091.d012794
  fun_prop



theorem d012796
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (_root_.GD.N0125.d008852 alpha beta).map _root_.GD.N0232.N0720.N1091.d012794 =
      _root_.GD.N0232.N0720.N1091.d012754 alpha beta := by
  letI : IsProbabilityMeasure (gammaMeasure alpha alpha) :=
    isProbabilityMeasure_gammaMeasure halpha halpha
  letI : IsProbabilityMeasure (gammaMeasure beta beta) :=
    isProbabilityMeasure_gammaMeasure hbeta hbeta
  letI : IsProbabilityMeasure _root_.GD.N0125.d008851 := by
    unfold _root_.GD.N0125.d008851
    exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  unfold _root_.GD.N0125.d008852 _root_.GD.N0232.N0720.N1091.d012754 _root_.GD.N0232.N0720.N1091.d012794
  change Measure.map (Prod.map id Prod.fst)
      ((gammaMeasure alpha alpha).prod
        ((gammaMeasure beta beta).prod _root_.GD.N0125.d008851)) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_fst]
  simp




theorem d012797
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (g : ℝ → ℝ) (hg : Measurable g) :
    _root_.GD.N0120.d008809 alpha beta p
        (fun z : ℝ × ℝ => g z.1) =
      ∫ q, g (_root_.GD.N0232.N0720.N1091.d012759 p q) ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta := by
  rw [_root_.GD.N0125.d008860
    halpha hbeta]
  rw [← _root_.GD.N0125.d008873 halpha hbeta]
  calc
    (∫ s : _root_.GD.N0124.d006387,
        g (_root_.GD.N0124.d006391 p s).1
          ∂_root_.GD.N0125.d008852 alpha beta) =
        ∫ s : _root_.GD.N0124.d006387,
          g (_root_.GD.N0232.N0720.N1091.d012759 p (_root_.GD.N0232.N0720.N1091.d012794 s))
            ∂_root_.GD.N0125.d008852 alpha beta := by
      apply integral_congr_ae
      filter_upwards with s
      rfl
    _ = ∫ q, g (_root_.GD.N0232.N0720.N1091.d012759 p q)
          ∂(_root_.GD.N0125.d008852 alpha beta).map
            _root_.GD.N0232.N0720.N1091.d012794 := by
      symm
      simpa only [Function.comp_apply] using
        integral_map _root_.GD.N0232.N0720.N1091.d012795.aemeasurable
          ((hg.comp (_root_.GD.N0232.N0720.N1091.d012767 p)).aestronglyMeasurable)
    _ = ∫ q, g (_root_.GD.N0232.N0720.N1091.d012759 p q)
          ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta := by
      rw [_root_.GD.N0232.N0720.N1091.d012796 halpha hbeta]



theorem d012798
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hpush : _root_.GD.N0232.N0720.N1091.d012761 alpha beta)
    (hcoord :
      ∀ᵐ q ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta,
        _root_.GD.N0232.N0720.N1091.d012759 p q =
          _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p)
            (_root_.GD.N0232.N0720.N1091.d012760 alpha beta q)) :
    (∫ q, (_root_.GD.N0232.N0720.N1091.d012759 p q - p) ^ 2
      ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta) =
      _root_.GD.N0232.N0720.N1091.d012790 alpha beta p := by
  have htest : Measurable
      (fun u => (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2) := by
    exact ((_root_.GD.N0232.N0720.N1091.d012771 _).sub measurable_const).pow_const 2
  rw [show _root_.GD.N0232.N0720.N1091.d012790 alpha beta p =
      ∫ u, (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2
        ∂(_root_.GD.N0232.N0720.N1091.d012754 alpha beta).map (_root_.GD.N0232.N0720.N1091.d012760 alpha beta) by
      rw [hpush]
      rfl]
  rw [integral_map (_root_.GD.N0232.N0720.N1091.d012770 alpha beta).aemeasurable
    htest.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hcoord] with q hq
  rw [hq]



theorem d012799
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hpush : _root_.GD.N0232.N0720.N1091.d012761 alpha beta) :
    (∫ q, (_root_.GD.N0232.N0720.N1091.d012759 p q - p) ^ 2
      ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta) =
      _root_.GD.N0232.N0720.N1091.d012790 alpha beta p :=
  _root_.GD.N0232.N0720.N1091.d012798
    halpha hbeta hp0 hp1 hpush
      (_root_.GD.N0232.N0720.N1091.d012782 halpha hbeta hp0 hp1)





theorem d012800
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 alpha beta p =
      _root_.GD.N0232.N0720.N1091.d012791 alpha beta p := by
  unfold _root_.GD.N0232.N0720.N1091.d012790 _root_.GD.N0232.N0720.N1091.d012791
  apply integral_congr_ae
  have hsupport :
      ∀ᵐ u ∂betaMeasure alpha beta, u ∈ Set.Ioo (0 : ℝ) 1 := by
    unfold betaMeasure betaPDF
    rw [ae_withDensity_iff
      ((measurable_betaPDFReal alpha beta).ennreal_ofReal)]
    filter_upwards with u
    intro hu
    by_contra hnot
    have houtside : ¬(0 < u ∧ u < 1) := by
      simpa only [Set.mem_Ioo] using hnot
    simp [betaPDF, betaPDFReal, houtside] at hu
  filter_upwards [hsupport] with u hu
  exact _root_.GD.N0232.N0720.N1091.d012784 hbeta.ne' hp1.ne
    (_root_.GD.N0232.N0720.N1091.d012785 halpha hbeta hp0 hp1 hu.1 hu.2).ne'



theorem d012801
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012761 alpha beta →
    _root_.GD.N0120.d008809 alpha beta p
        (fun z : ℝ × ℝ => (z.1 - p) ^ 2) =
      _root_.GD.N0232.N0720.N1091.d012791 alpha beta p := by
  intro hpush
  rw [_root_.GD.N0232.N0720.N1091.d012797
    halpha hbeta (fun l => (l - p) ^ 2) (by fun_prop)]
  rw [_root_.GD.N0232.N0720.N1091.d012799
    halpha hbeta hp0 hp1 hpush]
  exact _root_.GD.N0232.N0720.N1091.d012800 halpha hbeta hp0 hp1




theorem d012802
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {U D L F : Omega → ℝ}
    {alpha beta p Sigma : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun omega => D omega * (L omega - p)) 2 P)
    (hOrthogonality :
      (∫ omega, U omega * (D omega * (L omega - p)) ∂P) = 0)
    (hLaw : _root_.GD.N0125.d008847
      P D L F alpha beta p Sigma)
    (hpush : _root_.GD.N0232.N0720.N1091.d012761 alpha beta) :
    _root_.GD.N0141.d006684 P
          (_root_.GD.N0141.d006685 U D L p) -
        _root_.GD.N0141.d006684 P U =
      Sigma * _root_.GD.N0232.N0720.N1091.d012791 alpha beta p := by
  rw [_root_.GD.N0232.N0720.N1207.d012753
      hU hWeight hOrthogonality hLaw]
  rw [_root_.GD.N0232.N0720.N1091.d012801
    halpha hbeta hp0 hp1 hpush]




theorem d012803
    {alpha beta p v : ℝ} (hp0 : p ≠ 0) :
    (v / p) * _root_.GD.N0232.N0720.N1091.d012791 alpha beta p =
      v * p * (1 - p) ^ 2 *
        (∫ u,
          (_root_.GD.N0232.N0720.N1091.d012765 alpha beta u) ^ 2 /
            (_root_.GD.N0232.N0720.N1091.d012764 alpha beta p u) ^ 2
          ∂betaMeasure alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1091.d012791
  calc
    (v / p) *
        (∫ u,
          p ^ 2 * (1 - p) ^ 2 * _root_.GD.N0232.N0720.N1091.d012765 alpha beta u ^ 2 /
            _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u ^ 2
          ∂betaMeasure alpha beta) =
        ∫ u,
          (v / p) *
            (p ^ 2 * (1 - p) ^ 2 * _root_.GD.N0232.N0720.N1091.d012765 alpha beta u ^ 2 /
              _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u ^ 2)
          ∂betaMeasure alpha beta := by rw [integral_const_mul]
    _ = ∫ u,
          (v * p * (1 - p) ^ 2) *
            (_root_.GD.N0232.N0720.N1091.d012765 alpha beta u ^ 2 /
              _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u ^ 2)
          ∂betaMeasure alpha beta := by
      apply integral_congr_ae
      filter_upwards with u
      field_simp [hp0]
    _ = v * p * (1 - p) ^ 2 *
        (∫ u,
          _root_.GD.N0232.N0720.N1091.d012765 alpha beta u ^ 2 /
            _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u ^ 2
          ∂betaMeasure alpha beta) := by rw [integral_const_mul]

#print axioms _root_.GD.N0232.N0720.N1091.d012781
#print axioms _root_.GD.N0232.N0720.N1091.d012783
#print axioms _root_.GD.N0232.N0720.N1091.d012784
#print axioms _root_.GD.N0232.N0720.N1091.d012798
#print axioms _root_.GD.N0232.N0720.N1091.d012799
#print axioms _root_.GD.N0232.N0720.N1091.d012792
#print axioms _root_.GD.N0232.N0720.N1091.d012793
#print axioms _root_.GD.N0232.N0720.N1091.d012801
#print axioms _root_.GD.N0232.N0720.N1091.d012802
#print axioms _root_.GD.N0232.N0720.N1091.d012800
#print axioms _root_.GD.N0232.N0720.N1091.d012803

end

end N1091
end N0720
end N0232
end GD
