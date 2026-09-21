import GD.Module0847
import GD.Module0875
import GD.Module0846

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0783

noncomputable section

open _root_.GD.N0228.N0547.N0778
  _root_.GD.N0228.N0547.N0787
  _root_.GD.N0228.N0547.N0781
  _root_.GD.N0228.N0547.N0790
  _root_.GD.N0228.N0547.N0795
  _root_.GD.N0228.N0547.N0796


abbrev d013523 := ℝ × (ℝ × ℝ)


def d013524 (rho : ℝ) (q : _root_.GD.N0228.N0547.N0783.d013523) : _root_.GD.N0228.N0547.N0783.d013523 :=
  (q.1, (rho * q.2.1, (1 - rho) * q.2.2))

@[fun_prop]
theorem d013525 (rho : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0783.d013524 rho) := by
  unfold _root_.GD.N0228.N0547.N0783.d013524
  fun_prop


def d013526 (rho : ℝ) (z : _root_.GD.N0228.N0547.N0783.d013523) : _root_.GD.N0228.N0547.N0783.d013523 :=
  _root_.GD.N0228.N0547.N0783.d013524 rho (_root_.GD.N0228.N0547.N0781.d012917 z)

@[fun_prop]
theorem d013527 (rho : ℝ) : Measurable (_root_.GD.N0228.N0547.N0783.d013526 rho) := by
  unfold _root_.GD.N0228.N0547.N0783.d013526
  fun_prop


def d013528 (q : _root_.GD.N0228.N0547.N0783.d013523) : ℝ × ℝ :=
  (q.1 / (q.2.1 + q.2.2), q.2.1 / (q.2.1 + q.2.2))

@[fun_prop]
theorem d013529 : Measurable _root_.GD.N0228.N0547.N0783.d013528 := by
  unfold _root_.GD.N0228.N0547.N0783.d013528
  fun_prop

theorem d013530 (rho : ℝ) :
    _root_.GD.N0228.N0547.N0787.d012939 rho = _root_.GD.N0228.N0547.N0783.d013528 ∘ _root_.GD.N0228.N0547.N0783.d013526 rho := by
  funext z
  simp only [_root_.GD.N0228.N0547.N0787.d012939, _root_.GD.N0228.N0547.N0787.d012938, _root_.GD.N0228.N0547.N0783.d013528, _root_.GD.N0228.N0547.N0783.d013526,
    _root_.GD.N0228.N0547.N0783.d013524, _root_.GD.N0228.N0547.N0781.d012917, Function.comp_apply]



theorem d013531
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    (_root_.GD.N0228.N0547.N0790.d012894 r s).map (_root_.GD.N0228.N0547.N0783.d013526 rho) =
      (gammaMeasure (1 / 2) (1 / 2)).prod
        ((gammaMeasure ((r : ℝ) / 2) (1 / (2 * rho))).prod
          (gammaMeasure ((s : ℝ) / 2) (1 / (2 * (1 - rho))))) := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 r) :=
    _root_.GD.N0228.N0547.N0790.d012889 hr
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 s) :=
    _root_.GD.N0228.N0547.N0790.d012889 hs
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 1) :=
    _root_.GD.N0228.N0547.N0790.d012889 (by norm_num)
  have hrR : (0 : ℝ) < (r : ℝ) / 2 := by positivity
  have hsR : (0 : ℝ) < (s : ℝ) / 2 := by positivity
  have h1rho : 0 < 1 - rho := sub_pos.mpr hrho1
  have hrateR : (1 / 2 : ℝ) / rho = 1 / (2 * rho) := by
    field_simp
  have hrateS : (1 / 2 : ℝ) / (1 - rho) =
      1 / (2 * (1 - rho)) := by
    field_simp
  have hscalePair : Measurable
      (Prod.map (rho * ·) ((1 - rho) * ·) : ℝ × ℝ → ℝ × ℝ) := by
    fun_prop
  calc
    (_root_.GD.N0228.N0547.N0790.d012894 r s).map (_root_.GD.N0228.N0547.N0783.d013526 rho) =
        ((_root_.GD.N0228.N0547.N0790.d012894 r s).map _root_.GD.N0228.N0547.N0781.d012917).map
          (_root_.GD.N0228.N0547.N0783.d013524 rho) := by
      rw [Measure.map_map (_root_.GD.N0228.N0547.N0783.d013525 rho)
        _root_.GD.N0228.N0547.N0781.d012918]
      rfl
    _ = ((_root_.GD.N0228.N0547.N0778.d009365 1).prod
          ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))).map
            (_root_.GD.N0228.N0547.N0783.d013524 rho) := by
      rw [show _root_.GD.N0228.N0547.N0790.d012894 r s = _root_.GD.N0228.N0547.N0781.d012916 r s by rfl,
        _root_.GD.N0228.N0547.N0781.d012919 hr hs]
    _ = ((_root_.GD.N0228.N0547.N0778.d009365 1).map id).prod
        (((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)).map
          (Prod.map (rho * ·) ((1 - rho) * ·))) := by
      exact (Measure.map_prod_map (_root_.GD.N0228.N0547.N0778.d009365 1)
        ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)) measurable_id
        hscalePair).symm
    _ = ((_root_.GD.N0228.N0547.N0778.d009365 1).map id).prod
        (((_root_.GD.N0228.N0547.N0778.d009365 r).map (rho * ·)).prod
          ((_root_.GD.N0228.N0547.N0778.d009365 s).map ((1 - rho) * ·))) := by
      rw [Measure.map_prod_map (_root_.GD.N0228.N0547.N0778.d009365 r) (_root_.GD.N0228.N0547.N0778.d009365 s)
        (by fun_prop) (by fun_prop)]
    _ = _ := by
      rw [Measure.map_id]
      unfold _root_.GD.N0228.N0547.N0778.d009365
      rw [_root_.GD.N0232.N0719.N0954.d009354
          hrR (by norm_num) hrho0,
        _root_.GD.N0232.N0719.N0954.d009354
          hsR (by norm_num) h1rho,
        hrateR, hrateS]
      norm_num


def d013532 (r s : ℕ) (rho : ℝ) : Measure _root_.GD.N0228.N0547.N0783.d013523 :=
  (gammaMeasure (1 / 2) (1 / 2)).prod
    ((gammaMeasure ((r : ℝ) / 2) (1 / (2 * rho))).prod
      (gammaMeasure ((s : ℝ) / 2) (1 / (2 * (1 - rho)))))



theorem d013533
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    _root_.GD.N0228.N0547.N0783.d013532 r s rho =
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))).withDensity
          (fun q ↦ ENNReal.ofReal
            (_root_.GD.N0228.N0547.N0796.d013507 ((r : ℝ) / 2) ((s : ℝ) / 2) rho q)) := by
  have hrR : (0 : ℝ) < (r : ℝ) / 2 := by positivity
  have hsR : (0 : ℝ) < (s : ℝ) / 2 := by positivity
  have hrateR : 0 < (1 / (2 * rho) : ℝ) := by positivity
  have hrateS : 0 < (1 / (2 * (1 - rho)) : ℝ) := by positivity
  have hpdf0 : Measurable (gammaPDF (1 / 2) (1 / 2)) :=
    (measurable_gammaPDFReal (1 / 2) (1 / 2)).ennreal_ofReal
  have hpdfR : Measurable
      (gammaPDF ((r : ℝ) / 2) (1 / (2 * rho))) :=
    (measurable_gammaPDFReal ((r : ℝ) / 2) (1 / (2 * rho))).ennreal_ofReal
  have hpdfS : Measurable
      (gammaPDF ((s : ℝ) / 2) (1 / (2 * (1 - rho)))) :=
    (measurable_gammaPDFReal ((s : ℝ) / 2)
      (1 / (2 * (1 - rho)))).ennreal_ofReal
  have hpdfPair : Measurable (fun z : ℝ × ℝ ↦
      gammaPDF ((r : ℝ) / 2) (1 / (2 * rho)) z.1 *
        gammaPDF ((s : ℝ) / 2) (1 / (2 * (1 - rho))) z.2) :=
    (hpdfR.comp measurable_fst).mul (hpdfS.comp measurable_snd)
  unfold _root_.GD.N0228.N0547.N0783.d013532 gammaMeasure
  rw [prod_withDensity hpdfR hpdfS]
  rw [prod_withDensity hpdf0 hpdfPair]
  congr 1
  funext q
  simp only [gammaPDF, _root_.GD.N0228.N0547.N0796.d013507]
  rw [ENNReal.ofReal_mul
      (gammaPDFReal_nonneg (by norm_num) (by norm_num) q.1),
    ENNReal.ofReal_mul
      (gammaPDFReal_nonneg hrR hrateR q.2.1)]

theorem d013534
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    _root_.GD.N0228.N0547.N0787.d012941 r s rho =
      (_root_.GD.N0228.N0547.N0783.d013532 r s rho).map _root_.GD.N0228.N0547.N0783.d013528 := by
  unfold _root_.GD.N0228.N0547.N0787.d012941
  calc
    (_root_.GD.N0228.N0547.N0790.d012894 r s).map (_root_.GD.N0228.N0547.N0787.d012939 rho) =
        (_root_.GD.N0228.N0547.N0790.d012894 r s).map
          (_root_.GD.N0228.N0547.N0783.d013528 ∘ _root_.GD.N0228.N0547.N0783.d013526 rho) := by
      rw [_root_.GD.N0228.N0547.N0783.d013530 rho]
    _ = ((_root_.GD.N0228.N0547.N0790.d012894 r s).map (_root_.GD.N0228.N0547.N0783.d013526 rho)).map
          _root_.GD.N0228.N0547.N0783.d013528 := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0783.d013529
        (_root_.GD.N0228.N0547.N0783.d013527 rho)]
    _ = (_root_.GD.N0228.N0547.N0783.d013532 r s rho).map _root_.GD.N0228.N0547.N0783.d013528 := by
      rw [_root_.GD.N0228.N0547.N0783.d013531 hr hs hrho0 hrho1]
      rfl


def d013535 : Set (ℝ × ℝ) :=
  Set.Ioi 0 ×ˢ Set.Ioo 0 1

theorem d013536 : MeasurableSet _root_.GD.N0228.N0547.N0783.d013535 :=
  measurableSet_Ioi.prod measurableSet_Ioo


def d013537 (r s : ℕ) (rho : ℝ) : Measure (ℝ × ℝ) :=
  (((volume : Measure ℝ).prod volume).restrict _root_.GD.N0228.N0547.N0783.d013535).withDensity
    (fun tx ↦ ENNReal.ofReal
      (_root_.GD.N0228.N0547.N0795.d003450 ((r : ℝ) / 2) ((s : ℝ) / 2) rho tx.1 tx.2))

private theorem d013538 :
    ∀ᵐ q ∂((volume : Measure ℝ).prod
      ((volume : Measure ℝ).prod (volume : Measure ℝ))),
      q.1 ≠ 0 ∧ q.2.1 ≠ 0 ∧ q.2.2 ≠ 0 := by
  have hinnerSet : MeasurableSet
      (({0}ᶜ : Set ℝ) ×ˢ ({0}ᶜ : Set ℝ)) :=
    (measurableSet_singleton 0).compl.prod
      (measurableSet_singleton 0).compl
  have hinner : ∀ᵐ q ∂(volume : Measure ℝ).prod volume,
      q ∈ ({0}ᶜ : Set ℝ) ×ˢ ({0}ᶜ : Set ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae hinnerSet).2
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with q₁ hq₁
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with q₂ hq₂
    exact ⟨hq₁, hq₂⟩
  have houterSet : MeasurableSet
      (({0}ᶜ : Set ℝ) ×ˢ
        (({0}ᶜ : Set ℝ) ×ˢ ({0}ᶜ : Set ℝ))) :=
    (measurableSet_singleton 0).compl.prod hinnerSet
  have hout : ∀ᵐ q ∂((volume : Measure ℝ).prod
      ((volume : Measure ℝ).prod (volume : Measure ℝ))),
      q ∈ ({0}ᶜ : Set ℝ) ×ˢ
        (({0}ᶜ : Set ℝ) ×ˢ ({0}ᶜ : Set ℝ)) := by
    apply (Measure.ae_prod_iff_ae_ae houterSet).2
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with q₀ hq₀
    filter_upwards [hinner] with qs hqs
    exact ⟨hq₀, hqs⟩
  filter_upwards [hout] with q hq
  exact ⟨hq.1, hq.2.1, hq.2.2⟩

private theorem d013539
    {r s : ℕ} {rho : ℝ}
    (g : _root_.GD.N0228.N0547.N0783.d013523 → ℝ) :
    (∫ q, _root_.GD.N0228.N0547.N0796.d013507 ((r : ℝ) / 2) ((s : ℝ) / 2) rho q * g q) =
      ∫ q in _root_.GD.N0228.N0547.N0796.d013491,
        _root_.GD.N0228.N0547.N0796.d013507 ((r : ℝ) / 2) ((s : ℝ) / 2) rho q * g q := by
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [_root_.GD.N0228.N0547.N0783.d013538] with q hq hnot
  have hout : ¬(0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2) := by
    simpa only [_root_.GD.N0228.N0547.N0796.d013491, Set.mem_prod, Set.mem_Ioi] using hnot
  rcases not_and_or.mp hout with hT | hUV
  · have hTneg : q.1 < 0 := lt_of_le_of_ne (le_of_not_gt hT) hq.1
    simp [_root_.GD.N0228.N0547.N0796.d013507, gammaPDFReal, not_le.mpr hTneg]
  · rcases not_and_or.mp hUV with hU | hV
    · have hUneg : q.2.1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hU) hq.2.1
      simp [_root_.GD.N0228.N0547.N0796.d013507, gammaPDFReal, not_le.mpr hUneg]
    · have hVneg : q.2.2 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hV) hq.2.2
      simp [_root_.GD.N0228.N0547.N0796.d013507, gammaPDFReal, not_le.mpr hVneg]

private theorem d013540
    {p : _root_.GD.N0228.N0547.N0783.d013523} (hp : p ∈ _root_.GD.N0228.N0547.N0796.d013492) :
    _root_.GD.N0228.N0547.N0783.d013528 (_root_.GD.N0228.N0547.N0795.d003428 p) = (p.1, p.2.1) := by
  have hR : p.2.2 ≠ 0 := hp.2.2.ne'
  apply Prod.ext
  · simp only [_root_.GD.N0228.N0547.N0783.d013528, _root_.GD.N0228.N0547.N0795.d003428, _root_.GD.N0228.N0547.N0795.d003425,
      _root_.GD.N0228.N0547.N0795.d003426, _root_.GD.N0228.N0547.N0795.d003427]
    field_simp
    ring
  · simp only [_root_.GD.N0228.N0547.N0783.d013528, _root_.GD.N0228.N0547.N0795.d003428, _root_.GD.N0228.N0547.N0795.d003425,
      _root_.GD.N0228.N0547.N0795.d003426, _root_.GD.N0228.N0547.N0795.d003427]
    field_simp
    ring


def d013541 : _root_.GD.N0228.N0547.N0783.d013523 ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  MeasurableEquiv.prodAssoc.symm

theorem d013542 : MeasurePreserving _root_.GD.N0228.N0547.N0783.d013541
    ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))
    (((volume : Measure ℝ).prod volume).prod volume) :=
  MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) volume volume)

theorem d013543 :
    _root_.GD.N0228.N0547.N0783.d013541 '' _root_.GD.N0228.N0547.N0796.d013492 = _root_.GD.N0228.N0547.N0783.d013535 ×ˢ Set.Ioi 0 := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
  · intro hz
    exact ⟨(z.1.1, (z.1.2, z.2)), ⟨hz.1.1, hz.1.2, hz.2⟩, rfl⟩




theorem d013544
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) :
    (∫ q in _root_.GD.N0228.N0547.N0796.d013491,
      _root_.GD.N0228.N0547.N0796.d013507 ((r : ℝ) / 2) ((s : ℝ) / 2) rho q *
        f (_root_.GD.N0228.N0547.N0783.d013528 q)) =
      ∫ tx in _root_.GD.N0228.N0547.N0783.d013535,
        _root_.GD.N0228.N0547.N0795.d003450 ((r : ℝ) / 2) ((s : ℝ) / 2) rho tx.1 tx.2 *
          f tx := by
  let alpha : ℝ := (r : ℝ) / 2
  let beta : ℝ := (s : ℝ) / 2
  have halpha : 0 < alpha := by simp only [alpha]; positivity
  have hbeta : 0 < beta := by simp only [beta]; positivity
  let H : _root_.GD.N0228.N0547.N0783.d013523 → ℝ := fun p ↦
    _root_.GD.N0228.N0547.N0796.d013515 alpha beta rho p * f (p.1, p.2.1)
  have hH : IntegrableOn H _root_.GD.N0228.N0547.N0796.d013492 := by
    have hbase := _root_.GD.N0228.N0547.N0796.d013517
      halpha hbeta hrho0 hrho1
    apply hbase.mul_bdd
    · exact (f.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with p
      exact f.norm_coe_le_norm (p.1, p.2.1)
  have hchange :
      (∫ q in _root_.GD.N0228.N0547.N0796.d013491,
        _root_.GD.N0228.N0547.N0796.d013507 alpha beta rho q * f (_root_.GD.N0228.N0547.N0783.d013528 q)) =
        ∫ p in _root_.GD.N0228.N0547.N0796.d013492, H p := by
    rw [_root_.GD.N0228.N0547.N0796.d013505
      (fun q ↦ _root_.GD.N0228.N0547.N0796.d013507 alpha beta rho q * f (_root_.GD.N0228.N0547.N0783.d013528 q))]
    apply setIntegral_congr_fun _root_.GD.N0228.N0547.N0796.d013494
    intro p hp
    simp only [smul_eq_mul, H]
    rw [_root_.GD.N0228.N0547.N0783.d013540 hp]
    calc
      p.2.2 ^ 2 *
          (_root_.GD.N0228.N0547.N0796.d013507 alpha beta rho (_root_.GD.N0228.N0547.N0795.d003428 p) *
            f (p.1, p.2.1)) =
          (_root_.GD.N0228.N0547.N0796.d013507 alpha beta rho (_root_.GD.N0228.N0547.N0795.d003428 p) * p.2.2 ^ 2) *
            f (p.1, p.2.1) := by ring
      _ = H p := by
        rw [_root_.GD.N0228.N0547.N0796.d013516
          hrho0 hrho1 hp]
  let K : ((ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    H (_root_.GD.N0228.N0547.N0783.d013541.symm z)
  have hK : IntegrableOn K (_root_.GD.N0228.N0547.N0783.d013535 ×ˢ Set.Ioi 0) := by
    rw [← _root_.GD.N0228.N0547.N0783.d013543]
    have h := _root_.GD.N0228.N0547.N0783.d013542.integrableOn_image
      _root_.GD.N0228.N0547.N0783.d013541.measurableEmbedding (f := K) (s := _root_.GD.N0228.N0547.N0796.d013492)
    have hcomp : K ∘ _root_.GD.N0228.N0547.N0783.d013541 = H := by
      funext p
      simp [K]
    rw [hcomp] at h
    exact h.mpr hH
  have htransport :
      (∫ p in _root_.GD.N0228.N0547.N0796.d013492, H p) =
        ∫ z in _root_.GD.N0228.N0547.N0783.d013535 ×ˢ Set.Ioi 0, K z := by
    change (∫ p in _root_.GD.N0228.N0547.N0796.d013492, H p
        ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))) =
      ∫ z in _root_.GD.N0228.N0547.N0783.d013535 ×ˢ Set.Ioi 0, K z
        ∂(((volume : Measure ℝ).prod volume).prod volume)
    rw [← _root_.GD.N0228.N0547.N0783.d013543]
    have h := _root_.GD.N0228.N0547.N0783.d013542.setIntegral_image_emb
      _root_.GD.N0228.N0547.N0783.d013541.measurableEmbedding K _root_.GD.N0228.N0547.N0796.d013492
    simpa [K] using h.symm
  calc
    (∫ q in _root_.GD.N0228.N0547.N0796.d013491,
      _root_.GD.N0228.N0547.N0796.d013507 ((r : ℝ) / 2) ((s : ℝ) / 2) rho q *
        f (_root_.GD.N0228.N0547.N0783.d013528 q)) =
        ∫ p in _root_.GD.N0228.N0547.N0796.d013492, H p := by
      simpa only [alpha, beta] using hchange
    _ = ∫ z in _root_.GD.N0228.N0547.N0783.d013535 ×ˢ Set.Ioi 0, K z := htransport
    _ = ∫ tx in _root_.GD.N0228.N0547.N0783.d013535, ∫ R in Set.Ioi 0, K (tx, R) := by
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod K hK
    _ = ∫ tx in _root_.GD.N0228.N0547.N0783.d013535,
        _root_.GD.N0228.N0547.N0795.d003450 alpha beta rho tx.1 tx.2 * f tx := by
      apply setIntegral_congr_fun _root_.GD.N0228.N0547.N0783.d013536
      intro tx htx
      simp only [K, H, _root_.GD.N0228.N0547.N0783.d013541]
      change (∫ R in Set.Ioi 0,
        _root_.GD.N0228.N0547.N0796.d013515 alpha beta rho (tx.1, (tx.2, R)) *
          f tx) = _
      have hmarg : (∫ R in Set.Ioi 0,
          _root_.GD.N0228.N0547.N0796.d013515 alpha beta rho (tx.1, (tx.2, R))) =
          _root_.GD.N0228.N0547.N0795.d003450 alpha beta rho tx.1 tx.2 := by
        simpa only [_root_.GD.N0228.N0547.N0796.d013515] using
          (_root_.GD.N0228.N0547.N0795.d003452
            halpha hbeta hrho0 hrho1 htx.1 htx.2.1 htx.2.2)
      rw [integral_mul_const]
      rw [hmarg]
    _ = ∫ tx in _root_.GD.N0228.N0547.N0783.d013535,
        _root_.GD.N0228.N0547.N0795.d003450 ((r : ℝ) / 2) ((s : ℝ) / 2) rho tx.1 tx.2 *
          f tx := by rfl

private theorem d013545
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (q : _root_.GD.N0228.N0547.N0783.d013523) :
    0 ≤ _root_.GD.N0228.N0547.N0796.d013507 ((r : ℝ) / 2) ((s : ℝ) / 2) rho q := by
  unfold _root_.GD.N0228.N0547.N0796.d013507
  exact mul_nonneg
    (gammaPDFReal_nonneg (by norm_num) (by norm_num) q.1)
    (mul_nonneg
      (gammaPDFReal_nonneg (by positivity) (by positivity) q.2.1)
      (gammaPDFReal_nonneg (by positivity) (by positivity) q.2.2))

private theorem d013546
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    {tx : ℝ × ℝ} (htx : tx ∈ _root_.GD.N0228.N0547.N0783.d013535) :
    0 ≤ _root_.GD.N0228.N0547.N0795.d003450 ((r : ℝ) / 2) ((s : ℝ) / 2) rho tx.1 tx.2 := by
  have ht : 0 < tx.1 := htx.1
  have hxi0 : 0 < tx.2 := htx.2.1
  have hxi1 : tx.2 < 1 := htx.2.2
  have halpha : 0 < (r : ℝ) / 2 := by positivity
  have hbeta : 0 < (s : ℝ) / 2 := by positivity
  have hm : 0 < _root_.GD.N0228.N0547.N0795.d003442 ((r : ℝ) / 2) ((s : ℝ) / 2) := by
    unfold _root_.GD.N0228.N0547.N0795.d003442
    positivity
  have hD : 0 < _root_.GD.N0228.N0547.N0794.d003409 rho tx.1 tx.2 :=
    _root_.GD.N0228.N0547.N0795.d003440
      hrho0 hrho1 htx.1 htx.2.1 htx.2.2
  have hGammaM : 0 < Real.Gamma
      (_root_.GD.N0228.N0547.N0795.d003442 ((r : ℝ) / 2) ((s : ℝ) / 2)) :=
    Real.Gamma_pos_of_pos hm
  have hGammaHalf : 0 < Real.Gamma (1 / 2 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hGammaAlpha : 0 < Real.Gamma ((r : ℝ) / 2) :=
    Real.Gamma_pos_of_pos halpha
  have hGammaBeta : 0 < Real.Gamma ((s : ℝ) / 2) :=
    Real.Gamma_pos_of_pos hbeta
  have hangular : 0 < _root_.GD.N0228.N0547.N0795.d003443
      ((r : ℝ) / 2) ((s : ℝ) / 2) tx.1 tx.2 := by
    unfold _root_.GD.N0228.N0547.N0795.d003443
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos ht _)
        (Real.rpow_pos_of_pos hxi0 _))
      (Real.rpow_pos_of_pos (sub_pos.mpr hxi1) _)
  unfold _root_.GD.N0228.N0547.N0795.d003450
  positivity

private theorem d013547
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    IntegrableOn (fun tx : ℝ × ℝ ↦
      _root_.GD.N0228.N0547.N0795.d003450 ((r : ℝ) / 2) ((s : ℝ) / 2) rho tx.1 tx.2)
      _root_.GD.N0228.N0547.N0783.d013535 ((volume : Measure ℝ).prod volume) := by
  let f : ℝ × ℝ → ℝ := fun x ↦
    _root_.GD.N0228.N0547.N0795.d003450 ((r : ℝ) / 2) ((s : ℝ) / 2) rho x.2 x.1
  have hbase : IntegrableOn f
      _root_.GD.N0232.N0720.N1436.d013218 :=
    _root_.GD.N0228.N0547.N0796.d013519
      (by positivity) (by positivity) hrho0 hrho1
  have hswap : IntegrableOn (f ∘ Prod.swap)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [_root_.GD.N0232.N0720.N1436.d013218,
      Measure.prod_swap] using hbase.swap
  have hfun : (f ∘ Prod.swap) = fun tx : ℝ × ℝ ↦
      _root_.GD.N0228.N0547.N0795.d003450 ((r : ℝ) / 2) ((s : ℝ) / 2) rho tx.1 tx.2 := by
    funext tx
    rcases tx with ⟨t, xi⟩
    rfl
  rw [hfun] at hswap
  simpa only [_root_.GD.N0228.N0547.N0783.d013535] using hswap

private theorem d013548
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (g : _root_.GD.N0228.N0547.N0783.d013523 → ℝ) :
    (∫ q, g q ∂(_root_.GD.N0228.N0547.N0783.d013532 r s rho)) =
      ∫ q, _root_.GD.N0228.N0547.N0796.d013507 ((r : ℝ) / 2) ((s : ℝ) / 2) rho q * g q := by
  rw [_root_.GD.N0228.N0547.N0783.d013533 hr hs hrho0 hrho1]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards with q
    rw [ENNReal.toReal_ofReal
      (_root_.GD.N0228.N0547.N0783.d013545 hr hs hrho0 hrho1 q)]
    simp only [smul_eq_mul]
  · exact (_root_.GD.N0228.N0547.N0796.d013508 _ _ _).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

private theorem d013549
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (g : ℝ × ℝ → ℝ) :
    (∫ tx, g tx ∂(_root_.GD.N0228.N0547.N0783.d013537 r s rho)) =
      ∫ tx in _root_.GD.N0228.N0547.N0783.d013535,
        _root_.GD.N0228.N0547.N0795.d003450 ((r : ℝ) / 2) ((s : ℝ) / 2) rho tx.1 tx.2 * g tx := by
  unfold _root_.GD.N0228.N0547.N0783.d013537
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem _root_.GD.N0228.N0547.N0783.d013536]
      with tx htx
    rw [ENNReal.toReal_ofReal
      (_root_.GD.N0228.N0547.N0783.d013546 hr hs hrho0 hrho1 htx)]
    simp only [smul_eq_mul]
  · unfold _root_.GD.N0228.N0547.N0795.d003450 _root_.GD.N0228.N0547.N0795.d003443 _root_.GD.N0228.N0547.N0794.d003409
    fun_prop
  · exact Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top



theorem d013550
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) :
    (∫ tx, f tx ∂(_root_.GD.N0228.N0547.N0787.d012941 r s rho)) =
      ∫ tx, f tx ∂(_root_.GD.N0228.N0547.N0783.d013537 r s rho) := by
  rw [_root_.GD.N0228.N0547.N0783.d013534 hr hs hrho0 hrho1]
  rw [integral_map _root_.GD.N0228.N0547.N0783.d013529.aemeasurable
    f.continuous.aestronglyMeasurable]
  rw [_root_.GD.N0228.N0547.N0783.d013548 hr hs hrho0 hrho1]
  rw [_root_.GD.N0228.N0547.N0783.d013539]
  rw [_root_.GD.N0228.N0547.N0783.d013544
    hr hs hrho0 hrho1 f]
  exact (_root_.GD.N0228.N0547.N0783.d013549 hr hs hrho0 hrho1 f).symm




theorem d013551
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    _root_.GD.N0228.N0547.N0787.d012941 r s rho = _root_.GD.N0228.N0547.N0783.d013537 r s rho := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 r) :=
    _root_.GD.N0228.N0547.N0790.d012889 hr
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 s) :=
    _root_.GD.N0228.N0547.N0790.d012889 hs
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012894 r s) := by
    unfold _root_.GD.N0228.N0547.N0790.d012894
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0787.d012941 r s rho) := by
    unfold _root_.GD.N0228.N0547.N0787.d012941
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0228.N0547.N0787.d012940 rho).aemeasurable
  have hInt := _root_.GD.N0228.N0547.N0783.d013547
    hr hs hrho0 hrho1
  letI : IsFiniteMeasure (_root_.GD.N0228.N0547.N0783.d013537 r s rho) := by
    unfold _root_.GD.N0228.N0547.N0783.d013537
    exact isFiniteMeasure_withDensity_ofReal hInt.hasFiniteIntegral
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact _root_.GD.N0228.N0547.N0783.d013550
    hr hs hrho0 hrho1 f



theorem d013552
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (g : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ tx, g tx ∂(_root_.GD.N0228.N0547.N0787.d012941 r s rho)) =
      ∫⁻ tx, g tx ∂(_root_.GD.N0228.N0547.N0783.d013537 r s rho) := by
  rw [_root_.GD.N0228.N0547.N0783.d013551
    hr hs hrho0 hrho1]

end

end GD.N0228.N0547.N0783

#print axioms _root_.GD.N0228.N0547.N0783.d013551
#print axioms _root_.GD.N0228.N0547.N0783.d013552

