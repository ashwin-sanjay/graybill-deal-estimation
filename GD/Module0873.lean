import GD.Module0868
import GD.Module0640
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import GD.Module0613
import GD.Module0429


























open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Matrix

namespace GD
namespace N0232
namespace N0720
namespace N1435

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1430
open _root_.GD.N0232.N0720.N1462




abbrev d013432 := Fin 3 → ℝ


def d013433 : Set _root_.GD.N0232.N0720.N1435.d013432 :=
  {u | ∀ i, 0 < u i}


def d013434 : Set _root_.GD.N0232.N0720.N1435.d013432 :=
  {z | 0 < z 0 ∧ 0 < z 1 ∧ z 1 < 1 ∧ 0 < z 2}


def d013435 (z : _root_.GD.N0232.N0720.N1435.d013432) : _root_.GD.N0232.N0720.N1435.d013432 :=
  ![z 0 * (1 - z 1), z 0 * z 1, z 0 * z 2]


def d013436 (u : _root_.GD.N0232.N0720.N1435.d013432) : _root_.GD.N0232.N0720.N1435.d013432 :=
  ![u 0 + u 1, u 1 / (u 0 + u 1), u 2 / (u 0 + u 1)]

@[fun_prop]
theorem d013437 : Measurable _root_.GD.N0232.N0720.N1435.d013435 := by
  unfold _root_.GD.N0232.N0720.N1435.d013435
  fun_prop

@[fun_prop]
theorem d013438 : Measurable _root_.GD.N0232.N0720.N1435.d013436 := by
  unfold _root_.GD.N0232.N0720.N1435.d013436
  fun_prop

theorem d013439 : MeasurableSet _root_.GD.N0232.N0720.N1435.d013433 := by
  rw [show _root_.GD.N0232.N0720.N1435.d013433 = ⋂ i : Fin 3, {u : _root_.GD.N0232.N0720.N1435.d013432 | 0 < u i} by
    ext u
    simp [_root_.GD.N0232.N0720.N1435.d013433]]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (measurable_pi_apply i)

theorem d013440 : MeasurableSet _root_.GD.N0232.N0720.N1435.d013434 := by
  unfold _root_.GD.N0232.N0720.N1435.d013434
  rw [show
      {z : _root_.GD.N0232.N0720.N1435.d013432 | 0 < z 0 ∧ 0 < z 1 ∧ z 1 < 1 ∧ 0 < z 2} =
        {z | 0 < z 0} ∩ {z | 0 < z 1} ∩
          {z | z 1 < 1} ∩ {z | 0 < z 2} by
    ext z
    simp only [mem_setOf_eq, mem_inter_iff]
    tauto]
  exact
    (((measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_lt measurable_const (measurable_pi_apply 1))).inter
      (measurableSet_lt (measurable_pi_apply 1) measurable_const)).inter
      (measurableSet_lt measurable_const (measurable_pi_apply 2))

theorem d013441
    {z : _root_.GD.N0232.N0720.N1435.d013432} (hz : z ∈ _root_.GD.N0232.N0720.N1435.d013434) :
    _root_.GD.N0232.N0720.N1435.d013435 z ∈ _root_.GD.N0232.N0720.N1435.d013433 := by
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1435.d013435] using mul_pos hz.1 (sub_pos.mpr hz.2.2.1)
  · simpa [_root_.GD.N0232.N0720.N1435.d013435] using mul_pos hz.1 hz.2.1
  · simpa [_root_.GD.N0232.N0720.N1435.d013435] using mul_pos hz.1 hz.2.2.2

theorem d013442
    {u : _root_.GD.N0232.N0720.N1435.d013432} (hu : u ∈ _root_.GD.N0232.N0720.N1435.d013433) :
    _root_.GD.N0232.N0720.N1435.d013436 u ∈ _root_.GD.N0232.N0720.N1435.d013434 := by
  have hsum : 0 < u 0 + u 1 := add_pos (hu 0) (hu 1)
  refine ⟨hsum, div_pos (hu 1) hsum, ?_, div_pos (hu 2) hsum⟩
  change u 1 / (u 0 + u 1) < 1
  rw [div_lt_one hsum]
  linarith [hu 0]

theorem d013443
    {u : _root_.GD.N0232.N0720.N1435.d013432} (hu : u ∈ _root_.GD.N0232.N0720.N1435.d013433) :
    _root_.GD.N0232.N0720.N1435.d013435 (_root_.GD.N0232.N0720.N1435.d013436 u) = u := by
  have hsum : u 0 + u 1 ≠ 0 := (add_pos (hu 0) (hu 1)).ne'
  funext i
  fin_cases i <;> simp [_root_.GD.N0232.N0720.N1435.d013435, _root_.GD.N0232.N0720.N1435.d013436] <;>
    field_simp [hsum] <;> ring

theorem d013444
    {z : _root_.GD.N0232.N0720.N1435.d013432} (hz : z ∈ _root_.GD.N0232.N0720.N1435.d013434) :
    _root_.GD.N0232.N0720.N1435.d013436 (_root_.GD.N0232.N0720.N1435.d013435 z) = z := by
  have hL : z 0 ≠ 0 := hz.1.ne'
  funext i
  fin_cases i <;> simp [_root_.GD.N0232.N0720.N1435.d013435, _root_.GD.N0232.N0720.N1435.d013436] <;>
    field_simp [hL] <;> ring

theorem d013445 :
    _root_.GD.N0232.N0720.N1435.d013435 '' _root_.GD.N0232.N0720.N1435.d013434 = _root_.GD.N0232.N0720.N1435.d013433 := by
  ext u
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact _root_.GD.N0232.N0720.N1435.d013441 hz
  · intro hu
    exact ⟨_root_.GD.N0232.N0720.N1435.d013436 u, _root_.GD.N0232.N0720.N1435.d013442 hu,
      _root_.GD.N0232.N0720.N1435.d013443 hu⟩

theorem d013446 : Set.InjOn _root_.GD.N0232.N0720.N1435.d013435 _root_.GD.N0232.N0720.N1435.d013434 := by
  intro z hz w hw hzw
  rw [← _root_.GD.N0232.N0720.N1435.d013444 hz,
    ← _root_.GD.N0232.N0720.N1435.d013444 hw, hzw]




def d013447 (z : _root_.GD.N0232.N0720.N1435.d013432) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - z 1, -z 0, 0;
     z 1,       z 0, 0;
     z 2,       0,   z 0]


def d013448 (z : _root_.GD.N0232.N0720.N1435.d013432) :
    _root_.GD.N0232.N0720.N1435.d013432 →L[ℝ] _root_.GD.N0232.N0720.N1435.d013432 :=
  (Matrix.toLin' (_root_.GD.N0232.N0720.N1435.d013447 z)).toContinuousLinearMap

theorem d013449 (z : _root_.GD.N0232.N0720.N1435.d013432) :
    HasFDerivAt _root_.GD.N0232.N0720.N1435.d013435 (_root_.GD.N0232.N0720.N1435.d013448 z) z := by
  have h0 : HasFDerivAt (fun w : _root_.GD.N0232.N0720.N1435.d013432 => w 0)
      (ContinuousLinearMap.proj 0) z :=
    (ContinuousLinearMap.proj 0 : _root_.GD.N0232.N0720.N1435.d013432 →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun w : _root_.GD.N0232.N0720.N1435.d013432 => w 1)
      (ContinuousLinearMap.proj 1) z :=
    (ContinuousLinearMap.proj 1 : _root_.GD.N0232.N0720.N1435.d013432 →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun w : _root_.GD.N0232.N0720.N1435.d013432 => w 2)
      (ContinuousLinearMap.proj 2) z :=
    (ContinuousLinearMap.proj 2 : _root_.GD.N0232.N0720.N1435.d013432 →L[ℝ] ℝ).hasFDerivAt
  have hcomp : ∀ i : Fin 3,
      HasFDerivAt (fun w : _root_.GD.N0232.N0720.N1435.d013432 => _root_.GD.N0232.N0720.N1435.d013435 w i)
        (ContinuousLinearMap.proj i ∘L _root_.GD.N0232.N0720.N1435.d013448 z) z := by
    intro i
    fin_cases i
    · convert h0.mul ((hasFDerivAt_const (1 : ℝ) z).sub h1) using 1 <;>
        ext w <;> simp [_root_.GD.N0232.N0720.N1435.d013435, _root_.GD.N0232.N0720.N1435.d013448,
          _root_.GD.N0232.N0720.N1435.d013447, Matrix.toLin'_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ] <;> ring
    · convert h0.mul h1 using 1 <;>
        ext w <;> simp [_root_.GD.N0232.N0720.N1435.d013435, _root_.GD.N0232.N0720.N1435.d013448,
          _root_.GD.N0232.N0720.N1435.d013447, Matrix.toLin'_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ] <;> ring
    · convert h0.mul h2 using 1 <;>
        ext w <;> simp [_root_.GD.N0232.N0720.N1435.d013435, _root_.GD.N0232.N0720.N1435.d013448,
          _root_.GD.N0232.N0720.N1435.d013447, Matrix.toLin'_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ] <;> ring
  exact hasFDerivAt_pi.2 hcomp

theorem d013450 (z : _root_.GD.N0232.N0720.N1435.d013432) :
    (_root_.GD.N0232.N0720.N1435.d013448 z).det = (z 0) ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1435.d013448
  rw [LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin']
  rw [Matrix.det_fin_three]
  simp [_root_.GD.N0232.N0720.N1435.d013447]
  ring

theorem d013451
    {z : _root_.GD.N0232.N0720.N1435.d013432} (hz : z ∈ _root_.GD.N0232.N0720.N1435.d013434) :
    |(_root_.GD.N0232.N0720.N1435.d013448 z).det| = (z 0) ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1435.d013450, abs_of_nonneg (sq_nonneg _)]


theorem d013452
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : _root_.GD.N0232.N0720.N1435.d013432 → E) :
    (∫ u in _root_.GD.N0232.N0720.N1435.d013433, G u) =
      ∫ z in _root_.GD.N0232.N0720.N1435.d013434, (z 0) ^ 2 • G (_root_.GD.N0232.N0720.N1435.d013435 z) := by
  rw [← _root_.GD.N0232.N0720.N1435.d013445]
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := (volume : Measure _root_.GD.N0232.N0720.N1435.d013432))
      _root_.GD.N0232.N0720.N1435.d013440
      (fun z _hz => (_root_.GD.N0232.N0720.N1435.d013449 z).hasFDerivWithinAt)
      _root_.GD.N0232.N0720.N1435.d013446 G
  rw [hchange]
  apply setIntegral_congr_fun _root_.GD.N0232.N0720.N1435.d013440
  intro z hz
  change |(_root_.GD.N0232.N0720.N1435.d013448 z).det| • G (_root_.GD.N0232.N0720.N1435.d013435 z) =
    (z 0) ^ 2 • G (_root_.GD.N0232.N0720.N1435.d013435 z)
  rw [_root_.GD.N0232.N0720.N1435.d013451 hz]




def d013453 (m n : ℕ) : Fin 3 → ℝ :=
  ![_root_.GD.N0232.N0720.N1436.d013207 m, _root_.GD.N0232.N0720.N1436.d013208 n, _root_.GD.N0232.N0720.N1436.d013209]


def d013454 (m n : ℕ) (t : ℝ) : Fin 3 → ℝ :=
  ![_root_.GD.N0232.N0720.N1436.d013207 m / (1 - t),
    _root_.GD.N0232.N0720.N1436.d013208 n / t, (1 : ℝ) / 2]

theorem d013455
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∀ i, 0 < _root_.GD.N0232.N0720.N1435.d013453 m n i := by
  intro i
  fin_cases i
  · exact _root_.GD.N0232.N0720.N1436.d013211 hm
  · exact _root_.GD.N0232.N0720.N1436.d013212 hn
  · exact _root_.GD.N0232.N0720.N1436.d013213

theorem d013456
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ i, 0 < _root_.GD.N0232.N0720.N1435.d013454 m n t i := by
  intro i
  fin_cases i
  · exact div_pos (_root_.GD.N0232.N0720.N1436.d013211 hm) (sub_pos.mpr ht1)
  · exact div_pos (_root_.GD.N0232.N0720.N1436.d013212 hn) ht0
  · change 0 < (1 : ℝ) / 2
    norm_num


def d013457 : _root_.GD.N0232.N0720.N1435.d013432 ≃ᵐ ℝ × (ℝ × ℝ) where
  toEquiv :=
    { toFun := fun u => (u 0, (u 1, u 2))
      invFun := fun z => ![z.1, z.2.1, z.2.2]
      left_inv := by
        intro u
        funext i
        fin_cases i <;> rfl
      right_inv := by
        rintro ⟨z0, z1, z2⟩
        rfl }
  measurable_toFun := by
    exact (measurable_pi_apply 0).prod
      ((measurable_pi_apply 1).prod (measurable_pi_apply 2))
  measurable_invFun := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · change Measurable (fun z : ℝ × (ℝ × ℝ) => z.1)
      fun_prop
    · change Measurable (fun z : ℝ × (ℝ × ℝ) => z.2.1)
      fun_prop
    · change Measurable (fun z : ℝ × (ℝ × ℝ) => z.2.2)
      fun_prop


theorem d013458
    (mu : Fin 3 → Measure ℝ) [∀ i, SigmaFinite (mu i)] :
    MeasurePreserving _root_.GD.N0232.N0720.N1435.d013457 (Measure.pi mu)
      ((mu 0).prod ((mu 1).prod (mu 2))) := by
  have hhead := measurePreserving_piFinSuccAbove mu (0 : Fin 3)
  have htail := measurePreserving_piFinTwo
    (fun j : Fin 2 => mu ((0 : Fin 3).succAbove j))
  have hprod := (MeasurePreserving.id (mu 0)).prod htail
  have hcomp := hprod.comp hhead
  have hfun :
      (Prod.map id
          (MeasurableEquiv.piFinTwo
            (fun j : Fin 2 => ℝ)) ∘
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin 3 => ℝ) (0 : Fin 3)) =
        _root_.GD.N0232.N0720.N1435.d013457 := by
    funext u
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  rw [hfun] at hcomp
  simpa using hcomp

theorem d013459
    (mu : Fin 3 → Measure ℝ) [∀ i, SigmaFinite (mu i)] :
    MeasurePreserving _root_.GD.N0232.N0720.N1435.d013457.symm
      ((mu 0).prod ((mu 1).prod (mu 2))) (Measure.pi mu) :=
  MeasurePreserving.symm _root_.GD.N0232.N0720.N1435.d013457
    (_root_.GD.N0232.N0720.N1435.d013458 mu)


def d013460 (t : ℝ) (z : ℝ × (ℝ × ℝ)) :
    ℝ × (ℝ × ℝ) :=
  ((1 - t) * z.1, (t * z.2.1, z.2.2))

@[fun_prop]
theorem d013461 (t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1435.d013460 t) := by
  unfold _root_.GD.N0232.N0720.N1435.d013460
  fun_prop


def d013462 (t : ℝ) (z : ℝ × (ℝ × ℝ)) :
    _root_.GD.N0232.N0720.N1435.d013432 :=
  _root_.GD.N0232.N0720.N1435.d013457.symm (_root_.GD.N0232.N0720.N1435.d013460 t z)

@[fun_prop]
theorem d013463 (t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1435.d013462 t) := by
  unfold _root_.GD.N0232.N0720.N1435.d013462
  fun_prop


def d013464 (m n : ℕ) (t : ℝ) : Measure _root_.GD.N0232.N0720.N1435.d013432 :=
  _root_.GD.N0232.N0719.N0954.d009342
    (_root_.GD.N0232.N0720.N1435.d013453 m n) (_root_.GD.N0232.N0720.N1435.d013454 m n t)


theorem d013465
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (_root_.GD.N0125.d008852
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)).map
        (_root_.GD.N0232.N0720.N1435.d013460 t) =
      (gammaMeasure (_root_.GD.N0232.N0720.N1436.d013207 m)
          (_root_.GD.N0232.N0720.N1436.d013207 m / (1 - t))).prod
        ((gammaMeasure (_root_.GD.N0232.N0720.N1436.d013208 n)
            (_root_.GD.N0232.N0720.N1436.d013208 n / t)).prod
          _root_.GD.N0125.d008851) := by
  letI : IsProbabilityMeasure
      (gammaMeasure (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013207 m)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013211 hm)
  letI : IsProbabilityMeasure
      (gammaMeasure (_root_.GD.N0232.N0720.N1436.d013208 n) (_root_.GD.N0232.N0720.N1436.d013208 n)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0232.N0720.N1436.d013212 hn) (_root_.GD.N0232.N0720.N1436.d013212 hn)
  letI : IsProbabilityMeasure _root_.GD.N0125.d008851 := by
    unfold _root_.GD.N0125.d008851
    exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  unfold _root_.GD.N0125.d008852 _root_.GD.N0232.N0720.N1435.d013460
  change Measure.map
      (Prod.map ((1 - t) * ·) (Prod.map (t * ·) id))
      ((gammaMeasure (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013207 m)).prod
        ((gammaMeasure (_root_.GD.N0232.N0720.N1436.d013208 n) (_root_.GD.N0232.N0720.N1436.d013208 n)).prod
          _root_.GD.N0125.d008851)) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id]
  rw [_root_.GD.N0232.N0719.N0954.d009354
      (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013211 hm)
        (sub_pos.mpr ht1),
    _root_.GD.N0232.N0719.N0954.d009354
      (_root_.GD.N0232.N0720.N1436.d013212 hn) (_root_.GD.N0232.N0720.N1436.d013212 hn) ht0]
  simp


theorem d013466
    (m n : ℕ) (t : ℝ) :
    Measure.map _root_.GD.N0232.N0720.N1435.d013457.symm
      ((gammaMeasure (_root_.GD.N0232.N0720.N1436.d013207 m)
          (_root_.GD.N0232.N0720.N1436.d013207 m / (1 - t))).prod
        ((gammaMeasure (_root_.GD.N0232.N0720.N1436.d013208 n)
            (_root_.GD.N0232.N0720.N1436.d013208 n / t)).prod
          _root_.GD.N0125.d008851)) =
      _root_.GD.N0232.N0720.N1435.d013464 m n t := by
  let mu : Fin 3 → Measure ℝ := fun i =>
    gammaMeasure (_root_.GD.N0232.N0720.N1435.d013453 m n i) (_root_.GD.N0232.N0720.N1435.d013454 m n t i)
  have hmap := (_root_.GD.N0232.N0720.N1435.d013459 mu).map_eq
  simpa [mu, _root_.GD.N0232.N0720.N1435.d013464,
    _root_.GD.N0232.N0719.N0954.d009342,
    _root_.GD.N0232.N0720.N1435.d013453, _root_.GD.N0232.N0720.N1435.d013454, _root_.GD.N0125.d008851,
    _root_.GD.N0232.N0720.N1436.d013209] using hmap



theorem d013467
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Measure.map (_root_.GD.N0232.N0720.N1435.d013462 t)
        (_root_.GD.N0125.d008852
          (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)) =
      _root_.GD.N0232.N0720.N1435.d013464 m n t := by
  rw [show _root_.GD.N0232.N0720.N1435.d013462 t =
      _root_.GD.N0232.N0720.N1435.d013457.symm ∘ _root_.GD.N0232.N0720.N1435.d013460 t by rfl]
  rw [← Measure.map_map _root_.GD.N0232.N0720.N1435.d013457.symm.measurable
    (_root_.GD.N0232.N0720.N1435.d013461 t)]
  rw [_root_.GD.N0232.N0720.N1435.d013465 hm hn ht0 ht1]
  exact _root_.GD.N0232.N0720.N1435.d013466 m n t




def d013468 (u : _root_.GD.N0232.N0720.N1435.d013432) : _root_.GD.N0232.N0720.N1436.d013217 :=
  (u 1 / (u 0 + u 1), u 2 / (u 0 + u 1))

@[fun_prop]
theorem d013469 :
    Measurable _root_.GD.N0232.N0720.N1435.d013468 := by
  unfold _root_.GD.N0232.N0720.N1435.d013468
  fun_prop



def d013470 (t : ℝ)
    (z : ℝ × (ℝ × ℝ)) : _root_.GD.N0232.N0720.N1436.d013217 :=
  _root_.GD.N0232.N0720.N1435.d013468 (_root_.GD.N0232.N0720.N1435.d013462 t z)

@[fun_prop]
theorem d013471 (t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1435.d013470 t) := by
  unfold _root_.GD.N0232.N0720.N1435.d013470
  fun_prop

theorem d013472
    {z : _root_.GD.N0232.N0720.N1435.d013432} (hz : z ∈ _root_.GD.N0232.N0720.N1435.d013434) :
    _root_.GD.N0232.N0720.N1435.d013468 (_root_.GD.N0232.N0720.N1435.d013435 z) = (z 1, z 2) := by
  have hL : z 0 ≠ 0 := hz.1.ne'
  apply Prod.ext <;>
    simp [_root_.GD.N0232.N0720.N1435.d013468, _root_.GD.N0232.N0720.N1435.d013435] <;>
    field_simp [hL] <;> ring


def d013473 : _root_.GD.N0232.N0720.N1435.d013432 ≃ᵐ _root_.GD.N0232.N0720.N1436.d013217 × ℝ :=
  _root_.GD.N0232.N0720.N1435.d013457.trans MeasurableEquiv.prodComm

@[simp]
theorem d013474 (z : _root_.GD.N0232.N0720.N1435.d013432) :
    (_root_.GD.N0232.N0720.N1435.d013473 z).1 = (z 1, z 2) := by
  rfl

@[simp]
theorem d013475 (z : _root_.GD.N0232.N0720.N1435.d013432) :
    (_root_.GD.N0232.N0720.N1435.d013473 z).2 = z 0 := by
  rfl


def d013476 (x : _root_.GD.N0232.N0720.N1436.d013217) (L : ℝ) : _root_.GD.N0232.N0720.N1435.d013432 :=
  _root_.GD.N0232.N0720.N1435.d013473.symm (x, L)

@[simp]
theorem d013477 (x : _root_.GD.N0232.N0720.N1436.d013217) (L : ℝ) :
    _root_.GD.N0232.N0720.N1435.d013476 x L 0 = L := by
  rfl

@[simp]
theorem d013478 (x : _root_.GD.N0232.N0720.N1436.d013217) (L : ℝ) :
    _root_.GD.N0232.N0720.N1435.d013476 x L 1 = x.1 := by
  rfl

@[simp]
theorem d013479 (x : _root_.GD.N0232.N0720.N1436.d013217) (L : ℝ) :
    _root_.GD.N0232.N0720.N1435.d013476 x L 2 = x.2 := by
  rfl

theorem d013480 :
    MeasurePreserving _root_.GD.N0232.N0720.N1435.d013473
      (volume : Measure _root_.GD.N0232.N0720.N1435.d013432)
      (volume : Measure (_root_.GD.N0232.N0720.N1436.d013217 × ℝ)) := by
  have hnested := _root_.GD.N0232.N0720.N1435.d013458
    (fun _ : Fin 3 => (volume : Measure ℝ))
  have hswap : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  have hcomp := hswap.comp hnested
  change MeasurePreserving (Prod.swap ∘ ⇑_root_.GD.N0232.N0720.N1435.d013457)
    (volume : Measure _root_.GD.N0232.N0720.N1435.d013432)
    (volume : Measure (_root_.GD.N0232.N0720.N1436.d013217 × ℝ))
  simpa [volume_pi, Measure.volume_eq_prod] using hcomp

theorem d013481 :
    _root_.GD.N0232.N0720.N1435.d013473 '' _root_.GD.N0232.N0720.N1435.d013434 =
      _root_.GD.N0232.N0720.N1436.d013218 ×ˢ Set.Ioi 0 := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ((z 1, z 2) ∈ _root_.GD.N0232.N0720.N1436.d013218) ∧ z 0 ∈ Set.Ioi 0
    exact ⟨⟨⟨hz.2.1, hz.2.2.1⟩, hz.2.2.2⟩, hz.1⟩
  · intro hp
    refine ⟨_root_.GD.N0232.N0720.N1435.d013473.symm p, ?_, _root_.GD.N0232.N0720.N1435.d013473.apply_symm_apply p⟩
    change 0 < p.2 ∧ 0 < p.1.1 ∧ p.1.1 < 1 ∧ 0 < p.1.2
    exact ⟨hp.2, hp.1.1.1, hp.1.1.2, hp.1.2⟩


theorem d013482
    (H : _root_.GD.N0232.N0720.N1435.d013432 → ℝ) (hH : IntegrableOn H _root_.GD.N0232.N0720.N1435.d013434) :
    (∫ z in _root_.GD.N0232.N0720.N1435.d013434, H z) =
      ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        ∫ L in Set.Ioi 0, H (_root_.GD.N0232.N0720.N1435.d013476 x L) := by
  let e := _root_.GD.N0232.N0720.N1435.d013473
  let K : _root_.GD.N0232.N0720.N1436.d013217 × ℝ → ℝ :=
    fun p => H (e.symm p)
  have hImage : e '' _root_.GD.N0232.N0720.N1435.d013434 = _root_.GD.N0232.N0720.N1436.d013218 ×ˢ Set.Ioi 0 :=
    _root_.GD.N0232.N0720.N1435.d013481
  have htransport :
      (∫ p in e '' _root_.GD.N0232.N0720.N1435.d013434, K p) =
        ∫ z in _root_.GD.N0232.N0720.N1435.d013434, H z := by
    have h := _root_.GD.N0232.N0720.N1435.d013480.setIntegral_image_emb
      e.measurableEmbedding K _root_.GD.N0232.N0720.N1435.d013434
    simpa [K, e] using h
  have hK : IntegrableOn K (_root_.GD.N0232.N0720.N1436.d013218 ×ˢ Set.Ioi 0) := by
    rw [← hImage]
    apply (_root_.GD.N0232.N0720.N1435.d013480.integrableOn_image
      e.measurableEmbedding).2
    have hKe : K ∘ e = H := by
      funext z
      simp [K, e]
    rw [hKe]
    exact hH
  calc
    (∫ z in _root_.GD.N0232.N0720.N1435.d013434, H z) =
        ∫ p in _root_.GD.N0232.N0720.N1436.d013218 ×ˢ Set.Ioi 0, K p := by
      rw [← hImage, htransport]
    _ = ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          ∫ L in Set.Ioi 0, K (x, L) := by
      rw [Measure.volume_eq_prod]
      exact setIntegral_prod K hK
    _ = ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          ∫ L in Set.Ioi 0, H (_root_.GD.N0232.N0720.N1435.d013476 x L) := by
      rfl



def d013483
    (m n : ℕ) (t : ℝ) : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  Measure.map _root_.GD.N0232.N0720.N1435.d013468 (_root_.GD.N0232.N0720.N1435.d013464 m n t)

theorem d013484
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1435.d013464 m n t) := by
  letI : ∀ i : Fin 3,
      IsProbabilityMeasure
        (gammaMeasure (_root_.GD.N0232.N0720.N1435.d013453 m n i) (_root_.GD.N0232.N0720.N1435.d013454 m n t i)) :=
    fun i => isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0232.N0720.N1435.d013455 hm hn i) (_root_.GD.N0232.N0720.N1435.d013456 hm hn ht0 ht1 i)
  unfold _root_.GD.N0232.N0720.N1435.d013464
    _root_.GD.N0232.N0719.N0954.d009342
  infer_instance

theorem d013485
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1435.d013483 m n t) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1435.d013464 m n t) :=
    _root_.GD.N0232.N0720.N1435.d013484 hm hn ht0 ht1
  unfold _root_.GD.N0232.N0720.N1435.d013483
  exact Measure.isProbabilityMeasure_map
    _root_.GD.N0232.N0720.N1435.d013469.aemeasurable



theorem d013486
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Measure.map (_root_.GD.N0232.N0720.N1435.d013470 t)
        (_root_.GD.N0125.d008852
          (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)) =
      _root_.GD.N0232.N0720.N1435.d013483 m n t := by
  rw [show _root_.GD.N0232.N0720.N1435.d013470 t =
      _root_.GD.N0232.N0720.N1435.d013468 ∘ _root_.GD.N0232.N0720.N1435.d013462 t by rfl]
  rw [← Measure.map_map _root_.GD.N0232.N0720.N1435.d013469
    (_root_.GD.N0232.N0720.N1435.d013463 t)]
  rw [_root_.GD.N0232.N0720.N1435.d013467 hm hn ht0 ht1]
  rfl






theorem d013487
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1436.d013271 m n =
      _root_.GD.N0116.d006506
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) := by
  unfold _root_.GD.N0232.N0720.N1436.d013271 _root_.GD.N0116.d006506
    _root_.GD.N0232.N0720.N1436.d013209
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (2 : ℝ) ^ ((3 : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hfirst : Real.Gamma (_root_.GD.N0232.N0720.N1436.d013207 m) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (_root_.GD.N0232.N0720.N1436.d013211 hm)).ne'
  have hsecond : Real.Gamma (_root_.GD.N0232.N0720.N1436.d013208 n) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (_root_.GD.N0232.N0720.N1436.d013212 hn)).ne'
  have hcontrast : Real.Gamma ((3 : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  field_simp [hpow, hfirst, hsecond, hcontrast]
  <;> ring



theorem d013488
    {m n : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1462.d003110
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)
        t x.1 x.2 =
      t * (1 - t) * _root_.GD.N0232.N0720.N1436.d013268 m n t x := by
  rw [_root_.GD.N0232.N0720.N1430.d013382
    (m := m) (n := n) ht0 ht1 x]
  unfold _root_.GD.N0232.N0720.N1436.d013268
  ring



theorem d013489
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1436.d013273 m n t x =
      _root_.GD.N0116.d006511
        (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t x := by
  let alpha := _root_.GD.N0232.N0720.N1436.d013207 m
  let beta := _root_.GD.N0232.N0720.N1436.d013208 n
  let rate := _root_.GD.N0232.N0720.N1436.d013268 m n t x
  let N := _root_.GD.N0232.N0720.N1462.d003110 alpha beta t x.1 x.2
  have halpha : 0 < alpha := _root_.GD.N0232.N0720.N1436.d013211 hm
  have hbeta : 0 < beta := _root_.GD.N0232.N0720.N1436.d013212 hn
  have hrate : 0 < rate := _root_.GD.N0232.N0720.N1436.d013281 hm hn ht0 ht1 hx
  have hN_eq : N = t * (1 - t) * rate := by
    exact _root_.GD.N0232.N0720.N1435.d013488
      (m := m) (n := n) ht0.ne' ht1.ne x
  have hN : 0 < N := by
    rw [hN_eq]
    positivity
  have hrate_eq : rate = N / (t * (1 - t)) := by
    rw [hN_eq]
    field_simp [ht0.ne', (sub_pos.mpr ht1).ne']
  have hnuisance :=
    _root_.GD.N0116.d006514
      (α := alpha) (β := beta) (e := t) (N := N)
      ht0 ht1 hN
  have hshape :
      _root_.GD.N0232.N0720.N1436.d013269 m n x =
        _root_.GD.N0232.N0720.N1462.d003121 alpha beta x.1 x.2 := by
    exact _root_.GD.N0232.N0720.N1430.d013385 m n x
  have htotal :
      _root_.GD.N0232.N0720.N1436.d013210 m n =
        _root_.GD.N0116.d006509 alpha beta := by
    rfl
  have hreciprocal :
      (1 / rate) ^ (_root_.GD.N0232.N0720.N1436.d013210 m n) =
        (N / (t * (1 - t))) ^
          (-_root_.GD.N0116.d006509 alpha beta) := by
    rw [hrate_eq, htotal, one_div,
      Real.inv_rpow (div_nonneg hN.le
        (mul_nonneg ht0.le (sub_pos.mpr ht1).le)),
      ← Real.rpow_neg (div_nonneg hN.le
        (mul_nonneg ht0.le (sub_pos.mpr ht1).le))]
  unfold _root_.GD.N0232.N0720.N1436.d013273
  rw [_root_.GD.N0232.N0720.N1435.d013487 hm hn, hshape,
    hreciprocal]
  unfold _root_.GD.N0232.N0720.N1436.d013270
    _root_.GD.N0116.d006511
    _root_.GD.N0116.d006507
  change
    _root_.GD.N0116.d006506 alpha beta *
          ((1 - t) ^ (-alpha) * t ^ (-beta)) *
          _root_.GD.N0232.N0720.N1462.d003121 alpha beta x.1 x.2 *
          ((N / (t * (1 - t))) ^
            (-_root_.GD.N0116.d006509 alpha beta) *
            Real.Gamma (_root_.GD.N0116.d006509 alpha beta)) = _
  have hnuisance' :
      ((1 - t) ^ (-alpha) * t ^ (-beta)) *
          (N / (t * (1 - t))) ^
            (-_root_.GD.N0116.d006509 alpha beta) =
        _root_.GD.N0116.d006508 alpha beta t *
          N ^ (-_root_.GD.N0116.d006509 alpha beta) := by
    calc
      ((1 - t) ^ (-alpha) * t ^ (-beta)) *
            (N / (t * (1 - t))) ^
              (-_root_.GD.N0116.d006509 alpha beta) =
          t ^ (-beta) * (1 - t) ^ (-alpha) *
            (N / (t * (1 - t))) ^
              (-_root_.GD.N0116.d006509 alpha beta) := by ring
      _ = _root_.GD.N0116.d006508 alpha beta t *
            N ^ (-_root_.GD.N0116.d006509 alpha beta) := hnuisance
  calc
    _root_.GD.N0116.d006506 alpha beta *
          ((1 - t) ^ (-alpha) * t ^ (-beta)) *
          _root_.GD.N0232.N0720.N1462.d003121 alpha beta x.1 x.2 *
          ((N / (t * (1 - t))) ^
            (-_root_.GD.N0116.d006509 alpha beta) *
            Real.Gamma (_root_.GD.N0116.d006509 alpha beta)) =
        _root_.GD.N0116.d006506 alpha beta *
          Real.Gamma (_root_.GD.N0116.d006509 alpha beta) *
          _root_.GD.N0232.N0720.N1462.d003121 alpha beta x.1 x.2 *
          (((1 - t) ^ (-alpha) * t ^ (-beta)) *
            (N / (t * (1 - t))) ^
              (-_root_.GD.N0116.d006509 alpha beta)) := by ring
    _ = _root_.GD.N0116.d006506 alpha beta *
          Real.Gamma (_root_.GD.N0116.d006509 alpha beta) *
          _root_.GD.N0232.N0720.N1462.d003121 alpha beta x.1 x.2 *
          (_root_.GD.N0116.d006508 alpha beta t *
            N ^ (-_root_.GD.N0116.d006509 alpha beta)) := by
      rw [hnuisance']
    _ = _ := by
      dsimp [alpha, beta, N]
      unfold _root_.GD.N0116.d006508 _root_.GD.N0232.N0720.N1462.d003121
        _root_.GD.N0116.d006509 _root_.GD.N0232.N0720.N1462.d003110
      ring_nf

end

end N1435
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1435.d013452
#print axioms _root_.GD.N0232.N0720.N1435.d013482
#print axioms _root_.GD.N0232.N0720.N1435.d013467
#print axioms _root_.GD.N0232.N0720.N1435.d013485
#print axioms _root_.GD.N0232.N0720.N1435.d013486
#print axioms _root_.GD.N0232.N0720.N1435.d013487
#print axioms _root_.GD.N0232.N0720.N1435.d013489
