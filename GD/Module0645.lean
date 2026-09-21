import GD.Module0643
import GD.Module0263


























open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0947

noncomputable section



def d009460 (a y v mu t : ℝ) : ℝ :=
  t ^ (1 / 2 : ℝ) *
    Real.exp (-t * (a * v + (y - mu) ^ 2 / 2))



def d009461 (a v t : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * Real.exp (-t * (a * v))



theorem d009462
    (a y v mu t : ℝ) :
    _root_.GD.N0232.N0719.N0947.d009460 a y v mu t =
      t ^ (1 / 2 : ℝ) * Real.exp (-t * (a * v)) *
        Real.exp (-t * ((y - mu) ^ 2 / 2)) := by
  unfold _root_.GD.N0232.N0719.N0947.d009460
  rw [show -t * (a * v + (y - mu) ^ 2 / 2) =
      -t * (a * v) + -t * ((y - mu) ^ 2 / 2) by ring,
    Real.exp_add]
  ring



theorem d009463
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    t ^ (1 / 2 : ℝ) *
        (∫ mu : ℝ, Real.exp (-t * ((y - mu) ^ 2 / 2))) =
      Real.sqrt (2 * Real.pi) := by
  have hq : 0 < (1 / t : ℝ) := by positivity
  have hloc :=
    _root_.GD.N0232.N0719.N0928.d009425 hq y
  have hfun :
      (fun mu : ℝ ↦ Real.exp (-t * ((y - mu) ^ 2 / 2))) =
        fun mu : ℝ ↦
          Real.exp (-((mu - y) ^ 2 / 2) / (1 / t)) := by
    funext mu
    congr 1
    field_simp [ht.ne']
    ring
  rw [hfun, hloc]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have hquot : 2 * Real.pi * (1 / t) = (2 * Real.pi) / t := by
    field_simp [ht.ne']
  rw [hquot, Real.div_rpow htwoPi.le ht.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos ht (1 / 2 : ℝ))]


theorem d009464
    {b : ℝ} (_hb : 0 < b) :
    (∫ x : ℝ, x * Real.exp (-b * x ^ 2)) = 0 := by
  have hreflect :=
    MeasureTheory.integral_neg_eq_self
      (fun x : ℝ ↦ x * Real.exp (-b * x ^ 2)) volume
  have hodd :
      (fun x : ℝ ↦ (-x) * Real.exp (-b * (-x) ^ 2)) =
        fun x : ℝ ↦ -(x * Real.exp (-b * x ^ 2)) := by
    funext x
    rw [neg_sq]
    ring
  rw [hodd, MeasureTheory.integral_neg] at hreflect
  linarith



theorem d009465
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    (∫ mu : ℝ, mu * Real.exp (-t * ((y - mu) ^ 2 / 2))) =
      y * (∫ mu : ℝ, Real.exp (-t * ((y - mu) ^ 2 / 2))) := by
  let b : ℝ := t / 2
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have htranslate :=
    integral_add_right_eq_self (μ := volume)
      (fun x : ℝ ↦ (x + y) * Real.exp (-b * x ^ 2)) (-y)
  have hleft :
      (∫ mu : ℝ,
          (mu - y + y) * Real.exp (-b * (mu - y) ^ 2)) =
        ∫ mu : ℝ, mu * Real.exp (-t * ((y - mu) ^ 2 / 2)) := by
    apply integral_congr_ae
    filter_upwards with mu
    dsimp [b]
    congr 1
    · ring
    · congr 1
      ring
  have hright :
      (∫ x : ℝ, (x + y) * Real.exp (-b * x ^ 2)) =
        y * (∫ x : ℝ, Real.exp (-b * x ^ 2)) := by
    have hmul : Integrable (fun x : ℝ ↦ x * Real.exp (-b * x ^ 2)) :=
      integrable_mul_exp_neg_mul_sq hb
    have hgauss : Integrable (fun x : ℝ ↦ Real.exp (-b * x ^ 2)) :=
      integrable_exp_neg_mul_sq hb
    calc
      (∫ x : ℝ, (x + y) * Real.exp (-b * x ^ 2)) =
          (∫ x : ℝ, x * Real.exp (-b * x ^ 2)) +
            ∫ x : ℝ, y * Real.exp (-b * x ^ 2) := by
        rw [← integral_add hmul (hgauss.const_mul y)]
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = y * (∫ x : ℝ, Real.exp (-b * x ^ 2)) := by
        rw [_root_.GD.N0232.N0719.N0947.d009464 hb,
          integral_const_mul, zero_add]
  have htranslate' :
      (∫ mu : ℝ,
          (mu - y + y) * Real.exp (-b * (mu - y) ^ 2)) =
        ∫ x : ℝ, (x + y) * Real.exp (-b * x ^ 2) := by
    simpa [sub_eq_add_neg] using htranslate
  calc
    (∫ mu : ℝ, mu * Real.exp (-t * ((y - mu) ^ 2 / 2))) =
        ∫ mu : ℝ,
          (mu - y + y) * Real.exp (-b * (mu - y) ^ 2) := hleft.symm
    _ = ∫ x : ℝ, (x + y) * Real.exp (-b * x ^ 2) := htranslate'
    _ = y * (∫ x : ℝ, Real.exp (-b * x ^ 2)) := hright
    _ = y * (∫ mu : ℝ,
        Real.exp (-t * ((y - mu) ^ 2 / 2))) := by
      congr 1
      rw [show (fun mu : ℝ ↦ Real.exp (-t * ((y - mu) ^ 2 / 2))) =
          fun mu : ℝ ↦ Real.exp (-b * (mu - y) ^ 2) by
        funext mu
        dsimp [b]
        congr 1
        ring]
      symm
      have hshift :=
        integral_add_right_eq_self (μ := volume)
          (fun x : ℝ ↦ Real.exp (-b * x ^ 2)) (-y)
      calc
        (∫ mu : ℝ, Real.exp (-b * (mu - y) ^ 2)) =
            ∫ mu : ℝ, Real.exp (-b * (mu + -y) ^ 2) := by
          congr 1
        _ = ∫ x : ℝ, Real.exp (-b * x ^ 2) := hshift




theorem d009466
    (a y v : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ mu : ℝ, _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
      _root_.GD.N0232.N0719.N0947.d009461 a v t := by
  rw [show (fun mu : ℝ ↦ _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
      fun mu : ℝ ↦
        (t ^ (1 / 2 : ℝ) * Real.exp (-t * (a * v))) *
          Real.exp (-t * ((y - mu) ^ 2 / 2)) by
    funext mu
    rw [_root_.GD.N0232.N0719.N0947.d009462]]
  rw [integral_const_mul]
  unfold _root_.GD.N0232.N0719.N0947.d009461
  calc
    t ^ (1 / 2 : ℝ) * Real.exp (-t * (a * v)) *
          (∫ mu : ℝ, Real.exp (-t * ((y - mu) ^ 2 / 2))) =
        Real.exp (-t * (a * v)) *
          (t ^ (1 / 2 : ℝ) *
            (∫ mu : ℝ, Real.exp (-t * ((y - mu) ^ 2 / 2)))) := by
      ring
    _ = Real.exp (-t * (a * v)) * Real.sqrt (2 * Real.pi) := by
      rw [_root_.GD.N0232.N0719.N0947.d009463 ht y]
    _ = Real.sqrt (2 * Real.pi) * Real.exp (-t * (a * v)) := by
      ring


theorem d009467
    (a y v : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ mu : ℝ, mu * _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
      y * _root_.GD.N0232.N0719.N0947.d009461 a v t := by
  rw [show (fun mu : ℝ ↦ mu * _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
      fun mu : ℝ ↦
        (t ^ (1 / 2 : ℝ) * Real.exp (-t * (a * v))) *
          (mu * Real.exp (-t * ((y - mu) ^ 2 / 2))) by
    funext mu
    rw [_root_.GD.N0232.N0719.N0947.d009462]
    ring]
  rw [integral_const_mul,
    _root_.GD.N0232.N0719.N0947.d009465 ht y]
  unfold _root_.GD.N0232.N0719.N0947.d009461
  rw [show
      (t ^ (1 / 2 : ℝ) * Real.exp (-t * (a * v))) *
          (y * (∫ mu : ℝ,
            Real.exp (-t * ((y - mu) ^ 2 / 2)))) =
        y * Real.exp (-t * (a * v)) *
          (t ^ (1 / 2 : ℝ) *
            (∫ mu : ℝ,
              Real.exp (-t * ((y - mu) ^ 2 / 2)))) by ring,
    _root_.GD.N0232.N0719.N0947.d009463 ht y]
  ring


theorem d009468
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (y : ℝ) :
    (∫ t in Ioi (0 : ℝ), ∫ mu : ℝ, _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
      Real.sqrt (2 * Real.pi) / (a * v) := by
  calc
    (∫ t in Ioi (0 : ℝ), ∫ mu : ℝ, _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
        ∫ t in Ioi (0 : ℝ), _root_.GD.N0232.N0719.N0947.d009461 a v t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact _root_.GD.N0232.N0719.N0947.d009466 a y v ht
    _ = Real.sqrt (2 * Real.pi) *
        (∫ t in Ioi (0 : ℝ), Real.exp (-t * (a * v))) := by
      unfold _root_.GD.N0232.N0719.N0947.d009461
      rw [integral_const_mul]
    _ = Real.sqrt (2 * Real.pi) * (a * v)⁻¹ := by
      rw [_root_.GD.N0232.N0719.N0890.d003777 (mul_pos ha hv)]
    _ = Real.sqrt (2 * Real.pi) / (a * v) := by
      rw [div_eq_mul_inv]



theorem d009469
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (y : ℝ) :
    (∫ t in Ioi (0 : ℝ),
        ∫ mu : ℝ, mu * _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
      y * (Real.sqrt (2 * Real.pi) / (a * v)) := by
  calc
    (∫ t in Ioi (0 : ℝ),
        ∫ mu : ℝ, mu * _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
        ∫ t in Ioi (0 : ℝ), y * _root_.GD.N0232.N0719.N0947.d009461 a v t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact _root_.GD.N0232.N0719.N0947.d009467 a y v ht
    _ = y * (∫ t in Ioi (0 : ℝ), _root_.GD.N0232.N0719.N0947.d009461 a v t) := by
      rw [integral_const_mul]
    _ = y * (Real.sqrt (2 * Real.pi) / (a * v)) := by
      congr 1
      rw [← _root_.GD.N0232.N0719.N0947.d009468 ha hv y]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (_root_.GD.N0232.N0719.N0947.d009466 a y v ht).symm



theorem d009470
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (y : ℝ) :
    a * (∫ t in Ioi (0 : ℝ), ∫ mu : ℝ, _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
      Real.sqrt (2 * Real.pi) * (1 / v) := by
  rw [_root_.GD.N0232.N0719.N0947.d009468 ha hv y]
  field_simp [ha.ne', hv.ne']



theorem d009471
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) (y : ℝ) :
    a * (∫ t in Ioi (0 : ℝ),
        ∫ mu : ℝ, mu * _root_.GD.N0232.N0719.N0947.d009460 a y v mu t) =
      Real.sqrt (2 * Real.pi) * (y / v) := by
  rw [_root_.GD.N0232.N0719.N0947.d009469 ha hv y]
  field_simp [ha.ne', hv.ne']


def d009472 {I : Type*} [DecidableEq I]
    (i : I) (t : ℝ) : I → ℝ :=
  fun j => if j = i then t else 0



theorem d009473
    {I : Type*} [DecidableEq I] [Nontrivial I]
    (i : I) (t : ℝ) :
    ¬ ∀ j, 0 < _root_.GD.N0232.N0719.N0947.d009472 i t j := by
  obtain ⟨j, hji⟩ := exists_ne i
  intro hpos
  have hj := hpos j
  simp [_root_.GD.N0232.N0719.N0947.d009472, hji] at hj




def d009474 (v : ℝ) : ℝ := 1 / v


def d009475 (y v : ℝ) : ℝ := y / v


def d009476
    {I : Type*} [Fintype I] (y v : I → ℝ) : ℝ :=
  (∑ i, _root_.GD.N0232.N0719.N0947.d009475 (y i) (v i)) /
    (∑ i, _root_.GD.N0232.N0719.N0947.d009474 (v i))



theorem d009477
    {I : Type*} [Fintype I] (y v : I → ℝ) :
    _root_.GD.N0232.N0719.N0947.d009476 y v =
      (∑ i, y i / v i) / (∑ i, 1 / v i) := by
  rfl



theorem d009478
    {I : Type*} [Fintype I] [Nonempty I]
    (v : I → ℝ) (hv : ∀ i, 0 < v i) :
    0 < ∑ i, _root_.GD.N0232.N0719.N0947.d009474 (v i) := by
  unfold _root_.GD.N0232.N0719.N0947.d009474
  apply Finset.sum_pos'
  · intro i _
    exact (one_div_pos.mpr (hv i)).le
  · classical
    let i : I := Classical.choice inferInstance
    exact ⟨i, Finset.mem_univ i, one_div_pos.mpr (hv i)⟩

end

end GD.N0232.N0719.N0947

#print axioms _root_.GD.N0232.N0719.N0947.d009466
#print axioms _root_.GD.N0232.N0719.N0947.d009468
#print axioms _root_.GD.N0232.N0719.N0947.d009469
#print axioms _root_.GD.N0232.N0719.N0947.d009470
#print axioms _root_.GD.N0232.N0719.N0947.d009473
#print axioms _root_.GD.N0232.N0719.N0947.d009477
