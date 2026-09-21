import GD.Module0647

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0954

noncomputable section




def d009503 {k : ℕ} (shape : Fin k → ℝ) : ℝ :=
  ∑ i, shape i

theorem d009504
    {k : ℕ} (hk : 0 < k) {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i) :
    0 < _root_.GD.N0232.N0719.N0954.d009503 shape := by
  unfold _root_.GD.N0232.N0719.N0954.d009503
  exact Finset.sum_pos
    (fun i _ => hshape i)
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩


def d009505 {k : ℕ} (rate : Fin k → ℝ) : ℝ :=
  ∑ i, rate i


def d009506 {k : ℕ} (rate : Fin k → ℝ) (i : Fin k) : ℝ :=
  rate i / _root_.GD.N0232.N0719.N0954.d009505 rate


def d009507 {k : ℕ}
    (shape rate : Fin k → ℝ) : ℝ :=
  ∏ i, (rate i) ^ (shape i) / Real.Gamma (shape i)



def d009508 {k : ℕ}
    (shape rate p : Fin k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0954.d009507 shape rate *
    Real.Gamma (_root_.GD.N0232.N0719.N0954.d009503 shape) *
    (_root_.GD.N0232.N0719.N0951.d003587 rate p) ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape) *
    (∏ i, p i ^ (-(shape i + 1)))










def d009509 {k : ℕ}
    (shape rate : Fin k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0954.d009507 shape rate *
    Real.Gamma (_root_.GD.N0232.N0719.N0954.d009503 shape) *
    (_root_.GD.N0232.N0719.N0954.d009505 rate) ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape)




def d009510 {k : ℕ}
    (shape q p : Fin k → ℝ) : ℝ :=
  (∏ i, p i ^ (-(shape i + 1))) *
    (_root_.GD.N0232.N0719.N0951.d003587 q p) ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape)

theorem d009511
    {k : ℕ} (hk : 0 < k) {rate : Fin k → ℝ}
    (hrate : ∀ i, 0 < rate i) :
    0 < _root_.GD.N0232.N0719.N0954.d009505 rate := by
  unfold _root_.GD.N0232.N0719.N0954.d009505
  exact Finset.sum_pos
    (fun i _ => hrate i)
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩

theorem d009512
    {k : ℕ} (hk : 0 < k) {rate : Fin k → ℝ}
    (hrate : ∀ i, 0 < rate i) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0954.d009506 rate i :=
  div_pos (hrate i) (_root_.GD.N0232.N0719.N0954.d009511 hk hrate)

theorem d009513
    {k : ℕ} (hk : 0 < k) {rate : Fin k → ℝ}
    (hrate : ∀ i, 0 < rate i) :
    _root_.GD.N0232.N0719.N0951.d003581 (_root_.GD.N0232.N0719.N0954.d009506 rate) := by
  constructor
  · intro i
    exact (_root_.GD.N0232.N0719.N0954.d009512 hk hrate i).le
  · unfold _root_.GD.N0232.N0719.N0954.d009506
    rw [← Finset.sum_div, _root_.GD.N0232.N0719.N0954.d009505]
    exact div_self (_root_.GD.N0232.N0719.N0954.d009511 hk hrate).ne'



theorem d009514
    {k : ℕ} (hk : 0 < k)
    {rate p : Fin k → ℝ}
    (hrate : ∀ i, 0 < rate i) :
    _root_.GD.N0232.N0719.N0951.d003587 rate p =
      _root_.GD.N0232.N0719.N0954.d009505 rate *
        _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0954.d009506 rate) p := by
  have hS := (_root_.GD.N0232.N0719.N0954.d009511 hk hrate).ne'
  unfold _root_.GD.N0232.N0719.N0951.d003587 _root_.GD.N0232.N0719.N0954.d009506
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hS]








theorem d009515
    {k : ℕ} (hk : 0 < k)
    {shape rate p : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (hp : ∀ i, 0 < p i) :
    _root_.GD.N0232.N0719.N0954.d009508 shape rate p =
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        _root_.GD.N0232.N0719.N0954.d009510 shape (_root_.GD.N0232.N0719.N0954.d009506 rate) p := by
  have hS : 0 < _root_.GD.N0232.N0719.N0954.d009505 rate :=
    _root_.GD.N0232.N0719.N0954.d009511 hk hrate
  have hq : _root_.GD.N0232.N0719.N0951.d003581 (_root_.GD.N0232.N0719.N0954.d009506 rate) :=
    _root_.GD.N0232.N0719.N0954.d009513 hk hrate
  have hqRate :
      0 < _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0954.d009506 rate) p := by
    unfold _root_.GD.N0232.N0719.N0951.d003587
    exact Finset.sum_pos'
      (fun i _ => by
        exact div_nonneg (hq.1 i) (hp i).le)
      ⟨⟨0, hk⟩, Finset.mem_univ _, by
        exact div_pos (_root_.GD.N0232.N0719.N0954.d009512 hk hrate ⟨0, hk⟩)
          (hp ⟨0, hk⟩)⟩
  rw [_root_.GD.N0232.N0719.N0954.d009508,
    _root_.GD.N0232.N0719.N0954.d009509, _root_.GD.N0232.N0719.N0954.d009510,
    _root_.GD.N0232.N0719.N0954.d009514 hk hrate,
    Real.mul_rpow hS.le hqRate.le]
  ring

theorem d009516
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i) :
    0 < _root_.GD.N0232.N0719.N0954.d009509 shape rate := by
  unfold _root_.GD.N0232.N0719.N0954.d009509 _root_.GD.N0232.N0719.N0954.d009507
  have hA := _root_.GD.N0232.N0719.N0954.d009504 hk hshape
  have hS := _root_.GD.N0232.N0719.N0954.d009511 hk hrate
  exact mul_pos
    (mul_pos
      (Finset.prod_pos fun i _ =>
        div_pos
          (Real.rpow_pos_of_pos (hrate i) (shape i))
          (Real.Gamma_pos_of_pos (hshape i)))
      (Real.Gamma_pos_of_pos hA))
    (Real.rpow_pos_of_pos hS (-_root_.GD.N0232.N0719.N0954.d009503 shape))


def d009517 {k : ℕ}
    (shape : Fin k → ℝ) : ℝ :=
  (∏ i, (_root_.GD.N0232.N0719.N0951.d003579 k) ^ (-(shape i + 1))) *
    (4 * (k : ℝ) / 3) ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape)


def d009518 {k : ℕ}
    (shape : Fin k → ℝ) : ℝ :=
  (∏ i, (_root_.GD.N0232.N0719.N0951.d003578 k) ^ (-(shape i + 1))) *
    (4 * (k : ℝ) / 5) ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape)

theorem d009519
    {k : ℕ} (hk : 0 < k) {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i) :
    0 < _root_.GD.N0232.N0719.N0954.d009517 shape := by
  unfold _root_.GD.N0232.N0719.N0954.d009517
  apply mul_pos
  · exact Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos (_root_.GD.N0232.N0719.N0951.d003589 hk) _
  · have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    exact Real.rpow_pos_of_pos (by positivity) _

theorem d009520
    {k : ℕ} (hk : 0 < k) {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i) :
    0 < _root_.GD.N0232.N0719.N0954.d009518 shape := by
  unfold _root_.GD.N0232.N0719.N0954.d009518
  apply mul_pos
  · exact Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos (_root_.GD.N0232.N0719.N0951.d003588 hk) _
  · have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    exact Real.rpow_pos_of_pos (by positivity) _





theorem d009521
    {k : ℕ} (hk : 0 < k)
    {shape q p : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hq : _root_.GD.N0232.N0719.N0951.d003581 q)
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    _root_.GD.N0232.N0719.N0954.d009517 shape ≤
      _root_.GD.N0232.N0719.N0954.d009510 shape q p := by
  have hcoord :
      ∀ i : Fin k,
        _root_.GD.N0232.N0719.N0951.d003579 k ^ (-(shape i + 1)) ≤
          p i ^ (-(shape i + 1)) := by
    intro i
    exact Real.rpow_le_rpow_of_nonpos
      (_root_.GD.N0232.N0719.N0951.d003590 hk hp i)
      (hp i).2
      (by linarith [hshape i])
  have hprod :
      (∏ i, _root_.GD.N0232.N0719.N0951.d003579 k ^ (-(shape i + 1))) ≤
        ∏ i, p i ^ (-(shape i + 1)) :=
    Finset.prod_le_prod
      (fun i _ => (Real.rpow_pos_of_pos
        (_root_.GD.N0232.N0719.N0951.d003589 hk) _).le)
      (fun i _ => hcoord i)
  have hrate := _root_.GD.N0232.N0719.N0951.d003601 hk hq hp
  have hratePos := _root_.GD.N0232.N0719.N0951.d003602 hk hq hp
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratePow :
      (4 * (k : ℝ) / 3) ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape) ≤
        _root_.GD.N0232.N0719.N0951.d003587 q p ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape) :=
    Real.rpow_le_rpow_of_nonpos hratePos hrate
      (neg_nonpos.mpr (_root_.GD.N0232.N0719.N0954.d009504 hk hshape).le)
  unfold _root_.GD.N0232.N0719.N0954.d009517 _root_.GD.N0232.N0719.N0954.d009510
  exact mul_le_mul hprod hratePow
    (Real.rpow_nonneg (by positivity) _)
    (Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg
        (_root_.GD.N0232.N0719.N0951.d003590 hk hp i).le _)





theorem d009522
    {k : ℕ} (hk : 0 < k)
    {shape q p : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hq : _root_.GD.N0232.N0719.N0951.d003581 q)
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    _root_.GD.N0232.N0719.N0954.d009510 shape q p ≤
      _root_.GD.N0232.N0719.N0954.d009518 shape := by
  have hcoord :
      ∀ i : Fin k,
        p i ^ (-(shape i + 1)) ≤
          _root_.GD.N0232.N0719.N0951.d003578 k ^ (-(shape i + 1)) := by
    intro i
    exact Real.rpow_le_rpow_of_nonpos
      (_root_.GD.N0232.N0719.N0951.d003588 hk)
      (hp i).1
      (by linarith [hshape i])
  have hprod :
      (∏ i, p i ^ (-(shape i + 1))) ≤
        ∏ i, _root_.GD.N0232.N0719.N0951.d003578 k ^ (-(shape i + 1)) :=
    Finset.prod_le_prod
      (fun i _ =>
        (Real.rpow_pos_of_pos
          (_root_.GD.N0232.N0719.N0951.d003590 hk hp i)
          (-(shape i + 1))).le)
      (fun i _ => hcoord i)
  have hrate := _root_.GD.N0232.N0719.N0951.d003600 hk hq hp
  have hrateFloor : 0 < 4 * (k : ℝ) / 5 := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hratePow :
      _root_.GD.N0232.N0719.N0951.d003587 q p ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape) ≤
        (4 * (k : ℝ) / 5) ^ (-_root_.GD.N0232.N0719.N0954.d009503 shape) :=
    Real.rpow_le_rpow_of_nonpos hrateFloor hrate
      (neg_nonpos.mpr (_root_.GD.N0232.N0719.N0954.d009504 hk hshape).le)
  unfold _root_.GD.N0232.N0719.N0954.d009518 _root_.GD.N0232.N0719.N0954.d009510
  exact mul_le_mul hprod hratePow
    (Real.rpow_nonneg
      (_root_.GD.N0232.N0719.N0951.d003602 hk hq hp).le _)
    (Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg
        (_root_.GD.N0232.N0719.N0951.d003588 hk).le _)


theorem d009523
    {k : ℕ} (hk : 0 < k)
    {shape q p : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hq : _root_.GD.N0232.N0719.N0951.d003581 q)
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    0 < _root_.GD.N0232.N0719.N0954.d009517 shape ∧
      _root_.GD.N0232.N0719.N0954.d009517 shape ≤
        _root_.GD.N0232.N0719.N0954.d009510 shape q p ∧
      _root_.GD.N0232.N0719.N0954.d009510 shape q p ≤
        _root_.GD.N0232.N0719.N0954.d009518 shape ∧
      0 < _root_.GD.N0232.N0719.N0954.d009518 shape := by
  exact
    ⟨_root_.GD.N0232.N0719.N0954.d009519 hk hshape,
      _root_.GD.N0232.N0719.N0954.d009521 hk hshape hq hp,
      _root_.GD.N0232.N0719.N0954.d009522
        hk hshape hq hp,
      _root_.GD.N0232.N0719.N0954.d009520 hk hshape⟩























def d009524
    {X : Type*} [MeasurableSpace X]
    {k : ℕ} (μ : Measure X)
    (shape q : Fin k → ℝ)
    (p : X → Fin k → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0719.N0954.d009510 shape q (p x) ∂μ


def d009525
    {X : Type*} [MeasurableSpace X]
    {k : ℕ} (μ : Measure X)
    (shape q : Fin k → ℝ)
    (p : X → Fin k → ℝ)
    (F : X → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0719.N0954.d009510 shape q (p x) * F x ∂μ










theorem d009526
    {X : Type*} [MeasurableSpace X]
    {k : ℕ} (hk : 0 < k)
    (μ : Measure X) [IsProbabilityMeasure μ]
    {shape q : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hq : _root_.GD.N0232.N0719.N0951.d003581 q)
    (p : X → Fin k → ℝ)
    (hp : ∀ᵐ x ∂μ, _root_.GD.N0232.N0719.N0951.d003580 (p x))
    (F : X → ℝ)
    (hF : Integrable F μ)
    (hF_nonneg : ∀ᵐ x ∂μ, 0 ≤ F x)
    (hkernel :
      Integrable
        (fun x => _root_.GD.N0232.N0719.N0954.d009510 shape q (p x)) μ)
    (hmoment :
      Integrable
        (fun x =>
          _root_.GD.N0232.N0719.N0954.d009510 shape q (p x) * F x) μ) :
    (_root_.GD.N0232.N0719.N0954.d009517 shape / _root_.GD.N0232.N0719.N0954.d009518 shape) *
          _root_.GD.N0232.N0719.N0954.d009524 μ shape q p *
          (∫ x, F x ∂μ) ≤
      _root_.GD.N0232.N0719.N0954.d009525 μ shape q p F := by
  let L := _root_.GD.N0232.N0719.N0954.d009517 shape
  let U := _root_.GD.N0232.N0719.N0954.d009518 shape
  let Z := _root_.GD.N0232.N0719.N0954.d009524 μ shape q p
  let A := ∫ x, F x ∂μ
  let B := _root_.GD.N0232.N0719.N0954.d009525 μ shape q p F
  have hLpos : 0 < L := by
    exact _root_.GD.N0232.N0719.N0954.d009519 hk hshape
  have hUpos : 0 < U := by
    exact _root_.GD.N0232.N0719.N0954.d009520 hk hshape
  have hA : 0 ≤ A := by
    exact integral_nonneg_of_ae hF_nonneg
  have hlower :
      L * A ≤ B := by
    dsimp [A, B, _root_.GD.N0232.N0719.N0954.d009525]
    rw [← integral_const_mul]
    apply integral_mono_ae (hF.const_mul L) hmoment
    filter_upwards [hp, hF_nonneg] with x hpx hFx
    exact mul_le_mul_of_nonneg_right
      (_root_.GD.N0232.N0719.N0954.d009521 hk hshape hq hpx) hFx
  have hmassUpper :
      Z ≤ U := by
    dsimp [Z, _root_.GD.N0232.N0719.N0954.d009524]
    calc
      (∫ x, _root_.GD.N0232.N0719.N0954.d009510 shape q (p x) ∂μ) ≤
          ∫ _ : X, U ∂μ := by
        apply integral_mono_ae hkernel (integrable_const U)
        filter_upwards [hp] with x hpx
        exact
          _root_.GD.N0232.N0719.N0954.d009522
            hk hshape hq hpx
      _ = U := by simp
  have hcoefficient :
      0 ≤ (L / U) * A :=
    mul_nonneg (div_nonneg hLpos.le hUpos.le) hA
  calc
    (_root_.GD.N0232.N0719.N0954.d009517 shape / _root_.GD.N0232.N0719.N0954.d009518 shape) *
          _root_.GD.N0232.N0719.N0954.d009524 μ shape q p * (∫ x, F x ∂μ) =
        ((L / U) * A) * Z := by
          dsimp [L, U, A, Z]
          ring
    _ ≤ ((L / U) * A) * U :=
      mul_le_mul_of_nonneg_left hmassUpper hcoefficient
    _ = L * A := by
      field_simp [hUpos.ne']
      <;> ring
    _ ≤ B := hlower











theorem d009527
    {X : Type*} [MeasurableSpace X]
    {k : ℕ} (hk : 0 < k)
    (μ : Measure X) [IsProbabilityMeasure μ]
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (p : X → Fin k → ℝ)
    (hp : ∀ᵐ x ∂μ, _root_.GD.N0232.N0719.N0951.d003580 (p x))
    (F : X → ℝ)
    (hF : Integrable F μ)
    (hF_nonneg : ∀ᵐ x ∂μ, 0 ≤ F x)
    (hkernel :
      Integrable
        (fun x =>
          _root_.GD.N0232.N0719.N0954.d009510 shape
            (_root_.GD.N0232.N0719.N0954.d009506 rate) (p x)) μ)
    (hmoment :
      Integrable
        (fun x =>
          _root_.GD.N0232.N0719.N0954.d009510 shape
            (_root_.GD.N0232.N0719.N0954.d009506 rate) (p x) * F x) μ) :
    (_root_.GD.N0232.N0719.N0954.d009517 shape / _root_.GD.N0232.N0719.N0954.d009518 shape) *
          (_root_.GD.N0232.N0719.N0954.d009509 shape rate *
            _root_.GD.N0232.N0719.N0954.d009524 μ shape
              (_root_.GD.N0232.N0719.N0954.d009506 rate) p) *
          (∫ x, F x ∂μ) ≤
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        _root_.GD.N0232.N0719.N0954.d009525 μ shape
          (_root_.GD.N0232.N0719.N0954.d009506 rate) p F := by
  have hbase :=
    _root_.GD.N0232.N0719.N0954.d009526
      hk μ hshape
      (_root_.GD.N0232.N0719.N0954.d009513 hk hrate)
      p hp F hF hF_nonneg hkernel hmoment
  have hpref :
      0 ≤ _root_.GD.N0232.N0719.N0954.d009509 shape rate :=
    (_root_.GD.N0232.N0719.N0954.d009516 hk hshape hrate).le
  calc
    (_root_.GD.N0232.N0719.N0954.d009517 shape / _root_.GD.N0232.N0719.N0954.d009518 shape) *
          (_root_.GD.N0232.N0719.N0954.d009509 shape rate *
            _root_.GD.N0232.N0719.N0954.d009524 μ shape
              (_root_.GD.N0232.N0719.N0954.d009506 rate) p) *
          (∫ x, F x ∂μ) =
        _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          ((_root_.GD.N0232.N0719.N0954.d009517 shape / _root_.GD.N0232.N0719.N0954.d009518 shape) *
            _root_.GD.N0232.N0719.N0954.d009524 μ shape
              (_root_.GD.N0232.N0719.N0954.d009506 rate) p *
            (∫ x, F x ∂μ)) := by
              ring
    _ ≤ _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          _root_.GD.N0232.N0719.N0954.d009525 μ shape
            (_root_.GD.N0232.N0719.N0954.d009506 rate) p F :=
      mul_le_mul_of_nonneg_left hbase hpref

end

end GD.N0232.N0719.N0954
