import GD.Module0759
import GD.Module0627






















namespace GD
namespace N0232
namespace N0719
namespace N0860

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0919
open _root_.GD.N0238.N0753
open _root_.GD.N0238.N0754

noncomputable section


def d011425 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i, s.mean i


def d011426 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : Prop :=
  ∀ i, 0 ≤ s.meanVariance i

theorem d011427
    {k : ℕ} {s : _root_.GD.N0232.N0719.N0900.d009096 k} (hs : _root_.GD.N0232.N0719.N0860.d011426 s)
    (shift dilation : ℝ) :
    _root_.GD.N0232.N0719.N0860.d011426 (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) := by
  intro i
  exact mul_nonneg (sq_nonneg dilation) (hs i)


theorem d011428
    {k : ℕ} (hk : 0 < k)
    (shift dilation : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) =
      shift + dilation * _root_.GD.N0232.N0719.N0860.d011425 s := by
  unfold _root_.GD.N0232.N0719.N0860.d011425 _root_.GD.N0232.N0719.N0900.d009101
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp [hkR]



def d011429 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0238.N0754.d004717 k :=
  (fun i ↦ s.mean i - _root_.GD.N0232.N0719.N0860.d011425 s,
    fun i ↦ Real.sqrt (s.meanVariance i))



def d011430 {k : ℕ} (z : _root_.GD.N0238.N0754.d004717 k) : Prop :=
  (∑ i, z.1 i) = 0 ∧ ∀ i, 0 ≤ z.2 i


theorem d011431
    {k : ℕ} (hk : 0 < k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hs : ∀ i, 0 ≤ s.meanVariance i) :
    _root_.GD.N0232.N0719.N0860.d011430 (_root_.GD.N0232.N0719.N0860.d011429 s) := by
  constructor
  · unfold _root_.GD.N0232.N0719.N0860.d011429 _root_.GD.N0232.N0719.N0860.d011425
    simp only [Prod.fst, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp [hkR]
    ring
  · intro i
    exact Real.sqrt_nonneg _


theorem d011432
    {k : ℕ} {z : _root_.GD.N0238.N0754.d004717 k}
    (hz : _root_.GD.N0232.N0719.N0860.d011430 z)
    (a : ℝ) (ha : 0 ≤ a) :
    _root_.GD.N0232.N0719.N0860.d011430 (a • z) := by
  constructor
  · change (∑ i, a * z.1 i) = 0
    rw [← Finset.mul_sum, hz.1, mul_zero]
  · intro i
    change 0 ≤ a * z.2 i
    exact mul_nonneg ha (hz.2 i)



theorem d011433
    {k : ℕ} (hk : 0 < k)
    (shift dilation : ℝ) (hdilation : 0 ≤ dilation)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0860.d011429 (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) =
      dilation • _root_.GD.N0232.N0719.N0860.d011429 s := by
  apply Prod.ext
  · funext i
    change
      shift + dilation * s.mean i -
          _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) =
        dilation * (s.mean i - _root_.GD.N0232.N0719.N0860.d011425 s)
    rw [_root_.GD.N0232.N0719.N0860.d011428 hk]
    ring
  · funext i
    change Real.sqrt (dilation ^ 2 * s.meanVariance i) =
      dilation * Real.sqrt (s.meanVariance i)
    rw [Real.sqrt_mul (sq_nonneg dilation), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hdilation]


def d011434 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  ‖_root_.GD.N0232.N0719.N0860.d011429 s‖

theorem d011435 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    0 ≤ _root_.GD.N0232.N0719.N0860.d011434 s := norm_nonneg _

theorem d011436 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    0 < _root_.GD.N0232.N0719.N0860.d011434 s ↔ _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0 := by
  exact norm_pos_iff



theorem d011437
    {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hr : _root_.GD.N0232.N0719.N0860.d011434 s = 0) (i : Fin k) :
    s.mean i = _root_.GD.N0232.N0719.N0860.d011425 s := by
  have hfiber : _root_.GD.N0232.N0719.N0860.d011429 s = 0 := by
    exact norm_eq_zero.mp hr
  have hi := congrArg (fun z : _root_.GD.N0238.N0754.d004717 k ↦ z.1 i) hfiber
  change s.mean i - _root_.GD.N0232.N0719.N0860.d011425 s = 0 at hi
  linarith



theorem d011438
    {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : _root_.GD.N0232.N0719.N0860.d011426 s)
    (hr : _root_.GD.N0232.N0719.N0860.d011434 s = 0) (i : Fin k) :
    s.meanVariance i = 0 := by
  have hfiber : _root_.GD.N0232.N0719.N0860.d011429 s = 0 := by
    exact norm_eq_zero.mp hr
  have hi := congrArg (fun z : _root_.GD.N0238.N0754.d004717 k ↦ z.2 i) hfiber
  change Real.sqrt (s.meanVariance i) = 0 at hi
  calc
    s.meanVariance i = (Real.sqrt (s.meanVariance i)) ^ 2 := by
      symm
      exact Real.sq_sqrt (hs i)
    _ = 0 := by rw [hi]; norm_num


theorem d011439
    {k : ℕ} (hk : 0 < k)
    (shift dilation : ℝ) (hdilation : 0 ≤ dilation)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0860.d011434 (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) =
      dilation * _root_.GD.N0232.N0719.N0860.d011434 s := by
  unfold _root_.GD.N0232.N0719.N0860.d011434
  rw [_root_.GD.N0232.N0719.N0860.d011433 hk shift dilation hdilation]
  simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdilation]



abbrev d011440 (k : ℕ) :=
  {u : _root_.GD.N0238.N0753.d004398 (_root_.GD.N0238.N0754.d004717 k) //
    _root_.GD.N0232.N0719.N0860.d011430 (u : _root_.GD.N0238.N0754.d004717 k)}



def d011441
    {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0)
    (hcone : _root_.GD.N0232.N0719.N0860.d011430 (_root_.GD.N0232.N0719.N0860.d011429 s)) :
    _root_.GD.N0232.N0719.N0860.d011440 k :=
  ⟨_root_.GD.N0238.N0753.d004399 (_root_.GD.N0232.N0719.N0860.d011429 s) hz, by
    change _root_.GD.N0232.N0719.N0860.d011430
      ((‖_root_.GD.N0232.N0719.N0860.d011429 s‖⁻¹ : ℝ) • _root_.GD.N0232.N0719.N0860.d011429 s)
    exact _root_.GD.N0232.N0719.N0860.d011432 hcone _
      (inv_nonneg.mpr (norm_nonneg _))⟩


theorem d011442
    {k : ℕ} (hk : 0 < k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0)
    (hcone : _root_.GD.N0232.N0719.N0860.d011430 (_root_.GD.N0232.N0719.N0860.d011429 s))
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0860.d011441 (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s)
        (by
          rw [_root_.GD.N0232.N0719.N0860.d011433 hk shift dilation hdilation.le]
          exact smul_ne_zero hdilation.ne' hz)
        (by
          rw [_root_.GD.N0232.N0719.N0860.d011433 hk shift dilation hdilation.le]
          exact _root_.GD.N0232.N0719.N0860.d011432 hcone dilation hdilation.le) =
      _root_.GD.N0232.N0719.N0860.d011441 s hz hcone := by
  apply Subtype.ext
  apply Subtype.ext
  change
    (‖_root_.GD.N0232.N0719.N0860.d011429
        (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s)‖⁻¹ : ℝ) •
        _root_.GD.N0232.N0719.N0860.d011429
          (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) =
      (‖_root_.GD.N0232.N0719.N0860.d011429 s‖⁻¹ : ℝ) • _root_.GD.N0232.N0719.N0860.d011429 s
  rw [_root_.GD.N0232.N0719.N0860.d011433 hk shift dilation hdilation.le]
  exact congrArg Subtype.val
    (_root_.GD.N0238.N0753.d004400 dilation hdilation (_root_.GD.N0232.N0719.N0860.d011429 s) hz)



def d011443 {k : ℕ}
    (u : _root_.GD.N0232.N0719.N0860.d011440 k) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean i := (u : _root_.GD.N0238.N0754.d004717 k).1 i
  meanVariance i := ((u : _root_.GD.N0238.N0754.d004717 k).2 i) ^ 2



def d011444 {k : ℕ}
    (center radius : ℝ) (u : _root_.GD.N0232.N0719.N0860.d011440 k) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean i := center + radius * (u : _root_.GD.N0238.N0754.d004717 k).1 i
  meanVariance i := (radius * (u : _root_.GD.N0238.N0754.d004717 k).2 i) ^ 2

theorem d011445
    {k : ℕ} (center radius : ℝ)
    (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011444 center radius u =
      _root_.GD.N0232.N0719.N0900.d009101 center radius
        (_root_.GD.N0232.N0719.N0860.d011443 u) := by
  ext i <;> simp [_root_.GD.N0232.N0719.N0860.d011444, _root_.GD.N0232.N0719.N0860.d011443,
    _root_.GD.N0232.N0719.N0900.d009101] <;>
    ring


theorem d011446
    {k : ℕ} (hk : 0 < k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hs : ∀ i, 0 ≤ s.meanVariance i)
    (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0) :
    _root_.GD.N0232.N0719.N0860.d011444 (_root_.GD.N0232.N0719.N0860.d011425 s) (_root_.GD.N0232.N0719.N0860.d011434 s)
        (_root_.GD.N0232.N0719.N0860.d011441 s hz (_root_.GD.N0232.N0719.N0860.d011431 hk s hs)) = s := by
  let u := _root_.GD.N0232.N0719.N0860.d011441 s hz (_root_.GD.N0232.N0719.N0860.d011431 hk s hs)
  have hreconstruct :
      _root_.GD.N0232.N0719.N0860.d011434 s • (u : _root_.GD.N0238.N0754.d004717 k) = _root_.GD.N0232.N0719.N0860.d011429 s := by
    exact _root_.GD.N0238.N0753.d004408 (_root_.GD.N0232.N0719.N0860.d011429 s) hz
  apply _root_.GD.N0232.N0719.N0900.d009096.ext
  · funext i
    have hmean := congrArg (fun z : _root_.GD.N0238.N0754.d004717 k ↦ z.1 i)
      hreconstruct
    change _root_.GD.N0232.N0719.N0860.d011434 s * (u : _root_.GD.N0238.N0754.d004717 k).1 i =
      s.mean i - _root_.GD.N0232.N0719.N0860.d011425 s at hmean
    change _root_.GD.N0232.N0719.N0860.d011425 s + _root_.GD.N0232.N0719.N0860.d011434 s *
      (u : _root_.GD.N0238.N0754.d004717 k).1 i = s.mean i
    linarith
  · funext i
    have hscale := congrArg (fun z : _root_.GD.N0238.N0754.d004717 k ↦ z.2 i)
      hreconstruct
    change _root_.GD.N0232.N0719.N0860.d011434 s * (u : _root_.GD.N0238.N0754.d004717 k).2 i =
      Real.sqrt (s.meanVariance i) at hscale
    change (_root_.GD.N0232.N0719.N0860.d011434 s * (u : _root_.GD.N0238.N0754.d004717 k).2 i) ^ 2 =
      s.meanVariance i
    rw [hscale, Real.sq_sqrt (hs i)]


def d011447 {k : ℕ}
    (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) : Prop :=
  ∀ (shift dilation : ℝ), 0 < dilation → ∀ s,
    d (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) =
      shift + dilation * d s


def d011448 {k : ℕ}
    (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) : Prop :=
  ∀ (shift dilation : ℝ), 0 < dilation → ∀ s,
    _root_.GD.N0232.N0719.N0860.d011426 s →
      d (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) =
        shift + dilation * d s

theorem d011449
    {k : ℕ} {d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ}
    (hd : _root_.GD.N0232.N0719.N0860.d011447 d) :
    _root_.GD.N0232.N0719.N0860.d011448 d := by
  intro shift dilation hdilation s hs
  exact hd shift dilation hdilation s



theorem d011450
    {k : ℕ} (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ)
    (hd : _root_.GD.N0232.N0719.N0860.d011448 d)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : _root_.GD.N0232.N0719.N0860.d011426 s)
    (hr : _root_.GD.N0232.N0719.N0860.d011434 s = 0) :
    d s = _root_.GD.N0232.N0719.N0860.d011425 s := by
  have hfixed :
      _root_.GD.N0232.N0719.N0900.d009101 (-_root_.GD.N0232.N0719.N0860.d011425 s) 2 s = s := by
    apply _root_.GD.N0232.N0719.N0900.d009096.ext
    · funext i
      change -_root_.GD.N0232.N0719.N0860.d011425 s + 2 * s.mean i = s.mean i
      rw [_root_.GD.N0232.N0719.N0860.d011437 s hr i]
      ring
    · funext i
      change 2 ^ 2 * s.meanVariance i = s.meanVariance i
      rw [_root_.GD.N0232.N0719.N0860.d011438 s hs hr i]
      ring
  have hcov := hd (-_root_.GD.N0232.N0719.N0860.d011425 s) 2 (by norm_num) s hs
  rw [hfixed] at hcov
  linarith



theorem d011451
    {k : ℕ} (hk : 0 < k)
    (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) (hd : _root_.GD.N0232.N0719.N0860.d011447 d)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : ∀ i, 0 ≤ s.meanVariance i)
    (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0) :
    d s = _root_.GD.N0232.N0719.N0860.d011425 s + _root_.GD.N0232.N0719.N0860.d011434 s *
      d (_root_.GD.N0232.N0719.N0860.d011443
        (_root_.GD.N0232.N0719.N0860.d011441 s hz (_root_.GD.N0232.N0719.N0860.d011431 hk s hs))) := by
  let u := _root_.GD.N0232.N0719.N0860.d011441 s hz (_root_.GD.N0232.N0719.N0860.d011431 hk s hs)
  have hr : 0 < _root_.GD.N0232.N0719.N0860.d011434 s :=
    (_root_.GD.N0232.N0719.N0860.d011436 s).2 hz
  have hcov := hd (_root_.GD.N0232.N0719.N0860.d011425 s) (_root_.GD.N0232.N0719.N0860.d011434 s) hr
    (_root_.GD.N0232.N0719.N0860.d011443 u)
  rw [← _root_.GD.N0232.N0719.N0860.d011445] at hcov
  rw [_root_.GD.N0232.N0719.N0860.d011446 hk s hs hz] at hcov
  exact hcov


theorem d011452
    {k : ℕ} (hk : 0 < k)
    (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ)
    (hd : _root_.GD.N0232.N0719.N0860.d011448 d)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : _root_.GD.N0232.N0719.N0860.d011426 s)
    (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0) :
    d s = _root_.GD.N0232.N0719.N0860.d011425 s + _root_.GD.N0232.N0719.N0860.d011434 s *
      d (_root_.GD.N0232.N0719.N0860.d011443
        (_root_.GD.N0232.N0719.N0860.d011441 s hz (_root_.GD.N0232.N0719.N0860.d011431 hk s hs))) := by
  let u := _root_.GD.N0232.N0719.N0860.d011441 s hz (_root_.GD.N0232.N0719.N0860.d011431 hk s hs)
  have hr : 0 < _root_.GD.N0232.N0719.N0860.d011434 s :=
    (_root_.GD.N0232.N0719.N0860.d011436 s).2 hz
  have hcov := hd (_root_.GD.N0232.N0719.N0860.d011425 s) (_root_.GD.N0232.N0719.N0860.d011434 s) hr
    (_root_.GD.N0232.N0719.N0860.d011443 u) (by
      intro i
      exact sq_nonneg ((u : _root_.GD.N0238.N0754.d004717 k).2 i))
  rw [← _root_.GD.N0232.N0719.N0860.d011445] at hcov
  rw [_root_.GD.N0232.N0719.N0860.d011446 hk s hs hz] at hcov
  exact hcov



def d011453
    {k : ℕ} (phi : _root_.GD.N0232.N0719.N0860.d011440 k → ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0)
    (hcone : _root_.GD.N0232.N0719.N0860.d011430 (_root_.GD.N0232.N0719.N0860.d011429 s)) : ℝ :=
  _root_.GD.N0232.N0719.N0860.d011425 s + _root_.GD.N0232.N0719.N0860.d011434 s * phi (_root_.GD.N0232.N0719.N0860.d011441 s hz hcone)




theorem d011454
    {k : ℕ} (hk : 0 < k)
    (phi : _root_.GD.N0232.N0719.N0860.d011440 k → ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0)
    (hcone : _root_.GD.N0232.N0719.N0860.d011430 (_root_.GD.N0232.N0719.N0860.d011429 s))
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0860.d011453 phi (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s)
        (by
          rw [_root_.GD.N0232.N0719.N0860.d011433 hk shift dilation hdilation.le]
          exact smul_ne_zero hdilation.ne' hz)
        (by
          rw [_root_.GD.N0232.N0719.N0860.d011433 hk shift dilation hdilation.le]
          exact _root_.GD.N0232.N0719.N0860.d011432 hcone dilation hdilation.le) =
      shift + dilation * _root_.GD.N0232.N0719.N0860.d011453 phi s hz hcone := by
  unfold _root_.GD.N0232.N0719.N0860.d011453
  rw [_root_.GD.N0232.N0719.N0860.d011428 hk,
    _root_.GD.N0232.N0719.N0860.d011439 hk shift dilation hdilation.le,
    _root_.GD.N0232.N0719.N0860.d011442 hk s hz hcone shift dilation hdilation]
  ring







noncomputable def d011455
    {k : ℕ} (hk : 0 < k)
    (phi : _root_.GD.N0232.N0719.N0860.d011440 k → ℝ) : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ := by
  classical
  exact fun s ↦
      if hs : _root_.GD.N0232.N0719.N0860.d011426 s then
        if hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0 then
          _root_.GD.N0232.N0719.N0860.d011425 s + _root_.GD.N0232.N0719.N0860.d011434 s *
            phi (_root_.GD.N0232.N0719.N0860.d011441 s hz
              (_root_.GD.N0232.N0719.N0860.d011431 hk s hs))
        else _root_.GD.N0232.N0719.N0860.d011425 s
      else 0



theorem d011456
    {k : ℕ} (hk : 0 < k)
    (phi : _root_.GD.N0232.N0719.N0860.d011440 k → ℝ) :
    _root_.GD.N0232.N0719.N0860.d011448 (_root_.GD.N0232.N0719.N0860.d011455 hk phi) := by
  intro shift dilation hdilation s hs
  have hs' : _root_.GD.N0232.N0719.N0860.d011426
      (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) :=
    _root_.GD.N0232.N0719.N0860.d011427 hs shift dilation
  by_cases hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0
  · have hz' : _root_.GD.N0232.N0719.N0860.d011429
        (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) ≠ 0 := by
      rw [_root_.GD.N0232.N0719.N0860.d011433 hk shift dilation hdilation.le]
      exact smul_ne_zero hdilation.ne' hz
    simpa only [_root_.GD.N0232.N0719.N0860.d011455, dif_pos hs, dif_pos hs', dif_pos hz, dif_pos hz',
      _root_.GD.N0232.N0719.N0860.d011453] using
      (_root_.GD.N0232.N0719.N0860.d011454 hk phi s hz
        (_root_.GD.N0232.N0719.N0860.d011431 hk s hs)
        shift dilation hdilation)
  · have hzero : _root_.GD.N0232.N0719.N0860.d011429 s = 0 := not_ne_iff.mp hz
    have hzero' : _root_.GD.N0232.N0719.N0860.d011429
        (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) = 0 := by
      rw [_root_.GD.N0232.N0719.N0860.d011433 hk shift dilation hdilation.le,
        hzero, smul_zero]
    have hz' : ¬ _root_.GD.N0232.N0719.N0860.d011429
        (_root_.GD.N0232.N0719.N0900.d009101 shift dilation s) ≠ 0 :=
      not_ne_iff.mpr hzero'
    simp only [_root_.GD.N0232.N0719.N0860.d011455, dif_pos hs, dif_pos hs', dif_neg hz, dif_neg hz']
    rw [_root_.GD.N0232.N0719.N0860.d011428 hk]


def d011457
    {k : ℕ} (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) :
    _root_.GD.N0232.N0719.N0860.d011440 k → ℝ :=
  fun u ↦ d (_root_.GD.N0232.N0719.N0860.d011443 u)



def d011458
    {k : ℕ} (hk : 0 < k) (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) :
    _root_.GD.N0232.N0719.N0900.d009096 k → ℝ :=
  _root_.GD.N0232.N0719.N0860.d011455 hk (_root_.GD.N0232.N0719.N0860.d011457 d)



theorem d011459
    {k : ℕ} (hk : 0 < k)
    (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ)
    (hd : _root_.GD.N0232.N0719.N0860.d011448 d)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : _root_.GD.N0232.N0719.N0860.d011426 s) :
    _root_.GD.N0232.N0719.N0860.d011458 hk d s = d s := by
  unfold _root_.GD.N0232.N0719.N0860.d011458 _root_.GD.N0232.N0719.N0860.d011455
  rw [dif_pos hs]
  by_cases hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0
  · rw [dif_pos hz]
    exact (_root_.GD.N0232.N0719.N0860.d011452 hk d hd s hs hz).symm
  · rw [dif_neg hz]
    exact (_root_.GD.N0232.N0719.N0860.d011450 d hd s hs
      (norm_eq_zero.mpr (not_ne_iff.mp hz))).symm



theorem d011460
    {k : ℕ} (hk : 0 < k)
    (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : _root_.GD.N0232.N0719.N0860.d011426 s) :
    _root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0860.d011458 hk d) s = _root_.GD.N0232.N0719.N0860.d011458 hk d s := by
  exact _root_.GD.N0232.N0719.N0860.d011459 hk (_root_.GD.N0232.N0719.N0860.d011458 hk d)
    (_root_.GD.N0232.N0719.N0860.d011456 hk (_root_.GD.N0232.N0719.N0860.d011457 d)) s hs

end

end N0860
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0860.d011446
#print axioms _root_.GD.N0232.N0719.N0860.d011451
#print axioms _root_.GD.N0232.N0719.N0860.d011454
