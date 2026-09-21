import GD.Module0760




















open MeasureTheory

namespace GD
namespace N0232
namespace N0719
namespace N0942

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0238.N0753
open _root_.GD.N0238.N0754

local instance {k : ℕ} : DecidableEq (_root_.GD.N0232.N0719.N0900.d009096 k) := Classical.decEq _




theorem d011461
    {k : ℕ} (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011426 (_root_.GD.N0232.N0719.N0860.d011443 u) := by
  intro i
  exact sq_nonneg _


theorem d011462
    {k : ℕ} (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0860.d011443 u) = 0 := by
  unfold _root_.GD.N0232.N0719.N0860.d011425 _root_.GD.N0232.N0719.N0860.d011443
  have hsum : (∑ i, (u : _root_.GD.N0238.N0754.d004717 k).1 i) = 0 := u.property.1
  rw [hsum, mul_zero]


theorem d011463
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011429 (_root_.GD.N0232.N0719.N0860.d011443 u) =
      (u : _root_.GD.N0238.N0754.d004717 k) := by
  apply Prod.ext
  · funext i
    change
      (u : _root_.GD.N0238.N0754.d004717 k).1 i -
          _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0860.d011443 u) =
        (u : _root_.GD.N0238.N0754.d004717 k).1 i
    rw [_root_.GD.N0232.N0719.N0942.d011462]
    ring
  · funext i
    change Real.sqrt (((u : _root_.GD.N0238.N0754.d004717 k).2 i) ^ 2) =
      (u : _root_.GD.N0238.N0754.d004717 k).2 i
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (u.property.2 i)]


theorem d011464
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011434 (_root_.GD.N0232.N0719.N0860.d011443 u) = 1 := by
  unfold _root_.GD.N0232.N0719.N0860.d011434
  rw [_root_.GD.N0232.N0719.N0942.d011463 hk]
  exact u.1.property


theorem d011465
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011441 (_root_.GD.N0232.N0719.N0860.d011443 u)
        (by
          rw [_root_.GD.N0232.N0719.N0942.d011463 hk]
          exact ne_of_apply_ne norm (by simp [u.1.property]))
        (_root_.GD.N0232.N0719.N0860.d011431 hk (_root_.GD.N0232.N0719.N0860.d011443 u)
          (_root_.GD.N0232.N0719.N0942.d011461 u)) = u := by
  apply Subtype.ext
  apply Subtype.ext
  change
    (‖_root_.GD.N0232.N0719.N0860.d011429 (_root_.GD.N0232.N0719.N0860.d011443 u)‖⁻¹ : ℝ) •
        _root_.GD.N0232.N0719.N0860.d011429 (_root_.GD.N0232.N0719.N0860.d011443 u) =
      (u : _root_.GD.N0238.N0754.d004717 k)
  rw [_root_.GD.N0232.N0719.N0942.d011463 hk, u.1.property,
    inv_one, one_smul]


theorem d011466
    {k : ℕ} (hk : 0 < k)
    (phi : _root_.GD.N0232.N0719.N0860.d011440 k → ℝ)
    (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011455 hk phi (_root_.GD.N0232.N0719.N0860.d011443 u) = phi u := by
  unfold _root_.GD.N0232.N0719.N0860.d011455
  rw [dif_pos (_root_.GD.N0232.N0719.N0942.d011461 u)]
  have hz : _root_.GD.N0232.N0719.N0860.d011429 (_root_.GD.N0232.N0719.N0860.d011443 u) ≠ 0 := by
    rw [_root_.GD.N0232.N0719.N0942.d011463 hk]
    exact ne_of_apply_ne norm (by simp [u.1.property])
  rw [dif_pos hz, _root_.GD.N0232.N0719.N0942.d011462,
    _root_.GD.N0232.N0719.N0942.d011464 hk]
  have hdir := _root_.GD.N0232.N0719.N0942.d011465 hk u
  simpa [hdir]


theorem d011467
    {k : ℕ} (hk : 0 < k)
    (phi : _root_.GD.N0232.N0719.N0860.d011440 k → ℝ) :
    _root_.GD.N0232.N0719.N0860.d011457 (_root_.GD.N0232.N0719.N0860.d011455 hk phi) = phi := by
  funext u
  exact _root_.GD.N0232.N0719.N0942.d011466 hk phi u


theorem d011468
    {k : ℕ} (hk : 0 < k)
    (phi : _root_.GD.N0232.N0719.N0860.d011440 k → ℝ) :
    _root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0860.d011455 hk phi) = _root_.GD.N0232.N0719.N0860.d011455 hk phi := by
  unfold _root_.GD.N0232.N0719.N0860.d011458
  rw [_root_.GD.N0232.N0719.N0942.d011467 hk]



theorem d011469
    {k : ℕ} (hk : 0 < k) (d e : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) :
    _root_.GD.N0232.N0719.N0860.d011458 hk d = _root_.GD.N0232.N0719.N0860.d011458 hk e ↔
      _root_.GD.N0232.N0719.N0860.d011457 d = _root_.GD.N0232.N0719.N0860.d011457 e := by
  constructor
  · intro h
    have h' := congrArg _root_.GD.N0232.N0719.N0860.d011457 h
    simpa [_root_.GD.N0232.N0719.N0860.d011458, _root_.GD.N0232.N0719.N0942.d011467 hk] using h'
  · intro h
    unfold _root_.GD.N0232.N0719.N0860.d011458
    rw [h]






theorem d011470
    {k : ℕ} (hk : 0 < k) (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hs : _root_.GD.N0232.N0719.N0860.d011426 s)
    (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0) :
    _root_.GD.N0232.N0719.N0860.d011458 hk d s =
      _root_.GD.N0232.N0719.N0860.d011425 s + _root_.GD.N0232.N0719.N0860.d011434 s *
        d (_root_.GD.N0232.N0719.N0860.d011443
          (_root_.GD.N0232.N0719.N0860.d011441 s hz
            (_root_.GD.N0232.N0719.N0860.d011431 hk s hs))) := by
  simp [_root_.GD.N0232.N0719.N0860.d011458, _root_.GD.N0232.N0719.N0860.d011455, _root_.GD.N0232.N0719.N0860.d011457, hs, hz]







def d011471
    {k : ℕ} (amplitude : ℝ) : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ :=
  fun s ↦
    if _root_.GD.N0232.N0719.N0860.d011425 s = 0 ∧ _root_.GD.N0232.N0719.N0860.d011434 s = 1 then amplitude else 0

@[simp] theorem d011472
    {k : ℕ} (hk : 0 < k) (amplitude : ℝ)
    (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0942.d011471 amplitude (_root_.GD.N0232.N0719.N0860.d011443 u) = amplitude := by
  simp [_root_.GD.N0232.N0719.N0942.d011471, _root_.GD.N0232.N0719.N0942.d011462,
    _root_.GD.N0232.N0719.N0942.d011464 hk]


theorem d011473
    {k : ℕ} (hk : 0 < k) (amplitude : ℝ) :
    _root_.GD.N0232.N0719.N0860.d011457 (_root_.GD.N0232.N0719.N0942.d011471 (k := k) amplitude) =
      fun _ ↦ amplitude := by
  funext u
  exact _root_.GD.N0232.N0719.N0942.d011472 hk amplitude u



theorem d011474
    {k : ℕ} (hk : 0 < k) (amplitude : ℝ) :
    _root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0942.d011471 (k := k) amplitude) =
      _root_.GD.N0232.N0719.N0860.d011455 hk (fun _ ↦ amplitude) := by
  unfold _root_.GD.N0232.N0719.N0860.d011458
  rw [_root_.GD.N0232.N0719.N0942.d011473 hk]


def d011475
    {k : ℕ} (u : _root_.GD.N0232.N0719.N0860.d011440 k) : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ :=
  fun s ↦ if s = _root_.GD.N0232.N0719.N0860.d011443 u then 1 else 0

@[simp] theorem d011476
    {k : ℕ} (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0942.d011475 u (_root_.GD.N0232.N0719.N0860.d011443 u) = 1 := by
  simp [_root_.GD.N0232.N0719.N0942.d011475]



theorem d011477
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011444 0 2 u ≠ _root_.GD.N0232.N0719.N0860.d011443 u := by
  intro h
  have hr := congrArg _root_.GD.N0232.N0719.N0860.d011434 h
  rw [_root_.GD.N0232.N0719.N0860.d011445,
    _root_.GD.N0232.N0719.N0860.d011439 hk 0 2 (by norm_num),
    _root_.GD.N0232.N0719.N0942.d011464 hk] at hr
  norm_num at hr


@[simp] theorem d011478
    {k : ℕ} (hk : 0 < k) (amplitude : ℝ)
    (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0942.d011471 amplitude (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) = 0 := by
  unfold _root_.GD.N0232.N0719.N0942.d011471
  have hr : _root_.GD.N0232.N0719.N0860.d011434 (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) = 2 := by
    rw [_root_.GD.N0232.N0719.N0860.d011445,
      _root_.GD.N0232.N0719.N0860.d011439 hk 0 2 (by norm_num),
      _root_.GD.N0232.N0719.N0942.d011464 hk]
    norm_num
  simp [hr]



theorem d011479
    {k : ℕ} (hk : 0 < k) (amplitude : ℝ)
    (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0942.d011471 amplitude)
        (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) = 2 * amplitude := by
  rw [_root_.GD.N0232.N0719.N0942.d011474 hk]
  have hequiv := _root_.GD.N0232.N0719.N0860.d011456 hk
    (fun _ : _root_.GD.N0232.N0719.N0860.d011440 k ↦ amplitude)
  have hcov := hequiv 0 2 (by norm_num) (_root_.GD.N0232.N0719.N0860.d011443 u)
    (_root_.GD.N0232.N0719.N0942.d011461 u)
  rw [← _root_.GD.N0232.N0719.N0860.d011445,
    _root_.GD.N0232.N0719.N0942.d011466 hk] at hcov
  simpa using hcov



theorem d011480
    {k : ℕ} (hk : 0 < k) (amplitude : ℝ)
    (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    (_root_.GD.N0232.N0719.N0942.d011471 amplitude (_root_.GD.N0232.N0719.N0860.d011444 0 2 u)) ^ 2 = 0 ∧
    (_root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0942.d011471 amplitude)
        (_root_.GD.N0232.N0719.N0860.d011444 0 2 u)) ^ 2 = 4 * amplitude ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0942.d011478 hk,
    _root_.GD.N0232.N0719.N0942.d011479 hk]
  constructor <;> ring

theorem d011481
    {k : ℕ} (hk : 0 < k) {amplitude : ℝ} (ha : amplitude ≠ 0)
    (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    (_root_.GD.N0232.N0719.N0942.d011471 amplitude (_root_.GD.N0232.N0719.N0860.d011444 0 2 u)) ^ 2 <
      (_root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0942.d011471 amplitude)
        (_root_.GD.N0232.N0719.N0860.d011444 0 2 u)) ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0942.d011478 hk,
    _root_.GD.N0232.N0719.N0942.d011479 hk]
  have hsquare : 0 < amplitude ^ 2 := sq_pos_of_ne_zero ha
  nlinarith

@[simp] theorem d011482
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0942.d011475 u (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) = 0 := by
  simp [_root_.GD.N0232.N0719.N0942.d011475, _root_.GD.N0232.N0719.N0942.d011477 hk u]



theorem d011483
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0942.d011475 u) (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) = 2 := by
  unfold _root_.GD.N0232.N0719.N0860.d011458
  have hequiv := _root_.GD.N0232.N0719.N0860.d011456 hk
    (_root_.GD.N0232.N0719.N0860.d011457 (_root_.GD.N0232.N0719.N0942.d011475 u))
  have hcanonical :
      _root_.GD.N0232.N0719.N0860.d011457 (_root_.GD.N0232.N0719.N0942.d011475 u) u = 1 := by
    exact _root_.GD.N0232.N0719.N0942.d011476 u
  have hcov := hequiv 0 2 (by norm_num) (_root_.GD.N0232.N0719.N0860.d011443 u)
    (_root_.GD.N0232.N0719.N0942.d011461 u)
  rw [← _root_.GD.N0232.N0719.N0860.d011445] at hcov
  rw [_root_.GD.N0232.N0719.N0942.d011466 hk, hcanonical] at hcov
  norm_num at hcov
  exact hcov


theorem d011484
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    _root_.GD.N0232.N0719.N0860.d011458 hk (fun _ ↦ 0) (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) = 0 := by
  unfold _root_.GD.N0232.N0719.N0860.d011458
  have hequiv := _root_.GD.N0232.N0719.N0860.d011456 hk
    (_root_.GD.N0232.N0719.N0860.d011457 (fun _ : _root_.GD.N0232.N0719.N0900.d009096 k ↦ 0))
  have hcov := hequiv 0 2 (by norm_num) (_root_.GD.N0232.N0719.N0860.d011443 u)
    (_root_.GD.N0232.N0719.N0942.d011461 u)
  rw [← _root_.GD.N0232.N0719.N0860.d011445] at hcov
  rw [_root_.GD.N0232.N0719.N0942.d011466 hk] at hcov
  simpa [_root_.GD.N0232.N0719.N0860.d011457] using hcov




theorem d011485
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    (_root_.GD.N0232.N0719.N0942.d011475 u (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) - 0) ^ 2 = 0 ∧
    (_root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0942.d011475 u) (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) - 0) ^ 2 = 4 := by
  rw [_root_.GD.N0232.N0719.N0942.d011482 hk,
    _root_.GD.N0232.N0719.N0942.d011483 hk]
  norm_num




def d011486 {k : ℕ} (observed : _root_.GD.N0232.N0719.N0900.d009096 k) (target : ℝ)
    (d : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) : ℝ :=
  (d observed - target) ^ 2



theorem d011487
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    ∀ target,
      _root_.GD.N0232.N0719.N0942.d011486 (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) target (_root_.GD.N0232.N0719.N0942.d011475 u) =
        _root_.GD.N0232.N0719.N0942.d011486 (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) target (fun _ ↦ 0) := by
  intro target
  simp [_root_.GD.N0232.N0719.N0942.d011486, _root_.GD.N0232.N0719.N0942.d011482 hk]




theorem d011488
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0860.d011440 k) :
    (∀ target,
      _root_.GD.N0232.N0719.N0942.d011486 (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) target (_root_.GD.N0232.N0719.N0942.d011475 u) =
        _root_.GD.N0232.N0719.N0942.d011486 (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) target (fun _ ↦ 0)) ∧
      _root_.GD.N0232.N0719.N0942.d011486 (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) 0
          (_root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0942.d011475 u)) ≠
        _root_.GD.N0232.N0719.N0942.d011486 (_root_.GD.N0232.N0719.N0860.d011444 0 2 u) 0
          (_root_.GD.N0232.N0719.N0860.d011458 hk (fun _ ↦ 0)) := by
  refine ⟨_root_.GD.N0232.N0719.N0942.d011487 hk u, ?_⟩
  norm_num [_root_.GD.N0232.N0719.N0942.d011486, _root_.GD.N0232.N0719.N0942.d011483 hk,
    _root_.GD.N0232.N0719.N0942.d011484 hk]

end

end N0942
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0942.d011467
#print axioms _root_.GD.N0232.N0719.N0942.d011485
#print axioms _root_.GD.N0232.N0719.N0942.d011488
