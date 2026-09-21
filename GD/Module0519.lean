import GD.Module0518
import GD.Module0418















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace GD.N0106.N0428.N0766.N1692.N1762

open Set Filter _root_.GD.N0232.N0720.N1254
open _root_.GD.N0110 _root_.GD.N0132 _root_.GD.N0130
open scoped Topology

noncomputable section

theorem d007775 (alpha beta e s t : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s t =
      _root_.GD.N0132.d006445 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) s t := rfl

theorem d007776 (alpha beta : ℝ) (N : ℕ) :
    _root_.GD.N0232.N0720.N1254.d002519 alpha beta N = _root_.GD.N0132.d006443 alpha beta N := by
  unfold _root_.GD.N0232.N0720.N1254.d002519 _root_.GD.N0232.N0720.N1254.d002518 _root_.GD.N0232.N0720.N1254.d002510 _root_.GD.N0132.d006443 _root_.GD.N0132.d006442
  simp only [div_div]
  congr 1
  ring

theorem d007777 (alpha beta : ℝ) (N : ℕ) :
    _root_.GD.N0232.N0720.N1254.d002520 alpha beta N = _root_.GD.N0132.d006444 alpha beta N := rfl



theorem d007778 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e : ℝ) (p q : ℕ) :
    _root_.GD.N0132.d006446 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) 0 0 p q =
      iteratedDeriv p
        (fun s => iteratedDeriv q (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s t) 0) 0 := by
  have hn : _root_.GD.N0111.d006136
      (alpha * beta / (alpha + beta)) (beta - (alpha + beta) * e)
      (e * (1 - e) / 2) 0 0 ≠ 0 := by
    simpa [_root_.GD.N0111.d006136, _root_.GD.N0232.N0720.N1254.d002512, _root_.GD.N0232.N0720.N1254.d002510] using
      (_root_.GD.N0232.N0720.N1254.d002523 ha hb).ne'
  exact (_root_.GD.N0132.d006456
    (alpha / (alpha + beta) - e) (alpha * beta / (alpha + beta))
    (beta - (alpha + beta) * e) (e * (1 - e) / 2)
    (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) 0 0 p q hn).symm



def d007779 (alpha beta e : ℝ) (N : ℕ) : _root_.GD.N0232.N0720.N1254.d002559 where
  minusTwoEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (-2 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
    (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
  minusEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (-_root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
    (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
  zeroEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
  plusEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
  plusTwoEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (2 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
    (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
  minusTwoEtaLevel := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (-_root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
    (2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
  zeroTwoEtaLevel := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 (2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
  plusTwoEtaLevel := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
    (2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N)

def d007780 (alpha beta : ℝ) (N : ℕ) (e : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002566 alpha beta (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
    (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N)

abbrev d007781 (alpha beta : ℝ) (p q : ℕ) : ℝ :=
  _root_.GD.N0111.d006160 alpha beta (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) p q

abbrev d007782 (alpha beta e : ℝ) (p q : ℕ) : ℝ :=
  _root_.GD.N0132.d006446 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) 0 0 p q



theorem d007783 (alpha beta e : ℝ) (N : ℕ) :
    _root_.GD.N0232.N0720.N1254.d002560 (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) =
      _root_.GD.N0132.d006445 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) 0 (_root_.GD.N0132.d006444 alpha beta N) ∧
    _root_.GD.N0232.N0720.N1254.d002561 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) =
      _root_.GD.N0110.d006121 (fun s => _root_.GD.N0132.d006445 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) s
        (_root_.GD.N0132.d006444 alpha beta N)) (_root_.GD.N0132.d006443 alpha beta N) ∧
    _root_.GD.N0232.N0720.N1254.d002562 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) =
      _root_.GD.N0110.d006122 (fun s => _root_.GD.N0132.d006445 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) s
        (_root_.GD.N0132.d006444 alpha beta N)) (_root_.GD.N0132.d006443 alpha beta N) ∧
    _root_.GD.N0232.N0720.N1254.d002563 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) =
      _root_.GD.N0110.d006123 (fun s => _root_.GD.N0132.d006445 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) s
        (_root_.GD.N0132.d006444 alpha beta N)) (_root_.GD.N0132.d006443 alpha beta N) ∧
    _root_.GD.N0232.N0720.N1254.d002564 (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) =
      _root_.GD.N0110.d006130 (fun t => _root_.GD.N0132.d006445 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) 0 t)
        (_root_.GD.N0132.d006444 alpha beta N) ∧
    _root_.GD.N0232.N0720.N1254.d002565 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
      (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) =
      _root_.GD.N0110.d006121 (fun s => _root_.GD.N0130.d006472 alpha beta e (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) N s)
        (_root_.GD.N0132.d006443 alpha beta N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779, _root_.GD.N0232.N0720.N1254.d002560, _root_.GD.N0232.N0720.N1254.d002561, _root_.GD.N0232.N0720.N1254.d002562, _root_.GD.N0232.N0720.N1254.d002563,
    _root_.GD.N0232.N0720.N1254.d002564, _root_.GD.N0232.N0720.N1254.d002565, _root_.GD.N0110.d006121, _root_.GD.N0110.d006122, _root_.GD.N0110.d006123,
    _root_.GD.N0130.d006472, _root_.GD.N0110.d006130, _root_.GD.N0106.N0428.N0766.N1692.N1762.d007775,
    _root_.GD.N0106.N0428.N0766.N1692.N1762.d007776, _root_.GD.N0106.N0428.N0766.N1692.N1762.d007777]
  all_goals simp only [div_eq_mul_inv, mul_inv_rev]
  all_goals ring



theorem d007784 {alpha beta e : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1) (hN : 1 ≤ N) :
    |_root_.GD.N0232.N0720.N1254.d002560 (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 0 0| ≤
      _root_.GD.N0232.N0720.N1254.d002520 alpha beta N * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 0 1 ∧
    |_root_.GD.N0232.N0720.N1254.d002561 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 1 0| ≤
      _root_.GD.N0232.N0720.N1254.d002520 alpha beta N * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 1 1 +
        _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 0 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2 / 6 ∧
    |_root_.GD.N0232.N0720.N1254.d002562 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 2 0| ≤
      _root_.GD.N0232.N0720.N1254.d002520 alpha beta N * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 2 1 +
        _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 4 0 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2 / 12 ∧
    |_root_.GD.N0232.N0720.N1254.d002563 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 3 0| ≤
      _root_.GD.N0232.N0720.N1254.d002520 alpha beta N * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 1 +
        (17 / 60 : ℝ) * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 5 0 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2 ∧
    |_root_.GD.N0232.N0720.N1254.d002564 (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N) (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 0 1| ≤
      2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 0 2 ∧
    |_root_.GD.N0232.N0720.N1254.d002565 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
      (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N) - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 1 1| ≤
      2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 1 2 +
        _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 1 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2 / 6 := by
  have hr : 0 ≤ _root_.GD.N0232.N0720.N1254.d002513 alpha beta := by
    have := _root_.GD.N0232.N0720.N1254.d002524 ha hb
    linarith
  obtain ⟨h0, h1, h2, h3, ht, hst⟩ := _root_.GD.N0106.N0428.N0766.N1692.N1762.d007783 alpha beta e N
  rw [h0, h1, h2, h3, ht, hst, _root_.GD.N0106.N0428.N0766.N1692.N1762.d007776, _root_.GD.N0106.N0428.N0766.N1692.N1762.d007777]
  refine ⟨?_, _root_.GD.N0132.d006469 ha hb he.1 he.2 hr hN,
    _root_.GD.N0132.d006470 ha hb he.1 he.2 hr hN,
    _root_.GD.N0132.d006471 ha hb he.1 he.2 hr hN,
    _root_.GD.N0130.d006476 ha hb he.1 he.2 hr hN,
    _root_.GD.N0130.d006479 ha hb he.1 he.2 hr hN⟩
  simpa only [_root_.GD.N0106.N0428.N0766.N1692.N1762.d007782, _root_.GD.N0132.d006446, _root_.GD.N0132.d006445, _root_.GD.N0111.d006148] using
    _root_.GD.N0132.d006468 (r := _root_.GD.N0232.N0720.N1254.d002513 alpha beta) 0 0 ha hb he.1 he.2 hr hN

def d007785 (alpha beta : ℝ) : ℝ :=
  |_root_.GD.N0232.N0720.N1254.d002545 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 0 1 +
    |_root_.GD.N0232.N0720.N1254.d002546 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 1 1 +
    |_root_.GD.N0232.N0720.N1254.d002547 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 2 1 +
    |_root_.GD.N0232.N0720.N1254.d002548 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 1 +
    2 * |_root_.GD.N0232.N0720.N1254.d002549 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 0 2 +
    2 * |_root_.GD.N0232.N0720.N1254.d002550 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 1 2

def d007786 (alpha beta : ℝ) : ℝ :=
  |_root_.GD.N0232.N0720.N1254.d002546 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 0 / 6 +
    |_root_.GD.N0232.N0720.N1254.d002547 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 4 0 / 12 +
    (17 / 60 : ℝ) * |_root_.GD.N0232.N0720.N1254.d002548 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 5 0 +
    |_root_.GD.N0232.N0720.N1254.d002550 alpha beta| * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 1 / 6

theorem d007787 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta) :
    0 ≤ _root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 alpha beta ∧ 0 ≤ _root_.GD.N0106.N0428.N0766.N1692.N1762.d007786 alpha beta := by
  have hr : 0 ≤ _root_.GD.N0232.N0720.N1254.d002513 alpha beta := by
    have := _root_.GD.N0232.N0720.N1254.d002524 ha hb
    linarith
  have hB (p q : ℕ) : 0 ≤ _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta p q :=
    _root_.GD.N0132.d006467 p q ha hb hr
  have b01 := hB 0 1
  have b11 := hB 1 1
  have b21 := hB 2 1
  have b31 := hB 3 1
  have b02 := hB 0 2
  have b12 := hB 1 2
  have b30 := hB 3 0
  have b40 := hB 4 0
  have b50 := hB 5 0
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 _root_.GD.N0106.N0428.N0766.N1692.N1762.d007786
  constructor <;> positivity

private theorem d007788 (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  have h5 := abs_add_le (a + b + c + d + e) f
  linarith

theorem d007789 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e : ℝ) :
    _root_.GD.N0232.N0720.N1254.d002545 alpha beta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 0 0 +
      _root_.GD.N0232.N0720.N1254.d002546 alpha beta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 1 0 +
      _root_.GD.N0232.N0720.N1254.d002547 alpha beta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 2 0 +
      _root_.GD.N0232.N0720.N1254.d002548 alpha beta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 3 0 +
      _root_.GD.N0232.N0720.N1254.d002549 alpha beta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 0 1 +
      _root_.GD.N0232.N0720.N1254.d002550 alpha beta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 1 1 =
        (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) := by
  simpa only [_root_.GD.N0106.N0428.N0766.N1692.N1762.d007782, _root_.GD.N0106.N0428.N0766.N1692.N1762.d007778 ha hb, iteratedDeriv_succ, iteratedDeriv_zero] using
    _root_.GD.N0106.N0428.N0766.N1692.d007774 ha hb e



theorem d007790 {alpha beta e : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1) (hN : 1 ≤ N) :
    |_root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e + (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)| ≤
      _root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 alpha beta * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N +
        _root_.GD.N0106.N0428.N0766.N1692.N1762.d007786 alpha beta * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2 := by
  obtain ⟨h0, h1, h2, h3, ht, hst⟩ := _root_.GD.N0106.N0428.N0766.N1692.N1762.d007784 ha hb he hN
  let g := _root_.GD.N0106.N0428.N0766.N1692.N1762.d007779 alpha beta e N
  let h := _root_.GD.N0232.N0720.N1254.d002519 alpha beta N
  let eta := _root_.GD.N0232.N0720.N1254.d002520 alpha beta N
  have hid : _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e +
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) =
      -(_root_.GD.N0232.N0720.N1254.d002545 alpha beta * (_root_.GD.N0232.N0720.N1254.d002560 g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 0 0) +
        _root_.GD.N0232.N0720.N1254.d002546 alpha beta * (_root_.GD.N0232.N0720.N1254.d002561 h g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 1 0) +
        _root_.GD.N0232.N0720.N1254.d002547 alpha beta * (_root_.GD.N0232.N0720.N1254.d002562 h g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 2 0) +
        _root_.GD.N0232.N0720.N1254.d002548 alpha beta * (_root_.GD.N0232.N0720.N1254.d002563 h g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 3 0) +
        _root_.GD.N0232.N0720.N1254.d002549 alpha beta * (_root_.GD.N0232.N0720.N1254.d002564 eta g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 0 1) +
        _root_.GD.N0232.N0720.N1254.d002550 alpha beta * (_root_.GD.N0232.N0720.N1254.d002565 h eta g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 1 1)) := by
    rw [← _root_.GD.N0106.N0428.N0766.N1692.N1762.d007789 ha hb e]
    unfold _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 _root_.GD.N0232.N0720.N1254.d002566
    dsimp only [g, h, eta]
    ring
  rw [hid, abs_neg]
  calc
    _ ≤ |_root_.GD.N0232.N0720.N1254.d002545 alpha beta * (_root_.GD.N0232.N0720.N1254.d002560 g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 0 0)| +
        |_root_.GD.N0232.N0720.N1254.d002546 alpha beta * (_root_.GD.N0232.N0720.N1254.d002561 h g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 1 0)| +
        |_root_.GD.N0232.N0720.N1254.d002547 alpha beta * (_root_.GD.N0232.N0720.N1254.d002562 h g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 2 0)| +
        |_root_.GD.N0232.N0720.N1254.d002548 alpha beta * (_root_.GD.N0232.N0720.N1254.d002563 h g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 3 0)| +
        |_root_.GD.N0232.N0720.N1254.d002549 alpha beta * (_root_.GD.N0232.N0720.N1254.d002564 eta g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 0 1)| +
        |_root_.GD.N0232.N0720.N1254.d002550 alpha beta * (_root_.GD.N0232.N0720.N1254.d002565 h eta g - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007782 alpha beta e 1 1)| :=
      _root_.GD.N0106.N0428.N0766.N1692.N1762.d007788 _ _ _ _ _ _
    _ ≤ |_root_.GD.N0232.N0720.N1254.d002545 alpha beta| * (eta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 0 1) +
        |_root_.GD.N0232.N0720.N1254.d002546 alpha beta| * (eta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 1 1 + _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 0 * h ^ 2 / 6) +
        |_root_.GD.N0232.N0720.N1254.d002547 alpha beta| * (eta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 2 1 + _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 4 0 * h ^ 2 / 12) +
        |_root_.GD.N0232.N0720.N1254.d002548 alpha beta| * (eta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 1 + (17 / 60 : ℝ) * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 5 0 * h ^ 2) +
        |_root_.GD.N0232.N0720.N1254.d002549 alpha beta| * (2 * eta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 0 2) +
        |_root_.GD.N0232.N0720.N1254.d002550 alpha beta| * (2 * eta * _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 1 2 + _root_.GD.N0106.N0428.N0766.N1692.N1762.d007781 alpha beta 3 1 * h ^ 2 / 6) := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left h3 (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left ht (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hst (abs_nonneg _))
    _ = _root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 alpha beta * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N +
        _root_.GD.N0106.N0428.N0766.N1692.N1762.d007786 alpha beta * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2 := by
      unfold _root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 _root_.GD.N0106.N0428.N0766.N1692.N1762.d007786
      dsimp only [h, eta]
      ring

private theorem d007791 (alpha beta : ℝ) :
    Tendsto (fun N : ℕ => _root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 alpha beta * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N +
        _root_.GD.N0106.N0428.N0766.N1692.N1762.d007786 alpha beta * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2) atTop (𝓝 0) := by
  have hH : Tendsto (_root_.GD.N0232.N0720.N1254.d002519 alpha beta) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (_root_.GD.N0232.N0720.N1254.d002518 alpha beta / 16) using 1
    funext N
    unfold _root_.GD.N0232.N0720.N1254.d002519
    ring
  have hE : Tendsto (_root_.GD.N0232.N0720.N1254.d002520 alpha beta) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (_root_.GD.N0232.N0720.N1254.d002512 alpha beta / 8) using 1
    funext N
    unfold _root_.GD.N0232.N0720.N1254.d002520
    ring
  simpa using ((hE.const_mul (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 alpha beta)).add
    ((hH.pow 2).const_mul (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007786 alpha beta)))



theorem d007792 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∀ epsilon > 0, ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ e ∈ Icc (0 : ℝ) 1,
      |_root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e + (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)|
        < epsilon := by
  intro epsilon hepsilon
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007791 alpha beta)
    epsilon hepsilon
  refine ⟨max 1 N0, le_max_left _ _, ?_⟩
  intro N hN e he
  have hNone := (le_max_left 1 N0).trans hN
  have hclose := hN0 N ((le_max_right 1 N0).trans hN)
  have hlt : _root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 alpha beta * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N +
      _root_.GD.N0106.N0428.N0766.N1692.N1762.d007786 alpha beta * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2 < epsilon := by
    have habs : |_root_.GD.N0106.N0428.N0766.N1692.N1762.d007785 alpha beta * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N +
        _root_.GD.N0106.N0428.N0766.N1692.N1762.d007786 alpha beta * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N ^ 2| < epsilon := by
      simpa only [Real.dist_eq, sub_zero] using hclose
    exact (le_abs_self _).trans_lt habs
  exact (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007790 ha hb he hNone).trans_lt hlt



theorem d007793 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ e ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e ≤
        -3 * (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) / 4 := by
  let target := (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)
  have htarget : 0 < target := Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1254.d002523 ha hb) _
  obtain ⟨N, hN, hclose⟩ := _root_.GD.N0106.N0428.N0766.N1692.N1762.d007792 ha hb (target / 4) (by positivity)
  refine ⟨N, hN, ?_⟩
  intro e he
  have herr := hclose N le_rfl e he
  have hupp := le_abs_self (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e + target)
  change _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e ≤ -3 * target / 4
  linarith

end
end GD.N0106.N0428.N0766.N1692.N1762

#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1762.d007778
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1762.d007784
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1762.d007790
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1762.d007792
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1762.d007793
