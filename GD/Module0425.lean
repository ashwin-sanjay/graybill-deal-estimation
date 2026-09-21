import Mathlib
import GD.Module0424













namespace GD.N0115

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135



structure d006615 (q : ℚ) where
  lower : ℚ
  upper : ℚ
  q_pos : 0 < q
  lower_nonneg : 0 ≤ lower
  lower_sq_le : lower ^ 2 ≤ q
  q_le_upper_sq : q ≤ upper ^ 2
  upper_nonneg : 0 ≤ upper

namespace d006615

theorem d006616 {q : ℚ} (E : _root_.GD.N0115.d006615 q) :
    E.lower ≤ E.upper := by
  by_contra h
  have hlt : E.upper < E.lower := lt_of_not_ge h
  have hsquare : E.upper ^ 2 < E.lower ^ 2 :=
    (sq_lt_sq₀ E.upper_nonneg E.lower_nonneg).2 hlt
  nlinarith [E.lower_sq_le, E.q_le_upper_sq]

theorem d006617 {q : ℚ} (E : _root_.GD.N0115.d006615 q) :
    (E.lower : ℝ) ≤ Real.sqrt (q : ℝ) := by
  apply (Real.le_sqrt
    (by exact_mod_cast E.lower_nonneg)
    (by exact_mod_cast E.q_pos.le)).2
  exact_mod_cast E.lower_sq_le

theorem d006618 {q : ℚ} (E : _root_.GD.N0115.d006615 q) :
    Real.sqrt (q : ℝ) ≤ (E.upper : ℝ) := by
  apply (Real.sqrt_le_iff).2
  constructor
  · exact_mod_cast E.upper_nonneg
  · exact_mod_cast E.q_le_upper_sq



theorem d006619
    {q epsilon : ℚ} (hq : 0 < q) (hepsilon : 0 < epsilon) :
    ∃ E : _root_.GD.N0115.d006615 q,
      0 < E.lower ∧ E.upper - E.lower < epsilon := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqR
  let d : ℝ := min (Real.sqrt (q : ℝ) / 2) ((epsilon : ℝ) / 4)
  have hd : 0 < d := lt_min (half_pos hsqrt)
    (div_pos (by exact_mod_cast hepsilon) (by norm_num))
  obtain ⟨lo, hlo₁, hlo₂⟩ :
      ∃ lo : ℚ,
        Real.sqrt (q : ℝ) - d < (lo : ℝ)
          ∧ (lo : ℝ) < Real.sqrt (q : ℝ) :=
    exists_rat_btwn (sub_lt_self _ hd)
  obtain ⟨hi, hhi₁, hhi₂⟩ :
      ∃ hi : ℚ,
        Real.sqrt (q : ℝ) < (hi : ℝ)
          ∧ (hi : ℝ) < Real.sqrt (q : ℝ) + d :=
    exists_rat_btwn (lt_add_of_pos_right _ hd)
  have hdS : d ≤ Real.sqrt (q : ℝ) / 2 := min_le_left _ _
  have hdE : d ≤ (epsilon : ℝ) / 4 := min_le_right _ _
  have hloPosR : 0 < (lo : ℝ) := by nlinarith
  have hhiPosR : 0 < (hi : ℝ) := lt_trans hsqrt hhi₁
  have hsquare : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt hqR.le
  let E : _root_.GD.N0115.d006615 q :=
    { lower := lo
      upper := hi
      q_pos := hq
      lower_nonneg := by exact_mod_cast hloPosR.le
      lower_sq_le := by
        exact_mod_cast (show (lo : ℝ) ^ 2 ≤ (q : ℝ) by nlinarith)
      q_le_upper_sq := by
        exact_mod_cast (show (q : ℝ) ≤ (hi : ℝ) ^ 2 by nlinarith)
      upper_nonneg := by exact_mod_cast hhiPosR.le }
  refine ⟨E, ?_, ?_⟩
  · exact_mod_cast hloPosR
  · change hi - lo < epsilon
    exact_mod_cast (show (hi : ℝ) - lo < (epsilon : ℝ) by nlinarith)

end d006615

def d006620 (q lower : ℚ) (k : ℕ) : ℚ :=
  q ^ k * lower

def d006621 (q upper : ℚ) (k : ℕ) : ℚ :=
  q ^ k * upper

def d006622 (q upper : ℚ) (k : ℕ) : ℚ :=
  1 / (q ^ k * upper)

def d006623 (q lower : ℚ) (k : ℕ) : ℚ :=
  1 / (q ^ k * lower)

theorem d006624 {q : ℚ} (hq : 0 < q) (k : ℕ) :
    (q : ℝ) ^ ((k : ℝ) + 1 / 2)
      = (q : ℝ) ^ k * Real.sqrt (q : ℝ) := by
  rw [Real.rpow_add (by exact_mod_cast hq),
    Real.rpow_natCast, ← Real.sqrt_eq_rpow]

theorem d006625 {q : ℚ} (hq : 0 < q) (k : ℕ) :
    (q : ℝ) ^ (-((k : ℝ) + 1 / 2))
      = ((q : ℝ) ^ k * Real.sqrt (q : ℝ))⁻¹ := by
  rw [Real.rpow_neg (by exact_mod_cast hq.le),
    _root_.GD.N0115.d006624 hq]

theorem d006626
    {q : ℚ} (E : _root_.GD.N0115.d006615 q) (k : ℕ) :
    (_root_.GD.N0115.d006620 q E.lower k : ℝ)
        ≤ (q : ℝ) ^ ((k : ℝ) + 1 / 2)
      ∧
    (q : ℝ) ^ ((k : ℝ) + 1 / 2)
        ≤ (_root_.GD.N0115.d006621 q E.upper k : ℝ) := by
  rw [_root_.GD.N0115.d006624 E.q_pos]
  simp only [_root_.GD.N0115.d006620, _root_.GD.N0115.d006621,
    Rat.cast_mul, Rat.cast_pow]
  constructor
  · exact mul_le_mul_of_nonneg_left E.d006617
      (pow_nonneg (by exact_mod_cast E.q_pos.le) _)
  · exact mul_le_mul_of_nonneg_left E.d006618
      (pow_nonneg (by exact_mod_cast E.q_pos.le) _)

theorem d006627
    {q : ℚ} (E : _root_.GD.N0115.d006615 q)
    (hlower : 0 < E.lower) (k : ℕ) :
    (_root_.GD.N0115.d006622 q E.upper k : ℝ)
        ≤ (q : ℝ) ^ (-((k : ℝ) + 1 / 2))
      ∧
    (q : ℝ) ^ (-((k : ℝ) + 1 / 2))
        ≤ (_root_.GD.N0115.d006623 q E.lower k : ℝ) := by
  rw [_root_.GD.N0115.d006625 E.q_pos]
  have hcastLower :
      (_root_.GD.N0115.d006622 q E.upper k : ℝ) =
        (((q : ℝ) ^ k * (E.upper : ℝ))⁻¹) := by
    norm_num [_root_.GD.N0115.d006622]
  have hcastUpper :
      (_root_.GD.N0115.d006623 q E.lower k : ℝ) =
        (((q : ℝ) ^ k * (E.lower : ℝ))⁻¹) := by
    norm_num [_root_.GD.N0115.d006623]
  rw [hcastLower, hcastUpper]
  have hpow : 0 < (q : ℝ) ^ k :=
    pow_pos (by exact_mod_cast E.q_pos) _
  have hsqrt : 0 < Real.sqrt (q : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast E.q_pos)
  have hlo : 0 < (E.lower : ℝ) := by exact_mod_cast hlower
  have hhi : 0 < (E.upper : ℝ) :=
    lt_of_lt_of_le hlo (by exact_mod_cast E.d006616)
  constructor
  · exact
      (inv_le_inv₀ (mul_pos hpow hhi) (mul_pos hpow hsqrt)).2
        (mul_le_mul_of_nonneg_left E.d006618 hpow.le)
  · exact
      (inv_le_inv₀ (mul_pos hpow hsqrt) (mul_pos hpow hlo)).2
        (mul_le_mul_of_nonneg_left E.d006617 hpow.le)



def d006628 (lower upper : ℚ) : ℚ :=
  2 / (lower + upper)

def d006629 (lower upper : ℚ) : ℚ :=
  (upper - lower) / (upper + lower)

theorem d006630
    {lower upper : ℚ} {rho : ℝ}
    (hlower : 0 < lower)
    (hlrho : (lower : ℝ) ≤ rho)
    (hrhou : rho ≤ (upper : ℝ)) :
    |(_root_.GD.N0115.d006628 lower upper : ℝ) * rho - 1|
      ≤ (_root_.GD.N0115.d006629 lower upper : ℝ) := by
  have hupper : 0 < upper := by
    exact_mod_cast (show 0 < upper by
      have : lower ≤ upper := by exact_mod_cast hlrho.trans hrhou
      exact lt_of_lt_of_le hlower this)
  have hsum : 0 < (lower : ℝ) + upper := by positivity
  have herr :
      (_root_.GD.N0115.d006628 lower upper : ℝ) * rho - 1
        = (2 * rho - ((lower : ℝ) + upper)) /
            ((lower : ℝ) + upper) := by
    simp only [_root_.GD.N0115.d006628, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_add]
    field_simp [ne_of_gt hsum]
  have hnum :
      |2 * rho - ((lower : ℝ) + upper)|
        ≤ (upper : ℝ) - lower := by
    rw [abs_le]
    constructor <;> linarith
  rw [herr, abs_div, abs_of_pos hsum]
  have hdiv :=
    (div_le_div_iff_of_pos_right hsum).2 hnum
  simpa [_root_.GD.N0115.d006629, add_comm] using hdiv

def d006631 (center : ℚ × ℚ) (width : ℚ) (p : ℚ × ℚ) : Prop :=
  |p.1 - center.1| < width ∧ |p.2 - center.2| < width




structure d006632
    (rho : (ℚ × ℚ) → ℝ) where
  center : ℚ × ℚ
  width : ℚ
  width_pos : 0 < width
  lower : ℚ
  upper : ℚ
  lower_pos : 0 < lower
  bounds :
    ∀ p, _root_.GD.N0115.d006631 center width p →
      (lower : ℝ) ≤ rho p ∧ rho p ≤ (upper : ℝ)

namespace d006632

def d006633 {rho : (ℚ × ℚ) → ℝ}
    (B : _root_.GD.N0115.d006632 rho) : ℚ :=
  _root_.GD.N0115.d006628 B.lower B.upper

theorem d006634
    {rho : (ℚ × ℚ) → ℝ}
    (B : _root_.GD.N0115.d006632 rho)
    {p : ℚ × ℚ} (hp : _root_.GD.N0115.d006631 B.center B.width p) :
    |(B.d006633 : ℝ) * rho p - 1|
      ≤ (_root_.GD.N0115.d006629 B.lower B.upper : ℝ) := by
  exact _root_.GD.N0115.d006630 B.lower_pos
    (B.bounds p hp).1 (B.bounds p hp).2

end d006632



def d006635 (a : _root_.GD.N0135.d006593) : ℚ × ℚ :=
  (a.ell, a.f)

def d006636 (D : _root_.GD.N0134.d006518) (k : ℕ) : List (ℚ × ℚ) :=
  (_root_.GD.N0135.d006607 D k).map _root_.GD.N0115.d006635

def d006637 (D : _root_.GD.N0134.d006518) (k : ℕ) : List (ℚ × ℚ) :=
  (_root_.GD.N0135.d006608 D k).map _root_.GD.N0115.d006635

def d006638 (D : _root_.GD.N0134.d006518) (k : ℕ) : ℚ :=
  min (_root_.GD.N0134.d006550 D k) (_root_.GD.N0134.d006551 D k) / 8

theorem d006639 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    0 < _root_.GD.N0115.d006638 D k := by
  unfold _root_.GD.N0115.d006638
  exact div_pos (lt_min (_root_.GD.N0134.d006555 D k) (_root_.GD.N0134.d006556 D k))
    (by norm_num)

theorem d006640 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    _root_.GD.N0115.d006638 D k ≤ _root_.GD.N0134.d006550 D k / 8 := by
  unfold _root_.GD.N0115.d006638
  exact div_le_div_of_nonneg_right
    (min_le_left _ _) (by norm_num)

theorem d006641 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    _root_.GD.N0115.d006638 D k ≤ _root_.GD.N0134.d006551 D k / 8 := by
  unfold _root_.GD.N0115.d006638
  exact div_le_div_of_nonneg_right
    (min_le_right _ _) (by norm_num)

theorem d006642 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    16 * _root_.GD.N0134.d006550 D k ≤ D.d006523 := by
  unfold _root_.GD.N0134.d006550
  have hN := _root_.GD.N0134.d006548 k
  have hNp := _root_.GD.N0134.d006547 k
  rw [show 16 * (D.d006523 / (16 * _root_.GD.N0134.d006546 k)) =
    D.d006523 / _root_.GD.N0134.d006546 k by ring]
  exact (div_le_iff₀ hNp).2
    (by nlinarith [D.d006532])

theorem d006643
    (D : _root_.GD.N0134.d006518) (k : ℕ) (c : ℚ × ℚ)
    (hc :
      c ∈ _root_.GD.N0115.d006636 D k ∨ c ∈ _root_.GD.N0115.d006637 D k) :
    D.d006520 - 2 * _root_.GD.N0134.d006550 D k ≤ c.1
      ∧ c.1 ≤ D.d006520 + 2 * _root_.GD.N0134.d006550 D k
      ∧ _root_.GD.N0134.d006551 D k ≤ c.2 := by
  rcases hc with hc | hc
  · simp [_root_.GD.N0115.d006636, _root_.GD.N0135.d006607, _root_.GD.N0115.d006635] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals
      exact ⟨by linarith [_root_.GD.N0134.d006555 D k],
        by constructor <;> linarith [_root_.GD.N0134.d006555 D k, _root_.GD.N0134.d006556 D k]⟩
  · simp [_root_.GD.N0115.d006637, _root_.GD.N0135.d006608, _root_.GD.N0115.d006635] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact ⟨by linarith [_root_.GD.N0134.d006555 D k],
        by constructor <;> linarith [_root_.GD.N0134.d006555 D k, _root_.GD.N0134.d006556 D k]⟩

theorem d006644
    (D : _root_.GD.N0134.d006518) (k : ℕ) (c p : ℚ × ℚ)
    (hc :
      c ∈ _root_.GD.N0115.d006636 D k ∨ c ∈ _root_.GD.N0115.d006637 D k)
    (hp : _root_.GD.N0115.d006631 c (_root_.GD.N0115.d006638 D k) p) :
    0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 := by
  have hC := _root_.GD.N0115.d006643 D k c hc
  have hwH := _root_.GD.N0115.d006640 D k
  have hwE := _root_.GD.N0115.d006641 D k
  have h16 := _root_.GD.N0115.d006642 D k
  have hL := D.d006533
  have hR := D.d006534
  have hsum := D.d006529
  have hh := _root_.GD.N0134.d006555 D k
  have hη := _root_.GD.N0134.d006556 D k
  rw [_root_.GD.N0115.d006631, abs_lt, abs_lt] at hp
  rcases hp with ⟨⟨hpL, hpU⟩, ⟨hpfL, hpfU⟩⟩
  constructor
  · linarith
  constructor <;> linarith

theorem d006645
    {first second p : ℚ × ℚ} {width sx sy : ℚ}
    (hw : 0 < width)
    (hwidthX : 2 * width < sx)
    (hwidthY : 2 * width < sy)
    (hsep :
      sx ≤ |first.1 - second.1| ∨
      sy ≤ |first.2 - second.2|)
    (hfirst : _root_.GD.N0115.d006631 first width p)
    (hsecond : _root_.GD.N0115.d006631 second width p) :
    False := by
  unfold _root_.GD.N0115.d006631 at hfirst hsecond
  rcases hfirst with ⟨hf₁, hf₂⟩
  rcases hsecond with ⟨hs₁, hs₂⟩
  rcases hsep with hsep | hsep
  · have htri :
        |first.1 - second.1|
          ≤ |p.1 - first.1| + |p.1 - second.1| := by
      calc
        |first.1 - second.1|
            = |-(p.1 - first.1) + (p.1 - second.1)| := by
              congr 1
              ring
        _ ≤ |-(p.1 - first.1)| + |p.1 - second.1| :=
          abs_add_le _ _
        _ = _ := by rw [abs_neg]
    linarith
  · have htri :
        |first.2 - second.2|
          ≤ |p.2 - first.2| + |p.2 - second.2| := by
      calc
        |first.2 - second.2|
            = |-(p.2 - first.2) + (p.2 - second.2)| := by
              congr 1
              ring
        _ ≤ |-(p.2 - first.2)| + |p.2 - second.2| :=
          abs_add_le _ _
        _ = _ := by rw [abs_neg]
    linarith

theorem d006646
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (first second : ℚ × ℚ)
    (hf : first ∈ _root_.GD.N0115.d006636 D k)
    (hs : second ∈ _root_.GD.N0115.d006636 D k)
    (hne : first ≠ second) :
    _root_.GD.N0134.d006550 D k ≤ |first.1 - second.1|
      ∨ _root_.GD.N0134.d006551 D k ≤ |first.2 - second.2| := by
  simp [_root_.GD.N0115.d006636, _root_.GD.N0135.d006607, _root_.GD.N0115.d006635] at hf hs
  rcases hf with rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl
  all_goals
    simp_all [abs_of_pos (_root_.GD.N0134.d006555 D k),
      abs_of_nonneg (_root_.GD.N0134.d006555 D k).le,
      abs_of_pos (_root_.GD.N0134.d006556 D k),
      abs_of_nonneg (_root_.GD.N0134.d006556 D k).le]
  all_goals try { left; rw [abs_of_nonneg] <;> linarith [_root_.GD.N0134.d006555 D k] }
  all_goals try { left; rw [abs_of_nonpos] <;> linarith [_root_.GD.N0134.d006555 D k] }
  all_goals try { right; rw [abs_of_nonneg] <;> linarith [_root_.GD.N0134.d006556 D k] }
  all_goals try { right; rw [abs_of_nonpos] <;> linarith [_root_.GD.N0134.d006556 D k] }

theorem d006647
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (first second : ℚ × ℚ)
    (hf : first ∈ _root_.GD.N0115.d006637 D k)
    (hs : second ∈ _root_.GD.N0115.d006637 D k)
    (hne : first ≠ second) :
    _root_.GD.N0134.d006550 D k ≤ |first.1 - second.1|
      ∨ _root_.GD.N0134.d006551 D k ≤ |first.2 - second.2| := by
  simp [_root_.GD.N0115.d006637, _root_.GD.N0135.d006608, _root_.GD.N0115.d006635] at hf hs
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp_all [abs_of_pos (_root_.GD.N0134.d006555 D k),
      abs_of_nonneg (_root_.GD.N0134.d006555 D k).le,
      abs_of_pos (_root_.GD.N0134.d006556 D k),
      abs_of_nonneg (_root_.GD.N0134.d006556 D k).le]
  all_goals try { left; rw [abs_of_nonneg] <;> linarith [_root_.GD.N0134.d006555 D k] }
  all_goals try { left; rw [abs_of_nonpos] <;> linarith [_root_.GD.N0134.d006555 D k] }
  all_goals try { right; rw [abs_of_nonneg] <;> linarith [_root_.GD.N0134.d006556 D k] }
  all_goals try { right; rw [abs_of_nonpos] <;> linarith [_root_.GD.N0134.d006556 D k] }

structure d006648 (D : _root_.GD.N0134.d006518) (k : ℕ) where
  centers : List (ℚ × ℚ)
  centers_eq :
    centers =
      if _root_.GD.N0135.d006594 D = 0 then _root_.GD.N0115.d006637 D k
      else _root_.GD.N0115.d006636 D k
  width : ℚ
  width_eq : width = _root_.GD.N0115.d006638 D k
  width_pos : 0 < width
  physical :
    ∀ c ∈ centers, ∀ p,
      _root_.GD.N0115.d006631 c width p → 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2
  pairwise_disjoint :
    ∀ first ∈ centers, ∀ second ∈ centers,
      first ≠ second →
        ¬ ∃ p, _root_.GD.N0115.d006631 first width p ∧ _root_.GD.N0115.d006631 second width p

theorem d006649
    (D : _root_.GD.N0134.d006518) (k : ℕ) :
    Nonempty (_root_.GD.N0115.d006648 D k) := by
  let centers :=
    if _root_.GD.N0135.d006594 D = 0 then _root_.GD.N0115.d006637 D k
    else _root_.GD.N0115.d006636 D k
  let width := _root_.GD.N0115.d006638 D k
  have hw : 0 < width := _root_.GD.N0115.d006639 D k
  have hwH : 2 * width < _root_.GD.N0134.d006550 D k := by
    have := _root_.GD.N0115.d006640 D k
    dsimp [width]
    linarith [_root_.GD.N0134.d006555 D k]
  have hwE : 2 * width < _root_.GD.N0134.d006551 D k := by
    have := _root_.GD.N0115.d006641 D k
    dsimp [width]
    linarith [_root_.GD.N0134.d006556 D k]
  refine ⟨{
    centers := centers
    centers_eq := rfl
    width := width
    width_eq := rfl
    width_pos := hw
    physical := ?_
    pairwise_disjoint := ?_ }⟩
  · intro c hc p hp
    apply _root_.GD.N0115.d006644 D k c p
    · dsimp [centers] at hc
      split at hc
      · exact Or.inr hc
      · exact Or.inl hc
    · simpa [width] using hp
  · intro first hf second hs hne
    rintro ⟨p, hp₁, hp₂⟩
    apply _root_.GD.N0115.d006645 hw hwH hwE
    · by_cases hb : _root_.GD.N0135.d006594 D = 0
      · have hf' : first ∈ _root_.GD.N0115.d006637 D k := by
          simpa [centers, hb] using hf
        have hs' : second ∈ _root_.GD.N0115.d006637 D k := by
          simpa [centers, hb] using hs
        exact _root_.GD.N0115.d006647 D k first second hf' hs' hne
      · have hf' : first ∈ _root_.GD.N0115.d006636 D k := by
          simpa [centers, hb] using hf
        have hs' : second ∈ _root_.GD.N0115.d006636 D k := by
          simpa [centers, hb] using hs
        exact _root_.GD.N0115.d006646 D k first second hf' hs' hne
    · simpa [width] using hp₁
    · simpa [width] using hp₂

end GD.N0115
