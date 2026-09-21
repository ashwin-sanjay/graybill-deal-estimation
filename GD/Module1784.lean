import GD.Module1761
import GD.Module0367















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Finset

namespace GD.N0106.N0428.N0765.N1687
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1539 ProbabilityTheory _root_.GD.N0106.N0428.N0765.N1568

def d029645 (a b j x : ℝ) : ℝ :=
  Real.exp (j * x) * _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x


def d029646 (a b j h c₀ : ℝ) (k : ℤ) : ℝ :=
  h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j (c₀ + (k : ℝ) * h)

def d029647 (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (fun n : ℕ => (n : ℤ))

def d029648 (a b j h cL : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1568.d005509 h (beta a b)⁻¹ (a + j) cL

def d029649 (a b j h cR : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1568.d005510 h (beta a b)⁻¹ (b - j) cR


def d029650 (a b j h cL cR : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1687.d029648 a b j h cL + _root_.GD.N0106.N0428.N0765.N1687.d029649 a b j h cR

def d029651 (a b j h c₀ : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1687.d029650 a b j h (c₀ - h) c₀

def d029652 (a b j h c₀ : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1687.d029650 a b j h (c₀ - h) (c₀ + N * h)

theorem d029653 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (j x : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j x :=
  mul_pos (Real.exp_pos _) (_root_.GD.N0106.N0428.N0765.N1539.d005375 ha hb x)

theorem d029654 {a b h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hh : 0 ≤ h) (j c₀ : ℝ) (k : ℤ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ k :=
  mul_nonneg hh (_root_.GD.N0106.N0428.N0765.N1687.d029653 ha hb j _).le

theorem d029655 {a b j h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hj : 0 < a + j) (hh : 0 < h) (cL : ℝ) :
    0 < _root_.GD.N0106.N0428.N0765.N1687.d029648 a b j h cL := by
  exact div_pos (mul_pos (mul_pos hh (inv_pos.mpr (beta_pos ha hb)))
    (Real.exp_pos _)) (_root_.GD.N0106.N0428.N0765.N1568.d005516 hj hh)

theorem d029656 {a b j h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hj : 0 < b - j) (hh : 0 < h) (cR : ℝ) :
    0 < _root_.GD.N0106.N0428.N0765.N1687.d029649 a b j h cR := by
  exact div_pos (mul_pos (mul_pos hh (inv_pos.mpr (beta_pos ha hb)))
    (Real.exp_pos _)) (_root_.GD.N0106.N0428.N0765.N1568.d005516 hj hh)

theorem d029657 {a b j h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hj : 0 < a + j) (hh : 0 < h) (cL : ℝ) :
    Summable (fun m : ℕ => h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)) ∧
      (∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)) ≤
        _root_.GD.N0106.N0428.N0765.N1687.d029648 a b j h cL := by
  apply _root_.GD.N0106.N0428.N0765.N1568.d005519 hj hh
  · intro m
    exact (_root_.GD.N0106.N0428.N0765.N1687.d029653 ha hb j _).le
  · intro m
    exact _root_.GD.N0106.N0428.N0765.N1688.d029141 ha hb j _

theorem d029658 {a b j h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hj : 0 < b - j) (hh : 0 < h) (cR : ℝ) :
    Summable (fun m : ℕ => h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)) ∧
      (∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)) ≤
        _root_.GD.N0106.N0428.N0765.N1687.d029649 a b j h cR := by
  apply _root_.GD.N0106.N0428.N0765.N1568.d005520 hj hh
  · intro m
    exact (_root_.GD.N0106.N0428.N0765.N1687.d029653 ha hb j _).le
  · intro m
    simpa only [_root_.GD.N0106.N0428.N0765.N1687.d029645, neg_mul] using _root_.GD.N0106.N0428.N0765.N1688.d029142 ha hb j
      (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)

theorem d029659 (f : ℤ → ℝ) (N : ℕ) :
    ∑ k ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, f k = ∑ n ∈ Finset.range N, f (n : ℤ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1687.d029647
  apply Finset.sum_image
  intro n hn m hm hnm
  exact Int.ofNat.inj hnm


theorem d029660 {a b j h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hjL : 0 < a + j) (hjR : 0 < b - j)
    (hh : 0 < h) (c₀ : ℝ) (N : ℕ) :
    HasSum (_root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀)
      ((∑ k ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ k) +
        (∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j (_root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h m)) +
        (∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j (_root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h m))) := by
  have hL := (_root_.GD.N0106.N0428.N0765.N1687.d029657 ha hb hjL hh (c₀ - h)).1.hasSum
  have hR := (_root_.GD.N0106.N0428.N0765.N1687.d029658 ha hb hjR hh (c₀ + N * h)).1.hasSum
  unfold _root_.GD.N0106.N0428.N0765.N1687.d029646
  simpa only [_root_.GD.N0106.N0428.N0765.N1687.d029659, _root_.GD.N0106.N0428.N0765.N1687.d029646, Int.cast_natCast] using
    (_root_.GD.N0106.N0428.N0765.N1568.d005521 (N := N) hL hR)

theorem d029661 {a b j h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hjL : 0 < a + j) (hjR : 0 < b - j)
    (hh : 0 < h) (c₀ : ℝ) : Summable (_root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀) :=
  (_root_.GD.N0106.N0428.N0765.N1687.d029660 ha hb hjL hjR hh c₀ 0).summable

theorem d029662 {a b j h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hjL : 0 < a + j) (hjR : 0 < b - j)
    (hh : 0 < h) (c₀ : ℝ) (N : ℕ) :
    0 ≤ (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ k) -
      ∑ k ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ k := by
  rw [(_root_.GD.N0106.N0428.N0765.N1687.d029660 ha hb hjL hjR hh c₀ N).tsum_eq]
  have hL : 0 ≤ ∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j (_root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h m) :=
    tsum_nonneg (fun m => mul_nonneg hh.le (_root_.GD.N0106.N0428.N0765.N1687.d029653 ha hb j _).le)
  have hR : 0 ≤ ∑' m : ℕ, h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j
      (_root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h m) :=
    tsum_nonneg (fun m => mul_nonneg hh.le (_root_.GD.N0106.N0428.N0765.N1687.d029653 ha hb j _).le)
  linarith

theorem d029663 {a b j h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hjL : 0 < a + j) (hjR : 0 < b - j)
    (hh : 0 < h) (c₀ : ℝ) (N : ℕ) :
    (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ k) -
      (∑ k ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ k) ≤
        _root_.GD.N0106.N0428.N0765.N1687.d029652 a b j h c₀ N := by
  rw [(_root_.GD.N0106.N0428.N0765.N1687.d029660 ha hb hjL hjR hh c₀ N).tsum_eq]
  have hL := (_root_.GD.N0106.N0428.N0765.N1687.d029657 ha hb hjL hh (c₀ - h)).2
  have hR := (_root_.GD.N0106.N0428.N0765.N1687.d029658 ha hb hjR hh (c₀ + N * h)).2
  unfold _root_.GD.N0106.N0428.N0765.N1687.d029652 _root_.GD.N0106.N0428.N0765.N1687.d029650
  linarith

theorem d029664 {a b j h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hjL : 0 < a + j) (hjR : 0 < b - j)
    (hh : 0 < h) (c₀ : ℝ) :
    (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ k) ≤ _root_.GD.N0106.N0428.N0765.N1687.d029651 a b j h c₀ := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1687.d029647, Finset.range_zero, Finset.image_empty, Finset.sum_empty,
    sub_zero, _root_.GD.N0106.N0428.N0765.N1687.d029652, Nat.cast_zero, zero_mul, add_zero, _root_.GD.N0106.N0428.N0765.N1687.d029651] using
    _root_.GD.N0106.N0428.N0765.N1687.d029663 ha hb hjL hjR hh c₀ 0


theorem d029665 (a b j h c₀ : ℝ) (k : ℤ) :
    (∑' n : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h (c₀ + (k : ℝ) * h) n) =
      ∑' n : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ n := by
  calc
    (∑' n : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h (c₀ + (k : ℝ) * h) n) =
        ∑' n : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ (n + k) := by
      apply tsum_congr
      intro n
      unfold _root_.GD.N0106.N0428.N0765.N1687.d029646
      apply congrArg (fun x : ℝ => h * _root_.GD.N0106.N0428.N0765.N1687.d029645 a b j x)
      push_cast
      ring
    _ = _ := (Equiv.addRight k).tsum_eq (_root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀)



theorem d029666 {a b j h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hjL : 0 < a + j) (hjR : 0 < b - j)
    (hh : 0 < h) (c₀ : ℝ) (k : ℤ) :
    (∑' n : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b j h c₀ n) ≤
      _root_.GD.N0106.N0428.N0765.N1687.d029651 a b j h (c₀ + (k : ℝ) * h) := by
  rw [← _root_.GD.N0106.N0428.N0765.N1687.d029665 a b j h c₀ k]
  exact _root_.GD.N0106.N0428.N0765.N1687.d029664 ha hb hjL hjR hh _


theorem d029667 (a b j h cL : ℝ) (N : ℕ) :
    _root_.GD.N0106.N0428.N0765.N1687.d029648 a b j h (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h N) =
      _root_.GD.N0106.N0428.N0765.N1687.d029648 a b j h cL * Real.exp (-((a + j) * h)) ^ N := by
  unfold _root_.GD.N0106.N0428.N0765.N1687.d029648 _root_.GD.N0106.N0428.N0765.N1568.d005509
  rw [_root_.GD.N0106.N0428.N0765.N1568.d005517]
  ring


theorem d029668 (a b j h cR : ℝ) (N : ℕ) :
    _root_.GD.N0106.N0428.N0765.N1687.d029649 a b j h (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h N) =
      _root_.GD.N0106.N0428.N0765.N1687.d029649 a b j h cR * Real.exp (-((b - j) * h)) ^ N := by
  unfold _root_.GD.N0106.N0428.N0765.N1687.d029649 _root_.GD.N0106.N0428.N0765.N1568.d005510
  rw [_root_.GD.N0106.N0428.N0765.N1568.d005518]
  ring

end
end GD.N0106.N0428.N0765.N1687

#print axioms _root_.GD.N0106.N0428.N0765.N1687.d029661
#print axioms _root_.GD.N0106.N0428.N0765.N1687.d029663
#print axioms _root_.GD.N0106.N0428.N0765.N1687.d029666
#print axioms _root_.GD.N0106.N0428.N0765.N1687.d029667
#print axioms _root_.GD.N0106.N0428.N0765.N1687.d029668
