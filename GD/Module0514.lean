import GD.Module0480
import GD.Module0513








set_option autoImplicit false
set_option warningAsError true

namespace GD.N0106.N0428.N0765.N1579.d007436
open _root_.GD.N0106.N0428.N0765.N1548

def d007727 (s : ℤ) (I : _root_.GD.N0106.N0428.N0765.N1579.d007436) (x : ℝ) : Prop := I.interval.d006928 s x

theorem d007728 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hx : I.d006928 s x) : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 I).d007727 s x := hx

theorem d007729 (s : ℤ) : _root_.GD.N0106.N0428.N0765.N1579.d007436.d007439.d007727 s 0 := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006948 s

theorem d007730 {s : ℤ} (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007440 s).valid = true) : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007440 s).d007727 s 1 := by
  have hs : 0 < s := of_decide_eq_true hv
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006949 hs

theorem d007731 {s n d : ℤ} (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007441 s n d).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007441 s n d).d007727 s ((n : ℝ) / (d : ℝ)) := by
  have hc : 0 < s ∧ 0 < d := of_decide_eq_true hv
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006964 hc.1 hc.2 n

theorem d007732 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x y : ℝ}
    (hx : I.d007727 s x) (hy : J.d007727 s y) : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 I J).d007727 s (x + y) :=
  _root_.GD.N0106.N0428.N0765.N1548.d006926.d006951 hx hy

theorem d007733 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x : ℝ}
    (hx : I.d007727 s x) : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007443 I).d007727 s (-x) := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006952 hx

theorem d007734 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x y : ℝ}
    (hx : I.d007727 s x) (hy : J.d007727 s y) : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007444 I J).d007727 s (x - y) :=
  _root_.GD.N0106.N0428.N0765.N1548.d006926.d006953 hx hy

theorem d007735 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x y : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007445 s I J).valid = true) (hx : I.d007727 s x) (hy : J.d007727 s y) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007445 s I J).d007727 s (x * y) := by
  have hc : 0 < s ∧ 0 ≤ I.interval.lo ∧ 0 ≤ J.interval.lo :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hv).2
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006965 hc.1 hc.2.1 hc.2.2 hx hy

theorem d007736 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x y : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007446 s I J).valid = true) (hx : I.d007727 s x) (hy : J.d007727 s y) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007446 s I J).d007727 s (x * y) := by
  have hs : 0 < s := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).2
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d007725 hs hx hy

theorem d007737 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1579.d007436}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 s I J).valid = true) : I.valid = true ∧ J.valid = true := by
  by_cases hc : 0 ≤ I.interval.lo ∧ 0 ≤ J.interval.lo
  · simp only [_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447, if_pos hc, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007445] at hv
    exact Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1
  · simp only [_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447, if_neg hc, _root_.GD.N0106.N0428.N0765.N1579.d007436.d007446] at hv
    exact Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1

theorem d007738 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x y : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 s I J).valid = true) (hx : I.d007727 s x) (hy : J.d007727 s y) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 s I J).d007727 s (x * y) := by
  by_cases hc : 0 ≤ I.interval.lo ∧ 0 ≤ J.interval.lo
  · simp only [_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447, if_pos hc] at hv ⊢
    exact _root_.GD.N0106.N0428.N0765.N1579.d007436.d007735 hv hx hy
  · simp only [_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447, if_neg hc] at hv ⊢
    exact _root_.GD.N0106.N0428.N0765.N1579.d007436.d007736 hv hx hy

theorem d007739 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 s I).valid = true) (hx : I.d007727 s x) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 s I).d007727 s (1 / x) := by
  have hc : 0 < s ∧ 0 < I.interval.lo := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).2
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006966 hc.1 hc.2 hx

theorem d007740 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x y : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 s I J).valid = true) (hx : I.d007727 s x) (hy : J.d007727 s y) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 s I J).d007727 s (x / y) := by
  have hInv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 s J).valid = true := (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv).2
  have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv hx (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007739 hInv hy)
  simpa only [_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449, div_eq_mul_inv, one_div, one_mul] using h

theorem d007741 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x : ℝ} (n : ℕ)
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007450 s I n).valid = true) (hx : I.d007727 s x) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007450 s I n).d007727 s (x ^ n) := by
  have hc : 0 < s ∧ 0 ≤ I.interval.lo := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).2
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006967 hc.1 hc.2 hx n



theorem d007742 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007452 s I).valid = true) (hx : I.d007727 s x) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007452 s I).d007727 s (Real.sqrt x) := by
  have hv' := Bool.and_eq_true_iff.mp hv
  have hs : 0 < s := of_decide_eq_true (Bool.and_eq_true_iff.mp hv'.1).2
  have hc : _root_.GD.N0106.N0428.N0765.N1548.d006926.d006947 s I.interval (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007451 s I.interval) :=
    of_decide_eq_true hv'.2
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006968 hs hx hc

theorem d007743 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007453 s I).valid = true) (hx : I.d007727 s x) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007453 s I).d007727 s (x ^ 2) := by
  have hs : 0 < s := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).2
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d007726 hs hx

theorem d007744 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007454 s I).valid = true) (hx : I.d007727 s x)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007454 s I).d007727 s x := by
  have hc : 0 < s ∧ (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006942 s I.interval).lo ≤
      (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006942 s I.interval).hi := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).2
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006955 hc.1 hx hx0 hx1



theorem d007745 {s : ℤ} {L U : _root_.GD.N0106.N0428.N0765.N1579.d007436} {x : ℝ}
    (hlo : (L.interval.lo : ℝ) / (s : ℝ) ≤ x)
    (hhi : x ≤ (U.interval.hi : ℝ) / (s : ℝ)) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007455 L U).d007727 s x := ⟨hlo, hhi⟩

theorem d007746 {s : ℤ} {L U : _root_.GD.N0106.N0428.N0765.N1579.d007436} {l u x : ℝ}
    (hL : L.d007727 s l) (hU : U.d007727 s u) (hl : l ≤ x) (hu : x ≤ u) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007455 L U).d007727 s x := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007745 (hL.1.trans hl) (hu.trans hU.2)

end GD.N0106.N0428.N0765.N1579.d007436

#print axioms _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738
#print axioms _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740
#print axioms _root_.GD.N0106.N0428.N0765.N1579.d007436.d007742
#print axioms _root_.GD.N0106.N0428.N0765.N1579.d007436.d007746
