import GD.Module1529
import GD.Module1528
import GD.Module1787













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option cbv.warning false

namespace GD.N0106.N0428.N0765.N1578

open _root_.GD.N0106.N0428.N0765.N1579 _root_.GD.N0106.N0428.N0765.N1581 _root_.GD.N0106.N0428.N0765.N1572 _root_.GD.N0106.N0428.N0765.N1548
open _root_.GD.N0106.N0428.N0765.N1539



def d029778 (f : ℕ → _root_.GD.N0106.N0428.N0765.N1579.d007457) (n : ℕ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  ⟨_root_.GD.N0106.N0428.N0765.N1548.d006926.d006943 (fun i => (f i).interval) n,
    decide (∀ i : Fin n, (f i.val).valid = true)⟩

def d029779 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
    (_root_.GD.N0106.N0428.N0765.N1578.d029778 (fun i => _root_.GD.N0106.N0428.N0765.N1579.d007470 (cache.d007468 ((i : ℤ) - 224))) 281) (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 16)

def d029780 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
    (_root_.GD.N0106.N0428.N0765.N1578.d029778 (fun i => _root_.GD.N0106.N0428.N0765.N1579.d007471 (cache.d007468 ((i : ℤ) - 80))) 161) (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 16)

def d029781 (coefficient numerator denominator : _root_.GD.N0106.N0428.N0765.N1579.d007457) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 16) coefficient) numerator)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007444 _root_.GD.N0106.N0428.N0765.N1579.d007459 denominator)

def d029782 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1578.d029781 (_root_.GD.N0106.N0428.N0765.N1579.d007460 4849845 131072)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007452 _root_.GD.N0106.N0428.N0765.N1579.d007456 (cache.d007468 (-675)))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007452 _root_.GD.N0106.N0428.N0765.N1579.d007456 (cache.d007468 (-3)))

def d029783 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1578.d029781 (_root_.GD.N0106.N0428.N0765.N1579.d007460 4849845 131072) (cache.d007468 (-570)) (cache.d007468 (-10))

def d029784 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 (_root_.GD.N0106.N0428.N0765.N1578.d029782 cache) (_root_.GD.N0106.N0428.N0765.N1578.d029783 cache)

def d029785 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1578.d029781 (_root_.GD.N0106.N0428.N0765.N1579.d007460 630 1) (cache.d007468 (-405)) (cache.d007468 (-5))

def d029786 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 (_root_.GD.N0106.N0428.N0765.N1578.d029785 cache) (_root_.GD.N0106.N0428.N0765.N1578.d029785 cache)

def d029787 : _root_.GD.N0106.N0428.N0765.N1579.d007457 := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 _root_.GD.N0106.N0428.N0765.N1579.d007458) (_root_.GD.N0106.N0428.N0765.N1579.d007460 11 1)

def d029788 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029787
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1578.d029784 cache)
        (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 (_root_.GD.N0106.N0428.N0765.N1578.d029780 cache) (_root_.GD.N0106.N0428.N0765.N1578.d029786 cache)))
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1578.d029779 cache) (_root_.GD.N0106.N0428.N0765.N1578.d029786 cache)))

noncomputable def d029789 (i : ℕ) : ℝ := ((i : ℝ) - 224) / 16
noncomputable def d029790 (i : ℕ) : ℝ := ((i : ℝ) - 80) / 16

noncomputable def d029791 : ℝ :=
  (∑ i ∈ Finset.range 281, _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 (_root_.GD.N0106.N0428.N0765.N1578.d029789 i)) * (1 / 16)

noncomputable def d029792 : ℝ :=
  (∑ i ∈ Finset.range 161, _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 (_root_.GD.N0106.N0428.N0765.N1578.d029790 i)) * (1 / 16)

noncomputable def d029793 : ℝ :=
  (1 / 16) * (4849845 / 131072) * Real.exp (-675 / 32) /
      (1 - Real.exp (-3 / 32)) +
    (1 / 16) * (4849845 / 131072) * Real.exp (-570 / 16) /
      (1 - Real.exp (-10 / 16))

noncomputable def d029794 : ℝ :=
  (1 / 16) * 630 * Real.exp (-405 / 16) / (1 - Real.exp (-5 / 16)) +
    (1 / 16) * 630 * Real.exp (-405 / 16) / (1 - Real.exp (-5 / 16))

noncomputable def d029795 : ℝ :=
  (1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) / 11 *
    (_root_.GD.N0106.N0428.N0765.N1578.d029793 * (_root_.GD.N0106.N0428.N0765.N1578.d029792 + _root_.GD.N0106.N0428.N0765.N1578.d029794) + _root_.GD.N0106.N0428.N0765.N1578.d029791 * _root_.GD.N0106.N0428.N0765.N1578.d029794)

private theorem d029796 {f : ℕ → _root_.GD.N0106.N0428.N0765.N1579.d007457} {g : ℕ → ℝ} {n : ℕ}
    (h : ∀ i, i < n → (f i).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (g i)) :
    (_root_.GD.N0106.N0428.N0765.N1578.d029778 f n).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (∑ i ∈ Finset.range n, g i) :=
  _root_.GD.N0106.N0428.N0765.N1548.d006926.d006954 (fun i => (f i).interval) g n h

theorem d029797 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023725 cache)
    (hv : (_root_.GD.N0106.N0428.N0765.N1578.d029779 cache).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1578.d029779 cache).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029791 := by
  have hsum := (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv).1
  have hvalid : ∀ i : Fin 281,
      (_root_.GD.N0106.N0428.N0765.N1579.d007470 (cache.d007468 ((i.val : ℤ) - 224))).valid = true := of_decide_eq_true hsum
  have hstep : (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 16).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (1 / 16 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 1) (d := 16) (by decide))
  unfold _root_.GD.N0106.N0428.N0765.N1578.d029779 _root_.GD.N0106.N0428.N0765.N1578.d029791
  apply _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv ?_ hstep
  apply _root_.GD.N0106.N0428.N0765.N1578.d029796
  intro i hi
  have hgrid := hc.1 ((i : ℤ) - 224) (by constructor <;> omega)
  have hexp : (((i : ℤ) - 224 : ℤ) : ℝ) / 16 = _root_.GD.N0106.N0428.N0765.N1578.d029789 i := by
    simp [_root_.GD.N0106.N0428.N0765.N1578.d029789]
  rw [hexp] at hgrid
  exact _root_.GD.N0106.N0428.N0765.N1572.d023805 hgrid (hvalid ⟨i, hi⟩)

theorem d029798 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023725 cache)
    (hv : (_root_.GD.N0106.N0428.N0765.N1578.d029780 cache).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1578.d029780 cache).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029792 := by
  have hsum := (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv).1
  have hvalid : ∀ i : Fin 161,
      (_root_.GD.N0106.N0428.N0765.N1579.d007471 (cache.d007468 ((i.val : ℤ) - 80))).valid = true := of_decide_eq_true hsum
  have hstep : (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 16).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (1 / 16 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 1) (d := 16) (by decide))
  unfold _root_.GD.N0106.N0428.N0765.N1578.d029780 _root_.GD.N0106.N0428.N0765.N1578.d029792
  apply _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv ?_ hstep
  apply _root_.GD.N0106.N0428.N0765.N1578.d029796
  intro i hi
  have hgrid := hc.1 ((i : ℤ) - 80) (by constructor <;> omega)
  have hexp : (((i : ℤ) - 80 : ℤ) : ℝ) / 16 = _root_.GD.N0106.N0428.N0765.N1578.d029790 i := by
    simp [_root_.GD.N0106.N0428.N0765.N1578.d029790]
  rw [hexp] at hgrid
  exact _root_.GD.N0106.N0428.N0765.N1572.d023806 hgrid (hvalid ⟨i, hi⟩)

private theorem d029799 {C N D : _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (hv : (_root_.GD.N0106.N0428.N0765.N1578.d029781 C N D).valid = true) : N.valid = true ∧ D.valid = true := by
  have h := _root_.GD.N0106.N0428.N0765.N1572.d023749 hv
  have hden := h.2
  change (_root_.GD.N0106.N0428.N0765.N1579.d007459.valid && D.valid) = true at hden
  exact ⟨(_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 h.1).2, (Bool.and_eq_true_iff.mp hden).2⟩

private theorem d029800 {C N D : _root_.GD.N0106.N0428.N0765.N1579.d007457} {c n d : ℝ}
    (hv : (_root_.GD.N0106.N0428.N0765.N1578.d029781 C N D).valid = true)
    (hc : C.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 c) (hn : N.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 n) (hd : D.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 d) :
    (_root_.GD.N0106.N0428.N0765.N1578.d029781 C N D).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 ((1 / 16) * c * n / (1 - d)) := by
  have hnum := (_root_.GD.N0106.N0428.N0765.N1572.d023749 hv).1
  have hcoef := (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hnum).1
  have hstep : (_root_.GD.N0106.N0428.N0765.N1579.d007460 1 16).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (1 / 16 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 1) (d := 16) (by decide))
  exact _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hv
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hnum
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hcoef hstep hc) hn)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007734 _root_.GD.N0106.N0428.N0765.N1581.d023717 hd)

private theorem d029801 (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  have he : Real.exp x = (Real.exp (x / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

private theorem d029802 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023725 cache)
    (k : ℤ) (hk : -1690 ≤ k ∧ k ≤ 1690)
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007452 _root_.GD.N0106.N0428.N0765.N1579.d007456 (cache.d007468 k)).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007452 _root_.GD.N0106.N0428.N0765.N1579.d007456 (cache.d007468 k)).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (Real.exp ((k : ℝ) / 32)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007742 hv (hc.1 k hk)
  rw [_root_.GD.N0106.N0428.N0765.N1578.d029801, show ((k : ℝ) / 16) / 2 = (k : ℝ) / 32 by ring] at h
  exact h

theorem d029803 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023725 cache)
    (hv : (_root_.GD.N0106.N0428.N0765.N1578.d029784 cache).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1578.d029784 cache).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029793 := by
  have hparts := Bool.and_eq_true_iff.mp hv
  have hhalf := _root_.GD.N0106.N0428.N0765.N1578.d029799 hparts.1
  have hcoef : (_root_.GD.N0106.N0428.N0765.N1579.d007460 4849845 131072).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (4849845 / 131072 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 4849845) (d := 131072) (by decide))
  have hleft := _root_.GD.N0106.N0428.N0765.N1578.d029800 hparts.1
    hcoef
    (_root_.GD.N0106.N0428.N0765.N1578.d029802 hc (-675) (by constructor <;> norm_num) hhalf.1)
    (_root_.GD.N0106.N0428.N0765.N1578.d029802 hc (-3) (by constructor <;> norm_num) hhalf.2)
  have hright := _root_.GD.N0106.N0428.N0765.N1578.d029800 hparts.2
    hcoef
    (hc.1 (-570) (by constructor <;> norm_num))
    (hc.1 (-10) (by constructor <;> norm_num))
  simpa only [_root_.GD.N0106.N0428.N0765.N1578.d029784, _root_.GD.N0106.N0428.N0765.N1578.d029782, _root_.GD.N0106.N0428.N0765.N1578.d029783, _root_.GD.N0106.N0428.N0765.N1578.d029793,
    Int.cast_neg, Int.cast_ofNat] using
    _root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 hleft hright

theorem d029804 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023725 cache)
    (hv : (_root_.GD.N0106.N0428.N0765.N1578.d029786 cache).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1578.d029786 cache).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029794 := by
  have hone := (Bool.and_eq_true_iff.mp hv).1
  have hcoef : (_root_.GD.N0106.N0428.N0765.N1579.d007460 630 1).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (630 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 630) (d := 1) (by decide))
  have hside := _root_.GD.N0106.N0428.N0765.N1578.d029800 hone hcoef
    (hc.1 (-405) (by constructor <;> norm_num))
    (hc.1 (-5) (by constructor <;> norm_num))
  simpa only [_root_.GD.N0106.N0428.N0765.N1578.d029786, _root_.GD.N0106.N0428.N0765.N1578.d029785, _root_.GD.N0106.N0428.N0765.N1578.d029794, Int.cast_neg, Int.cast_ofNat] using
    _root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 hside hside

theorem d029805 (hv : _root_.GD.N0106.N0428.N0765.N1578.d029787.valid = true) :
    _root_.GD.N0106.N0428.N0765.N1578.d029787.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 ((1 + _root_.GD.N0106.N0428.N0765.N1572.d023746) / 11) := by
  have hden : (_root_.GD.N0106.N0428.N0765.N1579.d007460 11 1).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (11 : ℝ) := by
    simpa using (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 11) (d := 1) (by decide))
  unfold _root_.GD.N0106.N0428.N0765.N1578.d029787
  exact _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hv
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 _root_.GD.N0106.N0428.N0765.N1572.d023748) hden



theorem d029806 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023725 cache)
    (hv : (_root_.GD.N0106.N0428.N0765.N1578.d029788 cache).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1578.d029788 cache).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029795 := by
  have hparts := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv
  have hsums := Bool.and_eq_true_iff.mp hparts.2
  have hleft := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hsums.1
  have hright := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hsums.2
  have hbparts := Bool.and_eq_true_iff.mp hleft.2
  exact _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv (_root_.GD.N0106.N0428.N0765.N1578.d029805 hparts.1)
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hsums.1
        (_root_.GD.N0106.N0428.N0765.N1578.d029803 hc hleft.1)
        (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 (_root_.GD.N0106.N0428.N0765.N1578.d029798 hc hbparts.1)
          (_root_.GD.N0106.N0428.N0765.N1578.d029804 hc hbparts.2)))
      (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hsums.2
        (_root_.GD.N0106.N0428.N0765.N1578.d029797 hc hright.1) (_root_.GD.N0106.N0428.N0765.N1578.d029804 hc hright.2)))



def d029807 : _root_.GD.N0106.N0428.N0765.N1548.d006926 :=
  ⟨25583252836174566390213134311486087317566379900068,
    25583252836174566390213134311486087317570043054801⟩

theorem d029808 : _root_.GD.N0106.N0428.N0765.N1578.d029788 _root_.GD.N0106.N0428.N0765.N1575.d007495 = ⟨_root_.GD.N0106.N0428.N0765.N1578.d029807, true⟩ := by
  decide +kernel

theorem d029809 : _root_.GD.N0106.N0428.N0765.N1578.d029807.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029795 := by
  have hv : (_root_.GD.N0106.N0428.N0765.N1578.d029788 _root_.GD.N0106.N0428.N0765.N1575.d007495).valid = true := by
    rw [_root_.GD.N0106.N0428.N0765.N1578.d029808]
  have h := _root_.GD.N0106.N0428.N0765.N1578.d029806 _root_.GD.N0106.N0428.N0765.N1574.d023745 hv
  rw [_root_.GD.N0106.N0428.N0765.N1578.d029808] at h
  exact h



theorem d029810 : _root_.GD.N0106.N0428.N0765.N1582.d007423.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029795 := by
  apply _root_.GD.N0106.N0428.N0765.N1548.d006926.d006933 _root_.GD.N0106.N0428.N0765.N1573.d022632 _root_.GD.N0106.N0428.N0765.N1578.d029809
  · decide
  · decide



theorem d029811 :
    _root_.GD.N0106.N0428.N0765.N1518.d029719 (1 / 16) (-14) 281 = _root_.GD.N0106.N0428.N0765.N1578.d029791 := by
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029719 _root_.GD.N0106.N0428.N0765.N1578.d029791
  rw [_root_.GD.N0106.N0428.N0765.N1687.d029659, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029717 _root_.GD.N0106.N0428.N0765.N1687.d029646
    _root_.GD.N0106.N0428.N0765.N1687.d029645
  simp only [zero_mul, Real.exp_zero, one_mul, Int.cast_natCast]
  rw [show (-14 : ℝ) + (i : ℝ) * (1 / 16) = _root_.GD.N0106.N0428.N0765.N1578.d029789 i by
    unfold _root_.GD.N0106.N0428.N0765.N1578.d029789; ring]
  ring


theorem d029812 :
    _root_.GD.N0106.N0428.N0765.N1518.d029720 (1 / 16) (-5) 161 = _root_.GD.N0106.N0428.N0765.N1578.d029792 := by
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029720 _root_.GD.N0106.N0428.N0765.N1578.d029792
  rw [_root_.GD.N0106.N0428.N0765.N1687.d029659, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029718 _root_.GD.N0106.N0428.N0765.N1687.d029646
    _root_.GD.N0106.N0428.N0765.N1687.d029645
  simp only [zero_mul, Real.exp_zero, one_mul, Int.cast_natCast]
  rw [show (-5 : ℝ) + (i : ℝ) * (1 / 16) = _root_.GD.N0106.N0428.N0765.N1578.d029790 i by
    unfold _root_.GD.N0106.N0428.N0765.N1578.d029790; ring]
  ring


theorem d029813 :
    _root_.GD.N0106.N0428.N0765.N1518.d029721 (1 / 16) (-14) 281 = _root_.GD.N0106.N0428.N0765.N1578.d029793 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1518.d029721, _root_.GD.N0106.N0428.N0765.N1687.d029652,
    _root_.GD.N0106.N0428.N0765.N1687.d029650, _root_.GD.N0106.N0428.N0765.N1687.d029648,
    _root_.GD.N0106.N0428.N0765.N1687.d029649, _root_.GD.N0106.N0428.N0765.N1568.d005509,
    _root_.GD.N0106.N0428.N0765.N1568.d005510, _root_.GD.N0106.N0428.N0765.N1539.d005359, _root_.GD.N0106.N0428.N0765.N1578.d029793]


theorem d029814 :
    _root_.GD.N0106.N0428.N0765.N1518.d029722 (1 / 16) (-5) 161 = _root_.GD.N0106.N0428.N0765.N1578.d029794 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1518.d029722, _root_.GD.N0106.N0428.N0765.N1687.d029652,
    _root_.GD.N0106.N0428.N0765.N1687.d029650, _root_.GD.N0106.N0428.N0765.N1687.d029648,
    _root_.GD.N0106.N0428.N0765.N1687.d029649, _root_.GD.N0106.N0428.N0765.N1568.d005509,
    _root_.GD.N0106.N0428.N0765.N1568.d005510, _root_.GD.N0106.N0428.N0765.N1539.d005360, _root_.GD.N0106.N0428.N0765.N1578.d029794]


theorem d029815 :
    _root_.GD.N0106.N0428.N0765.N1518.d029724 _root_.GD.N0106.N0428.N0765.N1572.d023746 (1 / 16) (1 / 16) (-14) (-5) 281 161 =
      _root_.GD.N0106.N0428.N0765.N1578.d029795 := by
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029724 _root_.GD.N0106.N0428.N0765.N1578.d029795
  rw [_root_.GD.N0106.N0428.N0765.N1578.d029811, _root_.GD.N0106.N0428.N0765.N1578.d029812, _root_.GD.N0106.N0428.N0765.N1578.d029813, _root_.GD.N0106.N0428.N0765.N1578.d029814]


theorem d029816 : _root_.GD.N0106.N0428.N0765.N1582.d007423.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456
    (_root_.GD.N0106.N0428.N0765.N1518.d029724 _root_.GD.N0106.N0428.N0765.N1572.d023746 (1 / 16) (1 / 16) (-14) (-5) 281 161) := by
  rw [_root_.GD.N0106.N0428.N0765.N1578.d029815]
  exact _root_.GD.N0106.N0428.N0765.N1578.d029810


noncomputable def d029817 : ℝ :=
  ∑ i ∈ Finset.range 281, ∑ j ∈ Finset.range 161,
    (1 / 16 : ℝ) ^ 2 *
      _root_.GD.N0106.N0428.N0765.N1549.d023700 _root_.GD.N0106.N0428.N0765.N1572.d023746 (_root_.GD.N0106.N0428.N0765.N1578.d029789 i, _root_.GD.N0106.N0428.N0765.N1578.d029790 j)


theorem d029818 :
    (∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 281 ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 161,
      _root_.GD.N0106.N0428.N0765.N1518.d029723 _root_.GD.N0106.N0428.N0765.N1572.d023746 (1 / 16) (1 / 16) (-14) (-5) p) =
        _root_.GD.N0106.N0428.N0765.N1578.d029817 := by
  rw [Finset.sum_product]
  simp_rw [_root_.GD.N0106.N0428.N0765.N1687.d029659]
  unfold _root_.GD.N0106.N0428.N0765.N1578.d029817
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold _root_.GD.N0106.N0428.N0765.N1518.d029723
  simp only [Int.cast_natCast, Prod.fst, Prod.snd]
  rw [show (-14 : ℝ) + (i : ℝ) * (1 / 16) = _root_.GD.N0106.N0428.N0765.N1578.d029789 i by
    unfold _root_.GD.N0106.N0428.N0765.N1578.d029789; ring]
  rw [show (-5 : ℝ) + (j : ℝ) * (1 / 16) = _root_.GD.N0106.N0428.N0765.N1578.d029790 j by
    unfold _root_.GD.N0106.N0428.N0765.N1578.d029790; ring]
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029220 _root_.GD.N0106.N0428.N0765.N1549.d023700
  ring



theorem d029819 :
    |(∑' p, _root_.GD.N0106.N0428.N0765.N1518.d029723 _root_.GD.N0106.N0428.N0765.N1572.d023746 (1 / 16) (1 / 16) (-14) (-5) p) -
      _root_.GD.N0106.N0428.N0765.N1578.d029817| ≤ _root_.GD.N0106.N0428.N0765.N1578.d029795 := by
  have h := _root_.GD.N0106.N0428.N0765.N1518.d029726 _root_.GD.N0106.N0428.N0765.N1572.d023747
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (0 : ℝ) < 1 / 16)
    (-14) (-5) 281 161
  rw [_root_.GD.N0106.N0428.N0765.N1578.d029818, _root_.GD.N0106.N0428.N0765.N1578.d029815, Real.norm_eq_abs] at h
  exact h

end GD.N0106.N0428.N0765.N1578

#print axioms _root_.GD.N0106.N0428.N0765.N1578.d029810

#print axioms _root_.GD.N0106.N0428.N0765.N1578.d029816
#print axioms _root_.GD.N0106.N0428.N0765.N1578.d029819
