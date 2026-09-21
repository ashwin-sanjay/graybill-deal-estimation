import GD.Module1397
import GD.Module1405
import GD.Module1402











set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace GD.N0189
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0180 _root_.GD.N0163 _root_.GD.N0172
open _root_.GD.N0164 _root_.GD.N0194 _root_.GD.N0188
open _root_.GD.N0193 _root_.GD.N0177 _root_.GD.N0160


def d022588 (g : _root_.GD.N0172.d022466) : Prop :=
  ∀ r : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0180.d022173 r (_root_.GD.N0163.d022211 g.1) ≤ Real.pi / 4

theorem d022589 (g : _root_.GD.N0172.d022466) :
    _root_.GD.N0189.d022588 g ↔ _root_.GD.N0194.d022558 g = _root_.GD.N0194.d022559 := by
  constructor
  · intro hg
    apply le_antisymm
    · rw [_root_.GD.N0170.d022587.2.1]
      exact iSup_le (fun r => ENNReal.ofReal_le_ofReal (hg r))
    · exact iInf_le _root_.GD.N0194.d022558 g
  · intro hg r
    have hvalue : _root_.GD.N0194.d022558 g = ENNReal.ofReal (Real.pi / 4) :=
      hg.trans _root_.GD.N0170.d022587.2.1
    have hfinite : _root_.GD.N0194.d022558 g ≠ ⊤ := by rw [hvalue]; exact ENNReal.ofReal_ne_top
    have h := _root_.GD.N0194.d022560 g hfinite r
    simpa only [hvalue, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi / 4)] using h

theorem d022590 {I : Type*} [Fintype I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 ≤ p i)
    (hsum : (∑ i, p i) = 1) (g : _root_.GD.N0172.d022466) (hg : _root_.GD.N0189.d022588 g) :
    (∫ r, _root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g.1) r ∂_root_.GD.N0164.d022432 p t) ≤ Real.pi / 4 := by
  rw [_root_.GD.N0164.d022435 p t hp]
  have hsumBound : _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 g.1) ≤
      ∑ i, p i * (Real.pi / 4) := by
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hg (t i)) (hp i))
  simpa only [← Finset.sum_mul, hsum, one_mul] using hsumBound


def d022591 {N : ℕ} (hN : 2 ≤ N) : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  _root_.GD.N0188.d022486 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)

theorem d022592 {N : ℕ} (hN : 2 ≤ N) :
    IsFiniteMeasure (_root_.GD.N0189.d022591 hN) := by
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  exact _root_.GD.N0188.d022490 _ _ (fun _ => _root_.GD.N0193.d007367 hN)

def d022593 {N : ℕ} (hN : 2 ≤ N) (g : _root_.GD.N0172.d022466) :
    Lp ℝ 2 (_root_.GD.N0189.d022591 hN) := by
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  exact _root_.GD.N0188.d022498 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
    (fun _ => _root_.GD.N0193.d007367 hN) g


def d022594 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0172.d022466 := by
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  exact _root_.GD.N0172.d022478 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
    (fun _ => _root_.GD.N0193.d007367 hN)

theorem d022595 {N : ℕ} (hN : 2 ≤ N) (x : _root_.GD.N0232.N0720.N1436.d013218) :
    (_root_.GD.N0189.d022594 hN).1 x =
      _root_.GD.N0163.d022179 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) x /
        _root_.GD.N0163.d022178 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) x := by
  exact _root_.GD.N0163.d022193 _ _ x.property


theorem d022596 {N : ℕ} (hN : 2 ≤ N) (g : _root_.GD.N0172.d022466) :
    ‖_root_.GD.N0189.d022593 hN g -
        _root_.GD.N0189.d022593 hN (_root_.GD.N0189.d022594 hN)‖ ^ 2 =
      (∫ r, _root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g.1) r ∂_root_.GD.N0193.d007351 N) - _root_.GD.N0160.d022516 N := by
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  rw [_root_.GD.N0164.d022436 hN, _root_.GD.N0160.d022517 hN]
  exact _root_.GD.N0188.d022501 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
    (fun _ => _root_.GD.N0193.d007367 hN) g


theorem d022597 {N : ℕ} (hN : 16 ≤ N)
    (g : _root_.GD.N0172.d022466) (hg : _root_.GD.N0189.d022588 g) :
    ‖_root_.GD.N0189.d022593 (Nat.le_trans (Nat.le_add_right 2 14) hN) g -
        _root_.GD.N0189.d022593 (Nat.le_trans (Nat.le_add_right 2 14) hN)
          (_root_.GD.N0189.d022594 (Nat.le_trans (Nat.le_add_right 2 14) hN))‖ ^ 2 ≤
        Real.pi / 4 - _root_.GD.N0160.d022516 N ∧
      Real.pi / 4 - _root_.GD.N0160.d022516 N < 14 / (N : ℝ) := by
  have hN2 : 2 ≤ N := by omega
  have hchain := _root_.GD.N0191.d022552 hN
  refine ⟨?_, hchain.1.trans_lt (hchain.2.1.trans_lt hchain.2.2)⟩
  rw [_root_.GD.N0189.d022596 hN2]
  apply sub_le_sub_right
  rw [_root_.GD.N0164.d022436 hN2]
  exact _root_.GD.N0189.d022590 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N)
    (_root_.GD.N0177.d022414 hN2) (fun _ => (_root_.GD.N0193.d007367 hN2).le) (_root_.GD.N0193.d007374 hN2) g hg


theorem d022598 {N : ℕ} (hN : 16 ≤ N)
    (g h : _root_.GD.N0172.d022466) (hg : _root_.GD.N0189.d022588 g) (hh : _root_.GD.N0189.d022588 h) :
    ‖_root_.GD.N0189.d022593 (Nat.le_trans (Nat.le_add_right 2 14) hN) g -
        _root_.GD.N0189.d022593 (Nat.le_trans (Nat.le_add_right 2 14) hN) h‖ ^ 2 < 56 / (N : ℝ) := by
  have hN2 : 2 ≤ N := by omega
  let a := _root_.GD.N0189.d022593 hN2 g
  let b := _root_.GD.N0189.d022593 hN2 h
  let c := _root_.GD.N0189.d022593 hN2 (_root_.GD.N0189.d022594 hN2)
  have hg2 : ‖a - c‖ ^ 2 < 14 / (N : ℝ) :=
    (_root_.GD.N0189.d022597 hN g hg).1.trans_lt (_root_.GD.N0189.d022597 hN g hg).2
  have hh2 : ‖b - c‖ ^ 2 < 14 / (N : ℝ) :=
    (_root_.GD.N0189.d022597 hN h hh).1.trans_lt (_root_.GD.N0189.d022597 hN h hh).2
  have htriangle : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
    calc
      ‖a - b‖ = ‖(a - c) - (b - c)‖ := by congr 1; abel
      _ ≤ ‖a - c‖ + ‖b - c‖ := norm_sub_le _ _
  have hsquare : ‖a - b‖ ^ 2 ≤ (‖a - c‖ + ‖b - c‖) ^ 2 := by
    nlinarith [norm_nonneg (a - b), norm_nonneg (a - c), norm_nonneg (b - c)]
  have hcross := sq_nonneg (‖a - c‖ - ‖b - c‖)
  change ‖a - b‖ ^ 2 < _
  calc
    ‖a - b‖ ^ 2 < 2 * (14 / (N : ℝ)) + 2 * (14 / (N : ℝ)) := by
      nlinarith
    _ = 56 / (N : ℝ) := by ring

end
end GD.N0189

#print axioms _root_.GD.N0189.d022589
#print axioms _root_.GD.N0189.d022590
#print axioms _root_.GD.N0189.d022592
#print axioms _root_.GD.N0189.d022595
#print axioms _root_.GD.N0189.d022596
#print axioms _root_.GD.N0189.d022597
#print axioms _root_.GD.N0189.d022598
