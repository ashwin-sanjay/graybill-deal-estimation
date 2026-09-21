import GD.Module0453
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace GD.N0059



def d007001 (n : ℕ) (f : Fin n → Bool) : Bool := (List.finRange n).all f

theorem d007002 {n : ℕ} (f : Fin n → Bool) :
    _root_.GD.N0059.d007001 n f = true ↔ ∀ i, f i = true := by
  simp [_root_.GD.N0059.d007001, List.all_eq_true]

def d007003 (c : _root_.GD.N0059.d006978) (i : Fin 7) : Bool :=
  if c.root i = 0 then _root_.GD.N0059.d007001 4 (fun j => decide (c.density j i = 0)) else
    let qn := c.d006985 i
    let qd := c.d006984 i
    let rd := c.d006987 i
    let rm := c.d006988 i
    decide (0 < c.root i) && decide (0 < qn) && decide (0 < qd) &&
      decide (qn * _root_.GD.N0059.d006972 ^ 2 ≤ c.root i ^ 2 * qd) &&
      _root_.GD.N0059.d007001 4 (fun j =>
        let f := c.d006986 i j
        decide (0 ≤ f) && decide (((c.density j i * rd : ℕ) : ℤ) ≤ (rm : ℤ) * f))

theorem d007004 (c : _root_.GD.N0059.d006978) (i : Fin 7) :
    _root_.GD.N0059.d007003 c i = true ↔ c.d006989 i := by
  by_cases h : c.root i = 0
  · simp only [_root_.GD.N0059.d007003, _root_.GD.N0059.d006978.d006989, if_pos h, _root_.GD.N0059.d007002,
      decide_eq_true_eq]
  · simp only [_root_.GD.N0059.d007003, _root_.GD.N0059.d006978.d006989, if_neg h, Bool.and_eq_true,
      decide_eq_true_eq, _root_.GD.N0059.d007002, and_assoc]

def d007005 (f : Fin 7 → ℕ) : ℕ := f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6

theorem d007006 (f : Fin 7 → ℕ) : _root_.GD.N0059.d007005 f = ∑ i, f i := by
  simp [_root_.GD.N0059.d007005, Fin.sum_univ_succ, Nat.add_assoc]

def d007007 (c : _root_.GD.N0059.d006978) (j : Fin 4) : Bool :=
  let a := _root_.GD.N0059.d007005 (c.density j)
  let b := _root_.GD.N0059.d007005 (fun i => c.density j i * _root_.GD.N0059.d006976 i)
  let cc := _root_.GD.N0059.d007005 (fun i => c.density j i * _root_.GD.N0059.d006976 i ^ 2)
  decide (0 < a) && decide (b ^ 2 + a * c.quadratic j ≤ a * cc)

theorem d007008 (c : _root_.GD.N0059.d006978) (j : Fin 4) :
    _root_.GD.N0059.d007007 c j = true ↔ c.d006993 j := by
  simp only [_root_.GD.N0059.d007007, _root_.GD.N0059.d006978.d006993, Bool.and_eq_true, decide_eq_true_eq,
    _root_.GD.N0059.d007006, _root_.GD.N0059.d006978.d006990, _root_.GD.N0059.d006978.d006991, _root_.GD.N0059.d006978.d006992]

def d007009 (c : _root_.GD.N0059.d006978) : Bool :=
  decide (c.iu < 40) && decide (c.iz < 112) && decide (c.uLo < c.uHi) &&
    decide (c.uHi ≤ _root_.GD.N0059.d006974) && decide (0 < c.zLo) && decide (c.zLo < c.zHi) &&
    _root_.GD.N0059.d007001 7 (_root_.GD.N0059.d007003 c) && _root_.GD.N0059.d007001 4 (_root_.GD.N0059.d007007 c)

theorem d007010 (c : _root_.GD.N0059.d006978) : _root_.GD.N0059.d007009 c = true ↔ c.d006994 := by
  simp only [_root_.GD.N0059.d007009, _root_.GD.N0059.d006978.d006994, Bool.and_eq_true, decide_eq_true_eq,
    _root_.GD.N0059.d007002, _root_.GD.N0059.d007004, _root_.GD.N0059.d007008, and_assoc]

def d007011 (U Z : List ℕ) (cs : List _root_.GD.N0059.d006978) : Bool :=
  cs.all (fun c => _root_.GD.N0059.d007009 c && decide (c.d006995 U Z))

theorem d007012 (U Z : List ℕ) (css : List (List _root_.GD.N0059.d006978)) :
    _root_.GD.N0059.d007011 U Z css.flatten = css.all (_root_.GD.N0059.d007011 U Z) := by
  simp only [_root_.GD.N0059.d007011, List.all_flatten]
  rfl


theorem d007013 {U Z : List ℕ} {cs : List _root_.GD.N0059.d006978} :
    _root_.GD.N0059.d007011 U Z cs = true ↔ _root_.GD.N0059.d006996 U Z cs = true := by
  simp only [_root_.GD.N0059.d007011, _root_.GD.N0059.d006996, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, _root_.GD.N0059.d007010]

theorem d007014 {U Z : List ℕ} {cs : List _root_.GD.N0059.d006978}
    (h : _root_.GD.N0059.d007011 U Z cs = true) {c : _root_.GD.N0059.d006978} (hc : c ∈ cs) : c.d006994 :=
  _root_.GD.N0059.d006997 (_root_.GD.N0059.d007013.mp h) hc

theorem d007015 {U Z : List ℕ} {cs : List _root_.GD.N0059.d006978}
    (h : _root_.GD.N0059.d007011 U Z cs = true) {c : _root_.GD.N0059.d006978} (hc : c ∈ cs) : c.d006995 U Z :=
  _root_.GD.N0059.d006998 (_root_.GD.N0059.d007013.mp h) hc

end GD.N0059

#print axioms _root_.GD.N0059.d007004
#print axioms _root_.GD.N0059.d007010
#print axioms _root_.GD.N0059.d007013
#print axioms _root_.GD.N0059.d007014
#print axioms _root_.GD.N0059.d007015
