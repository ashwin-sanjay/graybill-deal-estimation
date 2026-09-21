import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace GD.N0059

def d006971 : ℕ := 2 ^ 80
def d006972 : ℕ := 2 ^ 24
def d006973 : ℕ := 1024
def d006974 : ℕ := 4096
def d006975 : ℕ := 512
def d006976 : Fin 7 → ℕ := ![1, 8, 128, 512, 896, 1016, 1023]
def d006977 : Fin 7 → ℕ := ![3, 16, 26, 10, 26, 16, 3]

structure d006978 where
  iu : ℕ
  iz : ℕ
  uLo : ℕ
  uHi : ℕ
  zLo : ℕ
  zHi : ℕ
  root : Fin 7 → ℕ
  density : Fin 4 → Fin 7 → ℕ
  quadratic : Fin 4 → ℕ

def d006978.d006979 (c : _root_.GD.N0059.d006978) : ℕ := c.iu * 112 + c.iz
def d006978.d006980 (c : _root_.GD.N0059.d006978) : ℕ := c.uLo + c.uHi
def d006978.d006981 (c : _root_.GD.N0059.d006978) : ℕ := c.zLo + c.zHi
def d006978.d006982 (c : _root_.GD.N0059.d006978) (j : Fin 4) : ℕ := if j.val < 2 then c.uLo else c.uHi
def d006978.d006983 (c : _root_.GD.N0059.d006978) (j : Fin 4) : ℕ := if j.val % 2 = 0 then c.zLo else c.zHi


def d006978.d006984 (_c : _root_.GD.N0059.d006978) (i : Fin 7) : ℕ :=
  _root_.GD.N0059.d006973 ^ 2 * _root_.GD.N0059.d006974 * _root_.GD.N0059.d006976 i *
    (_root_.GD.N0059.d006973 - _root_.GD.N0059.d006976 i)


def d006978.d006985 (c : _root_.GD.N0059.d006978) (i : Fin 7) : ℕ :=
  c.d006981 ^ 2 * _root_.GD.N0059.d006974 * _root_.GD.N0059.d006976 i *
      (_root_.GD.N0059.d006973 - _root_.GD.N0059.d006976 i) +
    _root_.GD.N0059.d006973 ^ 3 *
      ((2 * _root_.GD.N0059.d006974 - c.d006980) * _root_.GD.N0059.d006976 i +
        c.d006980 * (_root_.GD.N0059.d006973 - _root_.GD.N0059.d006976 i))


def d006978.d006986 (c : _root_.GD.N0059.d006978) (i : Fin 7) (j : Fin 4) : ℤ :=
  6 * (c.d006981 : ℤ) * c.d006985 i - 7 *
    (3 * (c.d006981 : ℤ) * (_root_.GD.N0059.d006973 : ℤ) ^ 3 *
        ((_root_.GD.N0059.d006973 : ℤ) - 2 * _root_.GD.N0059.d006976 i) *
        (2 * (c.d006982 j : ℤ) - c.d006980) +
      2 * (_root_.GD.N0059.d006974 : ℤ) * _root_.GD.N0059.d006976 i *
        ((_root_.GD.N0059.d006973 : ℤ) - _root_.GD.N0059.d006976 i) *
        (8 * (c.d006983 j : ℤ) ^ 3 - (c.d006981 : ℤ) ^ 3))

def d006978.d006987 (c : _root_.GD.N0059.d006978) (i : Fin 7) : ℕ :=
  60 * c.d006981 * _root_.GD.N0059.d006976 i ^ 2 *
    (_root_.GD.N0059.d006973 - _root_.GD.N0059.d006976 i) ^ 2 *
    c.d006985 i ^ 4 * c.root i

def d006978.d006988 (c : _root_.GD.N0059.d006978) (i : Fin 7) : ℕ :=
  _root_.GD.N0059.d006971 * _root_.GD.N0059.d006977 i * _root_.GD.N0059.d006973 ^ 4 *
    c.d006984 i ^ 3 * _root_.GD.N0059.d006972

def d006978.d006989 (c : _root_.GD.N0059.d006978) (i : Fin 7) : Prop :=
  if c.root i = 0 then ∀ j, c.density j i = 0 else
    0 < c.root i ∧ 0 < c.d006985 i ∧ 0 < c.d006984 i ∧
      c.d006985 i * _root_.GD.N0059.d006972 ^ 2 ≤
        c.root i ^ 2 * c.d006984 i ∧
      ∀ j, 0 ≤ c.d006986 i j ∧
        ((c.density j i * c.d006987 i : ℕ) : ℤ) ≤
          (c.d006988 i : ℤ) * c.d006986 i j

instance (c : _root_.GD.N0059.d006978) (i : Fin 7) : Decidable (c.d006989 i) := by
  unfold _root_.GD.N0059.d006978.d006989
  infer_instance

def d006978.d006990 (c : _root_.GD.N0059.d006978) (j : Fin 4) : ℕ := ∑ i, c.density j i
def d006978.d006991 (c : _root_.GD.N0059.d006978) (j : Fin 4) : ℕ :=
  ∑ i, c.density j i * _root_.GD.N0059.d006976 i
def d006978.d006992 (c : _root_.GD.N0059.d006978) (j : Fin 4) : ℕ :=
  ∑ i, c.density j i * _root_.GD.N0059.d006976 i ^ 2

def d006978.d006993 (c : _root_.GD.N0059.d006978) (j : Fin 4) : Prop :=
  0 < c.d006990 j ∧ c.d006991 j ^ 2 + c.d006990 j * c.quadratic j ≤
    c.d006990 j * c.d006992 j

instance (c : _root_.GD.N0059.d006978) (j : Fin 4) : Decidable (c.d006993 j) := by
  unfold _root_.GD.N0059.d006978.d006993
  infer_instance

def d006978.d006994 (c : _root_.GD.N0059.d006978) : Prop :=
  c.iu < 40 ∧ c.iz < 112 ∧ c.uLo < c.uHi ∧ c.uHi ≤ _root_.GD.N0059.d006974 ∧
    0 < c.zLo ∧ c.zLo < c.zHi ∧
    (∀ i, c.d006989 i) ∧ (∀ j, c.d006993 j)

instance (c : _root_.GD.N0059.d006978) : Decidable c.d006994 := by
  unfold _root_.GD.N0059.d006978.d006994
  infer_instance

def d006978.d006995 (c : _root_.GD.N0059.d006978) (U Z : List ℕ) : Prop :=
  c.uLo = U.getD c.iu 0 ∧ c.uHi = U.getD (c.iu + 1) 0 ∧
    c.zLo = Z.getD c.iz 0 ∧ c.zHi = Z.getD (c.iz + 1) 0

instance (c : _root_.GD.N0059.d006978) (U Z : List ℕ) : Decidable (c.d006995 U Z) := by
  unfold _root_.GD.N0059.d006978.d006995
  infer_instance

def d006996 (U Z : List ℕ) (cs : List _root_.GD.N0059.d006978) : Bool :=
  cs.all (fun c => decide (c.d006994 ∧ c.d006995 U Z))

theorem d006997 {U Z : List ℕ} {cs : List _root_.GD.N0059.d006978} (h : _root_.GD.N0059.d006996 U Z cs = true)
    {c : _root_.GD.N0059.d006978} (hc : c ∈ cs) : c.d006994 := by
  exact (of_decide_eq_true ((List.all_eq_true.mp h) c hc)).1

theorem d006998 {U Z : List ℕ} {cs : List _root_.GD.N0059.d006978}
    (h : _root_.GD.N0059.d006996 U Z cs = true) {c : _root_.GD.N0059.d006978} (hc : c ∈ cs) : c.d006995 U Z := by
  exact (of_decide_eq_true ((List.all_eq_true.mp h) c hc)).2

def d006978.d006999 (c : _root_.GD.N0059.d006978) : ℕ :=
  (c.uHi - c.uLo) * (c.zHi ^ 3 - c.zLo ^ 3) * (∑ j, c.quadratic j)

def d007000 (cs : List _root_.GD.N0059.d006978) : ℕ := (cs.map _root_.GD.N0059.d006978.d006999).sum

end GD.N0059

#print axioms _root_.GD.N0059.d006997

#print axioms _root_.GD.N0059.d006998
