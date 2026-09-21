import GD.Module0453
import GD.Module0455
import GD.Module0354
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0060
noncomputable section

open _root_.GD.N0059 _root_.GD.N0025

def d007101 (c : _root_.GD.N0059.d006978) : ℝ := (c.uLo : ℝ) / _root_.GD.N0059.d006974
def d007102 (c : _root_.GD.N0059.d006978) : ℝ := (c.uHi : ℝ) / _root_.GD.N0059.d006974
def d007103 (c : _root_.GD.N0059.d006978) : ℝ := (c.zLo : ℝ) / _root_.GD.N0059.d006975
def d007104 (c : _root_.GD.N0059.d006978) : ℝ := (c.zHi : ℝ) / _root_.GD.N0059.d006975

def d007105 (c : _root_.GD.N0059.d006978) : Set (ℝ × ℝ) :=
  _root_.GD.N0025.d005230 (_root_.GD.N0060.d007101 c) (_root_.GD.N0060.d007102 c) (_root_.GD.N0060.d007103 c) (_root_.GD.N0060.d007104 c)

def d007106 (j : _root_.GD.N0025.d005225) : Fin 4 :=
  ⟨2 * (j.1 : ℕ) + (j.2 : ℕ), by omega⟩

def d007107 (i : Fin 41) : ℝ := (_root_.GD.N0059.d007016.getD i.val 0 : ℝ) / _root_.GD.N0059.d006974
def d007108 (i : Fin 113) : ℝ := (_root_.GD.N0059.d007017.getD i.val 0 : ℝ) / _root_.GD.N0059.d006975

private theorem d007109 (l : List ℕ) (h : l.IsChain (· < ·))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l.getD i 0 ≤ l.getD j 0 := by
  have hget := h.sortedLT.strictMono_get.monotone
    (show (⟨i, hi⟩ : Fin l.length) ≤ ⟨j, hj⟩ from hij)
  simpa only [← List.getD_eq_get l 0] using hget

theorem d007110 : Monotone _root_.GD.N0060.d007107 := by
  intro i j hij
  have h := _root_.GD.N0060.d007109 _root_.GD.N0059.d007016 _root_.GD.N0059.d007020
    (by simpa only [_root_.GD.N0059.d007018] using i.isLt)
    (by simpa only [_root_.GD.N0059.d007018] using j.isLt) hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [_root_.GD.N0059.d006974])

theorem d007111 : Monotone _root_.GD.N0060.d007108 := by
  intro i j hij
  have h := _root_.GD.N0060.d007109 _root_.GD.N0059.d007017 _root_.GD.N0059.d007021
    (by simpa only [_root_.GD.N0059.d007019] using i.isLt)
    (by simpa only [_root_.GD.N0059.d007019] using j.isLt) hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [_root_.GD.N0059.d006975])

def d007112 (cs : List _root_.GD.N0059.d006978) (hvalid : ∀ c ∈ cs, c.d006994)
    (i : Fin cs.length) : Fin 40 × Fin 112 :=
  let h := hvalid (cs.get i) (List.get_mem cs i)
  (⟨(cs.get i).iu, h.1⟩, ⟨(cs.get i).iz, h.2.1⟩)

theorem d007113 (cs : List _root_.GD.N0059.d006978)
    (hkey : (cs.map _root_.GD.N0059.d006978.d006979).IsChain (· < ·)) :
    StrictMono (fun i : Fin cs.length => (cs.get i).d006979) := by
  have hp : cs.Pairwise (fun a b => a.d006979 < b.d006979) := by
    simpa only [List.pairwise_map] using hkey.sortedLT.pairwise
  intro i j hij
  exact List.pairwise_iff_get.mp hp i j hij

theorem d007114 (cs : List _root_.GD.N0059.d006978) (hvalid : ∀ c ∈ cs, c.d006994)
    (hkey : (cs.map _root_.GD.N0059.d006978.d006979).IsChain (· < ·)) :
    Function.Injective (_root_.GD.N0060.d007112 cs hvalid) := by
  intro i j hij
  have hu := congrArg (fun p : Fin 40 × Fin 112 => p.1.val) hij
  have hz := congrArg (fun p : Fin 40 × Fin 112 => p.2.val) hij
  change (cs.get i).iu = (cs.get j).iu at hu
  change (cs.get i).iz = (cs.get j).iz at hz
  apply (_root_.GD.N0060.d007113 cs hkey).injective
  simp only [_root_.GD.N0059.d006978.d006979, hu, hz]

theorem d007115 (cs : List _root_.GD.N0059.d006978) (hvalid : ∀ c ∈ cs, c.d006994)
    (hmatch : ∀ c ∈ cs, c.d006995 _root_.GD.N0059.d007016 _root_.GD.N0059.d007017) (i : Fin cs.length) :
    _root_.GD.N0060.d007105 (cs.get i) =
      _root_.GD.N0025.d005230 (_root_.GD.N0060.d007107 (_root_.GD.N0060.d007112 cs hvalid i).1.castSucc)
        (_root_.GD.N0060.d007107 (_root_.GD.N0060.d007112 cs hvalid i).1.succ)
        (_root_.GD.N0060.d007108 (_root_.GD.N0060.d007112 cs hvalid i).2.castSucc)
        (_root_.GD.N0060.d007108 (_root_.GD.N0060.d007112 cs hvalid i).2.succ) := by
  obtain ⟨hu0, hu1, hz0, hz1⟩ := hmatch (cs.get i) (List.get_mem cs i)
  simp only [_root_.GD.N0060.d007105, _root_.GD.N0060.d007101, _root_.GD.N0060.d007102, _root_.GD.N0060.d007103, _root_.GD.N0060.d007104,
    _root_.GD.N0060.d007107, _root_.GD.N0060.d007108, _root_.GD.N0060.d007112, Fin.val_castSucc, Fin.val_succ, hu0, hu1, hz0, hz1]


theorem d007116 (cs : List _root_.GD.N0059.d006978)
    (hvalid : ∀ c ∈ cs, c.d006994)
    (hmatch : ∀ c ∈ cs, c.d006995 _root_.GD.N0059.d007016 _root_.GD.N0059.d007017)
    (hkey : (cs.map _root_.GD.N0059.d006978.d006979).IsChain (· < ·)) :
    Pairwise (fun i j : Fin cs.length => Disjoint (_root_.GD.N0060.d007105 (cs.get i)) (_root_.GD.N0060.d007105 (cs.get j))) := by
  have h := _root_.GD.N0025.d005247 _root_.GD.N0060.d007107 _root_.GD.N0060.d007108
    _root_.GD.N0060.d007110 _root_.GD.N0060.d007111 (_root_.GD.N0060.d007112 cs hvalid)
    (_root_.GD.N0060.d007114 cs hvalid hkey)
  intro i j hij
  rw [_root_.GD.N0060.d007115 cs hvalid hmatch i, _root_.GD.N0060.d007115 cs hvalid hmatch j]
  exact h hij

theorem d007117 (f : Fin 4 → ℝ) : (∑ j : _root_.GD.N0025.d005225, f (_root_.GD.N0060.d007106 j)) = ∑ j, f j := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ, _root_.GD.N0060.d007106]
  ring


theorem d007118 (c : _root_.GD.N0059.d006978) (hc : c.d006994) :
    ((_root_.GD.N0060.d007102 c - _root_.GD.N0060.d007101 c) * ((_root_.GD.N0060.d007104 c) ^ 3 - (_root_.GD.N0060.d007103 c) ^ 3) / 4) *
      (∑ j : _root_.GD.N0025.d005225, (c.quadratic (_root_.GD.N0060.d007106 j) : ℝ) /
        ((_root_.GD.N0059.d006971 : ℝ) * (_root_.GD.N0059.d006973 : ℝ) ^ 2)) =
      (c.d006999 : ℝ) / (2 : ℝ) ^ 141 := by
  have hu : c.uLo ≤ c.uHi := hc.2.2.1.le
  have hz : c.zLo ^ 3 ≤ c.zHi ^ 3 := Nat.pow_le_pow_left hc.2.2.2.2.2.1.le 3
  rw [_root_.GD.N0060.d007117 (fun j : Fin 4 => (c.quadratic j : ℝ) /
    ((_root_.GD.N0059.d006971 : ℝ) * (_root_.GD.N0059.d006973 : ℝ) ^ 2)), ← Finset.sum_div]
  simp only [_root_.GD.N0059.d006978.d006999, Nat.cast_mul, Nat.cast_sub hu, Nat.cast_sub hz,
    Nat.cast_pow, Nat.cast_sum]
  norm_num only [_root_.GD.N0060.d007102, _root_.GD.N0060.d007101, _root_.GD.N0060.d007104, _root_.GD.N0060.d007103,
    _root_.GD.N0059.d006974, _root_.GD.N0059.d006975, _root_.GD.N0059.d006971, _root_.GD.N0059.d006973]
  ring

private theorem d007119 (cs : List _root_.GD.N0059.d006978) :
    (∑ i : Fin cs.length, (cs.get i).d006999) = _root_.GD.N0059.d007000 cs := by
  unfold _root_.GD.N0059.d007000
  rw [← List.sum_ofFn]
  congr 1
  exact (List.ofFn_comp' cs.get _root_.GD.N0059.d006978.d006999).trans
    (congrArg (List.map _root_.GD.N0059.d006978.d006999) (List.ofFn_get cs))


theorem d007120 (cs : List _root_.GD.N0059.d006978) (hvalid : ∀ c ∈ cs, c.d006994) :
    (∑ i : Fin cs.length,
      ((_root_.GD.N0060.d007102 (cs.get i) - _root_.GD.N0060.d007101 (cs.get i)) *
        ((_root_.GD.N0060.d007104 (cs.get i)) ^ 3 - (_root_.GD.N0060.d007103 (cs.get i)) ^ 3) / 4) *
      (∑ j : _root_.GD.N0025.d005225, ((cs.get i).quadratic (_root_.GD.N0060.d007106 j) : ℝ) /
        ((_root_.GD.N0059.d006971 : ℝ) * (_root_.GD.N0059.d006973 : ℝ) ^ 2))) =
      (_root_.GD.N0059.d007000 cs : ℝ) / (2 : ℝ) ^ 141 := by
  calc
    _ = ∑ i : Fin cs.length, ((cs.get i).d006999 : ℝ) / (2 : ℝ) ^ 141 := by
      apply Finset.sum_congr rfl
      intro i _
      exact _root_.GD.N0060.d007118 (cs.get i) (hvalid _ (List.get_mem cs i))
    _ = (∑ i : Fin cs.length, ((cs.get i).d006999 : ℝ)) / (2 : ℝ) ^ 141 :=
      (Finset.sum_div _ _ _).symm
    _ = _ := by
      congr 1
      exact_mod_cast _root_.GD.N0060.d007119 cs

end
end GD.N0060

#print axioms _root_.GD.N0060.d007110
#print axioms _root_.GD.N0060.d007111
#print axioms _root_.GD.N0060.d007113
#print axioms _root_.GD.N0060.d007114
#print axioms _root_.GD.N0060.d007115
#print axioms _root_.GD.N0060.d007116
#print axioms _root_.GD.N0060.d007117
#print axioms _root_.GD.N0060.d007118
#print axioms _root_.GD.N0060.d007120
