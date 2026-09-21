import GD.Module1526











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace GD.N0106.N0428.N0765.N1580

open _root_.GD.N0106.N0428.N0765.N1579 _root_.GD.N0106.N0428.N0765.N1581



def d023727 (previous : _root_.GD.N0106.N0428.N0765.N1579.d007457) : List _root_.GD.N0106.N0428.N0765.N1579.d007457 → Bool
  | [] => true
  | x :: xs =>
      decide (x = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 previous
        (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007421)) &&
      x.valid && d023727 x xs

def d023728 : List _root_.GD.N0106.N0428.N0765.N1579.d007457 → Bool
  | [] => false
  | x :: xs => decide (x = _root_.GD.N0106.N0428.N0765.N1579.d007459) && x.valid && _root_.GD.N0106.N0428.N0765.N1580.d023727 x xs



def d023729 : List _root_.GD.N0106.N0428.N0765.N1579.d007457 → List _root_.GD.N0106.N0428.N0765.N1579.d007457 → Bool
  | [], [] => true
  | p :: ps, n :: ns =>
      decide (n = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 _root_.GD.N0106.N0428.N0765.N1579.d007456 p) &&
      n.valid && d023729 ps ns
  | _, _ => false

def d023730 : List _root_.GD.N0106.N0428.N0765.N1579.d007457 → List _root_.GD.N0106.N0428.N0765.N1579.d007457 → Bool
  | _ :: ps, n :: ns => decide (n = _root_.GD.N0106.N0428.N0765.N1579.d007459) && n.valid && _root_.GD.N0106.N0428.N0765.N1580.d023729 ps ns
  | _, _ => false



def d023731 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : Bool :=
  let positive := cache.positive.toList
  let negative := cache.negative.toList
  decide (cache.positive.size = 1691) &&
  _root_.GD.N0106.N0428.N0765.N1580.d023728 positive &&
  decide (cache.negative.size = 1691) &&
  _root_.GD.N0106.N0428.N0765.N1580.d023730 positive negative &&
  decide (_root_.GD.N0106.N0428.N0765.N1581.d023713 cache) &&
  decide (cache.epsilon = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007422)

private def d023732 (xs : List _root_.GD.N0106.N0428.N0765.N1579.d007457) (i : ℕ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  (xs[i]?).getD _root_.GD.N0106.N0428.N0765.N1579.d007436.d007438

private theorem d023733 (x : _root_.GD.N0106.N0428.N0765.N1579.d007457) (xs : List _root_.GD.N0106.N0428.N0765.N1579.d007457) :
    _root_.GD.N0106.N0428.N0765.N1580.d023732 (x :: xs) 0 = x := rfl

private theorem d023734 (x : _root_.GD.N0106.N0428.N0765.N1579.d007457) (xs : List _root_.GD.N0106.N0428.N0765.N1579.d007457) (i : ℕ) :
    _root_.GD.N0106.N0428.N0765.N1580.d023732 (x :: xs) (i + 1) = _root_.GD.N0106.N0428.N0765.N1580.d023732 xs i := rfl

private theorem d023735 (a : Array _root_.GD.N0106.N0428.N0765.N1579.d007457) (i : ℕ) :
    _root_.GD.N0106.N0428.N0765.N1580.d023732 a.toList i = _root_.GD.N0106.N0428.N0765.N1581.d023709 a i := by
  simp only [_root_.GD.N0106.N0428.N0765.N1580.d023732, _root_.GD.N0106.N0428.N0765.N1581.d023709, Array.getElem?_toList]

private theorem d023736 {previous : _root_.GD.N0106.N0428.N0765.N1579.d007457} {xs : List _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (h : _root_.GD.N0106.N0428.N0765.N1580.d023727 previous xs = true) :
    ∀ i : ℕ, i < xs.length →
      (_root_.GD.N0106.N0428.N0765.N1580.d023732 xs i).valid = true ∧
      _root_.GD.N0106.N0428.N0765.N1580.d023732 xs i = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1580.d023732 (previous :: xs) i)
        (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007421) := by
  induction xs generalizing previous with
  | nil =>
      intro i hi
      simp only [List.length_nil] at hi
      omega
  | cons x xs ih =>
      have hh : (x = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 previous
          (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007421) ∧ x.valid = true) ∧
          _root_.GD.N0106.N0428.N0765.N1580.d023727 x xs = true := by
        simpa only [_root_.GD.N0106.N0428.N0765.N1580.d023727, Bool.and_eq_true, decide_eq_true_eq] using h
      intro i hi
      cases i with
      | zero =>
          simpa only [_root_.GD.N0106.N0428.N0765.N1580.d023733] using And.intro hh.1.2 hh.1.1
      | succ i =>
          have hi' : i < xs.length := by
            simp only [List.length_cons] at hi
            omega
          simpa only [Nat.succ_eq_add_one, _root_.GD.N0106.N0428.N0765.N1580.d023734] using ih hh.2 i hi'

private theorem d023737 {ps ns : List _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (h : _root_.GD.N0106.N0428.N0765.N1580.d023729 ps ns = true) :
    ∀ i : ℕ, i < ns.length →
      (_root_.GD.N0106.N0428.N0765.N1580.d023732 ns i).valid = true ∧
      _root_.GD.N0106.N0428.N0765.N1580.d023732 ns i = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1580.d023732 ps i) := by
  induction ps generalizing ns with
  | nil =>
      cases ns with
      | nil =>
          intro i hi
          simp only [List.length_nil] at hi
          omega
      | cons n ns => simp only [_root_.GD.N0106.N0428.N0765.N1580.d023729, Bool.false_eq_true] at h
  | cons p ps ih =>
      cases ns with
      | nil => simp only [_root_.GD.N0106.N0428.N0765.N1580.d023729, Bool.false_eq_true] at h
      | cons n ns =>
          have hh : (n = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 _root_.GD.N0106.N0428.N0765.N1579.d007456 p ∧ n.valid = true) ∧
              _root_.GD.N0106.N0428.N0765.N1580.d023729 ps ns = true := by
            simpa only [_root_.GD.N0106.N0428.N0765.N1580.d023729, Bool.and_eq_true, decide_eq_true_eq] using h
          intro i hi
          cases i with
          | zero =>
              simpa only [_root_.GD.N0106.N0428.N0765.N1580.d023733] using And.intro hh.1.2 hh.1.1
          | succ i =>
              have hi' : i < ns.length := by
                simp only [List.length_cons] at hi
                omega
              simpa only [Nat.succ_eq_add_one, _root_.GD.N0106.N0428.N0765.N1580.d023734] using ih hh.2 i hi'

theorem d023738 {a : Array _root_.GD.N0106.N0428.N0765.N1579.d007457} (hsize : a.size = 1691)
    (h : _root_.GD.N0106.N0428.N0765.N1580.d023728 a.toList = true) : _root_.GD.N0106.N0428.N0765.N1581.d023711 a := by
  have hlen : a.toList.length = 1691 := by
    simpa only [Array.length_toList] using hsize
  cases hlist : a.toList with
  | nil => simp only [hlist, _root_.GD.N0106.N0428.N0765.N1580.d023728, Bool.false_eq_true] at h
  | cons x xs =>
      have hh : (x = _root_.GD.N0106.N0428.N0765.N1579.d007459 ∧ x.valid = true) ∧ _root_.GD.N0106.N0428.N0765.N1580.d023727 x xs = true := by
        simpa only [hlist, _root_.GD.N0106.N0428.N0765.N1580.d023728, Bool.and_eq_true, decide_eq_true_eq] using h
      have hxs : xs.length = 1690 := by
        simp only [hlist, List.length_cons] at hlen
        omega
      refine ⟨hsize, ?_, ?_, ?_⟩
      · rw [← _root_.GD.N0106.N0428.N0765.N1580.d023735, hlist, _root_.GD.N0106.N0428.N0765.N1580.d023733]
        exact hh.1.1
      · intro k
        have hk : k.val < xs.length := by rw [hxs]; exact k.isLt
        have hs := (_root_.GD.N0106.N0428.N0765.N1580.d023736 hh.2 k.val hk).2
        simpa only [← _root_.GD.N0106.N0428.N0765.N1580.d023735, hlist, _root_.GD.N0106.N0428.N0765.N1580.d023734] using hs
      · intro k
        rcases k with ⟨k, hk⟩
        cases k with
        | zero =>
            simpa only [← _root_.GD.N0106.N0428.N0765.N1580.d023735, hlist, _root_.GD.N0106.N0428.N0765.N1580.d023733] using hh.1.2
        | succ k =>
            have hk' : k < xs.length := by rw [hxs]; omega
            have hv := (_root_.GD.N0106.N0428.N0765.N1580.d023736 hh.2 k hk').1
            simpa only [← _root_.GD.N0106.N0428.N0765.N1580.d023735, hlist, Nat.succ_eq_add_one,
              _root_.GD.N0106.N0428.N0765.N1580.d023734] using hv

theorem d023739 {positive negative : Array _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (hsize : negative.size = 1691)
    (h : _root_.GD.N0106.N0428.N0765.N1580.d023730 positive.toList negative.toList = true) :
    _root_.GD.N0106.N0428.N0765.N1581.d023712 positive negative := by
  have hlen : negative.toList.length = 1691 := by
    simpa only [Array.length_toList] using hsize
  cases hp : positive.toList with
  | nil => simp only [hp, _root_.GD.N0106.N0428.N0765.N1580.d023730, Bool.false_eq_true] at h
  | cons p ps =>
      cases hn : negative.toList with
      | nil => simp only [hp, hn, _root_.GD.N0106.N0428.N0765.N1580.d023730, Bool.false_eq_true] at h
      | cons n ns =>
          have hh : (n = _root_.GD.N0106.N0428.N0765.N1579.d007459 ∧ n.valid = true) ∧ _root_.GD.N0106.N0428.N0765.N1580.d023729 ps ns = true := by
            simpa only [hp, hn, _root_.GD.N0106.N0428.N0765.N1580.d023730, Bool.and_eq_true,
              decide_eq_true_eq] using h
          have hns : ns.length = 1690 := by
            simp only [hn, List.length_cons] at hlen
            omega
          refine ⟨hsize, ?_, ?_, ?_⟩
          · rw [← _root_.GD.N0106.N0428.N0765.N1580.d023735, hn, _root_.GD.N0106.N0428.N0765.N1580.d023733]
            exact hh.1.1
          · intro k
            have hk : k.val < ns.length := by rw [hns]; exact k.isLt
            have hs := (_root_.GD.N0106.N0428.N0765.N1580.d023737 hh.2 k.val hk).2
            simpa only [← _root_.GD.N0106.N0428.N0765.N1580.d023735, hp, hn, _root_.GD.N0106.N0428.N0765.N1580.d023734] using hs
          · intro k
            rcases k with ⟨k, hk⟩
            cases k with
            | zero =>
                simpa only [← _root_.GD.N0106.N0428.N0765.N1580.d023735, hn, _root_.GD.N0106.N0428.N0765.N1580.d023733] using hh.1.2
            | succ k =>
                have hk' : k < ns.length := by rw [hns]; omega
                have hv := (_root_.GD.N0106.N0428.N0765.N1580.d023737 hh.2 k hk').1
                simpa only [← _root_.GD.N0106.N0428.N0765.N1580.d023735, hn, Nat.succ_eq_add_one,
                  _root_.GD.N0106.N0428.N0765.N1580.d023734] using hv



theorem d023740 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463}
    (h : _root_.GD.N0106.N0428.N0765.N1580.d023731 cache = true) : _root_.GD.N0106.N0428.N0765.N1581.d023714 cache := by
  have hh : ((((cache.positive.size = 1691 ∧
      _root_.GD.N0106.N0428.N0765.N1580.d023728 cache.positive.toList = true) ∧
      cache.negative.size = 1691) ∧
      _root_.GD.N0106.N0428.N0765.N1580.d023730 cache.positive.toList cache.negative.toList = true) ∧
      _root_.GD.N0106.N0428.N0765.N1581.d023713 cache) ∧
      cache.epsilon = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007422 := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1580.d023731, Bool.and_eq_true, decide_eq_true_eq] using h
  exact ⟨_root_.GD.N0106.N0428.N0765.N1580.d023738 hh.1.1.1.1.1 hh.1.1.1.1.2,
    _root_.GD.N0106.N0428.N0765.N1580.d023739 hh.1.1.1.2 hh.1.1.2, hh.1.2, hh.2⟩



theorem d023741 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463}
    (h : _root_.GD.N0106.N0428.N0765.N1580.d023731 cache = true) : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true :=
  (_root_.GD.N0106.N0428.N0765.N1581.d023716 cache).mpr (_root_.GD.N0106.N0428.N0765.N1580.d023740 h)

theorem d023742 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463}
    (h : _root_.GD.N0106.N0428.N0765.N1580.d023731 cache = true) : _root_.GD.N0106.N0428.N0765.N1581.d023725 cache :=
  _root_.GD.N0106.N0428.N0765.N1581.d023726 (_root_.GD.N0106.N0428.N0765.N1580.d023741 h)

end GD.N0106.N0428.N0765.N1580

#print axioms _root_.GD.N0106.N0428.N0765.N1580.d023740
#print axioms _root_.GD.N0106.N0428.N0765.N1580.d023742
