import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators

namespace GD.N0152.N0437

def d007695 (f : ℝ → ℝ) (x : ℝ) : Prop := ∀ y, f y ≤ f x

theorem d007696 {f : ℝ → ℝ} {x : ℝ} (hx : _root_.GD.N0152.N0437.d007695 f x) :
    deriv f x = 0 :=
  ((isMaxOn_univ_iff.2 hx).isLocalMax Filter.univ_mem).deriv_eq_zero





theorem d007697 {f : ℝ → ℝ}
    (hf : Continuous f) (C S : Finset ℝ)
    (hC : ∀ x, deriv f x = 0 → x ∈ C)
    (hS : ∀ x ∈ S, _root_.GD.N0152.N0437.d007695 f x) :
    2 * S.card ≤ C.card + 1 := by
  classical
  by_cases hne : S.Nonempty
  · let k := S.card - 1
    have hcard : S.card = k + 1 := by
      have hp := Finset.card_pos.mpr hne
      dsimp [k]
      omega
    let x : Fin (k + 1) ↪o ℝ := S.orderEmbOfFin hcard
    have hxmem (i : Fin (k + 1)) : x i ∈ S := S.orderEmbOfFin_mem hcard i
    have hzexists (i : Fin k) :
        ∃ z ∈ Ioo (x i.castSucc) (x i.succ), deriv f z = 0 := by
      apply exists_deriv_eq_zero (x.strictMono (by exact_mod_cast Nat.lt_succ_self i.val))
        hf.continuousOn
      exact le_antisymm (hS (x i.succ) (hxmem i.succ) (x i.castSucc))
        (hS (x i.castSucc) (hxmem i.castSucc) (x i.succ))
    choose z hz hzcrit using hzexists
    have hzmono : StrictMono z := by
      intro i j hij
      have hidx : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        exact Nat.succ_le_of_lt hij
      exact (hz i).2.trans_le (x.monotone hidx) |>.trans (hz j).1
    have hzdisjoint (i : Fin k) (j : Fin (k + 1)) : z i ≠ x j := by
      by_cases hji : j.val ≤ i.val
      · have hidx : j ≤ i.castSucc := hji
        exact ne_of_gt ((x.monotone hidx).trans_lt (hz i).1)
      · have hidx : i.succ ≤ j := by change i.val + 1 ≤ j.val; omega
        exact ne_of_lt ((hz i).2.trans_le (x.monotone hidx))
    let Z : Finset ℝ := Finset.univ.image z
    have hZcard : Z.card = k := by
      rw [Finset.card_image_of_injective _ hzmono.injective]
      exact Finset.card_fin k
    have hdisjoint : Disjoint S Z := by
      apply Finset.disjoint_left.mpr
      intro a ha hza
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hza
      have ha' : a ∈ Set.range x := by
        change a ∈ Set.range (S.orderEmbOfFin hcard)
        rw [Finset.range_orderEmbOfFin]
        exact ha
      obtain ⟨j, hj⟩ := ha'
      exact hzdisjoint i j (hi.trans hj.symm)
    have hsub : S ∪ Z ⊆ C := by
      intro a ha
      rcases Finset.mem_union.mp ha with hs | hz'
      · exact hC a (_root_.GD.N0152.N0437.d007696 (hS a hs))
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz'
        exact hC (z i) (hzcrit i)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjoint, hZcard, hcard] at hc
    rw [hcard]
    omega
  · have hzero : S.card = 0 := by simpa using not_lt.mp (mt Finset.card_pos.mp hne)
    simp [hzero]

theorem d007698 {f : ℝ → ℝ}
    (hf : Continuous f) (C S : Finset ℝ) (r : ℕ)
    (hC : ∀ x, deriv f x = 0 → x ∈ C)
    (hS : ∀ x ∈ S, _root_.GD.N0152.N0437.d007695 f x) (hcard : C.card < 2 * r) : S.card ≤ r := by
  have h := _root_.GD.N0152.N0437.d007697 hf C S hC hS
  omega


theorem d007699 {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (C S : Finset ℝ)
    (hC : ∀ x, deriv f x = 0 → x ∈ C)
    (hS : ∀ x ∈ S, _root_.GD.N0152.N0437.d007695 f x) :
    2 * S.card ≤ C.card + 1 :=
  _root_.GD.N0152.N0437.d007697 hf.continuous C S hC hS



theorem d007700 {f : ℝ → ℝ}
    (hf : Continuous f) (p : Polynomial ℝ) (hp : p ≠ 0)
    (hcrit : ∀ x, deriv f x = 0 → p.eval x = 0)
    (S : Finset ℝ) (hS : ∀ x ∈ S, _root_.GD.N0152.N0437.d007695 f x)
    (r : ℕ) (hdegree : p.natDegree < 2 * r) : S.card ≤ r := by
  classical
  apply _root_.GD.N0152.N0437.d007698 hf p.roots.toFinset S r
  · intro x hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hcrit x hx))
  · exact hS
  · exact ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p)).trans_lt hdegree



theorem d007701 {f : ℝ → ℝ}
    (hf : Continuous f) (C : Finset ℝ) (r : ℕ)
    (hC : ∀ x, deriv f x = 0 → x ∈ C) (hcard : C.card < 2 * r)
    (hmax : ∃ x, _root_.GD.N0152.N0437.d007695 f x) :
    ∃ S : Finset ℝ, S.Nonempty ∧ S.card ≤ r ∧
      ∀ x, x ∈ S ↔ _root_.GD.N0152.N0437.d007695 f x := by
  classical
  let S := C.filter (_root_.GD.N0152.N0437.d007695 f)
  have hS (x : ℝ) : x ∈ S ↔ _root_.GD.N0152.N0437.d007695 f x := by
    constructor
    · exact fun hx => (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr ⟨hC x (_root_.GD.N0152.N0437.d007696 hx), hx⟩
  obtain ⟨x, hx⟩ := hmax
  exact ⟨S, ⟨x, (hS x).mpr hx⟩,
    _root_.GD.N0152.N0437.d007698 hf C S r hC
      (fun x hx => (hS x).mp hx) hcard, hS⟩

end GD.N0152.N0437

#print axioms _root_.GD.N0152.N0437.d007697
#print axioms _root_.GD.N0152.N0437.d007701
