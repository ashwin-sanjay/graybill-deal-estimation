import GD.Module1379








set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace GD.N0187
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0230.N0615
open _root_.GD.N0163

variable {I : Type*} [Fintype I] [Nonempty I]
variable (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 < p i)

include hp in
theorem d022318 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (lo hi : ℝ)
    (hlo : ∀ i, lo ≤ (t i : ℝ)) (hhi : ∀ i, (t i : ℝ) ≤ hi) :
    _root_.GD.N0163.d022181 p t x ∈ Icc lo hi := by
  rw [_root_.GD.N0163.d022193 p t hx]
  simpa only [Set.mem_Icc, _root_.GD.N0230.N0615.d000152, _root_.GD.N0230.N0615.d000151, _root_.GD.N0163.d022178, _root_.GD.N0163.d022179] using
    _root_.GD.N0230.N0615.d000161 (_root_.GD.N0163.d022177 p t x) (fun i => (t i : ℝ)) lo hi
      (fun i => (_root_.GD.N0163.d022194 p t hp hx i).le) (_root_.GD.N0163.d022195 p t hp hx) hlo hhi

include hp in

theorem d022319 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0163.d022181 p t x ∈ Icc
      (Finset.univ.inf' Finset.univ_nonempty (fun i => (t i : ℝ)))
      (Finset.univ.sup' Finset.univ_nonempty (fun i => (t i : ℝ))) := by
  classical
  exact _root_.GD.N0187.d022318 p t hp hx _ _
    (fun i => Finset.inf'_le _ (Finset.mem_univ i))
    (fun i => Finset.le_sup' (fun i => (t i : ℝ)) (Finset.mem_univ i))

section Ordered
variable [LinearOrder I]


theorem d022320 (f : I → I → ℝ)
    (hsym : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ i, ∑ j with i < j, f i j := by
  classical
  have split (i j : I) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst j
      simp [hdiag]
    · simp [h, not_lt_of_ge h.le]
  have reverse : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp only [h, if_true]
      exact hsym j i
    · simp only [h, if_false]
  calc
    (∑ i, ∑ j, f i j) =
        ∑ i, ∑ j, ((if i < j then f i j else 0) +
          (if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact split i j
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
      rw [reverse]
      ring
    _ = _ := by simp only [Finset.sum_filter]

include hp in

theorem d022321 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0163.d022182 p t x =
      (∑ i, ∑ j with i < j,
        p i * p j * _root_.GD.N0178.d007131 (t i) x.1 x.2 *
          _root_.GD.N0178.d007131 (t j) x.1 x.2 *
          ((t i : ℝ) - (t j : ℝ)) ^ 2) / _root_.GD.N0163.d022178 p t x := by
  classical
  let f : I → I → ℝ := fun i j =>
    _root_.GD.N0163.d022177 p t x i * _root_.GD.N0163.d022177 p t x j * ((t i : ℝ) - (t j : ℝ)) ^ 2
  have hs : ∀ i j, f i j = f j i := by
    intro i j
    dsimp [f]
    rw [sub_sq_comm (t j : ℝ) (t i : ℝ)]
    ring
  have hd : ∀ i, f i i = 0 := by intro i; simp [f]
  have h0 := (_root_.GD.N0163.d022195 p t hp hx).ne'
  rw [_root_.GD.N0163.d022200 p t hp hx]
  change (∑ i, ∑ j, f i j) / (2 * _root_.GD.N0163.d022178 p t x) = _
  rw [_root_.GD.N0187.d022320 f hs hd]
  have he : (∑ i, ∑ j with i < j, f i j) =
      ∑ i, ∑ j with i < j,
        p i * p j * _root_.GD.N0178.d007131 (t i) x.1 x.2 *
          _root_.GD.N0178.d007131 (t j) x.1 x.2 *
          ((t i : ℝ) - (t j : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f, _root_.GD.N0163.d022177]
    ring
  rw [he]
  field_simp [h0]

end Ordered
end
end GD.N0187

#print axioms _root_.GD.N0187.d022318
#print axioms _root_.GD.N0187.d022319
#print axioms _root_.GD.N0187.d022320
#print axioms _root_.GD.N0187.d022321
