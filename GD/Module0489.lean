import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0038
noncomputable section

variable {k : ℕ}

theorem d007535 (hk : 2 ≤ k) (i : Fin k) :
    (Finset.univ.erase i : Finset (Fin k)).Nonempty := by
  apply Finset.Nontrivial.erase_nonempty
  apply Finset.one_lt_card_iff_nontrivial.mp
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

theorem d007536 (hk : 2 ≤ k) : (Finset.univ : Finset (Fin k)).Nonempty :=
  ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

def d007537 (hk : 2 ≤ k) (e : Fin k → Fin k → ℝ) (i : Fin k) : ℝ :=
  (Finset.univ.erase i).inf' (_root_.GD.N0038.d007535 hk i) (e i)

def d007538 (hk : 2 ≤ k) (e : Fin k → Fin k → ℝ) (i : Fin k) : ℝ :=
  (Finset.univ.erase i).sup' (_root_.GD.N0038.d007535 hk i) (e i)


def d007539 (hk : 2 ≤ k) (e : Fin k → Fin k → ℝ) : ℝ :=
  Finset.univ.sup' (_root_.GD.N0038.d007536 hk) (_root_.GD.N0038.d007537 hk e)

theorem d007540 (hk : 2 ≤ k) (e : Fin k → Fin k → ℝ)
    (i j : Fin k) (hij : j ≠ i) : _root_.GD.N0038.d007537 hk e i ≤ e i j := by
  exact Finset.inf'_le (e i) (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩)

theorem d007541 (hk : 2 ≤ k) (e : Fin k → Fin k → ℝ)
    (i j : Fin k) (hij : j ≠ i) : e i j ≤ _root_.GD.N0038.d007538 hk e i := by
  exact Finset.le_sup' (e i) (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩)



theorem d007542 (hk : 2 ≤ k) (e : Fin k → Fin k → ℝ)
    (hsym : ∀ i j, e i j = e j i) (i j : Fin k) :
    _root_.GD.N0038.d007537 hk e i ≤ _root_.GD.N0038.d007538 hk e j := by
  by_cases hij : i = j
  · subst j
    obtain ⟨r, hr⟩ := _root_.GD.N0038.d007535 hk i
    exact (Finset.inf'_le (e i) hr).trans (Finset.le_sup' (e i) hr)
  · calc
      _root_.GD.N0038.d007537 hk e i ≤ e i j := _root_.GD.N0038.d007540 hk e i j (Ne.symm hij)
      _ = e j i := hsym i j
      _ ≤ _root_.GD.N0038.d007538 hk e j := _root_.GD.N0038.d007541 hk e j i hij

theorem d007543 (hk : 2 ≤ k) (e : Fin k → Fin k → ℝ)
    (hsym : ∀ i j, e i j = e j i) (i : Fin k) :
    _root_.GD.N0038.d007537 hk e i ≤ _root_.GD.N0038.d007539 hk e ∧ _root_.GD.N0038.d007539 hk e ≤ _root_.GD.N0038.d007538 hk e i := by
  constructor
  · exact Finset.le_sup' (_root_.GD.N0038.d007537 hk e) (Finset.mem_univ i)
  · exact Finset.sup'_le _ _ (fun j _ => _root_.GD.N0038.d007542 hk e hsym j i)



theorem d007544 {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (x μ : ℝ)
    (hlo : s.inf' hs f ≤ x) (hhi : x ≤ s.sup' hs f) :
    (x - μ) ^ 2 ≤ ∑ j ∈ s, (f j - μ) ^ 2 := by
  let M := s.sup' hs (fun j => |f j - μ|)
  have hM (j : ι) (hj : j ∈ s) : |f j - μ| ≤ M :=
    Finset.le_sup' (fun j => |f j - μ|) hj
  let j₀ := Classical.choose hs
  have hj₀ : j₀ ∈ s := Classical.choose_spec hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM j₀ hj₀)
  have hl : μ - M ≤ s.inf' hs f := by
    apply Finset.le_inf' hs f
    intro j hj
    have := (abs_le.mp (hM j hj)).1
    linarith
  have hu : s.sup' hs f ≤ μ + M := by
    apply Finset.sup'_le hs f
    intro j hj
    have := (abs_le.mp (hM j hj)).2
    linarith
  have ha : |x - μ| ≤ M := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsq : |x - μ| ^ 2 ≤ M ^ 2 := (sq_le_sq₀ (abs_nonneg _) hM0).mpr ha
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hs (fun j => |f j - μ|)
  change M = |f j - μ| at hmax
  rw [hmax, sq_abs, sq_abs] at hsq
  exact hsq.trans (Finset.single_le_sum (fun r _ => sq_nonneg (f r - μ)) hj)



theorem d007545 (hk : 2 ≤ k) (e : Fin k → Fin k → ℝ)
    (hsym : ∀ i j, e i j = e j i) (i : Fin k) (μ : ℝ) :
    (_root_.GD.N0038.d007539 hk e - μ) ^ 2 ≤ ∑ j ∈ Finset.univ.erase i, (e i j - μ) ^ 2 := by
  have h := _root_.GD.N0038.d007543 hk e hsym i
  exact _root_.GD.N0038.d007544 _ (_root_.GD.N0038.d007535 hk i) (e i)
    (_root_.GD.N0038.d007539 hk e) μ h.1 h.2

variable {Ω : Type*} [MeasurableSpace Ω]

def d007546 (hk : 2 ≤ k) (e : Fin k → Fin k → Ω → ℝ) : Ω → ℝ :=
  fun z => _root_.GD.N0038.d007539 hk (fun i j => e i j z)

theorem d007547 (hk : 2 ≤ k) (e : Fin k → Fin k → Ω → ℝ)
    (he : ∀ i j, Measurable (e i j)) : Measurable (_root_.GD.N0038.d007546 hk e) := by
  have hl (i : Fin k) : Measurable (fun z => _root_.GD.N0038.d007537 hk (fun i j => e i j z) i) := by
    have h : Measurable ((Finset.univ.erase i).inf' (_root_.GD.N0038.d007535 hk i) (e i)) :=
      Finset.inf'_induction (_root_.GD.N0038.d007535 hk i) (e i)
        (fun _ hf _ hg => hf.inf hg) (fun j _ => he i j)
    have hx : ((Finset.univ.erase i).inf' (_root_.GD.N0038.d007535 hk i) (e i)) =
        (fun z => _root_.GD.N0038.d007537 hk (fun i j => e i j z) i) := by
      funext z
      exact Finset.inf'_apply (_root_.GD.N0038.d007535 hk i) (e i) z
    exact hx ▸ h
  have h := Finset.measurable_sup' (_root_.GD.N0038.d007536 hk) (fun i _ => hl i)
  have hx : (Finset.univ.sup' (_root_.GD.N0038.d007536 hk)
      (fun i z => _root_.GD.N0038.d007537 hk (fun i j => e i j z) i)) = _root_.GD.N0038.d007546 hk e := by
    funext z
    exact Finset.sup'_apply (_root_.GD.N0038.d007536 hk) _ z
  exact hx ▸ h

end
end GD.N0038

#print axioms _root_.GD.N0038.d007542
#print axioms _root_.GD.N0038.d007543
#print axioms _root_.GD.N0038.d007545
#print axioms _root_.GD.N0038.d007547
