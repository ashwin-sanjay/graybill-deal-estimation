import GD.Module1857
import GD.Module1715
import GD.Module1543
import GD.Module1737

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace GD.N0050
noncomputable section
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0213.N0502
open _root_.GD.N0026 _root_.GD.N0040

variable {k : ℕ}

def d030475 (sizes : Fin (k + 2) → ℕ) : Prop :=
  ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 (k + 2) sizes, _root_.GD.N0232.N0719.N0970.d012309 (k + 2) sizes e ∧
    _root_.GD.N0232.N0719.N0970.d012310 (k + 2) sizes e ∧
    _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes e = _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes

theorem d030476
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l) :
    _root_.GD.N0026.d030461 sizes i j := by
  intro θ H hH hHt
  exact _root_.GD.N0040.d028700 sizes hn i j hdeleted θ H hH hHt



theorem d030477
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l) :
    _root_.GD.N0022.N0255.d030394
      (sizes i) (sizes (i.succAbove j)) ≤ _root_.GD.N0213.N0502.d022051 (k + 2) sizes :=
  _root_.GD.N0026.d030472 sizes hk hn i j
    (_root_.GD.N0050.d030476 sizes hn i j hdeleted)



theorem d030478
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 5) :
    _root_.GD.N0213.N0502.d022051 (k + 2) sizes = ⊤ := by
  by_cases hfinite : _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes ≠ ⊤
  · have hprod := (_root_.GD.N0067.d023925
      (by omega) sizes hn).mp hfinite
    have hdeleted (l : Fin (k + 2)) (hli : l ≠ i) (_hlj : l ≠ i.succAbove j) :
        4 ≤ sizes l := by
      have hp := hprod i l hli.symm
      simp only [hi, Nat.reduceSub, one_mul] at hp
      omega
    exact _root_.GD.N0026.d030474 sizes hk hn i j hi hj
      (_root_.GD.N0050.d030476 sizes hn i j hdeleted)
  · have htop : _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes = ⊤ := not_ne_iff.mp hfinite
    apply top_unique
    rw [← htop]
    exact _root_.GD.N0213.N0502.d022062 (k + 2) sizes

theorem d030479
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 5)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ)
    (hd : d ∈ _root_.GD.N0213.N0502.d022050 (k + 2) sizes) :
    _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d = ⊤ := by
  have hle := _root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0719.N0962.d012186 (k + 2) sizes) hd
  change _root_.GD.N0213.N0502.d022051 (k + 2) sizes ≤ _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d at hle
  rw [_root_.GD.N0050.d030478 sizes hk hn i j hi hj] at hle
  exact top_unique hle



theorem d030480
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 5)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (hfinite : _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d ≠ ⊤) :
    ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes) <
      _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d := by
  classical
  by_contra hnot
  have hbase : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes) :=
    fun θ => le_of_not_gt (fun hθ => hnot ⟨θ, hθ⟩)
  exact hfinite (_root_.GD.N0050.d030479 sizes hk hn i j hi hj d ⟨hd,hbase⟩)

theorem d030481
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 5)
    (hfinite : _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes ≠ ⊤) :
    _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes < _root_.GD.N0213.N0502.d022051 (k + 2) sizes := by
  rw [_root_.GD.N0050.d030478 sizes hk hn i j hi hj]
  exact lt_top_iff_ne_top.mpr hfinite



theorem d030482
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 5) :
    _root_.GD.N0050.d030475 sizes ↔ _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes = ⊤ := by
  unfold _root_.GD.N0050.d030475
  rw [← _root_.GD.N0213.N0524.d028850
    (k + 2) sizes (by omega) hn,
    _root_.GD.N0050.d030478 sizes hk hn i j hi hj]
  exact eq_comm

theorem d030483
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (hi : sizes i = 2) :
    _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes ≠ ⊤ ↔ ∀ l, l ≠ i → 5 ≤ sizes l := by
  constructor
  · intro hfinite l hli
    have hprod := (_root_.GD.N0067.d023925
      (by omega) sizes hn).mp hfinite i l hli.symm
    simp only [hi, Nat.reduceSub, one_mul] at hprod
    omega
  · intro hcomp
    exact (_root_.GD.N0067.d023926
      (by omega) sizes hn).mpr (Or.inr ⟨i, hi, hcomp⟩)

theorem d030484
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 5) :
    _root_.GD.N0050.d030475 sizes ↔ ∃ l, l ≠ i ∧ sizes l ≤ 4 := by
  rw [_root_.GD.N0050.d030482 sizes hk hn i j hi hj]
  constructor
  · intro htop
    by_contra hnot
    have hcomp (l : Fin (k + 2)) (hli : l ≠ i) : 5 ≤ sizes l := by
      by_contra hlt
      exact hnot ⟨l,hli,by omega⟩
    exact ((_root_.GD.N0050.d030483 sizes hn i hi).mpr hcomp) htop
  · rintro ⟨l,hli,hsmall⟩
    by_contra hfinite
    have hlarge := (_root_.GD.N0050.d030483 sizes hn i hi).mp hfinite l hli
    omega


theorem d030485
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (hfinite : _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes ≠ ⊤)
    (hcompatible : _root_.GD.N0050.d030475 sizes) :
    (∀ l, 3 ≤ sizes l) ∨
      ∃ i, sizes i = 2 ∧ ∀ l, l ≠ i → 6 ≤ sizes l := by
  rcases (_root_.GD.N0067.d023926
    (by omega) sizes hn).mp hfinite with hall | ⟨i,hi,hothers⟩
  · exact Or.inl hall
  · refine Or.inr ⟨i,hi,?_⟩
    intro l hli
    have h5 := hothers l hli
    by_contra h6
    have hl5 : sizes l = 5 := by omega
    obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hli
    have ht := (_root_.GD.N0050.d030482 sizes hk hn i j hi
      (by rw [hj]; exact hl5)).mp hcompatible
    exact hfinite ht

end
end GD.N0050

#print axioms _root_.GD.N0050.d030476
#print axioms _root_.GD.N0050.d030477
#print axioms _root_.GD.N0050.d030478
#print axioms _root_.GD.N0050.d030479
#print axioms _root_.GD.N0050.d030480
#print axioms _root_.GD.N0050.d030481
#print axioms _root_.GD.N0050.d030482
#print axioms _root_.GD.N0050.d030483
#print axioms _root_.GD.N0050.d030484
#print axioms _root_.GD.N0050.d030485
