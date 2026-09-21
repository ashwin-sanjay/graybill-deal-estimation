import GD.Module0378
import GD.Module0376
















set_option autoImplicit false
set_option warningAsError true

noncomputable section

open scoped BigOperators
open Matrix
open _root_.GD.N0229.N0550
open _root_.GD.N0232.N0720.N1249
open _root_.GD.N0106.N0428.N0765.N1603
open _root_.GD.N0106.N0428.N0765.N1604
open _root_.GD.N0106.N0428.N0765.N1626
open _root_.GD.N0106.N0428.N0765.N1622

namespace GD.N0106.N0428.N0765.N1625



theorem d005796 (t : ℝ) (h : Fin 5 → Fin 4 → ℝ)
    (hbox : ∀ c (r : Fin 4),
      |h c r - _root_.GD.N0106.N0428.N0765.N1603.d005578 r.castSucc c| ≤ t * _root_.GD.N0106.N0428.N0765.N1603.d005579 r.castSucc c) :
    _root_.GD.N0106.N0428.N0765.N1626.d005785 t (_root_.GD.N0106.N0428.N0765.N1603.d005609 h) := by
  intro r c
  induction r using Fin.lastCases with
  | last =>
    rw [_root_.GD.N0106.N0428.N0765.N1603.d005611, _root_.GD.N0106.N0428.N0765.N1603.d005583, _root_.GD.N0106.N0428.N0765.N1603.d005584, _root_.GD.N0106.N0428.N0765.N1604.d005554, _root_.GD.N0106.N0428.N0765.N1604.d005555,
      _root_.GD.N0106.N0428.N0765.N1604.d005560, _root_.GD.N0106.N0428.N0765.N1604.d005561]
    norm_num
  | cast r =>
    rw [_root_.GD.N0106.N0428.N0765.N1603.d005610]
    exact hbox c r




theorem d005797
    (g : Fin 5 → Fin 4 → ℝ) (colScale : Fin 5 → ℝ)
    (hcol : ∀ c, 0 < colScale c)
    (hbox : ∀ c (r : Fin 4),
      |_root_.GD.N0106.N0428.N0765.N1603.d005614 g colScale c r - _root_.GD.N0106.N0428.N0765.N1603.d005578 r.castSucc c| ≤
        2000 * _root_.GD.N0106.N0428.N0765.N1603.d005579 r.castSucc c) :
    ∃ alpha : Fin 5 → ℝ, (∀ c, 0 < alpha c) ∧
      ∀ r : Fin 4, ∑ c, alpha c * g c r = 0 := by
  have hA := _root_.GD.N0106.N0428.N0765.N1625.d005796 2000 (_root_.GD.N0106.N0428.N0765.N1603.d005614 g colScale) hbox
  obtain ⟨w, ⟨hw, _, hmargin⟩, _⟩ := _root_.GD.N0106.N0428.N0765.N1626.d005795 hA
  have hwpos : ∀ c, 0 < w c := fun c => lt_trans (by norm_num) (hmargin c)
  refine ⟨fun c => w c / colScale c,
    _root_.GD.N0229.N0550.d003503 colScale w hcol hwpos, ?_⟩
  have hrows : ∀ r : Fin 4,
      ∑ c, w c * (_root_.GD.N0232.N0720.N1249.d002229 r * g c r / colScale c) = 0 := by
    intro r
    exact _root_.GD.N0106.N0428.N0765.N1603.d005613 (_root_.GD.N0106.N0428.N0765.N1603.d005614 g colScale) hw r
  exact (_root_.GD.N0229.N0550.d003502 _root_.GD.N0232.N0720.N1249.d002229 colScale w g _root_.GD.N0232.N0720.N1249.d002230).mpr hrows



theorem d005798
    (forward : Fin 5 → Fin 5 → Fin 2 → ℝ)
    (colScale : Fin 5 → ℝ) (hcol : ∀ c, 0 < colScale c)
    (hbox : ∀ c (r : Fin 4),
      |_root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r - _root_.GD.N0106.N0428.N0765.N1603.d005578 r.castSucc c| ≤
        2000 * _root_.GD.N0106.N0428.N0765.N1603.d005579 r.castSucc c) :
    ∃ alpha : Fin 5 → ℝ, (∀ c, 0 < alpha c) ∧
      (∀ j, ∑ i, alpha i * forward i (1 : Fin 5) j = 0) ∧
      (∀ j, ∑ i, alpha i * forward i (3 : Fin 5) j = 0) := by
  obtain ⟨alpha, hpos, hbal⟩ :=
    _root_.GD.N0106.N0428.N0765.N1625.d005797 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale hcol hbox
  refine ⟨alpha, hpos, ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa [_root_.GD.N0106.N0428.N0765.N1603.d005619] using hbal 1
    · simpa [_root_.GD.N0106.N0428.N0765.N1603.d005619] using hbal 0
  · intro j
    fin_cases j
    · simpa [_root_.GD.N0106.N0428.N0765.N1603.d005619] using hbal 3
    · simpa [_root_.GD.N0106.N0428.N0765.N1603.d005619] using hbal 2



theorem d005799
    (eta : Fin 5 → ℝ)
    (forward reciprocal : Fin 5 → Fin 5 → Fin 2 → ℝ)
    (colScale : Fin 5 → ℝ)
    (heta : ∀ i, 0 < eta i) (hcol : ∀ i, 0 < colScale i)
    (hbox : ∀ c (r : Fin 4),
      |_root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r - _root_.GD.N0106.N0428.N0765.N1603.d005578 r.castSucc c| ≤
        2000 * _root_.GD.N0106.N0428.N0765.N1603.d005579 r.castSucc c)
    (hswap : ∀ i k j,
      eta i * reciprocal i k j = -((-1 : ℝ) ^ (k : ℕ)) * forward i k j) :
    ∃ alpha : Fin 5 → ℝ, (∀ atom, 0 < _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom) ∧
      ∀ k j, ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        _root_.GD.N0232.N0720.N1249.d002218 forward reciprocal atom k j = 0 := by
  obtain ⟨alpha, hpos, hoddOne, hoddThree⟩ :=
    _root_.GD.N0106.N0428.N0765.N1625.d005798 forward colScale hcol hbox
  exact ⟨alpha, _root_.GD.N0232.N0720.N1249.d002219 eta alpha heta hpos,
    _root_.GD.N0232.N0720.N1249.d002220 eta alpha forward reciprocal hswap hoddOne hoddThree⟩





theorem d005800
    (eta : Fin 5 → ℝ)
    (forward reciprocal : Fin 5 → Fin 5 → Fin 2 → ℝ)
    (colScale : Fin 5 → ℝ)
    (energy : Sum (Fin 5) (Fin 5) → (Fin 5 → Fin 2 → ℝ) → ℝ)
    (heta : ∀ i, 0 < eta i) (hcol : ∀ i, 0 < colScale i)
    (hbox : ∀ c (r : Fin 4),
      |_root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 forward) colScale c r - _root_.GD.N0106.N0428.N0765.N1603.d005578 r.castSucc c| ≤
        2000 * _root_.GD.N0106.N0428.N0765.N1603.d005579 r.castSucc c)
    (hswap : ∀ i k j,
      eta i * reciprocal i k j = -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (hcont : ∀ atom, Continuous (energy atom))
    (hhom : ∀ atom (a : ℝ) c, energy atom (a • c) = a ^ 2 * energy atom c)
    (henergy : ∀ atom c, 0 ≤ energy atom c)
    (hjoint : ∀ c, c ≠ 0 → ∃ atom, 0 < energy atom c) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ c, ∃ atom,
      κ * ‖c‖ ^ 2 ≤ 2 * _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom + energy atom c := by
  obtain ⟨alpha, hpos, hoddOne, hoddThree⟩ :=
    _root_.GD.N0106.N0428.N0765.N1625.d005798 forward colScale hcol hbox
  have hw := _root_.GD.N0232.N0720.N1249.d002219 eta alpha heta hpos
  apply _root_.GD.N0106.N0428.N0765.N1622.d005774 (_root_.GD.N0232.N0720.N1249.d002217 eta alpha)
    (fun atom c => _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom) energy hw
    (fun c => _root_.GD.N0232.N0720.N1249.d002222 eta alpha forward reciprocal c
      hswap hoddOne hoddThree) hcont hhom
  intro c hc
  unfold _root_.GD.N0106.N0428.N0765.N1622.d005772
  apply Finset.sum_pos'
  · intro atom _
    exact mul_nonneg (hw atom).le (henergy atom c)
  · obtain ⟨atom, hatom⟩ := hjoint c hc
    exact ⟨atom, Finset.mem_univ _, mul_pos (hw atom) hatom⟩

end GD.N0106.N0428.N0765.N1625

#print axioms _root_.GD.N0106.N0428.N0765.N1625.d005797
#print axioms _root_.GD.N0106.N0428.N0765.N1625.d005799
#print axioms _root_.GD.N0106.N0428.N0765.N1625.d005800
