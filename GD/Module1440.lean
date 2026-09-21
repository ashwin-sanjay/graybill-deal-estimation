import GD.Module1412
import GD.Module0802
import GD.Module0980

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0099
noncomputable section

open _root_.GD.N0232.N0719

variable {k : ℕ}

def d022902 (sizes : Fin (k + 2) → ℕ) (i : Fin (k + 2)) (j : Fin (k + 1)) :
    Fin k → ℕ := fun l => sizes (i.succAbove (j.succAbove l))

def d022903 (sizes : Fin (k + 2) → ℕ) (i : Fin (k + 2)) (j : Fin (k + 1)) :
    _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes ≃ᵐ
      _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes (i.succAbove j)) ×
        _root_.GD.N0232.N0719.N0859.d010811 k (_root_.GD.N0099.d022902 sizes i j) :=
  (MeasurableEquiv.piFinSuccAbove (fun l => _root_.GD.N0137.d008894 (sizes l)) i).trans
    (((MeasurableEquiv.refl _).prodCongr
      (MeasurableEquiv.piFinSuccAbove
        (fun l => _root_.GD.N0137.d008894 (sizes (i.succAbove l))) j)).trans
          MeasurableEquiv.prodAssoc.symm)

theorem d022904
    (sizes : Fin (k + 2) → ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (μ : ∀ l, Measure (_root_.GD.N0137.d008894 (sizes l))) [∀ l, SigmaFinite (μ l)] :
    MeasurePreserving (_root_.GD.N0099.d022903 sizes i j) (Measure.pi μ)
      (((μ i).prod (μ (i.succAbove j))).prod
        (Measure.pi fun l => μ (i.succAbove (j.succAbove l)))) := by
  have h1 := measurePreserving_piFinSuccAbove μ i
  have h2 := (MeasurePreserving.id (μ i)).prod
    (measurePreserving_piFinSuccAbove (fun l => μ (i.succAbove l)) j)
  have h3 := (measurePreserving_prodAssoc (μ i) (μ (i.succAbove j))
    (Measure.pi fun l => μ (i.succAbove (j.succAbove l)))).symm
  exact h3.comp (h2.comp h1)

def d022905 (i : Fin (k + 2)) (j : Fin (k + 1))
    (θ : _root_.GD.N0232.N0720.N1080.d014168)
    (L : ℝ) (hL : 0 < L) : _root_.GD.N0232.N0719.N0859.d010809 (k + 2) where
  location := θ.location
  scale l := if l = i then θ.scale₁ else if l = i.succAbove j then θ.scale₂ else 2 * L
  scale_pos l := by split_ifs; exact θ.scale₁_pos; exact θ.scale₂_pos; positivity

theorem d022906 (sizes : Fin (k + 2) → ℕ)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (θ : _root_.GD.N0232.N0720.N1080.d014168)
    (L : ℝ) (hL : 0 < L) :
    MeasurePreserving (_root_.GD.N0099.d022903 sizes i j)
      (_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes (_root_.GD.N0099.d022905 i j θ L hL))
      ((_root_.GD.N0232.N0720.N1080.d014171 (sizes i) (sizes (i.succAbove j)) θ).prod
        (_root_.GD.N0232.N0719.d009176 k (_root_.GD.N0099.d022902 sizes i j) θ.location (fun _ => 2 * L))) := by
  have hh := _root_.GD.N0099.d022904 sizes i j
    (fun l => _root_.GD.N0232.N0719.d009174 (sizes l) θ.location ((_root_.GD.N0099.d022905 i j θ L hL).scale l))
  convert hh using 1
  congr 1
  unfold _root_.GD.N0232.N0720.N1080.d014171
  rw [_root_.GD.N0232.N0720.d009061]
  simp [_root_.GD.N0099.d022905, Fin.succAbove_ne,
    _root_.GD.N0232.N0719.d009174, _root_.GD.N0232.N0719.d009176, _root_.GD.N0099.d022902]
  rfl

theorem d022907 (sizes : Fin (k + 2) → ℕ)
    (hn : ∀ l, 2 ≤ sizes l) (i : Fin (k + 2)) (j : Fin (k + 1))
    (θ : _root_.GD.N0232.N0720.N1080.d014168)
    (L : ℝ) (hL : 0 < L) :
    _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes (_root_.GD.N0099.d022905 i j θ L hL) ≤
      _root_.GD.N0232.N0720.N1257.d015508 (sizes i) (sizes (i.succAbove j)) θ := by
  have hsum : (sizes i : ℝ) / θ.scale₁ ^ 2 + (sizes (i.succAbove j) : ℝ) / θ.scale₂ ^ 2 ≤
      ∑ l, (sizes l : ℝ) / (_root_.GD.N0099.d022905 i j θ L hL).scale l ^ 2 := by
    rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ j]
    have hnn : 0 ≤ ∑ l, (sizes (i.succAbove (j.succAbove l)) : ℝ) /
      (2 * L) ^ 2 :=
      Finset.sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    simpa [_root_.GD.N0099.d022905, Fin.succAbove_ne, Fin.succAbove_right_inj, add_assoc] using hnn
  have hi : (0 : ℝ) < sizes i := Nat.cast_pos.mpr (by have := hn i; omega)
  have hj : (0 : ℝ) < sizes (i.succAbove j) := Nat.cast_pos.mpr (by have := hn (i.succAbove j); omega)
  change (∑ l, (sizes l : ℝ) / (_root_.GD.N0099.d022905 i j θ L hL).scale l ^ 2)⁻¹ ≤
    ((sizes i : ℝ) / θ.scale₁ ^ 2 + (sizes (i.succAbove j) : ℝ) / θ.scale₂ ^ 2)⁻¹
  simpa only [one_div] using one_div_le_one_div_of_le
    (add_pos (div_pos hi (sq_pos_of_pos θ.scale₁_pos))
      (div_pos hj (sq_pos_of_pos θ.scale₂_pos))) hsum

end
end GD.N0099

#print axioms _root_.GD.N0099.d022906
#print axioms _root_.GD.N0099.d022907
