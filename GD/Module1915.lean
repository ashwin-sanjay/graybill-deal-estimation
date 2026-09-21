import GD.Module1880
import GD.Module0813

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal
namespace GD.N0127
noncomputable section
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0026
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973
open _root_.GD.N0232.N0719.N0962 (d012190 d012191)
variable {k : ℕ}



theorem d030981
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 2)
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C) (hC1 : C < 1) :
    ¬ (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0972.d012340 (k + 2) sizes θ)) := by
  intro hcap
  have hcap' : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * (_root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ
        (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes)).toReal) := by
    intro θ
    rw [_root_.GD.N0232.N0719.N0972.d012341 (k + 2) sizes (by omega) hn,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0719.N0972.d012342 (k + 2) sizes (by omega) hn θ).le]
    exact hcap θ
  have hh := _root_.GD.N0127.d030687 sizes hk hn i j hdeleted d hd C hC hcap'
  rw [hi, hj] at hh
  obtain ⟨g, hg, hgb⟩ := hh
  apply _root_.GD.N0101.N0378.d030662
    g hg hC hC1
  intro θ
  convert hgb θ using 1
  congr 2
  unfold _root_.GD.N0026.d030459 _root_.GD.N0076.N0313.d030565
  rw [_root_.GD.N0232.N0720.N1080.d014199
    2 2 (by omega) (by omega)]
  rfl


theorem d030982
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 2)
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l) :
    _root_.GD.N0232.N0719.N0973.d012377 (k + 2) sizes (by omega) hn = 1 := by
  obtain ⟨e, _, heD, hvD, _, hv1⟩ :=
    _root_.GD.N0232.N0719.N0972.d012350 (k + 2) sizes (by omega) hn
  let M := _root_.GD.N0232.N0719.N0844.d012247 (k + 2) sizes
    (_root_.GD.N0232.N0719.N0972.d012343 (k + 2) sizes (by omega) hn) e
  have hM : M ≠ ⊤ := ne_top_of_le_ne_top (by simp) hv1
  have hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ e ≤
      ENNReal.ofReal (M.toReal * _root_.GD.N0232.N0719.N0972.d012340 (k + 2) sizes θ) := by
    intro θ
    apply (_root_.GD.N0232.N0719.N0844.d012250 (k + 2) sizes
      (_root_.GD.N0232.N0719.N0972.d012343 (k + 2) sizes (by omega) hn) (by omega)
      (fun l => by have := hn l; omega) M.toReal ENNReal.toReal_nonneg θ e).mp
    rw [ENNReal.ofReal_toReal hM]
    exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0844.d012246 (k + 2) sizes
      (_root_.GD.N0232.N0719.N0972.d012343 (k + 2) sizes (by omega) hn) θ e) θ
  have hge : 1 ≤ M.toReal := by
    by_contra hh
    exact _root_.GD.N0127.d030981 sizes hk hn i j hi hj hdeleted
      e heD.1 M.toReal ENNReal.toReal_nonneg (lt_of_not_ge hh) hcap
  have hreal : M.toReal = 1 := le_antisymm
    (by simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hv1) hge
  have hone : M = 1 := by rw [← ENNReal.ofReal_toReal hM, hreal]; norm_num
  exact hvD.symm.trans hone


theorem d030983
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 2)
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l) :
    _root_.GD.N0232.N0719.N0973.d012376 (k + 2) sizes (by omega) hn (_root_.GD.N0232.N0719.N0962.d012190 (k + 2) sizes) = 0 ∧
    _root_.GD.N0232.N0719.N0973.d012376 (k + 2) sizes (by omega) hn (_root_.GD.N0232.N0719.N0962.d012191 (k + 2) sizes) = 0 := by
  obtain ⟨_, _, _, hD, hE, _, _⟩ :=
    _root_.GD.N0232.N0719.N0973.d012380 (k + 2) sizes (by omega) hn
  rw [_root_.GD.N0127.d030982 sizes hk hn i j hi hj hdeleted] at hD hE
  simpa using And.intro hD hE



theorem d030984
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 2)
    (hpos : 0 < _root_.GD.N0232.N0719.N0973.d012376 (k + 2) sizes (by omega) hn
      (_root_.GD.N0232.N0719.N0962.d012190 (k + 2) sizes)) :
    ∃ l, l ≠ i ∧ l ≠ i.succAbove j ∧ (sizes l = 2 ∨ sizes l = 3) := by
  classical
  by_contra h
  have hdeleted (l : Fin (k + 2)) (hli : l ≠ i) (hlj : l ≠ i.succAbove j) :
      4 ≤ sizes l := by
    have hn' := hn l
    by_contra hlt
    exact h ⟨l, hli, hlj, by omega⟩
  have hz := (_root_.GD.N0127.d030983 sizes hk hn i j hi hj hdeleted).1
  rw [hz] at hpos
  exact (lt_irrefl _ hpos)


theorem d030985 :
    _root_.GD.N0232.N0719.N0973.d012376 3 ![2, 2, 4] (by omega)
      (by intro l; fin_cases l <;> norm_num)
      (_root_.GD.N0232.N0719.N0962.d012190 3 ![2, 2, 4]) = 0 ∧
    _root_.GD.N0232.N0719.N0973.d012376 3 ![2, 2, 4] (by omega)
      (by intro l; fin_cases l <;> norm_num)
      (_root_.GD.N0232.N0719.N0962.d012191 3 ![2, 2, 4]) = 0 := by
  apply _root_.GD.N0127.d030983 ![2, 2, 4] (by omega)
    (by intro l; fin_cases l <;> norm_num) 0 0
  · norm_num
  · norm_num
  · intro l h0 h1
    fin_cases l <;> norm_num at *



theorem d030986 :
    ∃ sizes : Fin 3 → ℕ,
      ∃ hn : ∀ l, 2 ≤ sizes l,
      (∃ i j, i ≠ j ∧ sizes i ≤ 3 ∧ sizes j ≤ 3) ∧
      _root_.GD.N0232.N0719.N0973.d012376 3 sizes (by omega)
        hn (_root_.GD.N0232.N0719.N0962.d012190 3 sizes) = 0 := by
  refine ⟨![2, 2, 4], ?_, ?_, _root_.GD.N0127.d030985.1⟩
  · intro l; fin_cases l <;> norm_num
  · exact ⟨0, 1, by decide, by norm_num, by norm_num⟩

end
end GD.N0127
#print axioms _root_.GD.N0127.d030981
#print axioms _root_.GD.N0127.d030982
#print axioms _root_.GD.N0127.d030983

#print axioms _root_.GD.N0127.d030985
#print axioms _root_.GD.N0127.d030986

#print axioms _root_.GD.N0127.d030984
