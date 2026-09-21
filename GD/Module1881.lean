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
open _root_.GD.N0230.N0611
variable {k : ℕ}

theorem d030688 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0026.d030459 m n θ = _root_.GD.N0076.N0313.d030565 m n hm hn θ := by
  unfold _root_.GD.N0026.d030459 _root_.GD.N0076.N0313.d030565
  rw [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  rfl


theorem d030689
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0972.d012340 (k + 2) sizes θ)) :
    _root_.GD.N0076.N0313.d030569 (sizes i) (sizes (i.succAbove j))
      (hn i) (hn (i.succAbove j)) ≤ ENNReal.ofReal C := by
  have hcap' : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * (_root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ
        (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes)).toReal) := by
    intro θ
    rw [_root_.GD.N0232.N0719.N0972.d012341 (k + 2) sizes (by omega) hn,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0719.N0972.d012342 (k + 2) sizes (by omega) hn θ).le]
    exact hbase θ
  obtain ⟨g, hg, hgb⟩ := _root_.GD.N0127.d030687
    sizes hk hn i j hdeleted d hd C hC hcap'
  have hfinite : g ∈ _root_.GD.N0232.N0720.N1256.d015551
      (sizes i) (sizes (i.succAbove j)) :=
    ⟨hg, fun θ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hgb θ)⟩
  apply (_root_.GD.N0230.N0611.d003520 _ hfinite).trans
  apply iSup_le
  intro θ
  apply (_root_.GD.N0076.N0313.d030571
    (sizes i) (sizes (i.succAbove j)) (hn i) (hn (i.succAbove j)) C hC θ g).mpr
  simpa only [_root_.GD.N0127.d030688 _ _ (hn i) (hn (i.succAbove j))] using hgb θ



theorem d030690
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l) :
    _root_.GD.N0076.N0313.d030569 (sizes i) (sizes (i.succAbove j))
      (hn i) (hn (i.succAbove j)) ≤ _root_.GD.N0232.N0719.N0973.d012377 (k + 2) sizes (by omega) hn := by
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
  have h := _root_.GD.N0127.d030689 sizes hk hn i j hdeleted
    e heD.1 M.toReal ENNReal.toReal_nonneg hcap
  rw [ENNReal.ofReal_toReal hM] at h
  exact h.trans_eq hvD



theorem d030691
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l) :
    _root_.GD.N0232.N0719.N0973.d012376 (k + 2) sizes (by omega) hn
      (_root_.GD.N0232.N0719.N0962.d012190 (k + 2) sizes) ≤
      ((1 - (_root_.GD.N0076.N0313.d030569 (sizes i) (sizes (i.succAbove j))
        (hn i) (hn (i.succAbove j))).toReal : ℝ) : EReal) := by
  obtain ⟨_, _, _, hD, _, _, _⟩ :=
    _root_.GD.N0232.N0719.N0973.d012380 (k + 2) sizes (by omega) hn
  rw [hD]
  have h := ENNReal.toReal_mono
    (_root_.GD.N0232.N0719.N0973.d012379 (k + 2) sizes (by omega) hn)
    (_root_.GD.N0127.d030690 sizes hk hn i j hdeleted)
  exact EReal.coe_le_coe_iff.mpr (sub_le_sub_left h 1)

end
end GD.N0127
#print axioms _root_.GD.N0127.d030688
#print axioms _root_.GD.N0127.d030689
#print axioms _root_.GD.N0127.d030690
#print axioms _root_.GD.N0127.d030691
