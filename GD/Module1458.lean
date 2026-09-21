import GD.Module1457
import GD.Module1443

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0068
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0962

variable {k : ℕ}


theorem d023037 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ i j, i ≠ j →
      _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j) ≤ ENNReal.ofReal C) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ ENNReal.ofReal ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * C) := by
  classical
  have hex := fun i j => _root_.GD.N0232.N0720.N1222.d015570
    (sizes i) (sizes j) (hn i) (hn j)
  choose d hd hv using hex
  apply _root_.GD.N0068.d023036 hk sizes hn d (fun i j => (hd i j).1.1) C hC
  intro i j hij θ
  apply (_root_.GD.N0232.N0720.N1256.d015553
    (sizes i) (sizes j) (by have := hn i; omega) C hC θ (d i j)).mp
  have hupper : _root_.GD.N0232.N0720.N1256.d015548
      (sizes i) (sizes j) (d i j) ≤ ENNReal.ofReal C :=
    (hv i j).le.trans (hpair i j hij)
  exact (le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547
    (sizes i) (sizes j) θ (d i j)) θ).trans hupper


def d023038 (sizes : Fin k → ℕ) : ℝ≥0∞ :=
  ⨆ i, ⨆ j, ⨆ _h : i ≠ j,
    _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j)

theorem d023039 (sizes : Fin k → ℕ) (i j : Fin k) (hij : i ≠ j) :
    _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j) ≤ _root_.GD.N0068.d023038 sizes :=
  le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hij le_rfl))

theorem d023040 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0068.d023038 sizes ≤ _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  exact iSup_le fun i => iSup_le fun j => iSup_le fun hij =>
    _root_.GD.N0036.d022918 sizes hn i j hij


theorem d023041 (sizes : Fin k → ℕ) :
    _root_.GD.N0068.d023038 sizes ≠ ⊤ ↔ ∀ i j, i ≠ j →
      _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j) ≠ ⊤ := by
  constructor
  · intro h i j hij
    exact ne_top_of_le_ne_top h (_root_.GD.N0068.d023039 sizes i j hij)
  · intro h
    exact _root_.iSup_ne_top fun i => _root_.iSup_ne_top fun j => _root_.iSup_ne_top fun hij => h i j hij



theorem d023042 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ (k : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞) * _root_.GD.N0068.d023038 sizes := by
  by_cases htop : _root_.GD.N0068.d023038 sizes = ⊤
  · have hk0 : k ≠ 0 := by omega
    have hk1 : k - 1 ≠ 0 := by omega
    rw [htop, ENNReal.mul_top (mul_ne_zero (Nat.cast_ne_zero.mpr hk0) (Nat.cast_ne_zero.mpr hk1))]
    exact le_top
  let C := (_root_.GD.N0068.d023038 sizes).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0068.d023038 sizes := ENNReal.ofReal_toReal htop
  have hbound := _root_.GD.N0068.d023037 hk sizes hn C hC (fun i j hij => by
    rw [hval]
    exact _root_.GD.N0068.d023039 sizes i j hij)
  have heq : ENNReal.ofReal ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * C) =
      (k : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞) * _root_.GD.N0068.d023038 sizes := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg k),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, hval]
  exact heq ▸ hbound


theorem d023043 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤ ↔ ∀ i j, i ≠ j →
      _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j) ≠ ⊤ := by
  rw [← _root_.GD.N0068.d023041 sizes]
  constructor
  · intro h
    exact ne_top_of_le_ne_top h (_root_.GD.N0068.d023040 sizes hn)
  · intro h
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) h)
      (_root_.GD.N0068.d023042 hk sizes hn)


theorem d023044 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes = ⊤ ↔ ∃ i j, i ≠ j ∧
      _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j) = ⊤ := by
  classical
  have hh := not_congr (_root_.GD.N0068.d023043 hk sizes hn)
  simpa only [not_not, not_forall, exists_prop] using hh

end
end GD.N0068

#print axioms _root_.GD.N0068.d023037
#print axioms _root_.GD.N0068.d023040
#print axioms _root_.GD.N0068.d023042
#print axioms _root_.GD.N0068.d023043
#print axioms _root_.GD.N0068.d023044
