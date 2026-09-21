import GD.Module1442

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace GD.N0036
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0099

variable {k : ℕ}


theorem d022915
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ)) :
    _root_.GD.N0232.N0720.N1256.d015549
      (sizes i) (sizes (i.succAbove j)) ≤ ENNReal.ofReal C := by
  have hc : Continuous (fun ε : ℝ => ∏ l, _root_.GD.N0036.d022652 ε ^ _root_.GD.N0099.d022902 sizes i j l) :=
    continuous_finsetProd _ (fun _ _ => _root_.GD.N0036.d022659.pow _)
  have hl : Tendsto (fun n : ℕ =>
      ∏ l, _root_.GD.N0036.d022652 (1 / ((n : ℝ) + 1)) ^ _root_.GD.N0099.d022902 sizes i j l) atTop (𝓝 1) := by
    simpa only [Function.comp_def, _root_.GD.N0036.d022660, one_pow, Finset.prod_const_one] using
      (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hv : Tendsto (fun n : ℕ => ENNReal.ofReal
      ((∏ l, _root_.GD.N0036.d022652 (1 / ((n : ℝ) + 1)) ^ _root_.GD.N0099.d022902 sizes i j l) * C))
      atTop (𝓝 (ENNReal.ofReal C)) := by
    simpa only [Function.comp_def, one_mul] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hl.mul_const C)
  exact ge_of_tendsto' hv (fun n => _root_.GD.N0036.d022914
    sizes hn i j d hd C hC (1 / ((n : ℝ) + 1)) (by positivity) hcap)



theorem d022916
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0720.N1256.d015549
      (sizes i) (sizes (i.succAbove j)) ≤
        _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d := by
  by_cases htop : _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d = ⊤
  · rw [htop]
    exact le_top
  let C := (_root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d :=
    ENNReal.ofReal_toReal htop
  rw [← hval]
  apply _root_.GD.N0036.d022915 sizes hn i j d hd C hC
  intro θ
  apply (_root_.GD.N0232.N0719.N0962.d012192 (k + 2) sizes
    (by omega) (fun l => by have := hn l; omega) C hC θ d).mp
  rw [hval]
  exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 (k + 2) sizes θ d) θ


theorem d022917
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    _root_.GD.N0232.N0720.N1256.d015549
      (sizes i) (sizes (i.succAbove j)) ≤
        _root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes := by
  unfold _root_.GD.N0232.N0719.N0962.d012188
    _root_.GD.N0230.N0611.d003517
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact _root_.GD.N0036.d022916 sizes hn i j d hd


theorem d022918
    {K : ℕ} (sizes : Fin K → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i j : Fin K) (hij : i ≠ j) :
    _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j) ≤
      _root_.GD.N0232.N0719.N0962.d012188 K sizes := by
  cases K with
  | zero => exact Fin.elim0 i
  | succ K =>
    cases K with
    | zero => exact (hij (Fin.ext (by have hi := i.isLt; have hj := j.isLt; omega))).elim
    | succ k =>
      obtain ⟨h, hh⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
      simpa only [hh] using _root_.GD.N0036.d022917 sizes hn i h


theorem d022919
    {K : ℕ} (sizes : Fin K → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i j : Fin K) (hij : i ≠ j)
    (hpair : _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j) = ⊤) :
    _root_.GD.N0232.N0719.N0962.d012188 K sizes = ⊤ := by
  apply top_unique
  rw [← hpair]
  exact _root_.GD.N0036.d022918 sizes hn i j hij

end
end GD.N0036

#print axioms _root_.GD.N0036.d022915
#print axioms _root_.GD.N0036.d022916
#print axioms _root_.GD.N0036.d022918
#print axioms _root_.GD.N0036.d022919
