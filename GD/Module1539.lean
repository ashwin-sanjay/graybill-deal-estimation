import GD.Module1538
import GD.Module1534

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0354
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962
open _root_.GD.N0230.N0611
open _root_.GD.N0069 _root_.GD.N0051 _root_.GD.N0038
open _root_.GD.N0101.N0355

variable {k : ℕ}




theorem d023879
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpair : ∀ i j : Fin k, i ≠ j →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable f ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤
          ENNReal.ofReal (C * min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable d ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0962.d012186 k sizes θ d ≤ ENNReal.ofReal C := by
  classical
  have hpairs (i j : Fin k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable f ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, i ≠ j → _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤
          ENNReal.ofReal (C * min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
    by_cases hij : i = j
    · exact ⟨0, le_rfl, fun _ => 0, measurable_const, fun _ h => (h hij).elim⟩
    · obtain ⟨C, hC, f, hf, hb⟩ := hpair i j hij
      exact ⟨C, hC, f, hf, fun θ _ => hb θ⟩
  choose c hc f hf hb using hpairs
  let C : ℝ := ∑ i, ∑ j, c i j
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hc i j
  have hcC (i j : Fin k) : c i j ≤ C := by
    exact (Finset.single_le_sum (fun r _ => hc i r) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun r _ => Finset.sum_nonneg fun s _ => hc r s) (Finset.mem_univ i))
  let e : Fin k → Fin k → _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
    fun i j => if i ≤ j then f i j else f j i
  have he (i j : Fin k) : Measurable (e i j) := by
    dsimp only [e]
    split_ifs <;> exact hf _ _
  have hsym (i j : Fin k) (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) : e i j z = e j i z := by
    by_cases hij : i ≤ j
    · by_cases hji : j ≤ i
      · have h := le_antisymm hij hji
        subst j
        rfl
      · simp only [e, if_pos hij, if_neg hji]
    · have hji : j ≤ i := (lt_of_not_ge hij).le
      simp only [e, if_neg hij, if_pos hji]
  have hecap (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i j : Fin k) (hij : i ≠ j) :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (e i j) ≤
        ENNReal.ofReal (C * min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
    have hmin : 0 ≤ min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j) :=
      le_min (_root_.GD.N0069.d023851 sizes hn θ i).le (_root_.GD.N0069.d023851 sizes hn θ j).le
    by_cases hle : i ≤ j
    · dsimp only [e]
      rw [if_pos hle]
      exact (hb i j θ hij).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hcC i j) hmin))
    · dsimp only [e]
      rw [if_neg hle]
      have h := hb j i θ (Ne.symm hij)
      rw [min_comm] at h
      exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hcC j i) hmin))
  obtain ⟨hd, hcap⟩ := _root_.GD.N0038.d023858 hk sizes hn e he hsym hC hecap
  exact ⟨(k : ℝ) * ((k - 1 : ℕ) : ℝ) * C, by positivity, _root_.GD.N0038.d007546 hk e, hd, hcap⟩


theorem d023880
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpair : ∀ i j : Fin k, i ≠ j → 1 ≤ _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable d ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0962.d012186 k sizes θ d ≤ ENNReal.ofReal C := by
  apply _root_.GD.N0101.N0354.d023879 hk sizes hn
  exact fun i j hij => _root_.GD.N0101.N0355.d023878 sizes hn i j hij (hpair i j hij)

theorem d023881
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpair : ∀ i j : Fin k, i ≠ j → 1 ≤ _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  obtain ⟨C, _, d, hd, hcap⟩ :=
    _root_.GD.N0101.N0354.d023880 hk sizes hn hpair
  have hw : _root_.GD.N0232.N0719.N0962.d012187 k sizes d ≤ ENNReal.ofReal C := iSup_le hcap
  exact ((_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd).trans hw).trans_lt
    ENNReal.ofReal_lt_top


theorem d023882 (sizes : Fin k → ℕ) (i j : Fin k) :
    1 ≤ _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j ↔ 4 ≤ (sizes i - 1) * (sizes j - 1) := by
  unfold _root_.GD.N0069.d022756
  constructor
  · intro h
    have hh : (4 : ℝ) ≤ ((sizes i - 1 : ℕ) : ℝ) * ((sizes j - 1 : ℕ) : ℝ) := by nlinarith
    exact_mod_cast hh
  · intro h
    have hh : (4 : ℝ) ≤ ((sizes i - 1 : ℕ) : ℝ) * ((sizes j - 1 : ℕ) : ℝ) := by exact_mod_cast h
    nlinarith

theorem d023883
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpairs : ∀ i j : Fin k, i ≠ j → 4 ≤ (sizes i - 1) * (sizes j - 1)) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  apply _root_.GD.N0101.N0354.d023881 hk sizes hn
  exact fun i j hij => (_root_.GD.N0101.N0354.d023882 sizes i j).mpr (hpairs i j hij)


theorem d023884
    (sizes : Fin k → ℕ) (i₀ : Fin k) (hsmall : 2 ≤ sizes i₀)
    (hlarge : ∀ i, i ≠ i₀ → 5 ≤ sizes i) :
    (∀ i, 2 ≤ sizes i) ∧
      ∀ i j : Fin k, i ≠ j → 4 ≤ (sizes i - 1) * (sizes j - 1) := by
  have hn (i : Fin k) : 2 ≤ sizes i := by
    by_cases hi : i = i₀
    · simpa only [hi] using hsmall
    · have := hlarge i hi
      omega
  refine ⟨hn, ?_⟩
  intro i j hij
  have hi : 1 ≤ sizes i - 1 := by have := hn i; omega
  have hj : 1 ≤ sizes j - 1 := by have := hn j; omega
  by_cases hi0 : i = i₀
  · have hj0 : j ≠ i₀ := by intro h; exact hij (hi0.trans h.symm)
    have hj4 : 4 ≤ sizes j - 1 := by have := hlarge j hj0; omega
    nlinarith
  · have hi4 : 4 ≤ sizes i - 1 := by have := hlarge i hi0; omega
    nlinarith

theorem d023885
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (i₀ : Fin k)
    (hsmall : 2 ≤ sizes i₀) (hlarge : ∀ i, i ≠ i₀ → 5 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  obtain ⟨hn, hpairs⟩ := _root_.GD.N0101.N0354.d023884 sizes i₀ hsmall hlarge
  exact _root_.GD.N0101.N0354.d023883 hk sizes hn hpairs



theorem d023886
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  apply _root_.GD.N0101.N0354.d023883 hk sizes
    (fun i => by have := hn i; omega)
  intro i j _
  have hi : 2 ≤ sizes i - 1 := by have := hn i; omega
  have hj : 2 ≤ sizes j - 1 := by have := hn j; omega
  nlinarith

end
end GD.N0101.N0354

#print axioms _root_.GD.N0101.N0354.d023879
#print axioms _root_.GD.N0101.N0354.d023880
#print axioms _root_.GD.N0101.N0354.d023881
#print axioms _root_.GD.N0101.N0354.d023882
#print axioms _root_.GD.N0101.N0354.d023883
#print axioms _root_.GD.N0101.N0354.d023885
#print axioms _root_.GD.N0101.N0354.d023886
