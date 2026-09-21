import GD.Module1540
import GD.Module1535
import GD.Module1443

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0032
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0069 _root_.GD.N0051 _root_.GD.N0038
open _root_.GD.N0230.N0611

variable {k : ℕ}




theorem d023889
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpair : ∀ i j : Fin k, i ≠ j → 1 ≤ _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable d ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0962.d012186 k sizes θ d ≤ ENNReal.ofReal C := by
  classical
  have hpairs (i j : Fin k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable f ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, i ≠ j → _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤
          ENNReal.ofReal (C * min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
    by_cases hij : i = j
    · exact ⟨0, le_rfl, fun _ => 0, measurable_const, fun _ h => (h hij).elim⟩
    · obtain ⟨C, hC, f, hf, hb⟩ := _root_.GD.N0032.d023888
        sizes hn i j hij (hpair i j hij)
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


theorem d023890
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpair : ∀ i j : Fin k, i ≠ j → 1 ≤ _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  obtain ⟨C, _, d, hd, hcap⟩ := _root_.GD.N0032.d023889 hk sizes hn hpair
  have hw : _root_.GD.N0232.N0719.N0962.d012187 k sizes d ≤ ENNReal.ofReal C := iSup_le hcap
  exact ((_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd).trans hw).trans_lt
    ENNReal.ofReal_lt_top

end
end GD.N0032

#print axioms _root_.GD.N0032.d023889
#print axioms _root_.GD.N0032.d023890

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0032
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0069

variable {k : ℕ}


theorem d023891 (sizes : Fin k → ℕ) (i j : Fin k) :
    1 ≤ _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j ↔ 4 ≤ (sizes i - 1) * (sizes j - 1) := by
  unfold _root_.GD.N0069.d022756
  constructor
  · intro h
    have hh : (4 : ℝ) ≤ ((sizes i - 1 : ℕ) : ℝ) * ((sizes j - 1 : ℕ) : ℝ) := by nlinarith
    exact_mod_cast hh
  · intro h
    have hh : (4 : ℝ) ≤ ((sizes i - 1 : ℕ) : ℝ) * ((sizes j - 1 : ℕ) : ℝ) := by exact_mod_cast h
    nlinarith



theorem d023892
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpairs : ∀ i j : Fin k, i ≠ j → 4 ≤ (sizes i - 1) * (sizes j - 1)) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  apply _root_.GD.N0032.d023890 hk sizes hn
  intro i j hij
  exact (_root_.GD.N0032.d023891 sizes i j).mpr (hpairs i j hij)

theorem d023893
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
    have hj5 : 4 ≤ sizes j - 1 := by have := hlarge j hj0; omega
    nlinarith
  · have hi5 : 4 ≤ sizes i - 1 := by have := hlarge i hi0; omega
    nlinarith



theorem d023894
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (i₀ : Fin k)
    (hsmall : 2 ≤ sizes i₀) (hlarge : ∀ i, i ≠ i₀ → 5 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  obtain ⟨hn, hpairs⟩ := _root_.GD.N0032.d023893 sizes i₀ hsmall hlarge
  exact _root_.GD.N0032.d023892 hk sizes hn hpairs



theorem d023895
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (i₀ : Fin k)
    (hsmall : 2 ≤ sizes i₀) (hlarge : ∀ i, i ≠ i₀ → 5 ≤ sizes i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable d ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0962.d012186 k sizes θ d ≤ ENNReal.ofReal C := by
  obtain ⟨hn, hpairs⟩ := _root_.GD.N0032.d023893 sizes i₀ hsmall hlarge
  apply _root_.GD.N0032.d023889 hk sizes hn
  intro i j hij
  exact (_root_.GD.N0032.d023891 sizes i j).mpr (hpairs i j hij)

end
end GD.N0032

#print axioms _root_.GD.N0032.d023891
#print axioms _root_.GD.N0032.d023892
#print axioms _root_.GD.N0032.d023894
#print axioms _root_.GD.N0032.d023895

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0030
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1256


theorem d023896
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hprod : 4 ≤ (m - 1) * (n - 1)) : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ := by
  let sizes : Fin 2 → ℕ := ![m, n]
  have hs : ∀ i, 2 ≤ sizes i := by
    intro i
    fin_cases i
    · exact hm
    · exact hn
  have hp : ∀ i j : Fin 2, i ≠ j → 4 ≤ (sizes i - 1) * (sizes j - 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hprod
    · change 4 ≤ (n - 1) * (m - 1)
      simpa only [mul_comm] using hprod
    · exact (hij rfl).elim
  have hh := _root_.GD.N0036.d022918 sizes hs 0 1 (by decide)
  have hb := _root_.GD.N0032.d023892
    (by decide : 2 ≤ 2) sizes hs hp
  exact ne_top_of_lt (hh.trans_lt hb)


theorem d023897
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hlarge : 5 ≤ m ∨ 5 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ := by
  apply _root_.GD.N0030.d023896 m n hm hn
  have hm1 : 1 ≤ m - 1 := by omega
  have hn1 : 1 ≤ n - 1 := by omega
  rcases hlarge with h | h
  · have : 4 ≤ m - 1 := by omega
    nlinarith
  · have : 4 ≤ n - 1 := by omega
    nlinarith


theorem d023898 : _root_.GD.N0232.N0720.N1256.d015549 2 5 ≠ ⊤ :=
  _root_.GD.N0030.d023896 2 5 (by decide) (by decide) (by decide)


theorem d023899
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤) :
    (m = 2 ∧ n ≤ 4) ∨ (n = 2 ∧ m ≤ 4) := by
  have hp : ¬ 4 ≤ (m - 1) * (n - 1) :=
    fun h => _root_.GD.N0030.d023896 m n hm hn h htop
  have hm1 : 1 ≤ m - 1 := by omega
  have hn1 : 1 ≤ n - 1 := by omega
  have hm5 : ¬ 5 ≤ m := by
    intro h
    exact _root_.GD.N0030.d023897 m n hm hn (Or.inl h) htop
  have hn5 : ¬ 5 ≤ n := by
    intro h
    exact _root_.GD.N0030.d023897 m n hm hn (Or.inr h) htop
  by_cases hm2 : m = 2
  · exact Or.inl ⟨hm2, by omega⟩
  · right
    have hm3 : 2 ≤ m - 1 := by omega
    have hn2 : n = 2 := by
      by_contra h
      have : 2 ≤ n - 1 := by omega
      apply hp
      nlinarith
    exact ⟨hn2, by omega⟩

end
end GD.N0030

#print axioms _root_.GD.N0030.d023896
#print axioms _root_.GD.N0030.d023897
#print axioms _root_.GD.N0030.d023898
#print axioms _root_.GD.N0030.d023899
