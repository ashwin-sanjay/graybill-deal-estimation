import GD.Module0491
import GD.Module1533
import GD.Module0802

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0038
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0069 _root_.GD.N0051
open _root_.GD.N0230.N0611

variable {k : ℕ}


theorem d023858 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i)
    (e : Fin k → Fin k → _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (he : ∀ i j, Measurable (e i j)) (hsym : ∀ i j z, e i j z = e j i z)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, ∀ i j, i ≠ j → _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (e i j) ≤
      ENNReal.ofReal (C * min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j))) :
    Measurable (_root_.GD.N0038.d007546 hk e) ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0962.d012186 k sizes θ (_root_.GD.N0038.d007546 hk e) ≤
        ENNReal.ofReal ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * C) := by
  refine ⟨_root_.GD.N0038.d007547 hk e he, ?_⟩
  intro θ
  apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
    (fun i => by have := hn i; omega) _ (by positivity) θ _).mpr
  have h := _root_.GD.N0038.d007559 hk (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location e he hsym
    (_root_.GD.N0069.d023850 sizes θ) (_root_.GD.N0069.d023851 sizes hn θ) hC (hb θ)
  simpa only [_root_.GD.N0038.d007554, _root_.GD.N0232.N0719.N0859.d010840, _root_.GD.N0232.N0719.N0963.d012141, _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096, _root_.GD.N0069.d023850, inv_div] using h




theorem d023859
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpair : ∀ i j : Fin k, i ≠ j → 1 < _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable d ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0962.d012186 k sizes θ d ≤ ENNReal.ofReal C := by
  classical
  have hpairs (i j : Fin k) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
        Measurable f ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, i ≠ j → _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤
          ENNReal.ofReal (C * min (_root_.GD.N0069.d023850 sizes θ i) (_root_.GD.N0069.d023850 sizes θ j)) := by
    by_cases hij : i = j
    · exact ⟨0, le_rfl, fun _ => 0, measurable_const, fun _ h => (h hij).elim⟩
    · obtain ⟨r, hr, hrb, hra⟩ := (_root_.GD.N0051.d022772 (_root_.GD.N0069.d022757 sizes hn i)).mpr (hpair i j hij)
      have hqr : r / 1 < _root_.GD.N0069.d022756 sizes j := by simpa using hrb
      have hcap := _root_.GD.N0069.d023857 sizes hn i j hij (by norm_num : (0 : ℝ) < 1)
        hr hra hqr
      exact ⟨_root_.GD.N0051.d023842 (_root_.GD.N0069.d022756 sizes i) (_root_.GD.N0069.d022756 sizes j) 1 r,
        (_root_.GD.N0051.d023843 (_root_.GD.N0069.d022757 sizes hn i) (_root_.GD.N0069.d022757 sizes hn j) hra hqr).le,
        _root_.GD.N0069.d023854 sizes i j (_root_.GD.N0051.d023841 1 r), hcap.1, fun θ _ => hcap.2 θ⟩
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


theorem d023860
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpair : ∀ i j : Fin k, i ≠ j → 1 < _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  obtain ⟨C, _, d, hd, hcap⟩ := _root_.GD.N0038.d023859 hk sizes hn hpair
  have hw : _root_.GD.N0232.N0719.N0962.d012187 k sizes d ≤ ENNReal.ofReal C := iSup_le hcap
  exact ((_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd).trans hw).trans_lt
    ENNReal.ofReal_lt_top

end
end GD.N0038

#print axioms _root_.GD.N0038.d023858
#print axioms _root_.GD.N0038.d023859
#print axioms _root_.GD.N0038.d023860
