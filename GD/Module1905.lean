import GD.Module1902
import GD.Module1899
import GD.Module1835
import GD.Module1357

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0014
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0024 _root_.GD.N0023
open _root_.GD.N0082.N0334
open _root_.GD.N0082.N0336

def d030874 : Fin 7 → ℕ := ![1, 8, 128, 512, 896, 1016, 1023]

def d030875 (i : Fin 7) : _root_.GD.N0024.N0277.d007878 :=
  ⟨(_root_.GD.N0014.d030874 i : ℝ) / 1024, by
    fin_cases i <;> norm_num [_root_.GD.N0014.d030874], by
    fin_cases i <;> norm_num [_root_.GD.N0014.d030874]⟩

def d030876 : Fin 7 → ℝ := ![3 / 100, 16 / 100, 26 / 100, 10 / 100,
  26 / 100, 16 / 100, 3 / 100]

def d030877 : Fin 7 → ℝ := ![25 / 14, 25 / 14, 77 / 50, 4 / 3,
  77 / 50, 25 / 14, 25 / 14]

def d030878 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) : ℝ :=
  ∑ i, _root_.GD.N0014.d030876 i *
    _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 3 3 (by omega) (by omega))
      g (_root_.GD.N0014.d030875 i)

theorem d030879 (i : Fin 7) : 0 ≤ _root_.GD.N0014.d030876 i := by
  fin_cases i <;> norm_num [_root_.GD.N0014.d030876]

theorem d030880 : (∑ i, _root_.GD.N0014.d030876 i) = 1 := by
  norm_num [_root_.GD.N0014.d030876, Fin.sum_univ_succ]

theorem d030881 :
    (∑ i, _root_.GD.N0014.d030876 i * (_root_.GD.N0014.d030877 i - 1)) = (32167 : ℝ) / 52500 := by
  norm_num [_root_.GD.N0014.d030876, _root_.GD.N0014.d030877, Fin.sum_univ_succ]




theorem d030882 (t : _root_.GD.N0024.N0277.d007878) :
    _root_.GD.N0023.N0258.d021868 3 3 t ≤ _root_.GD.N0082.N0334.d008258 id t.val := by
  let θ := _root_.GD.N0023.N0262.d021912 3 3 (by omega) (by omega) t
  have hf : _root_.GD.N0082.N0336.d030741 θ = t.val :=
    congrArg Subtype.val
      (_root_.GD.N0023.N0262.d021913 3 3 (by omega) (by omega) t)
  have h := _root_.GD.N0023.N0262.d021917 3 3 (by omega) (by omega) θ
  rw [_root_.GD.N0007.d030829, hf,
    _root_.GD.N0023.N0262.d021913] at h
  have hle := (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (_root_.GD.N0082.N0334.d008268 id t.val))).mp h.symm.le
  linarith



theorem d030883 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1425.d014719 3 3 g) ≤
      ENNReal.ofReal ((25 / 14 : ℝ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1425.d014719 3 3 g) ≤
      _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    ∀ i, _root_.GD.N0024.N0277.d007882
      (_root_.GD.N0023.N0261.d021897 3 3 (by omega) (by omega)) g (_root_.GD.N0014.d030875 i) ≤
        _root_.GD.N0014.d030877 i - 1 := by
  have hc := _root_.GD.N0023.N0262.d021914 3 3 (by omega) (by omega)
    g hg hb (25 / 14) (by norm_num) hcap
  have hd := _root_.GD.N0023.N0262.d021920
    3 3 (by omega) (by omega) g hg hb hbase
  have he (t : _root_.GD.N0024.N0277.d007878) := (hd t).trans (_root_.GD.N0014.d030882 t)
  intro i
  fin_cases i
  · simpa [_root_.GD.N0014.d030877] using hc (_root_.GD.N0014.d030875 0)
  · simpa [_root_.GD.N0014.d030877] using hc (_root_.GD.N0014.d030875 1)
  · have h := he (_root_.GD.N0014.d030875 2)
    rw [show (_root_.GD.N0014.d030875 2 : ℝ) = 1 / 8 by
      change (128 : ℝ) / 1024 = 1 / 8
      norm_num] at h
    have hE := _root_.GD.N0007.d030824
    norm_num [_root_.GD.N0014.d030877]
    exact h.trans (by linarith [hE])
  · have h := he (_root_.GD.N0014.d030875 3)
    rw [show (_root_.GD.N0014.d030875 3 : ℝ) = 1 / 2 by
      change (512 : ℝ) / 1024 = 1 / 2
      norm_num] at h
    have hE := _root_.GD.N0007.d030827
    norm_num [_root_.GD.N0014.d030877]
    exact h.trans (by linarith [hE])
  · have h := he (_root_.GD.N0014.d030875 4)
    rw [show (_root_.GD.N0014.d030875 4 : ℝ) = 7 / 8 by
      change (896 : ℝ) / 1024 = 7 / 8
      norm_num] at h
    have hE := _root_.GD.N0007.d030826
    norm_num [_root_.GD.N0014.d030877]
    exact h.trans (by linarith [hE])
  · simpa [_root_.GD.N0014.d030877] using hc (_root_.GD.N0014.d030875 5)
  · simpa [_root_.GD.N0014.d030877] using hc (_root_.GD.N0014.d030875 6)

theorem d030884 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (h : ∀ i, _root_.GD.N0024.N0277.d007882
      (_root_.GD.N0023.N0261.d021897 3 3 (by omega) (by omega)) g (_root_.GD.N0014.d030875 i) ≤
        _root_.GD.N0014.d030877 i - 1) : _root_.GD.N0014.d030878 g ≤ (32167 : ℝ) / 52500 := by
  rw [← _root_.GD.N0014.d030881]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i)
    (_root_.GD.N0014.d030879 i))

theorem d030885 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1425.d014719 3 3 g) ≤
      ENNReal.ofReal ((25 / 14 : ℝ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1425.d014719 3 3 g) ≤
      _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    _root_.GD.N0014.d030878 g ≤ (32167 : ℝ) / 52500 :=
  _root_.GD.N0014.d030884 g (_root_.GD.N0014.d030883 g hg hb hcap hbase)



theorem d030886 (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ)
    (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤
      ENNReal.ofReal ((25 / 14 : ℝ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧ _root_.GD.N0014.d030878 g ≤ (32167 : ℝ) / 52500 := by
  obtain ⟨g, hg, hb, hgb⟩ :=
    _root_.GD.N0020.d030259
      3 3 (by omega) (by omega) (25 / 14) (by norm_num) d hd hcap hbase
  exact ⟨g, hg, hb, _root_.GD.N0014.d030885 g hg hb
    (fun θ => (hgb θ).1) (fun θ => (hgb θ).2)⟩



theorem d030887
    (hlower : ∀ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g →
      (∀ z, g z ∈ Icc (0 : ℝ) 1) → (32167 : ℝ) / 52500 < _root_.GD.N0014.d030878 g)
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤
      ENNReal.ofReal ((25 / 14 : ℝ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    False := by
  obtain ⟨g, hg, hb, hbudget⟩ := _root_.GD.N0014.d030886 d hd hcap hbase
  exact (not_lt_of_ge hbudget) (hlower g hg hb)



theorem d030888
    (hlower : ∀ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g →
      (∀ z, g z ∈ Icc (0 : ℝ) 1) → (32167 : ℝ) / 52500 < _root_.GD.N0014.d030878 g)
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d)
    (hmin : _root_.GD.N0232.N0720.N1256.d015548 3 3 d = _root_.GD.N0232.N0720.N1256.d015549 3 3)
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    False := by
  apply _root_.GD.N0014.d030887 hlower d hd _ hbase
  intro θ
  apply (_root_.GD.N0232.N0720.N1256.d015553 3 3 (by omega) (25 / 14) (by norm_num) θ d).mp
  calc
    _root_.GD.N0232.N0720.N1256.d015547 3 3 θ d ≤ _root_.GD.N0232.N0720.N1256.d015548 3 3 d :=
      le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 3 3 θ d) θ
    _ = _root_.GD.N0232.N0720.N1256.d015549 3 3 := hmin
    _ ≤ ENNReal.ofReal (25 / 14 : ℝ) :=
      _root_.GD.N0010.d030858.le

end
end GD.N0014

#print axioms _root_.GD.N0014.d030879
#print axioms _root_.GD.N0014.d030880
#print axioms _root_.GD.N0014.d030881
#print axioms _root_.GD.N0014.d030882
#print axioms _root_.GD.N0014.d030883
#print axioms _root_.GD.N0014.d030884
#print axioms _root_.GD.N0014.d030885
#print axioms _root_.GD.N0014.d030886
#print axioms _root_.GD.N0014.d030887
#print axioms _root_.GD.N0014.d030888
