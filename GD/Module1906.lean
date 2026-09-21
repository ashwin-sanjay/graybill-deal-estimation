import GD.Module1905
import GD.Module1850

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0012
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0024 _root_.GD.N0023
open _root_.GD.N0022.N0255
open _root_.GD.N0082.N0334
open _root_.GD.N0014

def d030889 (δ : ℝ) : Fin 7 → ℝ :=
  ![25 / 14 + δ, 25 / 14 + δ, 77 / 50, 4 / 3, 77 / 50,
    25 / 14 + δ, 25 / 14 + δ]

def d030890 : ℝ := 25 / 14 + 1 / 1000



def d030891 : ℝ :=
  1709368612906862813690857739743261132972032 / 2 ^ 141

def d030892 : Prop := ∀ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g →
  (∀ z, g z ∈ Icc (0 : ℝ) 1) →
    (32167 : ℝ) / 52500 + 1 / 2000 < _root_.GD.N0014.d030878 g

def d030893 : Prop := ∀ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g →
  (∀ z, g z ∈ Icc (0 : ℝ) 1) → _root_.GD.N0012.d030891 ≤ _root_.GD.N0014.d030878 g

theorem d030894 (δ : ℝ) :
    (∑ i, _root_.GD.N0014.d030876 i * (_root_.GD.N0012.d030889 δ i - 1)) =
      (32167 : ℝ) / 52500 + (19 / 50) * δ := by
  norm_num [_root_.GD.N0012.d030889, _root_.GD.N0014.d030876, Fin.sum_univ_succ]
  ring

theorem d030895 :
    (32167 : ℝ) / 52500 + 1 / 2000 < _root_.GD.N0012.d030891 := by
  norm_num [_root_.GD.N0012.d030891]

theorem d030896 (h : _root_.GD.N0012.d030893) : _root_.GD.N0012.d030892 := by
  intro g hg hb
  exact _root_.GD.N0012.d030895.trans_le (h g hg hb)

theorem d030897 :
    (19 / 50 : ℝ) * (1 / 1000) < 1 / 2000 := by norm_num



theorem d030898 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1425.d014719 3 3 g) ≤
      ENNReal.ofReal (((25 / 14 : ℝ) + δ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1425.d014719 3 3 g) ≤
      _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    ∀ i, _root_.GD.N0024.N0277.d007882
      (_root_.GD.N0023.N0261.d021897 3 3 (by omega) (by omega)) g (_root_.GD.N0014.d030875 i) ≤
        _root_.GD.N0012.d030889 δ i - 1 := by
  have hc := _root_.GD.N0023.N0262.d021914 3 3 (by omega) (by omega)
    g hg hb (25 / 14 + δ) (by linarith) hcap
  have hd := _root_.GD.N0023.N0262.d021920
    3 3 (by omega) (by omega) g hg hb hbase
  have he (t : _root_.GD.N0024.N0277.d007878) :=
    (hd t).trans (_root_.GD.N0014.d030882 t)
  intro i
  fin_cases i
  · simpa [_root_.GD.N0012.d030889] using hc (_root_.GD.N0014.d030875 0)
  · simpa [_root_.GD.N0012.d030889] using hc (_root_.GD.N0014.d030875 1)
  · have h := he (_root_.GD.N0014.d030875 2)
    rw [show (_root_.GD.N0014.d030875 2 : ℝ) = 1 / 8 by
      change (128 : ℝ) / 1024 = 1 / 8
      norm_num] at h
    have hE := _root_.GD.N0007.d030824
    norm_num [_root_.GD.N0012.d030889]
    exact h.trans (by linarith [hE])
  · have h := he (_root_.GD.N0014.d030875 3)
    rw [show (_root_.GD.N0014.d030875 3 : ℝ) = 1 / 2 by
      change (512 : ℝ) / 1024 = 1 / 2
      norm_num] at h
    have hE := _root_.GD.N0007.d030827
    norm_num [_root_.GD.N0012.d030889]
    exact h.trans (by linarith [hE])
  · have h := he (_root_.GD.N0014.d030875 4)
    rw [show (_root_.GD.N0014.d030875 4 : ℝ) = 7 / 8 by
      change (896 : ℝ) / 1024 = 7 / 8
      norm_num] at h
    have hE := _root_.GD.N0007.d030826
    norm_num [_root_.GD.N0012.d030889]
    exact h.trans (by linarith [hE])
  · simpa [_root_.GD.N0012.d030889] using hc (_root_.GD.N0014.d030875 5)
  · simpa [_root_.GD.N0012.d030889] using hc (_root_.GD.N0014.d030875 6)

theorem d030899 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1425.d014719 3 3 g) ≤
      ENNReal.ofReal (((25 / 14 : ℝ) + δ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1425.d014719 3 3 g) ≤
      _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    _root_.GD.N0014.d030878 g ≤ (32167 : ℝ) / 52500 + (19 / 50) * δ := by
  rw [← _root_.GD.N0012.d030894]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
    (_root_.GD.N0012.d030898 g hg hb δ hδ hcap hbase i) (_root_.GD.N0014.d030879 i))


theorem d030900 (hmargin : _root_.GD.N0012.d030892)
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤
      ENNReal.ofReal (_root_.GD.N0012.d030890 * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    False := by
  obtain ⟨g, hg, hb, hgb⟩ :=
    _root_.GD.N0020.d030259
      3 3 (by omega) (by omega) _root_.GD.N0012.d030890 (by norm_num [_root_.GD.N0012.d030890]) d hd hcap hbase
  have hbudget := _root_.GD.N0012.d030899 g hg hb (1 / 1000) (by norm_num)
    (fun θ => (hgb θ).1) (fun θ => (hgb θ).2)
  have hlower := hmargin g hg hb
  linarith [_root_.GD.N0012.d030897]

theorem d030901 (hmargin : _root_.GD.N0012.d030892)
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d)
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    ENNReal.ofReal _root_.GD.N0012.d030890 < _root_.GD.N0232.N0720.N1256.d015548 3 3 d := by
  by_contra h
  have hw : _root_.GD.N0232.N0720.N1256.d015548 3 3 d ≤ ENNReal.ofReal _root_.GD.N0012.d030890 := le_of_not_gt h
  apply _root_.GD.N0012.d030900 hmargin d hd _ hbase
  intro θ
  apply (_root_.GD.N0232.N0720.N1256.d015553 3 3 (by omega) _root_.GD.N0012.d030890
    (by norm_num [_root_.GD.N0012.d030890]) θ d).mp
  exact (le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 3 3 θ d) θ).trans hw

theorem d030902 :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1 / 1000 : ℝ) ≤ ENNReal.ofReal _root_.GD.N0012.d030890 := by
  rw [_root_.GD.N0012.d030890, ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact _root_.add_le_add
    _root_.GD.N0010.d030858.le le_rfl

theorem d030903 (hmargin : _root_.GD.N0012.d030892)
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d)
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3)) :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1 / 1000 : ℝ) < _root_.GD.N0232.N0720.N1256.d015548 3 3 d :=
  _root_.GD.N0012.d030902.trans_lt
    (_root_.GD.N0012.d030901 hmargin d hd hbase)

theorem d030904 (hmargin : _root_.GD.N0012.d030892) :
    ENNReal.ofReal _root_.GD.N0012.d030890 ≤ _root_.GD.N0022.N0255.d030394 3 3 := by
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact (_root_.GD.N0012.d030901 hmargin d hd.1 hd.2).le



theorem d030905 (hlower : _root_.GD.N0012.d030893) :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1 / 1000 : ℝ) ≤
      _root_.GD.N0022.N0255.d030394 3 3 :=
  _root_.GD.N0012.d030902.trans
    (_root_.GD.N0012.d030904 (_root_.GD.N0012.d030896 hlower))

end
end GD.N0012

#print axioms _root_.GD.N0012.d030894
#print axioms _root_.GD.N0012.d030895
#print axioms _root_.GD.N0012.d030896
#print axioms _root_.GD.N0012.d030897
#print axioms _root_.GD.N0012.d030898
#print axioms _root_.GD.N0012.d030899
#print axioms _root_.GD.N0012.d030900
#print axioms _root_.GD.N0012.d030901
#print axioms _root_.GD.N0012.d030902
#print axioms _root_.GD.N0012.d030903
#print axioms _root_.GD.N0012.d030904
#print axioms _root_.GD.N0012.d030905
