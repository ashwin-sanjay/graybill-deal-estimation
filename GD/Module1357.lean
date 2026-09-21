import GD.Module1354
import GD.Module1356
import GD.Module0980

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0023.N0262

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1424 _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1287
open _root_.GD.N0232.N0720.N1332
open _root_.GD.N0107
open _root_.GD.N0024

def d021905 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0024.N0277.d007878 :=
  ⟨_root_.GD.N0107.d009046 m n θ.scale₁ θ.scale₂,
    _root_.GD.N0107.d009050 (by omega) (by omega) θ.scale₁_pos θ.scale₂_pos,
    _root_.GD.N0107.d009051 (by omega) (by omega) θ.scale₁_pos θ.scale₂_pos⟩

def d021906 (m n : ℕ) (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ := _root_.GD.N0107.d009045 m n θ.scale₁ θ.scale₂

theorem d021907 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0023.N0262.d021906 m n θ :=
  _root_.GD.N0107.d009049 (by omega) (by omega) θ.scale₁_pos θ.scale₂_pos

theorem d021908 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a⁻¹ + b⁻¹)⁻¹ = (a + b) * (b / (a + b) * (1 - b / (a + b))) := by
  have hab := add_pos ha hb
  field_simp [ha.ne', hb.ne', hab.ne']
  ring

theorem d021909 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1257.d015508 m n θ = _root_.GD.N0023.N0262.d021906 m n θ * _root_.GD.N0024.N0277.d007879 (_root_.GD.N0023.N0262.d021905 m n hm hn θ) := by
  have h := _root_.GD.N0023.N0262.d021908 (_root_.GD.N0107.d009043 m θ.scale₁) (_root_.GD.N0107.d009044 n θ.scale₂)
    (_root_.GD.N0107.d009047 (by omega) θ.scale₁_pos) (_root_.GD.N0107.d009048 (by omega) θ.scale₂_pos)
  simpa only [_root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0023.N0262.d021906, _root_.GD.N0024.N0277.d007879, _root_.GD.N0023.N0262.d021905,
    _root_.GD.N0107.d009046, _root_.GD.N0107.d009045, _root_.GD.N0107.d009043, _root_.GD.N0107.d009044, inv_div] using h

theorem d021910 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) =
      ENNReal.ofReal (_root_.GD.N0023.N0262.d021906 m n θ *
        (_root_.GD.N0024.N0277.d007879 (_root_.GD.N0023.N0262.d021905 m n hm hn θ) +
          _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0023.N0262.d021905 m n hm hn θ).val)) := by
  rw [_root_.GD.N0232.N0720.N1332.d020109 m n hm hn θ hg hb]
  have horacle := _root_.GD.N0232.N0720.N1396.d014795 m n hm hn θ
  unfold _root_.GD.N0232.N0720.N1396.d014778 at horacle
  rw [horacle]
  congr 1
  unfold _root_.GD.N0023.N0262.d021906 _root_.GD.N0023.N0262.d021905 _root_.GD.N0024.N0277.d007879
  ring

theorem d021911 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) =
      ENNReal.ofReal (1 + _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn)
        g (_root_.GD.N0023.N0262.d021905 m n hm hn θ)) := by
  have hS := _root_.GD.N0023.N0262.d021907 m n hm hn θ
  have ht := _root_.GD.N0024.N0277.d007880 (_root_.GD.N0023.N0262.d021905 m n hm hn θ)
  unfold _root_.GD.N0232.N0720.N1256.d015547
  rw [_root_.GD.N0023.N0262.d021910 m n hm hn g hg hb, _root_.GD.N0023.N0262.d021909 m n hm hn,
    ← ENNReal.ofReal_div_of_pos (mul_pos hS ht)]
  congr 1
  unfold _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0277.d007881 _root_.GD.N0023.N0261.d021897 _root_.GD.N0232.N0720.N1332.d020106
  field_simp

def d021912 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0024.N0277.d007878) : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1332.d020110 m n hm hn t

theorem d021913 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0024.N0277.d007878) :
    _root_.GD.N0023.N0262.d021905 m n hm hn (_root_.GD.N0023.N0262.d021912 m n hm hn t) = t := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0720.N1332.d020112 m n hm hn t

theorem d021914 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (v : ℝ) (hv : 0 ≤ v)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
      ENNReal.ofReal (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ)) :
    ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) g t ≤ v - 1 := by
  intro t
  have h := (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) v hv (_root_.GD.N0023.N0262.d021912 m n hm hn t)
    (_root_.GD.N0232.N0720.N1425.d014719 m n g)).mpr (hcap (_root_.GD.N0023.N0262.d021912 m n hm hn t))
  rw [_root_.GD.N0023.N0262.d021911 m n hm hn g hg hb, _root_.GD.N0023.N0262.d021913] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff hv).mp h
  linarith

theorem d021915 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : ℝ) (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v) (hv : 0 < v)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ t, (v - 1) - ε < _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) g t := by
  by_contra hnot
  push Not at hnot
  have hbound : _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
      ENNReal.ofReal (v - ε) := by
    apply iSup_le
    intro θ
    rw [_root_.GD.N0023.N0262.d021911 m n hm hn g hg hb]
    exact ENNReal.ofReal_le_ofReal (by linarith [hnot (_root_.GD.N0023.N0262.d021905 m n hm hn θ)])
  have hmin := _root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0720.N1256.d015547 m n) (S := _root_.GD.N0232.N0720.N1256.d015545 m n)
    (_root_.GD.N0232.N0720.N1398.d019599 m n hg)
  change _root_.GD.N0232.N0720.N1256.d015549 m n ≤ _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1425.d014719 m n g) at hmin
  rw [hvalue] at hmin
  have hlt : ENNReal.ofReal (v - ε) < ENNReal.ofReal v :=
    (ENNReal.ofReal_lt_ofReal_iff hv).mpr (by linarith)
  exact (not_lt.mpr (hmin.trans hbound)) hlt

theorem d021916 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) =
      ENNReal.ofReal (_root_.GD.N0023.N0262.d021906 m n θ *
        (_root_.GD.N0024.N0277.d007879 (_root_.GD.N0023.N0262.d021905 m n hm hn θ) +
          _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 (_root_.GD.N0023.N0262.d021905 m n hm hn θ).val)) := by
  rw [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn, _root_.GD.N0232.N0720.N1287.d019529 m n hm hn]
  have horacle := _root_.GD.N0232.N0720.N1396.d014795 m n hm hn θ
  unfold _root_.GD.N0232.N0720.N1396.d014778 at horacle
  rw [horacle]
  congr 1
  unfold _root_.GD.N0023.N0262.d021906 _root_.GD.N0023.N0262.d021905 _root_.GD.N0024.N0277.d007879 _root_.GD.N0232.N0720.N1332.d020106 _root_.GD.N0232.N0720.N1424.d014839
  ring

theorem d021917 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) =
      ENNReal.ofReal (1 + _root_.GD.N0023.N0258.d021868 m n (_root_.GD.N0023.N0262.d021905 m n hm hn θ)) := by
  have hS := _root_.GD.N0023.N0262.d021907 m n hm hn θ
  have ht := _root_.GD.N0024.N0277.d007880 (_root_.GD.N0023.N0262.d021905 m n hm hn θ)
  unfold _root_.GD.N0232.N0720.N1256.d015547
  rw [_root_.GD.N0023.N0262.d021916 m n hm hn, _root_.GD.N0023.N0262.d021909 m n hm hn,
    ← ENNReal.ofReal_div_of_pos (mul_pos hS ht)]
  congr 1
  unfold _root_.GD.N0023.N0258.d021868
  change _root_.GD.N0023.N0262.d021906 m n θ *
      (_root_.GD.N0024.N0277.d007879 (_root_.GD.N0023.N0262.d021905 m n hm hn θ) + _) /
        (_root_.GD.N0023.N0262.d021906 m n θ * _root_.GD.N0024.N0277.d007879 (_root_.GD.N0023.N0262.d021905 m n hm hn θ)) =
      1 + _ / _root_.GD.N0024.N0277.d007879 (_root_.GD.N0023.N0262.d021905 m n hm hn θ)
  field_simp [hS.ne', ht.ne']

theorem d021918 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≤ ENNReal.ofReal (1 + _root_.GD.N0023.N0258.d021869 m n) := by
  have hd : _root_.GD.N0232.N0720.N1080.d014175 m n ∈ _root_.GD.N0232.N0720.N1256.d015545 m n :=
    _root_.GD.N0117.d014146 m n
  apply (_root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0720.N1256.d015547 m n) hd).trans
  apply iSup_le
  intro θ
  rw [_root_.GD.N0023.N0262.d021917 m n (by omega) (by omega)]
  exact ENNReal.ofReal_le_ofReal (add_le_add le_rfl
    (_root_.GD.N0023.N0258.d021873 m n hm hn _))

theorem d021919 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0023.N0262.d021918 m n hm hn)

theorem d021920 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) :
    ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) g t ≤
      _root_.GD.N0023.N0258.d021868 m n t := by
  intro t
  have h := hcap (_root_.GD.N0023.N0262.d021912 m n hm hn t)
  rw [_root_.GD.N0023.N0262.d021910 m n hm hn g hg hb, _root_.GD.N0023.N0262.d021916 m n hm hn, _root_.GD.N0023.N0262.d021913] at h
  have hS := _root_.GD.N0023.N0262.d021907 m n hm hn (_root_.GD.N0023.N0262.d021912 m n hm hn t)
  have ht := _root_.GD.N0024.N0277.d007880 t
  have hright : 0 ≤ _root_.GD.N0023.N0262.d021906 m n (_root_.GD.N0023.N0262.d021912 m n hm hn t) *
      (_root_.GD.N0024.N0277.d007879 t + _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 t.val) :=
    mul_nonneg hS.le (add_nonneg ht.le (_root_.GD.N0232.N0720.N1332.d020107 _ _ _ _))
  have hreal := (ENNReal.ofReal_le_ofReal_iff hright).mp h
  have hcancel := le_of_mul_le_mul_left hreal hS
  have hloss : _root_.GD.N0232.N0720.N1332.d020106 m n g t.val ≤ _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 t.val := by
    linarith
  exact div_le_div_of_nonneg_right hloss ht.le

end
end GD.N0023.N0262

#print axioms _root_.GD.N0023.N0262.d021907
#print axioms _root_.GD.N0023.N0262.d021908
#print axioms _root_.GD.N0023.N0262.d021909
#print axioms _root_.GD.N0023.N0262.d021910
#print axioms _root_.GD.N0023.N0262.d021911
#print axioms _root_.GD.N0023.N0262.d021913
#print axioms _root_.GD.N0023.N0262.d021914
#print axioms _root_.GD.N0023.N0262.d021915
#print axioms _root_.GD.N0023.N0262.d021916
#print axioms _root_.GD.N0023.N0262.d021917
#print axioms _root_.GD.N0023.N0262.d021918
#print axioms _root_.GD.N0023.N0262.d021919
#print axioms _root_.GD.N0023.N0262.d021920
