import GD.Module0525
import GD.Module1234
import GD.Module1236
import GD.Module1081

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0024.N0275

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1396
open _root_.GD.N0107

def d022892 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0024.N0277.d007878 :=
  ⟨_root_.GD.N0107.d009046 6 6 θ.scale₁ θ.scale₂,
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) θ.scale₁_pos θ.scale₂_pos,
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) θ.scale₁_pos θ.scale₂_pos⟩

def d022893 (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ := _root_.GD.N0107.d009045 6 6 θ.scale₁ θ.scale₂

theorem d022894 (θ : _root_.GD.N0232.N0720.N1080.d014168) : 0 < _root_.GD.N0024.N0275.d022893 θ :=
  _root_.GD.N0107.d009049 (by norm_num) (by norm_num) θ.scale₁_pos θ.scale₂_pos

theorem d022895 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1257.d015508 6 6 θ = _root_.GD.N0024.N0275.d022893 θ * _root_.GD.N0024.N0277.d007879 (_root_.GD.N0024.N0275.d022892 θ) := by
  have hx : θ.scale₁ ^ 2 ≠ 0 := (sq_pos_of_pos θ.scale₁_pos).ne'
  have hy : θ.scale₂ ^ 2 ≠ 0 := (sq_pos_of_pos θ.scale₂_pos).ne'
  have hs : θ.scale₁ ^ 2 + θ.scale₂ ^ 2 ≠ 0 :=
    (add_pos (sq_pos_of_pos θ.scale₁_pos) (sq_pos_of_pos θ.scale₂_pos)).ne'
  unfold _root_.GD.N0232.N0720.N1257.d015508 _root_.GD.N0024.N0275.d022893 _root_.GD.N0024.N0277.d007879 _root_.GD.N0024.N0275.d022892
    _root_.GD.N0107.d009046 _root_.GD.N0107.d009045 _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
  norm_num
  field_simp [θ.scale₁_pos.ne', θ.scale₂_pos.ne', hx, hy, hs]
  ring

theorem d022896 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 6 6 θ (_root_.GD.N0232.N0720.N1425.d014719 6 6 g) =
      ENNReal.ofReal (_root_.GD.N0024.N0275.d022893 θ *
        (_root_.GD.N0024.N0277.d007879 (_root_.GD.N0024.N0275.d022892 θ) +
          _root_.GD.N0024.N0277.d007881 (_root_.GD.N0232.N0720.N1441.d013678 6 6 (_root_.GD.N0024.N0275.d022892 θ)) g (_root_.GD.N0024.N0275.d022892 θ).val)) := by
  rw [_root_.GD.N0232.N0720.N1335.d020089
    6 6 (by norm_num) (by norm_num) θ hg hb]
  have horacle := _root_.GD.N0232.N0720.N1396.d014795 6 6 (by norm_num) (by norm_num) θ
  unfold _root_.GD.N0232.N0720.N1396.d014778 at horacle
  rw [horacle]
  congr 1
  unfold _root_.GD.N0024.N0275.d022893 _root_.GD.N0024.N0275.d022892 _root_.GD.N0024.N0277.d007879 _root_.GD.N0024.N0277.d007881
    _root_.GD.N0232.N0720.N1441.d013678 _root_.GD.N0232.N0720.N1335.d020087
  ring

theorem d022897 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 6 6 θ (_root_.GD.N0232.N0720.N1425.d014719 6 6 g) =
      ENNReal.ofReal (1 + _root_.GD.N0024.N0277.d007882 (_root_.GD.N0232.N0720.N1441.d013678 6 6) g (_root_.GD.N0024.N0275.d022892 θ)) := by
  have hS := _root_.GD.N0024.N0275.d022894 θ
  have ht := _root_.GD.N0024.N0277.d007880 (_root_.GD.N0024.N0275.d022892 θ)
  unfold _root_.GD.N0232.N0720.N1256.d015547
  rw [_root_.GD.N0024.N0275.d022896 g hg hb, _root_.GD.N0024.N0275.d022895, ← ENNReal.ofReal_div_of_pos (mul_pos hS ht)]
  congr 1
  unfold _root_.GD.N0024.N0277.d007882
  field_simp

def d022898 (t : _root_.GD.N0024.N0277.d007878) : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1332.d020110 6 6 (by norm_num) (by norm_num) t

theorem d022899 (t : _root_.GD.N0024.N0277.d007878) :
    _root_.GD.N0024.N0275.d022892 (_root_.GD.N0024.N0275.d022898 t) = t := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0720.N1332.d020112
    6 6 (by norm_num) (by norm_num) t

theorem d022900 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (v : ℝ) (hv : 0 ≤ v)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 6 6 θ (_root_.GD.N0232.N0720.N1425.d014719 6 6 g) ≤
      ENNReal.ofReal (v * _root_.GD.N0232.N0720.N1257.d015508 6 6 θ)) :
    ∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0232.N0720.N1441.d013678 6 6) g t ≤ v - 1 := by
  intro t
  have h := (_root_.GD.N0232.N0720.N1256.d015553 6 6 (by norm_num) v hv (_root_.GD.N0024.N0275.d022898 t)
    (_root_.GD.N0232.N0720.N1425.d014719 6 6 g)).mpr (hcap (_root_.GD.N0024.N0275.d022898 t))
  rw [_root_.GD.N0024.N0275.d022897 g hg hb, _root_.GD.N0024.N0275.d022899] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff hv).mp h
  linarith

theorem d022901 (v : ℝ)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 6 6 = ENNReal.ofReal v) (hv : 0 < v)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ t, (v - 1) - ε < _root_.GD.N0024.N0277.d007882 (_root_.GD.N0232.N0720.N1441.d013678 6 6) g t := by
  by_contra hnot
  push Not at hnot
  have hbound : _root_.GD.N0232.N0720.N1256.d015548 6 6 (_root_.GD.N0232.N0720.N1425.d014719 6 6 g) ≤
      ENNReal.ofReal (v - ε) := by
    apply iSup_le
    intro θ
    rw [_root_.GD.N0024.N0275.d022897 g hg hb]
    exact ENNReal.ofReal_le_ofReal (by linarith [hnot (_root_.GD.N0024.N0275.d022892 θ)])
  have hmin := _root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0720.N1256.d015547 6 6) (S := _root_.GD.N0232.N0720.N1256.d015545 6 6)
    (_root_.GD.N0232.N0720.N1398.d019599 6 6 hg)
  change _root_.GD.N0232.N0720.N1256.d015549 6 6 ≤ _root_.GD.N0232.N0720.N1256.d015548 6 6 (_root_.GD.N0232.N0720.N1425.d014719 6 6 g) at hmin
  rw [hvalue] at hmin
  have hlt : ENNReal.ofReal (v - ε) < ENNReal.ofReal v :=
    (ENNReal.ofReal_lt_ofReal_iff hv).mpr (by linarith)
  exact (not_lt.mpr (hmin.trans hbound)) hlt

end
end GD.N0024.N0275

#print axioms _root_.GD.N0024.N0275.d022895
#print axioms _root_.GD.N0024.N0275.d022896
#print axioms _root_.GD.N0024.N0275.d022897
#print axioms _root_.GD.N0024.N0275.d022899
#print axioms _root_.GD.N0024.N0275.d022900
#print axioms _root_.GD.N0024.N0275.d022901
