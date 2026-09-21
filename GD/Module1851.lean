import GD.Module1357
import GD.Module1834
import GD.Module0528
import GD.Module1850

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0023.N0259

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0046.N0305
open _root_.GD.N0034.N0289
open _root_.GD.N0024
open _root_.GD.N0022 _root_.GD.N0022.N0256 _root_.GD.N0022.N0255
open _root_.GD.N0023.N0262

local instance : DecidableEq _root_.GD.N0232.N0720.N1080.d014168 := Classical.decEq _

theorem d030405 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (V : ℝ)
    (hcap : ∀ t, _root_.GD.N0024.N0277.d007882
      (_root_.GD.N0023.N0261.d021897 m n (by omega) (by omega)) g t ≤ V)
    (hbaseline : ∀ t, _root_.GD.N0024.N0277.d007882
      (_root_.GD.N0023.N0261.d021897 m n (by omega) (by omega)) g t ≤ _root_.GD.N0023.N0258.d021868 m n t)
    (hminimax : ∀ f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable f →
      (∀ z, f z ∈ Icc (0 : ℝ) 1) →
      ∀ ε : ℝ, 0 < ε → ∃ t, V - ε < _root_.GD.N0024.N0277.d007882
        (_root_.GD.N0023.N0261.d021897 m n (by omega) (by omega)) f t) : False := by
  have hQ : ∀ t : _root_.GD.N0024.N0277.d007878,
      _root_.GD.N0023.N0261.d021897 m n (by omega) (by omega) t ≪
        _root_.GD.N0023.N0261.d021897 m n (by omega) (by omega) _root_.GD.N0024.N0276.d007902 := by
    intro t
    exact _root_.GD.N0232.N0720.N1436.d013292
      (by omega : 2 ≤ m) (by omega : 2 ≤ n) t.2.1 t.2.2
      _root_.GD.N0024.N0276.d007902.2.1 _root_.GD.N0024.N0276.d007902.2.2
  have hV := _root_.GD.N0024.N0276.d007903
    (_root_.GD.N0023.N0261.d021897 m n (by omega) (by omega)) hQ g hg hb V hcap
  obtain ⟨d, h, hd, hdhalf, hh, htail⟩ := _root_.GD.N0023.N0258.d021879 m n hm hn V hV
  exact _root_.GD.N0023.N0261.d021904 m n (by omega) (by omega)
    g hg hb d V h hd hdhalf hh hcap
    (fun t ht => (hbaseline t).trans (htail t ht)) hminimax



theorem d030406 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    _root_.GD.N0046.N0305.d030202 m n (by omega) (by omega) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hK
  let v : ℝ := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v :=
    (ENNReal.ofReal_toReal (_root_.GD.N0023.N0262.d021919 m n hm hn)).symm
  obtain ⟨g, hg, hb, hbound⟩ := _root_.GD.N0024.N0270.d030252
    m n (by omega) (by omega) v hv hvalue hK
  have hcap := _root_.GD.N0023.N0262.d021914 m n (by omega) (by omega)
    g hg hb v hv (fun θ => (hbound θ).1)
  have hbase := _root_.GD.N0023.N0262.d021920 m n (by omega) (by omega)
    g hg hb (fun θ => (hbound θ).2)
  have hnonneg : 0 ≤ _root_.GD.N0024.N0277.d007882
      (_root_.GD.N0023.N0261.d021897 m n (by omega) (by omega)) g _root_.GD.N0024.N0276.d007902 :=
    div_nonneg (integral_nonneg fun _ => sq_nonneg _)
      (_root_.GD.N0024.N0277.d007880 _root_.GD.N0024.N0276.d007902).le
  have hvpos : 0 < v := by linarith [hcap _root_.GD.N0024.N0276.d007902]
  exact _root_.GD.N0023.N0259.d030405 m n hm hn g hg hb (v - 1) hcap hbase
    (_root_.GD.N0023.N0262.d021915 m n (by omega) (by omega) v hvalue hvpos)

theorem d030407 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    _root_.GD.N0024.N0283.d030364 m n = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rw [_root_.GD.N0024.N0283.d030366 m n (by omega) (by omega),
    _root_.GD.N0023.N0259.d030406 m n hm hn]
  simp

theorem d030408 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n)
    (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hf : Measurable f) :
    ∃ θ : _root_.GD.N0232.N0720.N1080.d014168,
      min (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0024.N0283.d030361 m n))
        (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ)) < _root_.GD.N0232.N0720.N1080.d014197 m n θ f := by
  by_contra hnot
  push Not at hnot
  have hmem : f ∈ _root_.GD.N0024.N0283.d030364 m n := ⟨hf, hnot⟩
  rw [_root_.GD.N0023.N0259.d030407 m n hm hn] at hmem
  exact hmem

theorem d030409 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (ε : ℝ), 0 < ε ∧
      ∀ f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable f →
        ∃ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F,
          ENNReal.ofReal (_root_.GD.N0034.N0289.d030220 m n (by omega) (by omega) θ +
            ε * _root_.GD.N0232.N0720.N1257.d015508 m n θ) < _root_.GD.N0232.N0720.N1080.d014197 m n θ f :=
  _root_.GD.N0022.N0256.d030390 m n (by omega) (by omega)
    (_root_.GD.N0023.N0259.d030406 m n hm hn)

theorem d030410 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n < _root_.GD.N0022.N0255.d030394 m n :=
  (_root_.GD.N0022.N0255.d030398 m n (by omega) (by omega)).mp
    (_root_.GD.N0023.N0259.d030406 m n hm hn)

theorem d030411 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    _root_.GD.N0022.N0255.d030394 m n ≤ ENNReal.ofReal (1 + _root_.GD.N0023.N0258.d021869 m n) := by
  apply (_root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0022.N0255.d030400 m n)).trans
  apply iSup_le
  intro θ
  rw [_root_.GD.N0023.N0262.d021917 m n (by omega) (by omega)]
  exact ENNReal.ofReal_le_ofReal (add_le_add le_rfl
    (_root_.GD.N0023.N0258.d021873 m n hm hn _))

theorem d030412 (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    0 < (_root_.GD.N0022.N0255.d030394 m n).toReal - (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal := by
  apply sub_pos.mpr
  apply (ENNReal.toReal_lt_toReal (_root_.GD.N0023.N0262.d021919 m n hm hn)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0023.N0259.d030411 m n hm hn))).mpr
  exact _root_.GD.N0023.N0259.d030410 m n hm hn

end
end GD.N0023.N0259

#print axioms _root_.GD.N0023.N0259.d030405
#print axioms _root_.GD.N0023.N0259.d030406
#print axioms _root_.GD.N0023.N0259.d030407
#print axioms _root_.GD.N0023.N0259.d030408
#print axioms _root_.GD.N0023.N0259.d030409
#print axioms _root_.GD.N0023.N0259.d030410
#print axioms _root_.GD.N0023.N0259.d030411
#print axioms _root_.GD.N0023.N0259.d030412
