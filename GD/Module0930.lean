import Mathlib.Analysis.Convex.Function
import GD.Module0064
import GD.Module0095
import GD.Module0929

















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1065

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1075
open _root_.GD.N0232.N0720.N1076
open _root_.GD.N0230.N0566
open _root_.GD.N0230.N0567
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0595
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0703
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn





theorem d014553 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta) := by
  refine ⟨_root_.GD.N0232.N0720.N1025.d014312 m n hm hn, ?_⟩
  intro p hp q hq a b ha hb hab
  have hcomboMem : a • p + b • q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014312 m n hm hn hp hq ha hb hab
  let p' := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p
  let q' := (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm q
  have hpStrong : p' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn p).1 hp
  have hqStrong : q' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn q).1 hq
  have hcomboStrong : a • p' + b • q' ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0232.N0720.N1080.d014189 m n hm hn hpStrong hqStrong ha hb hab
  have hraw := _root_.GD.N0230.N0602.d000121
    (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
    theta.location p' q' ha hb hab
  have hpFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta p' ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hpStrong theta)
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
    exact ENNReal.ofReal_ne_top
  have hqFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta q' ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hqStrong theta)
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
    exact ENNReal.ofReal_ne_top
  have hcomboFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta (a • p' + b • q') ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hcomboStrong theta)
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
    exact ENNReal.ofReal_ne_top
  have hrawReal :
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta (a • p' + b • q')).toReal ≤
        a * (_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal +
          b * (_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal := by
    have htoReal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpFinite,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqFinite⟩)
      hraw
    rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpFinite)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqFinite),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at htoReal
    exact htoReal
  have hcapReal : 0 < (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal :=
    ENNReal.toReal_pos
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta)
  simp only [_root_.GD.N0232.N0720.N1066.d014327, hp, hq, hcomboMem, dite_true,
    _root_.GD.N0232.N0720.N1066.d014324, _root_.GD.N0232.N0720.N1025.d014305, ENNReal.toReal_div]
  change
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm (a • p + b • q))).toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal ≤
      a • ((_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal) +
        b • ((_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal)
  rw [map_add, map_smul, map_smul]
  change
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta (a • p' + b • q')).toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal ≤ _
  calc
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta (a • p' + b • q')).toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal ≤
        (a * (_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal +
          b * (_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal) /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal :=
      div_le_div_of_nonneg_right hrawReal hcapReal.le
    _ = a • ((_root_.GD.N0232.N0720.N1080.d014182 m n theta p').toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal) +
        b • ((_root_.GD.N0232.N0720.N1080.d014182 m n theta q').toReal /
          (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal) := by
      simp only [smul_eq_mul]
      ring



theorem d014554 :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn) := by
  letI : Nonempty _root_.GD.N0232.N0720.N1080.d014168 := ⟨_root_.GD.N0232.N0720.N1080.d014169⟩
  refine ⟨_root_.GD.N0232.N0720.N1025.d014312 m n hm hn, ?_⟩
  intro p hp q hq a b ha hb hab
  unfold _root_.GD.N0232.N0720.N1066.d014332 _root_.GD.N0230.N0567.d001636
  apply ciSup_le
  intro theta
  calc
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (a • p + b • q) ≤
        a • _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p +
          b • _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q :=
      (_root_.GD.N0232.N0720.N1065.d014553 m n hm hn theta).2
        hp hq ha hb hab
    _ ≤ a • (⨆ eta, _root_.GD.N0232.N0720.N1066.d014327 m n hm hn eta p) +
        b • (⨆ eta, _root_.GD.N0232.N0720.N1066.d014327 m n hm hn eta q) := by
      exact add_le_add
        (smul_le_smul_of_nonneg_left
          (le_ciSup (_root_.GD.N0232.N0720.N1066.d014344
            m n hm hn p) theta) ha)
        (smul_le_smul_of_nonneg_left
          (le_ciSup (_root_.GD.N0232.N0720.N1066.d014344
            m n hm hn q) theta) hb)



theorem d014555
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta) := by
  refine ⟨_root_.GD.N0232.N0720.N1025.d014312 m n hm hn, ?_⟩
  intro p hp q hq a b ha hb hab
  have hbase := (_root_.GD.N0232.N0720.N1065.d014553 m n hm hn theta).2
    hp hq ha hb hab
  have hscale : 0 ≤ _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta :=
    (_root_.GD.N0232.N0720.N1075.d014502
      m n hm hn hepsilon theta).le
  unfold _root_.GD.N0232.N0720.N1075.d014503
  calc
    (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (a • p + b • q) -
          _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
        _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta ≤
      (a • _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p +
          b • _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q -
            _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
        _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta :=
      div_le_div_of_nonneg_right
        (sub_le_sub_right hbase _) hscale
    _ = a • ((_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p -
          _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
        _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta) +
      b • ((_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q -
          _root_.GD.N0232.N0720.N1075.d014487 m n theta) /
        _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta) := by
      simp only [smul_eq_mul]
      linear_combination
        (_root_.GD.N0232.N0720.N1075.d014487 m n theta /
          _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta) * hab



theorem d014556
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1076.d014520
        m n hm hn band epsilon hepsilon) := by
  classical
  refine ⟨_root_.GD.N0232.N0720.N1025.d014312 m n hm hn, ?_⟩
  intro p hp q hq a b ha hb hab
  cases isEmpty_or_nonempty {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} with
  | inl hempty =>
      letI := hempty
      unfold _root_.GD.N0232.N0720.N1076.d014520 _root_.GD.N0230.N0567.d001636
      simp
  | inr hnonempty =>
      letI := hnonempty
      unfold _root_.GD.N0232.N0720.N1076.d014520 _root_.GD.N0230.N0567.d001636
      apply ciSup_le
      intro theta
      have hpUpper :
          _root_.GD.N0232.N0720.N1075.d014503
              m n hm hn epsilon theta.1 p ≤
            ⨆ eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // band eta},
              _root_.GD.N0232.N0720.N1075.d014503
                m n hm hn epsilon eta.1 p :=
        (_root_.GD.N0232.N0720.N1076.d014523
          m n hm hn band hepsilon hp).1 ⟨theta, rfl⟩
      have hqUpper :
          _root_.GD.N0232.N0720.N1075.d014503
              m n hm hn epsilon theta.1 q ≤
            ⨆ eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // band eta},
              _root_.GD.N0232.N0720.N1075.d014503
                m n hm hn epsilon eta.1 q :=
        (_root_.GD.N0232.N0720.N1076.d014523
          m n hm hn band hepsilon hq).1 ⟨theta, rfl⟩
      calc
        _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta.1
            (a • p + b • q) ≤
          a • _root_.GD.N0232.N0720.N1075.d014503
              m n hm hn epsilon theta.1 p +
            b • _root_.GD.N0232.N0720.N1075.d014503
              m n hm hn epsilon theta.1 q :=
          (_root_.GD.N0232.N0720.N1065.d014555
            m n hm hn hepsilon theta.1).2 hp hq ha hb hab
        _ ≤
          a • (⨆ eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // band eta},
              _root_.GD.N0232.N0720.N1075.d014503
                m n hm hn epsilon eta.1 p) +
            b • (⨆ eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // band eta},
              _root_.GD.N0232.N0720.N1075.d014503
                m n hm hn epsilon eta.1 q) := by
          exact add_le_add
            (smul_le_smul_of_nonneg_left hpUpper ha)
            (smul_le_smul_of_nonneg_left hqUpper hb)


theorem d014557 (j : ℕ) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1076.d014539 m n hm hn j) := by
  exact _root_.GD.N0232.N0720.N1065.d014556
    m n hm hn (_root_.GD.N0232.N0720.N1076.d014533 m n j) (_root_.GD.N0232.N0720.N1076.d014532 j)


theorem d014558 (j : ℕ) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1076.d014540 m n hm hn j) := by
  exact _root_.GD.N0232.N0720.N1065.d014556
    m n hm hn (_root_.GD.N0232.N0720.N1076.d014534 m n j) (_root_.GD.N0232.N0720.N1076.d014532 j)







def d014559 : ℕ → _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ
  | 0 => _root_.GD.N0232.N0720.N1066.d014332 m n hm hn
  | k + 1 =>
      if k % 2 = 0 then
        _root_.GD.N0232.N0720.N1076.d014539 m n hm hn (k / 2)
      else
        _root_.GD.N0232.N0720.N1076.d014540 m n hm hn (k / 2)

@[simp] theorem d014560 :
    _root_.GD.N0232.N0720.N1065.d014559 m n hm hn 0 =
      _root_.GD.N0232.N0720.N1066.d014332 m n hm hn := rfl

theorem d014561
    (k : ℕ) (hk : k % 2 = 0) :
    _root_.GD.N0232.N0720.N1065.d014559 m n hm hn (k + 1) =
      _root_.GD.N0232.N0720.N1076.d014539 m n hm hn (k / 2) := by
  simp [_root_.GD.N0232.N0720.N1065.d014559, hk]

theorem d014562
    (k : ℕ) (hk : k % 2 ≠ 0) :
    _root_.GD.N0232.N0720.N1065.d014559 m n hm hn (k + 1) =
      _root_.GD.N0232.N0720.N1076.d014540 m n hm hn (k / 2) := by
  simp [_root_.GD.N0232.N0720.N1065.d014559, hk]



theorem d014563 (i : ℕ) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn i)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  cases i with
  | zero =>
      exact _root_.GD.N0232.N0720.N1066.d014336 m n hm hn
  | succ k =>
      simp only [_root_.GD.N0232.N0720.N1065.d014559]
      split
      · exact _root_.GD.N0232.N0720.N1076.d014543
          m n hm hn (k / 2)
      · exact _root_.GD.N0232.N0720.N1076.d014544
          m n hm hn (k / 2)


theorem d014564 (i : ℕ) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn i) := by
  cases i with
  | zero => exact _root_.GD.N0232.N0720.N1065.d014554 m n hm hn
  | succ k =>
      simp only [_root_.GD.N0232.N0720.N1065.d014559]
      split
      · exact _root_.GD.N0232.N0720.N1065.d014557
          m n hm hn (k / 2)
      · exact _root_.GD.N0232.N0720.N1065.d014558
          m n hm hn (k / 2)



theorem d014565 :
    _root_.GD.N0230.N0596.d000732 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn) := by
  intro i e d hed
  cases i with
  | zero =>
      exact _root_.GD.N0232.N0720.N1066.d014347 m n hm hn hed
  | succ k =>
      simp only [_root_.GD.N0232.N0720.N1065.d014559]
      split
      · exact _root_.GD.N0232.N0720.N1076.d014547
          m n hm hn (k / 2) hed
      · exact _root_.GD.N0232.N0720.N1076.d014548
          m n hm hn (k / 2) hed



theorem d014566
    (i : ℕ) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1065.d014559 m n hm hn i
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1065.d014559 m n hm hn i p.1 := by
  cases i with
  | zero =>
      exact _root_.GD.N0232.N0720.N1066.d014350 m n hm hn g p
  | succ k =>
      simp only [_root_.GD.N0232.N0720.N1065.d014559]
      split
      · exact _root_.GD.N0232.N0720.N1076.d014551
          m n hm hn (k / 2) g p
      · exact _root_.GD.N0232.N0720.N1076.d014552
          m n hm hn (k / 2) g p


abbrev d014567 (i : ℕ) : Set (_root_.GD.N0232.N0720.N1025.d014303 m n) :=
  _root_.GD.N0230.N0566.d000753 (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) i



abbrev d014568 : Set (_root_.GD.N0232.N0720.N1025.d014303 m n) :=
  _root_.GD.N0230.N0595.d000761 (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)

theorem d014569
    (p : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    p ∈ _root_.GD.N0232.N0720.N1065.d014568 m n hm hn ↔
      ∀ i, p ∈ _root_.GD.N0232.N0720.N1065.d014567 m n hm hn i := by
  exact _root_.GD.N0230.N0595.d000762
    (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p





theorem d014570 :
    ∀ i, (_root_.GD.N0232.N0720.N1065.d014567 m n hm hn i).Nonempty ∧
      IsCompact (_root_.GD.N0232.N0720.N1065.d014567 m n hm hn i) ∧
      IsClosed (_root_.GD.N0232.N0720.N1065.d014567 m n hm hn i) := by
  apply _root_.GD.N0230.N0583.d000748
    (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (_root_.GD.N0232.N0720.N1065.d014567 m n hm hn)
    (_root_.GD.N0230.N0566.d000756
      (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn))
    (_root_.GD.N0232.N0720.N1025.d014310 m n hm hn)
    (_root_.GD.N0232.N0720.N1025.d014311 m n hm hn)
  intro i
  exact (_root_.GD.N0232.N0720.N1065.d014563
    m n hm hn i).mono
      (_root_.GD.N0230.N0595.d000759
        (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
        (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) i)



theorem d014571 :
    ∃ p, p ∈ _root_.GD.N0232.N0720.N1065.d014568 m n hm hn ∧
      _root_.GD.N0230.N0596.d000730 (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
        (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p := by
  obtain ⟨p, hp, hlex⟩ :=
    _root_.GD.N0230.N0583.d000750
      (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014567 m n hm hn)
      (_root_.GD.N0230.N0566.d000756
        (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
        (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn))
      (_root_.GD.N0232.N0720.N1025.d014310 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014311 m n hm hn)
      (fun i ↦
        (_root_.GD.N0232.N0720.N1065.d014563
          m n hm hn i).mono
            (_root_.GD.N0230.N0595.d000759
              (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
              (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) i))
  exact ⟨p, (_root_.GD.N0232.N0720.N1065.d014569
    m n hm hn p).2 hp, hlex⟩


theorem d014572 :
    (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn).Nonempty := by
  obtain ⟨p, hp, _⟩ :=
    _root_.GD.N0232.N0720.N1065.d014571 m n hm hn
  exact ⟨p, hp⟩


theorem d014573 :
    IsCompact (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn) := by
  have hclosed : IsClosed (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn) :=
    isClosed_iInter (fun i ↦
      (_root_.GD.N0232.N0720.N1065.d014570
        m n hm hn i).2.2)
  apply (_root_.GD.N0232.N0720.N1025.d014311 m n hm hn).of_isClosed_subset hclosed
  intro p hp
  have hp0 := (_root_.GD.N0232.N0720.N1065.d014569
    m n hm hn p).1 hp 0
  simpa using hp0


theorem d014574 :
    Convex ℝ (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn) := by
  exact _root_.GD.N0230.N0595.d000763
    (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (_root_.GD.N0232.N0720.N1065.d014564 m n hm hn)


theorem d014575 :
    (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn).Nonempty ∧
      IsCompact (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn) ∧
      Convex ℝ (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn) := by
  exact ⟨_root_.GD.N0232.N0720.N1065.d014572 m n hm hn,
    _root_.GD.N0232.N0720.N1065.d014573 m n hm hn,
    _root_.GD.N0232.N0720.N1065.d014574 m n hm hn⟩





def d014576
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    _root_.GD.N0232.N0720.N1025.d014303 m n := by
  classical
  exact if hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn then
    (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g ⟨d, hd⟩).1
  else d

@[simp] theorem d014577
    (g : _root_.GD.N0232.N0720.N1025.d014301) {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g d =
      (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g ⟨d, hd⟩).1 := by
  simp [_root_.GD.N0232.N0720.N1065.d014576, hd]

theorem d014578
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    MapsTo (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  intro d hd
  rw [_root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hd]
  exact (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g ⟨d, hd⟩).2

theorem d014579
    (i : ℕ) (g : _root_.GD.N0232.N0720.N1025.d014301)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1065.d014559 m n hm hn i
        (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g d) =
      _root_.GD.N0232.N0720.N1065.d014559 m n hm hn i d := by
  rw [_root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hd]
  exact _root_.GD.N0232.N0720.N1065.d014566
    m n hm hn i g ⟨d, hd⟩



theorem d014580
    (g : _root_.GD.N0232.N0720.N1025.d014301) (i : ℕ) :
    MapsTo (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
      (_root_.GD.N0232.N0720.N1065.d014567 m n hm hn i)
      (_root_.GD.N0232.N0720.N1065.d014567 m n hm hn i) := by
  exact _root_.GD.N0230.N0595.d000764
    (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
    (_root_.GD.N0232.N0720.N1065.d014578 m n hm hn g)
    (fun i d hd ↦
      _root_.GD.N0232.N0720.N1065.d014579
        m n hm hn i g hd) i



theorem d014581
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    MapsTo (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
      (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn) := by
  exact _root_.GD.N0230.N0595.d000765
    (_root_.GD.N0232.N0720.N1065.d014559 m n hm hn)
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
    (_root_.GD.N0232.N0720.N1065.d014578 m n hm hn g)
    (fun i d hd ↦
      _root_.GD.N0232.N0720.N1065.d014579
        m n hm hn i g hd)





theorem d014582
    (p q : _root_.GD.N0232.N0720.N1025.d014302 m n) (a b : ℝ) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦
        a • _root_.GD.N0232.N0720.N1214.d014265 m n p omega +
          b • _root_.GD.N0232.N0720.N1214.d014265 m n q omega := by
  filter_upwards [
    _root_.GD.N0232.N0720.N1214.d014267 m n (a • p + b • q),
    _root_.GD.N0232.N0720.N1214.d014267 m n p,
    _root_.GD.N0232.N0720.N1214.d014267 m n q,
    Lp.coeFn_add (a • p) (b • q),
    Lp.coeFn_smul a p,
    Lp.coeFn_smul b q] with
      omega hcombo hp hq hadd hsmulP hsmulQ
  rw [hcombo]
  simp only [hadd, hsmulP, hsmulQ, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, hp, hq]




theorem d014583
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p q : _root_.GD.N0232.N0720.N1025.d014302 m n)
    {a b : ℝ} (hab : a + b = 1) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q))
      =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦
          a • _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) omega +
            b • _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n q) omega := by
  let eta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  have hcomboReference := _root_.GD.N0232.N0720.N1065.d014582
    m n hm hn p q a b
  have hcomboEta :
      _root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n eta]
        fun omega ↦
          a • _root_.GD.N0232.N0720.N1214.d014265 m n p omega +
            b • _root_.GD.N0232.N0720.N1214.d014265 m n q omega :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n eta).ae_eq hcomboReference
  have hqmp : Measure.QuasiMeasurePreserving
      (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n eta) := by
    refine ⟨?_, ?_⟩
    · simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
        (_root_.GD.N0107.d009026
          m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239)
    · have hmap :
          (_root_.GD.N0232.N0720.N1080.d014172 m n).map (fun omega ↦ g⁻¹ • omega) =
            _root_.GD.N0232.N0720.N1080.d014171 m n eta := by
          simpa only [_root_.GD.N0232.N0720.N1080.d014172, eta, _root_.GD.N0232.N0720.N1214.d014259] using
            (_root_.GD.N0232.N0720.N1215.d014282 m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
      exact hmap ▸ Measure.AbsolutelyContinuous.rfl
  have hpull := hqmp.ae_eq_comp hcomboEta
  filter_upwards [hpull] with omega homega
  have homega' :
      _root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q) (g⁻¹ • omega) =
        a • _root_.GD.N0232.N0720.N1214.d014265 m n p (g⁻¹ • omega) +
          b • _root_.GD.N0232.N0720.N1214.d014265 m n q (g⁻¹ • omega) := by
    simpa only [Function.comp_apply] using homega
  unfold _root_.GD.N0232.N0720.N1214.d014261
  rw [homega']
  simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244, smul_eq_mul]
  calc
    g.shift + g.d009239 *
        (a * _root_.GD.N0232.N0720.N1214.d014265 m n p (g⁻¹ • omega) +
          b * _root_.GD.N0232.N0720.N1214.d014265 m n q (g⁻¹ • omega)) =
      (a + b) * g.shift + g.d009239 *
        (a * _root_.GD.N0232.N0720.N1214.d014265 m n p (g⁻¹ • omega) +
          b * _root_.GD.N0232.N0720.N1214.d014265 m n q (g⁻¹ • omega)) := by rw [hab, one_mul]
    _ = a * (g.shift + g.d009239 *
          _root_.GD.N0232.N0720.N1214.d014265 m n p (g⁻¹ • omega)) +
        b * (g.shift + g.d009239 *
          _root_.GD.N0232.N0720.N1214.d014265 m n q (g⁻¹ • omega)) := by ring



theorem d014584
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    {p q : _root_.GD.N0232.N0720.N1025.d014302 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g (a • p + b • q)
        (_root_.GD.N0232.N0720.N1080.d014189 m n hm hn hp hq ha hb hab) =
      a • _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp +
        b • _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g q hq := by
  let hcombo : a • p + b • q ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0232.N0720.N1080.d014189 m n hm hn hp hq ha hb hab
  let fp := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)
  let fq := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n q)
  let fcombo := _root_.GD.N0232.N0720.N1214.d014261 m n g
    (_root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q))
  let hpLp : MemLp fp 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p hp
  let hqLp : MemLp fq 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g q hq
  let hcomboLp : MemLp fcombo 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g (a • p + b • q) hcombo
  let hsumLp : MemLp
      (fun omega ↦ a • fp omega + b • fq omega)
      2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (hpLp.const_smul a).add (hqLp.const_smul b)
  have hraw : fcombo =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦ a • fp omega + b • fq omega := by
    simpa only [fcombo, fp, fq] using
      _root_.GD.N0232.N0720.N1065.d014583 m n hm hn g p q hab
  change MemLp.toLp fcombo hcomboLp =
    a • MemLp.toLp fp hpLp + b • MemLp.toLp fq hqLp
  calc
    MemLp.toLp fcombo hcomboLp =
        MemLp.toLp
          (fun omega ↦ a • fp omega + b • fq omega) hsumLp :=
      MemLp.toLp_congr hcomboLp hsumLp hraw
    _ = MemLp.toLp (a • fp) (hpLp.const_smul a) +
          MemLp.toLp (b • fq) (hqLp.const_smul b) :=
      MemLp.toLp_add (hpLp.const_smul a) (hqLp.const_smul b)
    _ = a • MemLp.toLp fp hpLp +
          b • MemLp.toLp fq hqLp := by
      rw [MemLp.toLp_const_smul, MemLp.toLp_const_smul]



theorem d014585
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g
      ⟨a • p.1 + b • q.1,
        _root_.GD.N0232.N0720.N1025.d014312 m n hm hn p.2 q.2 ha hb hab⟩).1 =
      a • (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 +
        b • (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q).1 := by
  apply (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm.injective
  simp only [_root_.GD.N0232.N0720.N1025.d014317, _root_.GD.N0232.N0720.N1025.d014309,
    _root_.GD.N0232.N0720.N1025.d014308, Equiv.apply_symm_apply, map_add,
    map_smul]
  exact _root_.GD.N0232.N0720.N1065.d014584 m n hm hn g
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p).2
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2 ha hb hab



theorem d014586
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g (a • p + b • q) =
      a • _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g p +
        b • _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g q := by
  have hcombo := _root_.GD.N0232.N0720.N1025.d014312 m n hm hn hp hq ha hb hab
  rw [_root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hcombo,
    _root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hp,
    _root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hq]
  exact _root_.GD.N0232.N0720.N1065.d014585 m n hm hn g
    ⟨p, hp⟩ ⟨q, hq⟩ ha hb hab





theorem d014587
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n) (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp)
      =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
  let f := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)
  let hf : MemLp f 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p hp
  have hcanonical :
      _root_.GD.N0232.N0720.N1214.d014265 m n (MemLp.toLp f hf) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ MemLp.toLp f hf omega :=
    _root_.GD.N0232.N0720.N1214.d014267 m n (MemLp.toLp f hf)
  have htoLp :
      (fun omega ↦ MemLp.toLp f hf omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] f := by
    simpa [f] using hf.coeFn_toLp
  simpa [_root_.GD.N0232.N0720.N1215.d014289, f, hf] using hcanonical.trans htoLp



theorem d014588
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hde : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] e) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g e := by
  let eta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  have hdeEta : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n eta] e :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n eta).ae_eq hde
  have hqmp : Measure.QuasiMeasurePreserving
      (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n eta) := by
    refine ⟨?_, ?_⟩
    · simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
        (_root_.GD.N0107.d009026
          m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239)
    · have hmap :
          (_root_.GD.N0232.N0720.N1080.d014172 m n).map (fun omega ↦ g⁻¹ • omega) =
            _root_.GD.N0232.N0720.N1080.d014171 m n eta := by
          simpa only [_root_.GD.N0232.N0720.N1080.d014172, eta, _root_.GD.N0232.N0720.N1214.d014259] using
            (_root_.GD.N0232.N0720.N1215.d014282 m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
      exact hmap ▸ Measure.AbsolutelyContinuous.rfl
  have hpull := hqmp.ae_eq_comp hdeEta
  filter_upwards [hpull] with omega homega
  unfold _root_.GD.N0232.N0720.N1214.d014261
  apply congrArg (fun y : ℝ ↦ g • y)
  simpa only [Function.comp_apply] using homega



theorem d014589
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n) (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn 1 p hp = p := by
  unfold _root_.GD.N0232.N0720.N1215.d014289
  simpa using _root_.GD.N0232.N0720.N1214.d014269 m n p



theorem d014590
    (g h : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1025.d014302 m n) (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g
        (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn h p hp)
        (_root_.GD.N0232.N0720.N1215.d014297 m n hm hn h p hp) =
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn (g * h) p hp := by
  let ph := _root_.GD.N0232.N0720.N1215.d014289 m n hm hn h p hp
  let hph : ph ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0232.N0720.N1215.d014297 m n hm hn h p hp
  let lhsRaw := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n ph)
  let rhsRaw := _root_.GD.N0232.N0720.N1214.d014261 m n (g * h) (_root_.GD.N0232.N0720.N1214.d014265 m n p)
  let hlhs : MemLp lhsRaw 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g ph hph
  let hrhs : MemLp rhsRaw 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn (g * h) p hp
  have hfirst :
      lhsRaw =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n g
          (_root_.GD.N0232.N0720.N1214.d014261 m n h (_root_.GD.N0232.N0720.N1214.d014265 m n p)) := by
    exact _root_.GD.N0232.N0720.N1065.d014588 m n hm hn g
      (_root_.GD.N0232.N0720.N1065.d014587 m n hm hn h p hp)
  have hraw : lhsRaw =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] rhsRaw := by
    filter_upwards [hfirst] with omega homega
    rw [homega]
    exact congrFun (_root_.GD.N0232.N0720.N1214.d014264 m n g h (_root_.GD.N0232.N0720.N1214.d014265 m n p)) omega
  change MemLp.toLp lhsRaw hlhs = MemLp.toLp rhsRaw hrhs
  exact MemLp.toLp_congr hlhs hrhs hraw

@[simp] theorem d014591
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014298 m n hm hn 1 p = p := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0720.N1065.d014589 m n hm hn p.1 p.2

theorem d014592
    (g h : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn h p) =
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn (g * h) p := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0720.N1065.d014590 m n hm hn g h p.1 p.2

@[simp] theorem d014593
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1025.d014316 m n hm hn 1 p = p := by
  simp [_root_.GD.N0232.N0720.N1025.d014316, _root_.GD.N0232.N0720.N1065.d014591 m n hm hn]

theorem d014594
    (g h : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn h p) =
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn (g * h) p := by
  simp only [_root_.GD.N0232.N0720.N1025.d014316, Function.comp_apply,
    Equiv.symm_apply_apply]
  rw [_root_.GD.N0232.N0720.N1065.d014592]

theorem d014595
    {p : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1065.d014576 m n hm hn 1 p = p := by
  rw [_root_.GD.N0232.N0720.N1065.d014577 m n hm hn 1 hp]
  exact congrArg Subtype.val (_root_.GD.N0232.N0720.N1065.d014593 m n hm hn ⟨p, hp⟩)



theorem d014596
    (g h : _root_.GD.N0232.N0720.N1025.d014301)
    {p : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g
        (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn h p) =
      _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (g * h) p := by
  have hhp : _root_.GD.N0232.N0720.N1065.d014576 m n hm hn h p ∈
      _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1065.d014578 m n hm hn h hp
  rw [_root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hhp,
    _root_.GD.N0232.N0720.N1065.d014577 m n hm hn (g * h) hp]
  have hsubtype :
      (⟨_root_.GD.N0232.N0720.N1065.d014576 m n hm hn h p, hhp⟩ :
          _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) =
        _root_.GD.N0232.N0720.N1025.d014316 m n hm hn h ⟨p, hp⟩ := by
    apply Subtype.ext
    exact _root_.GD.N0232.N0720.N1065.d014577 m n hm hn h hp
  rw [hsubtype]
  exact congrArg Subtype.val (_root_.GD.N0232.N0720.N1065.d014594 m n hm hn g h ⟨p, hp⟩)




theorem d014597 :
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm ''
        _root_.GD.N0232.N0720.N1025.d014304 m n hm hn =
      _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
  ext d
  constructor
  · rintro ⟨w, ⟨e, he, rfl⟩, rfl⟩
    simpa using he
  · intro hd
    exact ⟨toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) d,
      ⟨d, hd, rfl⟩, by simp⟩



theorem d014598 :
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm ''
        _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ⊆
      Metric.closedBall 0 (_root_.GD.N0232.N0720.N1080.d014248 m n hm hn) := by
  rw [_root_.GD.N0232.N0720.N1065.d014597 m n hm hn]
  intro d hd
  simpa [Metric.mem_closedBall, dist_eq_norm] using
    _root_.GD.N0232.N0720.N1080.d014250 m n hm hn d hd



theorem d014599 :
    _root_.GD.N0230.N0709.d001221 (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  exact Metric.isBounded_closedBall.subset
    (_root_.GD.N0232.N0720.N1065.d014598 m n hm hn)

theorem d014600 :
    _root_.GD.N0232.N0720.N1065.d014568 m n hm hn ⊆
      _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := by
  intro p hp
  have hp0 := (_root_.GD.N0232.N0720.N1065.d014569
    m n hm hn p).1 hp 0
  simpa using hp0



theorem d014601 :
    _root_.GD.N0230.N0709.d001221
      (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn) := by
  exact _root_.GD.N0230.N0709.d001221.d001222
    (_root_.GD.N0232.N0720.N1065.d014599 m n hm hn)
    (_root_.GD.N0232.N0720.N1065.d014600 m n hm hn)


def d014602 (t : ℝ) : _root_.GD.N0232.N0720.N1025.d014301 where
  shift := t
  logScale := 0


def d014603 (s : ℝ) : _root_.GD.N0232.N0720.N1025.d014301 where
  shift := 0
  logScale := s

omit hm hn in
@[simp] theorem d014604 (s t : ℝ) :
    _root_.GD.N0232.N0720.N1065.d014602 (s + t) =
      _root_.GD.N0232.N0720.N1065.d014602 s * _root_.GD.N0232.N0720.N1065.d014602 t := by
  ext <;> simp [_root_.GD.N0232.N0720.N1065.d014602]

omit hm hn in
@[simp] theorem d014605 (s t : ℝ) :
    _root_.GD.N0232.N0720.N1065.d014603 (s + t) =
      _root_.GD.N0232.N0720.N1065.d014603 s * _root_.GD.N0232.N0720.N1065.d014603 t := by
  ext <;> simp [_root_.GD.N0232.N0720.N1065.d014603]

omit hm hn in


theorem d014606 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1065.d014602 g.shift * _root_.GD.N0232.N0720.N1065.d014603 g.logScale = g := by
  ext <;> simp [_root_.GD.N0232.N0720.N1065.d014602, _root_.GD.N0232.N0720.N1065.d014603]

omit hm hn in


theorem d014607 (t s : ℝ) :
    _root_.GD.N0232.N0720.N1065.d014602 t * _root_.GD.N0232.N0720.N1065.d014603 s =
      _root_.GD.N0232.N0720.N1065.d014603 s * _root_.GD.N0232.N0720.N1065.d014602 (Real.exp (-s) * t) := by
  ext
  · dsimp [_root_.GD.N0232.N0720.N1065.d014602, _root_.GD.N0232.N0720.N1065.d014603]
    rw [Real.exp_zero, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  · dsimp [_root_.GD.N0232.N0720.N1065.d014602, _root_.GD.N0232.N0720.N1065.d014603]
    ring

@[simp] theorem d014608
    (g : _root_.GD.N0232.N0720.N1025.d014301) {p : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∉ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g p = p := by
  simp [_root_.GD.N0232.N0720.N1065.d014576, hp]


theorem d014609 (s t : ℝ) :
    Function.Commute
      (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 s))
      (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)) := by
  intro p
  by_cases hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  · rw [_root_.GD.N0232.N0720.N1065.d014596 m n hm hn
        (_root_.GD.N0232.N0720.N1065.d014602 s) (_root_.GD.N0232.N0720.N1065.d014602 t) hp,
      _root_.GD.N0232.N0720.N1065.d014596 m n hm hn
        (_root_.GD.N0232.N0720.N1065.d014602 t) (_root_.GD.N0232.N0720.N1065.d014602 s) hp]
    congr 1
    rw [← _root_.GD.N0232.N0720.N1065.d014604, add_comm, _root_.GD.N0232.N0720.N1065.d014604]
  · simp [_root_.GD.N0232.N0720.N1065.d014608 m n hm hn, hp]


theorem d014610 (s t : ℝ) :
    Function.Commute
      (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s))
      (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 t)) := by
  intro p
  by_cases hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  · rw [_root_.GD.N0232.N0720.N1065.d014596 m n hm hn
        (_root_.GD.N0232.N0720.N1065.d014603 s) (_root_.GD.N0232.N0720.N1065.d014603 t) hp,
      _root_.GD.N0232.N0720.N1065.d014596 m n hm hn
        (_root_.GD.N0232.N0720.N1065.d014603 t) (_root_.GD.N0232.N0720.N1065.d014603 s) hp]
    congr 1
    rw [← _root_.GD.N0232.N0720.N1065.d014605, add_comm, _root_.GD.N0232.N0720.N1065.d014605]
  · simp [_root_.GD.N0232.N0720.N1065.d014608 m n hm hn, hp]



theorem d014611 :
    _root_.GD.N0230.N0703.d001147
      (fun s : ℝ ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s))
      (fun t : ℝ ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)) := by
  intro s t
  refine ⟨Real.exp (-s) * t, ?_⟩
  funext p
  by_cases hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  · change _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)
        (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s) p) =
      _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)
        (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn
          (_root_.GD.N0232.N0720.N1065.d014602 (Real.exp (-s) * t)) p)
    rw [_root_.GD.N0232.N0720.N1065.d014596 m n hm hn
        (_root_.GD.N0232.N0720.N1065.d014602 t) (_root_.GD.N0232.N0720.N1065.d014603 s) hp,
      _root_.GD.N0232.N0720.N1065.d014596 m n hm hn
        (_root_.GD.N0232.N0720.N1065.d014603 s)
        (_root_.GD.N0232.N0720.N1065.d014602 (Real.exp (-s) * t)) hp,
      _root_.GD.N0232.N0720.N1065.d014607]
  · simp [Function.comp_apply,
      _root_.GD.N0232.N0720.N1065.d014608 m n hm hn, hp]



theorem d014612
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0230.N0710.d001232
      (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
      (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn) := by
  intro p hp q hq a b ha hb hab
  exact _root_.GD.N0232.N0720.N1065.d014586 m n hm hn g
    (_root_.GD.N0232.N0720.N1065.d014600 m n hm hn hp)
    (_root_.GD.N0232.N0720.N1065.d014600 m n hm hn hq)
    ha hb hab







theorem d014613
    (hcontinuous : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      ContinuousOn (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
        (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn)) :
    ∃ p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      p.1 ∈ _root_.GD.N0232.N0720.N1065.d014568 m n hm hn ∧
      ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
        _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p := by
  let inner : ℝ → _root_.GD.N0232.N0720.N1025.d014303 m n → _root_.GD.N0232.N0720.N1025.d014303 m n :=
    fun t ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)
  let outer : ℝ → _root_.GD.N0232.N0720.N1025.d014303 m n → _root_.GD.N0232.N0720.N1025.d014303 m n :=
    fun s ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)
  obtain ⟨x, hx, hxinner, hxouter⟩ :=
    _root_.GD.N0230.N0710.d001248
      inner outer (_root_.GD.N0232.N0720.N1065.d014568 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014573 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014574 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014572 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014601 m n hm hn)
      (fun t ↦ _root_.GD.N0232.N0720.N1065.d014581
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t))
      (fun t ↦ hcontinuous (_root_.GD.N0232.N0720.N1065.d014602 t))
      (fun t ↦ _root_.GD.N0232.N0720.N1065.d014612
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t))
      (_root_.GD.N0232.N0720.N1065.d014609 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014611 m n hm hn)
      (fun s ↦ _root_.GD.N0232.N0720.N1065.d014581
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s))
      (fun s ↦ hcontinuous (_root_.GD.N0232.N0720.N1065.d014603 s))
      (fun s ↦ _root_.GD.N0232.N0720.N1065.d014612
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s))
      (_root_.GD.N0232.N0720.N1065.d014610 m n hm hn)
  have hxCap : x ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1065.d014600 m n hm hn hx
  refine ⟨⟨x, hxCap⟩, hx, ?_⟩
  intro g
  apply Subtype.ext
  have hfactor := _root_.GD.N0232.N0720.N1065.d014606 g
  have hmul := _root_.GD.N0232.N0720.N1065.d014596 m n hm hn
    (_root_.GD.N0232.N0720.N1065.d014602 g.shift) (_root_.GD.N0232.N0720.N1065.d014603 g.logScale) hxCap
  have hfixAmbient : _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g x = x := by
    rw [← hfactor, ← hmul]
    change inner g.shift (outer g.logScale x) = x
    rw [hxouter g.logScale, hxinner g.shift]
  exact (_root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hxCap).symm.trans
    hfixAmbient

end

end N1065
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1065.d014553
#print axioms _root_.GD.N0232.N0720.N1065.d014575
#print axioms _root_.GD.N0232.N0720.N1065.d014581
#print axioms _root_.GD.N0232.N0720.N1065.d014585
#print axioms _root_.GD.N0232.N0720.N1065.d014613
