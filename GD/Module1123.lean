import GD.Module0971
import GD.Module1118








































open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1148

noncomputable section

open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}



theorem d018027 : _root_.GD.N0232.N0720.N1482.d015130.shift = 0 := rfl

theorem d018028 : _root_.GD.N0232.N0720.N1482.d015131.shift = 1 := rfl

theorem d018029 : _root_.GD.N0232.N0720.N1482.d015130.d009239 = 2 := by
  show Real.exp (Real.log 2) = 2
  exact Real.exp_log (by norm_num)

theorem d018030 :
    _root_.GD.N0232.N0720.N1482.d015131.d009239 = 3 := by
  show Real.exp (Real.log 3) = 3
  exact Real.exp_log (by norm_num)


def d018031 : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := 2⁻¹
  scale₂ := 2⁻¹
  scale₁_pos := by norm_num
  scale₂_pos := by norm_num



def d018032 : _root_.GD.N0232.N0720.N1080.d014168 where
  location := -3⁻¹
  scale₁ := 3⁻¹
  scale₂ := 3⁻¹
  scale₁_pos := by norm_num
  scale₂_pos := by norm_num

theorem d018033 :
    _root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1148.d018031 =
      _root_.GD.N0232.N0720.N1080.d014169 := by
  apply _root_.GD.N0232.N0720.N1215.d014277
  · rw [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1148.d018027, _root_.GD.N0232.N0720.N1148.d018029]
    show 0 + 2 * (0 : ℝ) = 0
    norm_num
  · rw [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1148.d018029]
    show (2 : ℝ) * 2⁻¹ = 1
    norm_num
  · rw [_root_.GD.N0232.N0720.N1215.d014275, _root_.GD.N0232.N0720.N1148.d018029]
    show (2 : ℝ) * 2⁻¹ = 1
    norm_num

theorem d018034 :
    _root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131 _root_.GD.N0232.N0720.N1148.d018032 =
      _root_.GD.N0232.N0720.N1080.d014169 := by
  apply _root_.GD.N0232.N0720.N1215.d014277
  · rw [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1148.d018028,
      _root_.GD.N0232.N0720.N1148.d018030]
    show 1 + 3 * (-3⁻¹ : ℝ) = 0
    norm_num
  · rw [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1148.d018030]
    show (3 : ℝ) * 3⁻¹ = 1
    norm_num
  · rw [_root_.GD.N0232.N0720.N1215.d014275, _root_.GD.N0232.N0720.N1148.d018030]
    show (3 : ℝ) * 3⁻¹ = 1
    norm_num

theorem d018035 :
    _root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130⁻¹ _root_.GD.N0232.N0720.N1080.d014169 =
      _root_.GD.N0232.N0720.N1148.d018031 := by
  conv_lhs => rw [← _root_.GD.N0232.N0720.N1148.d018033]
  rw [_root_.GD.N0232.N0720.N1215.d014280]

theorem d018036 :
    _root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131⁻¹ _root_.GD.N0232.N0720.N1080.d014169 =
      _root_.GD.N0232.N0720.N1148.d018032 := by
  conv_lhs => rw [← _root_.GD.N0232.N0720.N1148.d018034]
  rw [_root_.GD.N0232.N0720.N1215.d014280]





theorem d018037
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
      ENNReal.ofReal
        ((_root_.GD.N0232.N0720.N1159.d014647 m n s g +
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) / g.d009239 ^ 2) := by
  set P := _root_.GD.N0232.N0720.N1159.d014633 m n s.value with hPdef
  have hPmem : P ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n P :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s P hPmem
  have hdil : (0 : ℝ) < g.d009239 ^ 2 := pow_pos g.d009240 2
  have hdefect :
      _root_.GD.N0232.N0720.N1159.d014647 m n s g =
        ‖_root_.GD.N0232.N0720.N1159.d014642 m n g P hP‖ ^ 2 - ‖P‖ ^ 2 := rfl
  have hchar :=
    _root_.GD.N0232.N0720.N1159.d014643 m n g
      (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P hP
  rw [_root_.GD.N0232.N0720.N1215.d014279] at hchar
  have href := _root_.GD.N0232.N0720.N1080.d014190 m n (_root_.GD.N0232.N0720.N1159.d014642 m n g P hP)
  simp only [zero_sub, norm_neg] at href
  have hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P ≠ ⊤ := hP _
  have hEq : ENNReal.ofReal (g.d009239 ^ 2) *
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P =
      ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014642 m n g P hP‖ ^ 2) := by
    rw [← hchar, href]
  have htoReal :
      g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P).toReal =
        ‖_root_.GD.N0232.N0720.N1159.d014642 m n g P hP‖ ^ 2 := by
    have hcast := congrArg ENNReal.toReal hEq
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hdil.le,
      ENNReal.toReal_ofReal (sq_nonneg _)] at hcast
  have hval :
      (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P).toReal =
        (_root_.GD.N0232.N0720.N1159.d014647 m n s g + ‖P‖ ^ 2) / g.d009239 ^ 2 := by
    rw [eq_div_iff hdil.ne', hdefect]
    linear_combination htoReal
  calc _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P
      = ENNReal.ofReal
          ((_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P).toReal) :=
        (ENNReal.ofReal_toReal hfin).symm
    _ = _ := by rw [hval]



theorem d018038
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        ENNReal.ofReal
          (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 / g.d009239 ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1148.d018037 s g]
  have hdil : (0 : ℝ) < g.d009239 ^ 2 := pow_pos g.d009240 2
  constructor
  · intro h
    rw [h, zero_add]
  · intro h
    have hnn1 : 0 ≤ (_root_.GD.N0232.N0720.N1159.d014647 m n s g +
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) / g.d009239 ^ 2 :=
      div_nonneg
        (add_nonneg (_root_.GD.N0232.N0720.N1159.d014650 m n s g) (sq_nonneg _))
        hdil.le
    have hnn2 : 0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 /
        g.d009239 ^ 2 :=
      div_nonneg (sq_nonneg _) hdil.le
    have heq := (ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2).1 h
    have heq2 := (div_eq_div_iff hdil.ne' hdil.ne').1 heq
    have heq3 := mul_right_cancel₀ hdil.ne' heq2
    linarith



theorem d018039 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value = _root_.GD.N0232.N0720.N1029.d015364 m n hm hn := rfl






theorem d018040
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0 ↔
      _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0 :=
  (_root_.GD.N0232.N0720.N1477.d015755
    (m := m) (n := n) (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)).trans
    (_root_.GD.N0232.N0720.N1122.d017976
      (m := m) (n := n) hm hn)






theorem d018041
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0 ↔
      (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1148.d018031
          (_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value) =
        ENNReal.ofReal
          (‖_root_.GD.N0232.N0720.N1159.d014633 m n
              (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value‖ ^ 2 / 4) ∧
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1148.d018032
          (_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value) =
        ENNReal.ofReal
          (‖_root_.GD.N0232.N0720.N1159.d014633 m n
              (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value‖ ^ 2 / 9)) := by
  rw [← _root_.GD.N0232.N0720.N1148.d018040 hm hn]
  have hsplit :
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) =
        _root_.GD.N0232.N0720.N1159.d014647 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) _root_.GD.N0232.N0720.N1482.d015130 +
          _root_.GD.N0232.N0720.N1159.d014647 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
            _root_.GD.N0232.N0720.N1482.d015131 := rfl
  rw [hsplit,
    add_eq_zero_iff_of_nonneg
      (_root_.GD.N0232.N0720.N1159.d014650 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
        _root_.GD.N0232.N0720.N1482.d015130)
      (_root_.GD.N0232.N0720.N1159.d014650 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
        _root_.GD.N0232.N0720.N1482.d015131),
    _root_.GD.N0232.N0720.N1148.d018038
      (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) _root_.GD.N0232.N0720.N1482.d015130,
    _root_.GD.N0232.N0720.N1148.d018038
      (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) _root_.GD.N0232.N0720.N1482.d015131,
    _root_.GD.N0232.N0720.N1148.d018035,
    _root_.GD.N0232.N0720.N1148.d018036,
    _root_.GD.N0232.N0720.N1148.d018029, _root_.GD.N0232.N0720.N1148.d018030]
  norm_num



theorem d018042
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h₂ : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1148.d018031
        (_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value) =
      ENNReal.ofReal
        (‖_root_.GD.N0232.N0720.N1159.d014633 m n
            (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value‖ ^ 2 / 4))
    (h₃ : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1148.d018032
        (_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value) =
      ENNReal.ofReal
        (‖_root_.GD.N0232.N0720.N1159.d014633 m n
            (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value‖ ^ 2 / 9)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n :=
  _root_.GD.N0232.N0720.N1029.d015374 m n hm hn
    ((_root_.GD.N0232.N0720.N1148.d018041 hm hn).2
      ⟨h₂, h₃⟩)






theorem d018043
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    0 < _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) ↔
      ∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) e ∧
          e ≠ _root_.GD.N0232.N0720.N1029.d015364 m n hm hn := by
  constructor
  · intro hpos
    refine ⟨_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value,
      (_root_.GD.N0232.N0720.N1159.d014634 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value).1,
      ?_⟩
    intro heq
    have hzero :
        _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0 :=
      (_root_.GD.N0232.N0720.N1082.d015400 m n
        (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)).2 heq
    exact hpos.ne' hzero
  · rintro ⟨e, hbelow, hne⟩
    have hnonneg :=
      _root_.GD.N0232.N0720.N1201.d015334 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
    rcases hnonneg.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      have hunbeatable :=
        (_root_.GD.N0232.N0720.N1082.d015401 m n
          (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)).1 hzero.symm
      exact hne (hunbeatable e hbelow)


theorem d018044
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (he : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) e) :
    ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 - ‖e‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) :=
  _root_.GD.N0232.N0720.N1201.d015338
    m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) e he




theorem d018045
    (hm : 2 ≤ m) (hn : 2 ≤ n) {e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (he : e ∈ _root_.GD.N0232.N0720.N1159.d014630 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)) :
    e ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
  _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n)
    (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn) he



theorem d018046
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)‖ ^ 2 := by
  have hmem : _root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) ∈
      _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    _root_.GD.N0232.N0720.N1148.d018045 hm hn
      (_root_.GD.N0232.N0720.N1159.d014634 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)).1
  have hmin := (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).2.2 _ hmem
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hmin
  simp only [zero_sub, norm_neg] at hmin
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hmin




theorem d018047
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) ≤
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 -
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 := by
  have h :=
    _root_.GD.N0232.N0720.N1148.d018046 hm hn
  show ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 -
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)‖ ^ 2 ≤
    ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 -
      ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2
  linarith



theorem d018048
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (heq : _root_.GD.N0232.N0720.N1080.d014191 m n hm hn = _root_.GD.N0232.N0720.N1029.d015364 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1029.d015374
    m n hm hn
  apply (_root_.GD.N0232.N0720.N1082.d015401 m n
    (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)).2
  have hunbeatable := (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).2.1
  rw [heq] at hunbeatable
  exact hunbeatable

end

end N1148
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1148.d018037
#print axioms _root_.GD.N0232.N0720.N1148.d018038
#print axioms _root_.GD.N0232.N0720.N1148.d018040
#print axioms _root_.GD.N0232.N0720.N1148.d018041
#print axioms _root_.GD.N0232.N0720.N1148.d018042
#print axioms _root_.GD.N0232.N0720.N1148.d018043
#print axioms _root_.GD.N0232.N0720.N1148.d018044
#print axioms _root_.GD.N0232.N0720.N1148.d018046
#print axioms _root_.GD.N0232.N0720.N1148.d018047
#print axioms _root_.GD.N0232.N0720.N1148.d018048
