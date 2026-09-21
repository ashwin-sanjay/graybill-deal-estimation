import GD.Module1155


































open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1117

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1120
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1447
open _root_.GD.N0232.N0720.N1448

variable {m n : ℕ}






def d018538
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base neighbor : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  max (_root_.GD.N0232.N0720.N1103.d018279 s base - _root_.GD.N0232.N0720.N1103.d018279 s neighbor) 0

theorem d018539
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base neighbor : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1117.d018538 s base neighbor := by
  exact le_max_right _ _



def d018540
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base scaleTwo shiftOneScaleThree :
      _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1117.d018538 s base scaleTwo +
    _root_.GD.N0232.N0720.N1117.d018538 s base shiftOneScaleThree +
    _root_.GD.N0232.N0720.N1131.d017154 m n scaleTwo
      (_root_.GD.N0232.N0720.N1146.d015228 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n base)) +
    _root_.GD.N0232.N0720.N1131.d017154 m n shiftOneScaleThree
      (_root_.GD.N0232.N0720.N1146.d015229 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n base))

theorem d018541
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base scaleTwo shiftOneScaleThree :
      _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1117.d018540 s base scaleTwo
      shiftOneScaleThree := by
  unfold _root_.GD.N0232.N0720.N1117.d018540
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (_root_.GD.N0232.N0720.N1117.d018539 s base scaleTwo)
        (_root_.GD.N0232.N0720.N1117.d018539 s base shiftOneScaleThree))
      (_root_.GD.N0232.N0720.N1131.d017156 m n scaleTwo _))
    (_root_.GD.N0232.N0720.N1131.d017156 m n shiftOneScaleThree _)



theorem d018542
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base scaleTwo shiftOneScaleThree :
      _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1117.d018538 s base scaleTwo ≤
      _root_.GD.N0232.N0720.N1117.d018540 s base scaleTwo
        shiftOneScaleThree := by
  unfold _root_.GD.N0232.N0720.N1117.d018540
  have hshift := _root_.GD.N0232.N0720.N1117.d018539
    s base shiftOneScaleThree
  have hscaleTax := _root_.GD.N0232.N0720.N1131.d017156
    m n scaleTwo
      (_root_.GD.N0232.N0720.N1146.d015228 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n base))
  have hshiftTax := _root_.GD.N0232.N0720.N1131.d017156
    m n shiftOneScaleThree
      (_root_.GD.N0232.N0720.N1146.d015229 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n base))
  linarith



theorem d018543
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base scaleTwo shiftOneScaleThree :
      _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1117.d018538 s base shiftOneScaleThree ≤
      _root_.GD.N0232.N0720.N1117.d018540 s base scaleTwo
        shiftOneScaleThree := by
  unfold _root_.GD.N0232.N0720.N1117.d018540
  have hscale := _root_.GD.N0232.N0720.N1117.d018539 s base scaleTwo
  have hscaleTax := _root_.GD.N0232.N0720.N1131.d017156
    m n scaleTwo
      (_root_.GD.N0232.N0720.N1146.d015228 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n base))
  have hshiftTax := _root_.GD.N0232.N0720.N1131.d017156
    m n shiftOneScaleThree
      (_root_.GD.N0232.N0720.N1146.d015229 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n base))
  linarith



theorem d018544
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base scaleTwo shiftOneScaleThree :
      _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1120.d018530 m n base scaleTwo shiftOneScaleThree ≤
      _root_.GD.N0232.N0720.N1117.d018540 s base scaleTwo
        shiftOneScaleThree := by
  unfold _root_.GD.N0232.N0720.N1120.d018530 _root_.GD.N0232.N0720.N1117.d018540
  have hscale := _root_.GD.N0232.N0720.N1117.d018539 s base scaleTwo
  have hshift := _root_.GD.N0232.N0720.N1117.d018539
    s base shiftOneScaleThree
  linarith






theorem d018545
    (base : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268)
    (scaleTwo shiftOneScaleThree :
      ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (budget : ℕ → ℝ)
    (hbudget : Tendsto budget atTop (nhds 0))
    (hdefect : ∀ j,
      _root_.GD.N0232.N0720.N1117.d018540 _root_.GD.N0232.N0720.N1302.d018268
          (base.candidate j) (scaleTwo j) (shiftOneScaleThree j) ≤
        budget j) :
    _root_.GD.N0232.N0720.N1120.d018534 := by
  refine ⟨base, scaleTwo, shiftOneScaleThree, ?_, ?_, ?_⟩
  · apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1117.d018539
        _root_.GD.N0232.N0720.N1302.d018268 (base.candidate j) (scaleTwo j))
      (fun j ↦ ?_) hbudget
    exact (_root_.GD.N0232.N0720.N1117.d018542
      _root_.GD.N0232.N0720.N1302.d018268 (base.candidate j)
        (scaleTwo j) (shiftOneScaleThree j)).trans (hdefect j)
  · apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1117.d018539
        _root_.GD.N0232.N0720.N1302.d018268 (base.candidate j)
          (shiftOneScaleThree j))
      (fun j ↦ ?_) hbudget
    exact (_root_.GD.N0232.N0720.N1117.d018543
      _root_.GD.N0232.N0720.N1302.d018268 (base.candidate j)
        (scaleTwo j) (shiftOneScaleThree j)).trans (hdefect j)
  · apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1120.d018531 2 2
        (base.candidate j) (scaleTwo j) (shiftOneScaleThree j))
      (fun j ↦ ?_) hbudget
    exact (_root_.GD.N0232.N0720.N1117.d018544
      _root_.GD.N0232.N0720.N1302.d018268 (base.candidate j)
        (scaleTwo j) (shiftOneScaleThree j)).trans (hdefect j)




theorem d018546
    (base : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268)
    (budget : ℕ → ℝ)
    (hbudget : Tendsto budget atTop (nhds 0))
    (hlocal : ∀ j, ∃ scaleTwo shiftOneScaleThree :
        _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1117.d018540 _root_.GD.N0232.N0720.N1302.d018268
          (base.candidate j) scaleTwo shiftOneScaleThree ≤ budget j) :
    _root_.GD.N0232.N0720.N1120.d018534 := by
  choose scaleTwo shiftOneScaleThree hdefect using hlocal
  exact _root_.GD.N0232.N0720.N1117.d018545
    base scaleTwo shiftOneScaleThree budget hbudget hdefect





noncomputable def d018547
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : _root_.GD.N0232.N0720.N1103.d018281 s where
  candidate := (_root_.GD.N0232.N0720.N1103.d018292 s).candidate
  gap_tendsto_zero :=
    (_root_.GD.N0232.N0720.N1103.d018292 s).gap_tendsto_zero






def d018548 : Prop :=
  ∀ j, ∃ scaleTwo shiftOneScaleThree :
      _root_.GD.N0232.N0720.N1130.d017074,
    _root_.GD.N0232.N0720.N1117.d018540 _root_.GD.N0232.N0720.N1302.d018268
        ((_root_.GD.N0232.N0720.N1117.d018547
          _root_.GD.N0232.N0720.N1302.d018268).candidate j)
        scaleTwo shiftOneScaleThree ≤
      1 / ((j : ℝ) + 1)



theorem d018549
    (h : _root_.GD.N0232.N0720.N1117.d018548) :
    _root_.GD.N0232.N0720.N1120.d018534 := by
  apply _root_.GD.N0232.N0720.N1117.d018546
    (_root_.GD.N0232.N0720.N1117.d018547 _root_.GD.N0232.N0720.N1302.d018268)
    (fun j ↦ 1 / ((j : ℝ) + 1))
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact h



theorem d018550
    (h : _root_.GD.N0232.N0720.N1117.d018548) :
    _root_.GD.N0232.N0720.N1448.d018480 := by
  exact _root_.GD.N0232.N0720.N1120.d018536
    (_root_.GD.N0232.N0720.N1117.d018549 h)




theorem d018551
    (h : _root_.GD.N0232.N0720.N1117.d018548) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1120.d018537
    (_root_.GD.N0232.N0720.N1117.d018549 h)

end

end N1117
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1117.d018545
#print axioms _root_.GD.N0232.N0720.N1117.d018546
#print axioms _root_.GD.N0232.N0720.N1117.d018549
#print axioms _root_.GD.N0232.N0720.N1117.d018551
