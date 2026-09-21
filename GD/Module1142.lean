import GD.Module1112
import GD.Module1139
import Mathlib.Tactic


























open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1062

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1090
open _root_.GD.N0232.N0720.N1095
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1260
open _root_.GD.N0232.N0720.N1450

variable {m n : ℕ}






def d018360
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n)
      candidate.packet candidate.weight q -
    _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n)
      candidate.packet candidate.weight



theorem d018361
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    _root_.GD.N0232.N0720.N1062.d018360 candidate q =
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate q := by
  have hcompletion :=
    _root_.GD.N0232.N0720.N1125.d017255
      (m := m) (n := n) candidate.packet candidate.weight
      candidate.weight_nonneg q
      (fun i ↦ hq (candidate.packet i))
  unfold _root_.GD.N0232.N0720.N1062.d018360 _root_.GD.N0232.N0720.N1131.d017154
  linarith



theorem d018362
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1062.d018360 candidate s.value =
      ‖s.value‖ ^ 2 - _root_.GD.N0232.N0720.N1103.d018279 s candidate := by
  rw [_root_.GD.N0232.N0720.N1062.d018361 candidate s.value s.finiteRisk]
  exact _root_.GD.N0232.N0720.N1135.d018317 s candidate





def d018363
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  1 + ∑ i, candidate.weight i



def d018364
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  1 / _root_.GD.N0232.N0720.N1062.d018363 candidate

theorem d018365
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 < _root_.GD.N0232.N0720.N1062.d018363 candidate := by
  have hsum : 0 ≤ ∑ i, candidate.weight i :=
    Finset.sum_nonneg fun i _ ↦ candidate.weight_nonneg i
  unfold _root_.GD.N0232.N0720.N1062.d018363
  linarith

theorem d018366
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 < _root_.GD.N0232.N0720.N1062.d018364 candidate := by
  exact one_div_pos.mpr (_root_.GD.N0232.N0720.N1062.d018365 candidate)



def d018367
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  _root_.GD.N0232.N0720.N1062.d018364 candidate *
    _root_.GD.N0232.N0720.N1062.d018360 candidate q




theorem d018368
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1062.d018367 candidate q /
        _root_.GD.N0232.N0720.N1062.d018364 candidate =
      _root_.GD.N0232.N0720.N1062.d018360 candidate q := by
  unfold _root_.GD.N0232.N0720.N1062.d018367
  exact mul_div_cancel_left₀ _
    (ne_of_gt (_root_.GD.N0232.N0720.N1062.d018366 candidate))



theorem d018369
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1062.d018367 candidate q =
      _root_.GD.N0232.N0720.N1062.d018364 candidate *
          _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n)
            candidate.packet candidate.weight q -
        _root_.GD.N0232.N0720.N1062.d018364 candidate *
          _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n)
            candidate.packet candidate.weight := by
  unfold _root_.GD.N0232.N0720.N1062.d018367 _root_.GD.N0232.N0720.N1062.d018360
  ring



theorem d018370
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1201.d015333 m n s ≤
      _root_.GD.N0232.N0720.N1062.d018360 candidate s.value := by
  rw [_root_.GD.N0232.N0720.N1062.d018361 candidate s.value s.finiteRisk]
  exact _root_.GD.N0232.N0720.N1135.d018316 s candidate



theorem d018371
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1062.d018360
        ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j) s.value)
      atTop (nhds (_root_.GD.N0232.N0720.N1201.d015333 m n s)) := by
  have heq :
      (fun j ↦ _root_.GD.N0232.N0720.N1062.d018360
        ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j) s.value) =
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154 m n
        ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j) s.value) := by
    funext j
    exact _root_.GD.N0232.N0720.N1062.d018361
      ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j)
      s.value s.finiteRisk
  rw [heq]
  exact _root_.GD.N0232.N0720.N1135.d018319 s




theorem d018372
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto
      (fun j ↦
        _root_.GD.N0232.N0720.N1062.d018367
            ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j) s.value /
          _root_.GD.N0232.N0720.N1062.d018364
            ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j))
      atTop (nhds (_root_.GD.N0232.N0720.N1201.d015333 m n s)) := by
  simpa only [_root_.GD.N0232.N0720.N1062.d018368]
    using _root_.GD.N0232.N0720.N1062.d018371 s





def d018373 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ row : ℕ → _root_.GD.N0232.N0720.N1130.d017074,
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1062.d018360 (row j) s.value)
      atTop (nhds 0)



def d018374
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ row : ℕ → _root_.GD.N0232.N0720.N1130.d017074,
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1062.d018367 (row j) s.value /
        _root_.GD.N0232.N0720.N1062.d018364 (row j))
      atTop (nhds 0)



theorem d018375
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1062.d018374 s ↔
      _root_.GD.N0232.N0720.N1062.d018373 s := by
  unfold _root_.GD.N0232.N0720.N1062.d018374 _root_.GD.N0232.N0720.N1062.d018373
  apply exists_congr
  intro row
  simp only [_root_.GD.N0232.N0720.N1062.d018368]




theorem d018376
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1062.d018373 s ↔
      _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 := by
  constructor
  · rintro ⟨row, hrow⟩
    have hconstant : Tendsto
        (fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1201.d015333 m n s)
        atTop (nhds 0) := by
      apply squeeze_zero
      · intro j
        exact _root_.GD.N0232.N0720.N1201.d015334 m n s
      · intro j
        exact _root_.GD.N0232.N0720.N1062.d018370
          s (row j)
      · exact hrow
    exact tendsto_nhds_unique tendsto_const_nhds hconstant
  · intro hgap
    refine ⟨fun j ↦
      (_root_.GD.N0232.N0720.N1103.d018292 s).candidate j, ?_⟩
    simpa only [hgap] using
      _root_.GD.N0232.N0720.N1062.d018371 s




theorem d018377
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1062.d018373 s ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  rw [_root_.GD.N0232.N0720.N1062.d018376]
  exact _root_.GD.N0232.N0720.N1082.d015401 m n s


theorem d018378
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1062.d018374 s ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  rw [_root_.GD.N0232.N0720.N1062.d018375,
    _root_.GD.N0232.N0720.N1062.d018377]



theorem d018379
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (a : ℝ) :
    (∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      a ≤ _root_.GD.N0232.N0720.N1062.d018360 candidate s.value) ↔
      a ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  constructor
  · intro h
    apply (_root_.GD.N0232.N0720.N1135.d018326 s a).1
    intro candidate
    rw [← _root_.GD.N0232.N0720.N1062.d018361
      candidate s.value s.finiteRisk]
    exact h candidate
  · intro h
    have hcalibration :=
      (_root_.GD.N0232.N0720.N1135.d018326 s a).2 h
    intro candidate
    rw [_root_.GD.N0232.N0720.N1062.d018361
      candidate s.value s.finiteRisk]
    exact hcalibration candidate



theorem d018380
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 < _root_.GD.N0232.N0720.N1201.d015333 m n s ↔
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
          epsilon ≤ _root_.GD.N0232.N0720.N1062.d018360 candidate s.value := by
  constructor
  · intro hgap
    exact ⟨_root_.GD.N0232.N0720.N1201.d015333 m n s, hgap,
      fun candidate ↦
        _root_.GD.N0232.N0720.N1062.d018370
          s candidate⟩
  · rintro ⟨epsilon, hepsilon, hfloor⟩
    have hle : epsilon ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s :=
      (_root_.GD.N0232.N0720.N1062.d018379 s epsilon).1 hfloor
    exact hepsilon.trans_le hle




theorem d018381
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 < _root_.GD.N0232.N0720.N1062.d018360 candidate s.value := by
  rw [_root_.GD.N0232.N0720.N1062.d018361 candidate s.value s.finiteRisk]
  exact _root_.GD.N0232.N0720.N1135.d018323 s candidate



theorem d018382
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 < _root_.GD.N0232.N0720.N1062.d018367 candidate s.value /
        _root_.GD.N0232.N0720.N1062.d018364 candidate := by
  rw [_root_.GD.N0232.N0720.N1062.d018368]
  exact _root_.GD.N0232.N0720.N1062.d018381 s candidate





theorem d018383
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (row : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hrow : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1062.d018360 (row j) s.value)
      atTop (nhds 0))
    (B : ℝ) :
    ∃ j, B < _root_.GD.N0232.N0720.N1126.d016418 (row j).packet := by
  have hcalibration : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154 m n (row j) s.value)
      atTop (nhds 0) := by
    have heq :
        (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154 m n (row j) s.value) =
        (fun j ↦ _root_.GD.N0232.N0720.N1062.d018360 (row j) s.value) := by
      funext j
      exact (_root_.GD.N0232.N0720.N1062.d018361
        (row j) s.value s.finiteRisk).symm
    rw [heq]
    exact hrow
  exact _root_.GD.N0232.N0720.N1135.d018337
    s row hcalibration B





theorem d018384
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1090.d014987 m n hm hn =
      _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn) := by
  rfl



theorem d018385
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1062.d018360
        ((_root_.GD.N0232.N0720.N1103.d018292
          (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn)).candidate j)
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn))
      atTop (nhds (_root_.GD.N0232.N0720.N1090.d014987 m n hm hn)) := by
  rw [_root_.GD.N0232.N0720.N1062.d018384]
  simpa only [_root_.GD.N0232.N0720.N1450.d017835] using
    _root_.GD.N0232.N0720.N1062.d018371
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn)


theorem d018386
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Tendsto
      (fun j ↦
        let candidate := (_root_.GD.N0232.N0720.N1103.d018292
          (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn)).candidate j
        _root_.GD.N0232.N0720.N1062.d018367 candidate
              (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) /
          _root_.GD.N0232.N0720.N1062.d018364 candidate)
      atTop (nhds (_root_.GD.N0232.N0720.N1090.d014987 m n hm hn)) := by
  rw [_root_.GD.N0232.N0720.N1062.d018384]
  simpa only [_root_.GD.N0232.N0720.N1450.d017835] using
    _root_.GD.N0232.N0720.N1062.d018372
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn)



theorem d018387
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1062.d018373
        (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1090.d014987 m n hm hn = 0 := by
  rw [_root_.GD.N0232.N0720.N1062.d018376,
    _root_.GD.N0232.N0720.N1062.d018384]



theorem d018388
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1062.d018373
        (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn) ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) := by
  simpa only [_root_.GD.N0232.N0720.N1450.d017835] using
    _root_.GD.N0232.N0720.N1062.d018377
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn)



theorem d018389
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1062.d018374
        (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1090.d014987 m n hm hn = 0 := by
  rw [_root_.GD.N0232.N0720.N1062.d018375,
    _root_.GD.N0232.N0720.N1062.d018387]



theorem d018390
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (row : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hrow : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1062.d018360 (row j)
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn))
      atTop (nhds 0))
    (B : ℝ) :
    ∃ j, B < _root_.GD.N0232.N0720.N1126.d016418 (row j).packet := by
  simpa only [_root_.GD.N0232.N0720.N1450.d017835] using
    _root_.GD.N0232.N0720.N1062.d018383
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn) row hrow B



theorem d018391
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hrate : _root_.GD.N0232.N0720.N1062.d018373
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1090.d014990
    m n hm hn
  exact (_root_.GD.N0232.N0720.N1062.d018387
    hm hn).1 hrate



theorem d018392
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfail : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
        epsilon ≤ _root_.GD.N0232.N0720.N1062.d018360 candidate
          (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) := by
  have hgap : 0 < _root_.GD.N0232.N0720.N1201.d015333 m n
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn) := by
    rw [← _root_.GD.N0232.N0720.N1062.d018384]
    exact _root_.GD.N0232.N0720.N1090.d014991
      m n hm hn hfail
  simpa only [_root_.GD.N0232.N0720.N1450.d017835] using
    (_root_.GD.N0232.N0720.N1062.d018380
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn)).1 hgap


theorem d018393
    (hrate : _root_.GD.N0232.N0720.N1062.d018373
      (_root_.GD.N0232.N0720.N1450.d017834 2 2 (by omega) (by omega))) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 :=
  _root_.GD.N0232.N0720.N1062.d018391
    (m := 2) (n := 2) (by omega) (by omega) hrate

end

end N1062
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1062.d018361
#print axioms _root_.GD.N0232.N0720.N1062.d018368
#print axioms _root_.GD.N0232.N0720.N1062.d018371
#print axioms _root_.GD.N0232.N0720.N1062.d018372
#print axioms _root_.GD.N0232.N0720.N1062.d018377
#print axioms _root_.GD.N0232.N0720.N1062.d018378
#print axioms _root_.GD.N0232.N0720.N1062.d018379
#print axioms _root_.GD.N0232.N0720.N1062.d018383
#print axioms _root_.GD.N0232.N0720.N1062.d018385
#print axioms _root_.GD.N0232.N0720.N1062.d018386
#print axioms _root_.GD.N0232.N0720.N1062.d018387
#print axioms _root_.GD.N0232.N0720.N1062.d018389
#print axioms _root_.GD.N0232.N0720.N1062.d018390
#print axioms _root_.GD.N0232.N0720.N1062.d018392
#print axioms _root_.GD.N0232.N0720.N1062.d018393
