import GD.Module1151
























open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1447

noncomputable section

open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1448
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}





def d018514
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (base : _root_.GD.N0232.N0720.N1103.d018281 s)
    (neighbor : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hdom : ∀ j,
      _root_.GD.N0232.N0720.N1103.d018279 s (base.candidate j) ≤
        _root_.GD.N0232.N0720.N1103.d018279 s (neighbor j)) :
    _root_.GD.N0232.N0720.N1103.d018281 s where
  candidate := neighbor
  gap_tendsto_zero := by
    apply squeeze_zero
    · intro j
      exact sub_nonneg.mpr
        (_root_.GD.N0232.N0720.N1103.d018280 s (neighbor j))
    · intro j
      exact sub_le_sub_left (hdom j)
        (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)
    · exact base.gap_tendsto_zero


theorem d018515
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (base : _root_.GD.N0232.N0720.N1103.d018281 s)
    (neighbor : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hdom : ∀ j,
      _root_.GD.N0232.N0720.N1103.d018279 s (base.candidate j) ≤
        _root_.GD.N0232.N0720.N1103.d018279 s (neighbor j)) :
    Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1103.d018279 s (neighbor j)) atTop (nhds 0) :=
  (_root_.GD.N0232.N0720.N1447.d018514 s base neighbor hdom).gap_tendsto_zero




def d018516
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (base : _root_.GD.N0232.N0720.N1103.d018281 s)
    (neighbor : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (j : ℕ) : ℝ :=
  max
    (_root_.GD.N0232.N0720.N1103.d018279 s (base.candidate j) -
      _root_.GD.N0232.N0720.N1103.d018279 s (neighbor j)) 0



def d018517
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (base : _root_.GD.N0232.N0720.N1103.d018281 s)
    (neighbor : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hshortfall : Tendsto (_root_.GD.N0232.N0720.N1447.d018516 s base neighbor)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1103.d018281 s where
  candidate := neighbor
  gap_tendsto_zero := by
    apply squeeze_zero
    · intro j
      exact sub_nonneg.mpr
        (_root_.GD.N0232.N0720.N1103.d018280 s (neighbor j))
    · intro j
      have hpositivePart :
          _root_.GD.N0232.N0720.N1103.d018279 s (base.candidate j) -
              _root_.GD.N0232.N0720.N1103.d018279 s (neighbor j) ≤
            _root_.GD.N0232.N0720.N1447.d018516 s base neighbor j := by
        exact le_max_left _ _
      calc
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
              _root_.GD.N0232.N0720.N1103.d018279 s (neighbor j) =
            (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
                _root_.GD.N0232.N0720.N1103.d018279 s (base.candidate j)) +
              (_root_.GD.N0232.N0720.N1103.d018279 s (base.candidate j) -
                _root_.GD.N0232.N0720.N1103.d018279 s (neighbor j)) := by ring
        _ ≤
            (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
                _root_.GD.N0232.N0720.N1103.d018279 s (base.candidate j)) +
              _root_.GD.N0232.N0720.N1447.d018516 s base neighbor j :=
          by linarith
    · simpa only [zero_add] using
        base.gap_tendsto_zero.add hshortfall







def d018518 : Prop :=
  ∃ base : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268,
    ∃ scaleTwo shiftOneScaleThree :
        ℕ → _root_.GD.N0232.N0720.N1130.d017074,
      Tendsto
        (_root_.GD.N0232.N0720.N1447.d018516 _root_.GD.N0232.N0720.N1302.d018268 base scaleTwo)
        atTop (nhds 0) ∧
      Tendsto
        (_root_.GD.N0232.N0720.N1447.d018516 _root_.GD.N0232.N0720.N1302.d018268 base
          shiftOneScaleThree)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (scaleTwo j) -
            _root_.GD.N0232.N0720.N1146.d015228 2 2
              (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (shiftOneScaleThree j) -
            _root_.GD.N0232.N0720.N1146.d015229 2 2
              (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
        atTop (nhds 0)



theorem d018519
    (h : _root_.GD.N0232.N0720.N1447.d018518) :
    _root_.GD.N0232.N0720.N1448.d018480 := by
  rcases h with
    ⟨base, scaleTwo, shiftOneScaleThree, hscaleReserve,
      hshiftReserve, hscaleCovariance, hshiftCovariance⟩
  let scaleRow : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268 :=
    _root_.GD.N0232.N0720.N1447.d018517
      _root_.GD.N0232.N0720.N1302.d018268 base scaleTwo hscaleReserve
  let shiftRow : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268 :=
    _root_.GD.N0232.N0720.N1447.d018517
      _root_.GD.N0232.N0720.N1302.d018268 base shiftOneScaleThree hshiftReserve
  exact ⟨base, scaleRow, shiftRow, hscaleCovariance, hshiftCovariance⟩



theorem d018520 :
    _root_.GD.N0232.N0720.N1447.d018518 ↔
      _root_.GD.N0232.N0720.N1448.d018480 := by
  constructor
  · exact _root_.GD.N0232.N0720.N1447.d018519
  · rintro
      ⟨base, scaleRow, shiftRow, hscaleCovariance, hshiftCovariance⟩
    have reserve_tendsto
        (row : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268) :
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1103.d018279 _root_.GD.N0232.N0720.N1302.d018268
            (row.candidate j)) atTop
          (nhds
            (‖_root_.GD.N0232.N0720.N1159.d014633 2 2
              _root_.GD.N0232.N0720.N1302.d018268.value‖ ^ 2)) := by
      have hconst : Tendsto
          (fun _ : ℕ ↦
            ‖_root_.GD.N0232.N0720.N1159.d014633 2 2
              _root_.GD.N0232.N0720.N1302.d018268.value‖ ^ 2) atTop
          (nhds
            (‖_root_.GD.N0232.N0720.N1159.d014633 2 2
              _root_.GD.N0232.N0720.N1302.d018268.value‖ ^ 2)) :=
        tendsto_const_nhds
      have h := hconst.sub row.gap_tendsto_zero
      convert h using 1 <;> simp
    have shortfall_tendsto
        (row : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268) :
        Tendsto
          (_root_.GD.N0232.N0720.N1447.d018516 _root_.GD.N0232.N0720.N1302.d018268 base row.candidate)
          atTop (nhds 0) := by
      change Tendsto
        (fun j ↦ max
          (_root_.GD.N0232.N0720.N1103.d018279 _root_.GD.N0232.N0720.N1302.d018268
              (base.candidate j) -
            _root_.GD.N0232.N0720.N1103.d018279 _root_.GD.N0232.N0720.N1302.d018268
              (row.candidate j)) 0) atTop (nhds 0)
      have hdiff := (reserve_tendsto base).sub (reserve_tendsto row)
      have hmax : Continuous (fun x : ℝ ↦ max x 0) :=
        continuous_id.max continuous_const
      have ht := hmax.continuousAt.tendsto.comp hdiff
      simpa only [Function.comp_def, sub_self, max_self] using ht
    exact ⟨base, scaleRow.candidate, shiftRow.candidate,
      shortfall_tendsto scaleRow, shortfall_tendsto shiftRow,
      hscaleCovariance, hshiftCovariance⟩





def d018521
    (g : _root_.GD.N0232.N0720.N1482.d015118) (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1130.d017074 where
  width := candidate.width
  packet := fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (candidate.packet i)
  weight := candidate.weight
  weight_nonneg := candidate.weight_nonneg





def d018522 : Prop :=
  ∃ base : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268,
    Tendsto
        (_root_.GD.N0232.N0720.N1447.d018516 _root_.GD.N0232.N0720.N1302.d018268 base
          (fun j ↦ _root_.GD.N0232.N0720.N1447.d018521 _root_.GD.N0232.N0720.N1482.d015130 (base.candidate j)))
        atTop (nhds 0) ∧
      Tendsto
        (_root_.GD.N0232.N0720.N1447.d018516 _root_.GD.N0232.N0720.N1302.d018268 base
          (fun j ↦ _root_.GD.N0232.N0720.N1447.d018521 _root_.GD.N0232.N0720.N1482.d015131
            (base.candidate j)))
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 2 2
                (_root_.GD.N0232.N0720.N1447.d018521 _root_.GD.N0232.N0720.N1482.d015130 (base.candidate j)) -
            _root_.GD.N0232.N0720.N1146.d015228 2 2
              (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 2 2
                (_root_.GD.N0232.N0720.N1447.d018521 _root_.GD.N0232.N0720.N1482.d015131
                  (base.candidate j)) -
            _root_.GD.N0232.N0720.N1146.d015229 2 2
              (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
        atTop (nhds 0)

theorem d018523
    (h : _root_.GD.N0232.N0720.N1447.d018522) :
    _root_.GD.N0232.N0720.N1447.d018518 := by
  rcases h with
    ⟨base, hscaleReserve, hshiftReserve,
      hscaleCovariance, hshiftCovariance⟩
  exact ⟨base,
    (fun j ↦ _root_.GD.N0232.N0720.N1447.d018521 _root_.GD.N0232.N0720.N1482.d015130 (base.candidate j)),
    (fun j ↦ _root_.GD.N0232.N0720.N1447.d018521 _root_.GD.N0232.N0720.N1482.d015131
      (base.candidate j)),
    hscaleReserve, hshiftReserve, hscaleCovariance, hshiftCovariance⟩



theorem d018524
    (h : _root_.GD.N0232.N0720.N1447.d018518) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1448.d018484
    (_root_.GD.N0232.N0720.N1447.d018519 h)



theorem d018525
    (h : _root_.GD.N0232.N0720.N1447.d018522) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1447.d018524
    (_root_.GD.N0232.N0720.N1447.d018523 h)

end

end N1447
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1447.d018514
#print axioms _root_.GD.N0232.N0720.N1447.d018517
#print axioms _root_.GD.N0232.N0720.N1447.d018519
#print axioms _root_.GD.N0232.N0720.N1447.d018520
#print axioms _root_.GD.N0232.N0720.N1447.d018524
#print axioms _root_.GD.N0232.N0720.N1447.d018525
