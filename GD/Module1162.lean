import GD.Module1141
import GD.Module1119
import GD.Module1139
import GD.Module1161




































open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1026

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1059
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1115
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1409

variable {m n : ℕ}





def d018622
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  _root_.GD.N0232.N0720.N1131.d017154 m n candidate q +
    _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q



theorem d018623
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q =
      ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1103.d018279 s candidate := by
  have hexact := _root_.GD.N0232.N0720.N1131.d017159
    m n s candidate q hq
  unfold _root_.GD.N0232.N0720.N1026.d018622 _root_.GD.N0232.N0720.N1103.d018279
  linarith



theorem d018624
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value =
      ‖s.value‖ ^ 2 - ‖q‖ ^ 2 +
        _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q := by
  rw [_root_.GD.N0232.N0720.N1135.d018317,
    _root_.GD.N0232.N0720.N1026.d018623 s candidate q hq]
  ring



theorem d018625
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q =
      (‖q‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) +
        (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1103.d018279 s candidate) := by
  rw [_root_.GD.N0232.N0720.N1026.d018623
    s candidate q hq]
  ring



theorem d018626
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖q‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q := by
  rw [_root_.GD.N0232.N0720.N1026.d018625
    s candidate q hq]
  exact le_add_of_nonneg_right
    (sub_nonneg.mpr (_root_.GD.N0232.N0720.N1103.d018280 s candidate))



theorem d018627
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q := by
  exact (_root_.GD.N0232.N0720.N1159.d014648
    m n s.value q hq).trans
      (_root_.GD.N0232.N0720.N1026.d018626 s candidate q hq)





theorem d018628
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    (∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      ‖q‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
        _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
        _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q <
          (‖q‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) +
            epsilon) := by
  constructor
  · intro candidate
    exact _root_.GD.N0232.N0720.N1026.d018626
      s candidate q hq
  · intro epsilon hepsilon
    obtain ⟨candidate, hcost⟩ :=
      _root_.GD.N0232.N0720.N1115.d017989 s hepsilon
    refine ⟨candidate, ?_⟩
    have hgap :=
      _root_.GD.N0232.N0720.N1115.d017986
        m n s candidate
    rw [_root_.GD.N0232.N0720.N1026.d018625
      s candidate q hq]
    rw [show
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1103.d018279 s candidate =
        _root_.GD.N0232.N0720.N1115.d017981 m n s candidate by
          simpa only [_root_.GD.N0232.N0720.N1103.d018279] using hgap]
    simpa only [add_comm] using add_lt_add_left hcost
      (‖q‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)



def d018629
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q < epsilon



theorem d018630
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1026.d018629 s q ↔
      q = _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  constructor
  · intro hsmall
    by_contra hne
    have hdistPos :
        0 < ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
      have hnormPos :
          0 < ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      positivity
    obtain ⟨candidate, hcandidate⟩ := hsmall _ hdistPos
    exact (not_lt_of_ge
      (_root_.GD.N0232.N0720.N1026.d018627
        s candidate q hq)) hcandidate
  · intro hqProjection epsilon hepsilon
    obtain ⟨candidate, hcost⟩ :=
      _root_.GD.N0232.N0720.N1115.d017989 s hepsilon
    refine ⟨candidate, ?_⟩
    subst q
    have hgap :=
      _root_.GD.N0232.N0720.N1115.d017986
        m n s candidate
    rw [_root_.GD.N0232.N0720.N1026.d018623
      s candidate (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1]
    simpa only [_root_.GD.N0232.N0720.N1103.d018279] using hgap.trans_lt hcost





theorem d018631
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ∃ next : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1103.d018279 s candidate < _root_.GD.N0232.N0720.N1103.d018279 s next := by
  obtain ⟨theta, t, ht, htPos, hdescent⟩ :=
    _root_.GD.N0232.N0720.N1059.d018359
      m n s candidate
  let next := _root_.GD.N0232.N0720.N1059.d018354 candidate theta t ht
  refine ⟨next, ?_⟩
  rw [_root_.GD.N0232.N0720.N1135.d018317,
    _root_.GD.N0232.N0720.N1135.d018317] at hdescent
  simpa only [next] using (sub_lt_sub_iff_left (‖s.value‖ ^ 2)).mp hdescent




theorem d018632
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1103.d018279 s candidate <
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  obtain ⟨next, hnext⟩ :=
    _root_.GD.N0232.N0720.N1026.d018631 s candidate
  exact hnext.trans_le (_root_.GD.N0232.N0720.N1103.d018280 s next)




theorem d018633
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    0 < _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q := by
  have hnormGap :
      0 ≤ ‖q‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
    have htax := _root_.GD.N0232.N0720.N1159.d014648
      m n s.value q hq
    linarith [sq_nonneg
      ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖]
  have hdualGap :
      0 < ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1103.d018279 s candidate :=
    sub_pos.mpr (_root_.GD.N0232.N0720.N1026.d018632 s candidate)
  rw [_root_.GD.N0232.N0720.N1026.d018625
    s candidate q hq]
  linarith






theorem d018634
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hcomplementarity :
      _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q ≤
        ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 / 2) :
    ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 / 2 ≤
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate q := by
  have hcoercive :=
    _root_.GD.N0232.N0720.N1026.d018627
      s candidate q hq
  unfold _root_.GD.N0232.N0720.N1026.d018622 at hcoercive
  linarith



def d018635
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
    q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value → q ≠ s.value →
      ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
        _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q ≤
            ‖q - s.value‖ ^ 2 / 2 →
          ‖q - s.value‖ ^ 2 / 2 ≤
            _root_.GD.N0232.N0720.N1131.d017154 m n candidate q




def d018636
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ (q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
      (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074),
    (∀ j, q j ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) →
      Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1026.d018622
            m n s (candidate j) (q j)) atTop (nhds 0) →
        Tendsto (fun j ↦ ‖q j - s.value‖) atTop (nhds 0)



theorem d018637
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hq : ∀ j, q j ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hresidual : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1026.d018622
        m n s (candidate j) (q j)) atTop (nhds 0)) :
    Tendsto
      (fun j ↦ ‖q j - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖)
      atTop (nhds 0) := by
  have hsq : Tendsto
      (fun j ↦ ‖q j - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ sq_nonneg
        ‖q j - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖)
      (fun j ↦
        _root_.GD.N0232.N0720.N1026.d018627
          s (candidate j) (q j) (hq j))
      hresidual
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt



theorem d018638
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1026.d018636 s ↔
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  constructor
  · intro hAPR
    let row := _root_.GD.N0232.N0720.N1103.d018292 s
    let q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun _ ↦
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    have hq : ∀ j, q j ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := fun _ ↦
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    have hresidual : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1026.d018622
          m n s (row.candidate j) (q j)) atTop (nhds 0) := by
      apply row.gap_tendsto_zero.congr'
      filter_upwards with j
      rw [_root_.GD.N0232.N0720.N1026.d018623
        s (row.candidate j) (q j) (hq j)]
    have hseed := hAPR q row.candidate hq hresidual
    have hconstant : Tendsto
        (fun _ : ℕ ↦
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value - s.value‖)
        atTop (nhds 0) := by
      simpa only [q] using hseed
    have hzero :
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value - s.value‖ = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hconstant
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · intro hself q candidate hq hresidual
    have hprojection :=
      _root_.GD.N0232.N0720.N1026.d018637
        s q candidate hq hresidual
    simpa only [hself] using hprojection




theorem d018639
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1026.d018635 s ↔
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  constructor
  · intro hfloor
    by_contra hne
    let q := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    have hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    have hdistPos : 0 < ‖q - s.value‖ ^ 2 / 2 := by
      have hnormPos : 0 < ‖q - s.value‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      positivity
    have hsmall : _root_.GD.N0232.N0720.N1026.d018629 s q :=
      (_root_.GD.N0232.N0720.N1026.d018630
        s q hq).2 rfl
    obtain ⟨candidate, hcandidate⟩ := hsmall _ hdistPos
    have hstationarityNonneg :=
      _root_.GD.N0232.N0720.N1131.d017156 m n candidate q
    have hcomplementarityNonneg :=
      _root_.GD.N0232.N0720.N1131.d017155 m n s candidate q hq
    have hstationarityLt :
        _root_.GD.N0232.N0720.N1131.d017154 m n candidate q <
          ‖q - s.value‖ ^ 2 / 2 := by
      unfold _root_.GD.N0232.N0720.N1026.d018622 at hcandidate
      linarith
    have hcomplementarityLe :
        _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q ≤
          ‖q - s.value‖ ^ 2 / 2 := by
      unfold _root_.GD.N0232.N0720.N1026.d018622 at hcandidate
      linarith
    have hstationarityGe :=
      hfloor q hq hne candidate hcomplementarityLe
    exact (not_lt_of_ge hstationarityGe) hstationarityLt
  · intro hself q hq hne candidate hcomplementarity
    have hcomplementarity' :
        _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q ≤
          ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 / 2 := by
      simpa only [hself] using hcomplementarity
    have hfloor :=
      _root_.GD.N0232.N0720.N1026.d018634
        s candidate q hq hcomplementarity'
    simpa only [hself] using hfloor


def d018640
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ (candidate : _root_.GD.N0232.N0720.N1130.d017074)
      (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
    q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value →
      ‖q - s.value‖ ^ 2 ≤
        _root_.GD.N0232.N0720.N1026.d018622 m n s candidate q



theorem d018641
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1026.d018640 s ↔
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  constructor
  · intro hbound
    apply (_root_.GD.N0232.N0720.N1026.d018638 s).1
    intro q candidate hq hresidual
    have hsq : Tendsto (fun j ↦ ‖q j - s.value‖ ^ 2)
        atTop (nhds 0) := by
      exact squeeze_zero
        (fun j ↦ sq_nonneg ‖q j - s.value‖)
        (fun j ↦ hbound (candidate j) (q j) (hq j)) hresidual
    have hsqrt := hsq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  · intro hself candidate q hq
    rw [← hself]
    exact _root_.GD.N0232.N0720.N1026.d018627
      s candidate q hq




theorem d018642
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1026.d018636 s ↔
      _root_.GD.N0232.N0720.N1026.d018635 s ∧
        _root_.GD.N0232.N0720.N1026.d018640 s := by
  rw [_root_.GD.N0232.N0720.N1026.d018638,
    _root_.GD.N0232.N0720.N1026.d018639,
    _root_.GD.N0232.N0720.N1026.d018641]
  tauto

end

end N1026
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1026.d018623
#print axioms _root_.GD.N0232.N0720.N1026.d018627
#print axioms _root_.GD.N0232.N0720.N1026.d018628
#print axioms _root_.GD.N0232.N0720.N1026.d018630
#print axioms _root_.GD.N0232.N0720.N1026.d018632
#print axioms _root_.GD.N0232.N0720.N1026.d018633
#print axioms _root_.GD.N0232.N0720.N1026.d018634
#print axioms _root_.GD.N0232.N0720.N1026.d018638
#print axioms _root_.GD.N0232.N0720.N1026.d018639
#print axioms _root_.GD.N0232.N0720.N1026.d018641
#print axioms _root_.GD.N0232.N0720.N1026.d018642
