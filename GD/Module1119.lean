import GD.Module1118
import GD.Module1070























open Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1115

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1099
open _root_.GD.N0232.N0720.N1116
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1477

variable {m n : ℕ}





def d017978
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1131.d017154 m n candidate
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) -
    ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate -
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2


def d017979
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1131.d017153 m n s candidate
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)



def d017980
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1115.d017978 m n s candidate +
    _root_.GD.N0232.N0720.N1115.d017979 m n s candidate



def d017981
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate -
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 +
    _root_.GD.N0232.N0720.N1115.d017980 m n s candidate

theorem d017982
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1115.d017978 m n s candidate := by
  unfold _root_.GD.N0232.N0720.N1115.d017978
  exact sub_nonneg.mpr
    (_root_.GD.N0232.N0720.N1131.d017158
      m n s candidate (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1)

theorem d017983
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1115.d017979 m n s candidate := by
  unfold _root_.GD.N0232.N0720.N1115.d017979
  exact _root_.GD.N0232.N0720.N1131.d017155
    m n s candidate (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1

theorem d017984
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1115.d017980 m n s candidate := by
  unfold _root_.GD.N0232.N0720.N1115.d017980
  exact add_nonneg
    (_root_.GD.N0232.N0720.N1115.d017982 m n s candidate)
    (_root_.GD.N0232.N0720.N1115.d017983 m n s candidate)

theorem d017985
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1115.d017981 m n s candidate := by
  unfold _root_.GD.N0232.N0720.N1115.d017981
  exact add_nonneg (sq_nonneg _)
    (_root_.GD.N0232.N0720.N1115.d017984 m n s candidate)




theorem d017986
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight =
      _root_.GD.N0232.N0720.N1115.d017981 m n s candidate := by
  have hexact := _root_.GD.N0232.N0720.N1131.d017159
    m n s candidate (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  unfold _root_.GD.N0232.N0720.N1115.d017981 _root_.GD.N0232.N0720.N1115.d017980
    _root_.GD.N0232.N0720.N1115.d017978 _root_.GD.N0232.N0720.N1115.d017979
  linarith





theorem d017987
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ∃ candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074,
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1115.d017981 m n s (candidate j))
        atTop (nhds 0) := by
  obtain ⟨width, packet, weight, hweight, htight⟩ :=
    _root_.GD.N0232.N0720.N1116.d016457 s
  let candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074 := fun j ↦
    { width := width j
      packet := packet j
      weight := weight j
      weight_nonneg := hweight j }
  refine ⟨candidate, ?_⟩
  apply htight.congr'
  filter_upwards with j
  exact
    (_root_.GD.N0232.N0720.N1115.d017986
      m n s (candidate j))



theorem d017988
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ∃ candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074,
      Tendsto
        (fun j ↦ ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) -
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1115.d017978 m n s (candidate j))
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1115.d017979
          m n s (candidate j))
        atTop (nhds 0) := by
  obtain ⟨candidate, hcost⟩ :=
    _root_.GD.N0232.N0720.N1115.d017987 s
  have hdistance : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ sq_nonneg _)
      (fun j ↦ by
        unfold _root_.GD.N0232.N0720.N1115.d017981 _root_.GD.N0232.N0720.N1115.d017980
        linarith [_root_.GD.N0232.N0720.N1115.d017982 m n s (candidate j),
          _root_.GD.N0232.N0720.N1115.d017983
            m n s (candidate j)])
      hcost
  have hmass : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1115.d017978 m n s (candidate j))
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1115.d017982 m n s (candidate j))
      (fun j ↦ by
        unfold _root_.GD.N0232.N0720.N1115.d017981 _root_.GD.N0232.N0720.N1115.d017980
        linarith [sq_nonneg
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) -
            _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖,
          _root_.GD.N0232.N0720.N1115.d017983
            m n s (candidate j)])
      hcost
  have hcomplementarity : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1115.d017979
        m n s (candidate j))
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1115.d017983
        m n s (candidate j))
      (fun j ↦ by
        unfold _root_.GD.N0232.N0720.N1115.d017981 _root_.GD.N0232.N0720.N1115.d017980
        linarith [sq_nonneg
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) -
            _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖,
          _root_.GD.N0232.N0720.N1115.d017982 m n s (candidate j)])
      hcost
  exact ⟨candidate, hdistance, hmass, hcomplementarity⟩



theorem d017989
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1115.d017981 m n s candidate < epsilon := by
  obtain ⟨candidate, hcost⟩ :=
    _root_.GD.N0232.N0720.N1115.d017987 s
  have heventually : ∀ᶠ j in atTop,
      _root_.GD.N0232.N0720.N1115.d017981 m n s (candidate j) < epsilon :=
    (tendsto_order.1 hcost).2 epsilon hepsilon
  obtain ⟨j, hj⟩ := heventually.exists
  exact ⟨candidate j, hj⟩





def d017990
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1115.d017981 m n s candidate +
    _root_.GD.N0232.N0720.N1122.d017962 m n
      (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)

theorem d017991
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1115.d017990 m n s candidate := by
  unfold _root_.GD.N0232.N0720.N1115.d017990
  exact add_nonneg
    (_root_.GD.N0232.N0720.N1115.d017985 m n s candidate)
    (_root_.GD.N0232.N0720.N1122.d017963
      (_root_.GD.N0232.N0720.N1130.d017075 m n candidate))



def d017992
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1115.d017990 m n s candidate < epsilon





theorem d017993
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1115.d017992 m n s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  classical
  constructor
  · intro hsmall
    have hchoose : ∀ j : ℕ,
        ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
          _root_.GD.N0232.N0720.N1115.d017990 m n s candidate <
            1 / ((j : ℝ) + 1) := by
      intro j
      exact hsmall (1 / ((j : ℝ) + 1)) (by positivity)
    choose candidate hcandidate using hchoose
    let width : ℕ → ℕ := fun j ↦ (candidate j).width
    let packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168 :=
      fun j ↦ (candidate j).packet
    let weight : ∀ j, Fin (width j) → ℝ :=
      fun j ↦ (candidate j).weight
    have hweight : ∀ j i, 0 ≤ weight j i :=
      fun j i ↦ (candidate j).weight_nonneg i
    have hrecovery : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1115.d017981 m n s (candidate j))
        atTop (nhds 0) := by
      exact squeeze_zero
        (fun j ↦ _root_.GD.N0232.N0720.N1115.d017985
          m n s (candidate j))
        (fun j ↦ by
          unfold _root_.GD.N0232.N0720.N1115.d017990 at hcandidate
          exact le_trans (le_add_of_nonneg_right
            (_root_.GD.N0232.N0720.N1122.d017963
              (_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j))))
            (hcandidate j).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have htight : Tendsto
        (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
        atTop (nhds 0) := by
      apply hrecovery.congr'
      filter_upwards with j
      change _root_.GD.N0232.N0720.N1115.d017981 m n s (candidate j) =
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight
      exact
        (_root_.GD.N0232.N0720.N1115.d017986
          m n s (candidate j)).symm
    have hresidualCandidate : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
          (_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)))
        atTop (nhds 0) := by
      exact squeeze_zero
        (fun j ↦ _root_.GD.N0232.N0720.N1122.d017963
          (_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)))
        (fun j ↦ by
          have hupper := (hcandidate j).le
          unfold _root_.GD.N0232.N0720.N1115.d017990 at hupper
          have hrecoveryNonneg := _root_.GD.N0232.N0720.N1115.d017985
            m n s (candidate j)
          linarith)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hresidual : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            (packet j) (weight j) (hweight j)))
        atTop (nhds 0) := by
      apply hresidualCandidate.congr'
      filter_upwards with j
      rfl
    exact
      (_root_.GD.N0232.N0720.N1122.d017969
        s).2 ⟨width, packet, weight, hweight, htight, hresidual⟩
  · intro henergy epsilon hepsilon
    obtain ⟨width, packet, weight, hweight, htight, hresidual⟩ :=
      (_root_.GD.N0232.N0720.N1122.d017969
        s).1 henergy
    let candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074 := fun j ↦
      { width := width j
        packet := packet j
        weight := weight j
        weight_nonneg := hweight j }
    have hrecovery : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1115.d017981 m n s (candidate j))
        atTop (nhds 0) := by
      apply htight.congr'
      filter_upwards with j
      exact
        (_root_.GD.N0232.N0720.N1115.d017986
          m n s (candidate j))
    have hcost : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1115.d017990
          m n s (candidate j)) atTop (nhds 0) := by
      unfold _root_.GD.N0232.N0720.N1115.d017990
      simpa only [candidate, _root_.GD.N0232.N0720.N1130.d017075, zero_add] using
        hrecovery.add hresidual
    have heventually : ∀ᶠ j in atTop,
        _root_.GD.N0232.N0720.N1115.d017990 m n s (candidate j) <
          epsilon :=
      (tendsto_order.1 hcost).2 epsilon hepsilon
    obtain ⟨j, hj⟩ := heventually.exists
    exact ⟨candidate j, hj⟩


theorem d017994
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 < _root_.GD.N0232.N0720.N1477.d015749 m n s ↔
      ∃ eta : ℝ, 0 < eta ∧
        ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
          eta ≤ _root_.GD.N0232.N0720.N1115.d017990 m n s candidate := by
  constructor
  · intro hpositive
    by_contra hfloor
    have hsmall :
        _root_.GD.N0232.N0720.N1115.d017992 m n s := by
      intro epsilon hepsilon
      by_contra hnone
      have hall : ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
          epsilon ≤
            _root_.GD.N0232.N0720.N1115.d017990 m n s candidate := by
        intro candidate
        exact le_of_not_gt (fun hlt ↦ hnone ⟨candidate, hlt⟩)
      exact hfloor ⟨epsilon, hepsilon, hall⟩
    exact (ne_of_gt hpositive)
      ((_root_.GD.N0232.N0720.N1115.d017993
        s).1 hsmall)
  · rintro ⟨eta, heta, hfloor⟩
    have hnotSmall :
        ¬ _root_.GD.N0232.N0720.N1115.d017992 m n s := by
      intro hsmall
      obtain ⟨candidate, hcandidate⟩ := hsmall eta heta
      exact (not_lt_of_ge (hfloor candidate)) hcandidate
    have hne : _root_.GD.N0232.N0720.N1477.d015749 m n s ≠ 0 := by
      intro hzero
      exact hnotSmall
        ((_root_.GD.N0232.N0720.N1115.d017993
          s).2 hzero)
    exact lt_of_le_of_ne
      (_root_.GD.N0232.N0720.N1099.d015757 m n s) (Ne.symm hne)

end

end N1115
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1115.d017986
#print axioms _root_.GD.N0232.N0720.N1115.d017987
#print axioms _root_.GD.N0232.N0720.N1115.d017993
#print axioms _root_.GD.N0232.N0720.N1115.d017994
