import GD.Module1138
import GD.Module1037
import GD.Module0970
import GD.Module0971
import GD.Module1136
import GD.Module1031
import GD.Module1076




































open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1135

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0232.N0720.N1054
open _root_.GD.N0232.N0720.N1055
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1123
open _root_.GD.N0232.N0720.N1121
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1127
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201

variable {m n : ℕ}






theorem d018316
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1201.d015333 m n s ≤
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value := by
  have hdecomp :=
    _root_.GD.N0232.N0720.N1127.d016546
      m n s candidate.packet candidate.weight candidate.weight_nonneg
  have hcalibration :=
    _root_.GD.N0232.N0720.N1127.d016550
      m n s candidate.packet candidate.weight candidate.weight_nonneg
  have hterminalDistance :=
    _root_.GD.N0232.N0720.N1127.d016548
      m n s candidate.packet candidate.weight candidate.weight_nonneg
  have hcomplementarity :=
    _root_.GD.N0232.N0720.N1127.d016549
      m n s candidate.packet candidate.weight candidate.weight_nonneg
  change _root_.GD.N0232.N0720.N1127.d016543 m n s ≤
    ∫ omega,
      _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
        (s.value omega -
          _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n
  linarith




theorem d018317
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value =
      ‖s.value‖ ^ 2 - _root_.GD.N0232.N0720.N1103.d018279 s candidate := by
  have hcalibration :=
    _root_.GD.N0232.N0720.N1127.d016550
      m n s candidate.packet candidate.weight candidate.weight_nonneg
  simpa only [_root_.GD.N0232.N0720.N1131.d017154, _root_.GD.N0232.N0720.N1103.d018279] using
    hcalibration.symm




theorem d018318
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (row.candidate j) s.value)
      atTop (nhds (_root_.GD.N0232.N0720.N1201.d015333 m n s)) := by
  have hpoint :
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (row.candidate j) s.value) =
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n s +
        (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate j))) := by
    funext j
    calc
      _root_.GD.N0232.N0720.N1131.d017154
          m n (row.candidate j) s.value =
          ‖s.value‖ ^ 2 - _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate j) :=
            _root_.GD.N0232.N0720.N1135.d018317
              s (row.candidate j)
      _ = _root_.GD.N0232.N0720.N1201.d015333 m n s +
          (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
            _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate j)) := by
            unfold _root_.GD.N0232.N0720.N1201.d015333 _root_.GD.N0232.N0720.N1103.d018279
            ring
  rw [hpoint]
  simpa only [add_zero] using
    tendsto_const_nhds.add row.gap_tendsto_zero


theorem d018319
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154 m n
        ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j) s.value)
      atTop (nhds (_root_.GD.N0232.N0720.N1201.d015333 m n s)) := by
  let row : _root_.GD.N0232.N0720.N1103.d018281 s :=
    { candidate := (_root_.GD.N0232.N0720.N1103.d018292 s).candidate
      gap_tendsto_zero :=
        (_root_.GD.N0232.N0720.N1103.d018292 s).gap_tendsto_zero }
  simpa only [row] using
    _root_.GD.N0232.N0720.N1135.d018318 s row



theorem d018320
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration :
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value = 0) :
    _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 := by
  apply le_antisymm
  · exact (_root_.GD.N0232.N0720.N1135.d018316
      s candidate).trans_eq hcalibration
  · exact _root_.GD.N0232.N0720.N1201.d015334 m n s



theorem d018321
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (hexact : _root_.GD.N0232.N0720.N1130.d017075 m n candidate = s.value) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  apply (_root_.GD.N0232.N0720.N1082.d015400
    m n s).1
  apply _root_.GD.N0232.N0720.N1135.d018320
    s candidate
  exact (_root_.GD.N0232.N0720.N1123.d018313
    m n candidate s.value s.finiteRisk).2 hexact





theorem d018322
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1130.d017075 m n candidate ≠ s.value := by
  intro hexact
  have hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n
      (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) := by
    rw [hexact]
    exact s.riskCharacter
  exact
    (_root_.GD.N0232.N0720.N1055.d017240
      (m := m) (n := n) candidate.packet candidate.weight
        candidate.weight_nonneg) (by
          simpa only [_root_.GD.N0232.N0720.N1130.d017075] using hcharacter)




theorem d018323
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 < _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value := by
  have hne : _root_.GD.N0232.N0720.N1131.d017154
      m n candidate s.value ≠ 0 := by
    intro hzero
    exact _root_.GD.N0232.N0720.N1135.d018322 s candidate
      ((_root_.GD.N0232.N0720.N1123.d018313
        m n candidate s.value s.finiteRisk).1 hzero)
  exact lt_of_le_of_ne
    (_root_.GD.N0232.N0720.N1131.d017156 m n candidate s.value)
    (Ne.symm hne)






def d018324
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value < ε



theorem d018325
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (ε : ℝ) (hε : 0 < ε) :
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value <
        _root_.GD.N0232.N0720.N1201.d015333 m n s + ε := by
  have hsmall : ∀ᶠ j in atTop,
      _root_.GD.N0232.N0720.N1131.d017154 m n
          ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j) s.value <
        _root_.GD.N0232.N0720.N1201.d015333 m n s + ε :=
    (tendsto_order.1
      (_root_.GD.N0232.N0720.N1135.d018319 s)).2
      _ (lt_add_of_pos_right _ hε)
  obtain ⟨j, hj⟩ := hsmall.exists
  exact ⟨(_root_.GD.N0232.N0720.N1103.d018292 s).candidate j, hj⟩




theorem d018326
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (a : ℝ) :
    (∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      a ≤ _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value) ↔
      a ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  constructor
  · intro hlower
    by_contra hnot
    have hlt : _root_.GD.N0232.N0720.N1201.d015333 m n s < a := lt_of_not_ge hnot
    obtain ⟨candidate, hcandidate⟩ :=
      _root_.GD.N0232.N0720.N1135.d018325 s
        (a - _root_.GD.N0232.N0720.N1201.d015333 m n s) (sub_pos.mpr hlt)
    have hcandidate' :
        _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value < a := by
      convert hcandidate using 1 <;> ring
    exact (not_lt_of_ge (hlower candidate)) hcandidate'
  · intro ha candidate
    exact ha.trans (_root_.GD.N0232.N0720.N1135.d018316
      s candidate)



theorem d018327
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (happrox : _root_.GD.N0232.N0720.N1135.d018324 s) :
    _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 := by
  apply le_antisymm
  · by_contra hnot
    push Not at hnot
    obtain ⟨candidate, hcandidate⟩ := happrox
      (_root_.GD.N0232.N0720.N1201.d015333 m n s) hnot
    exact (not_lt_of_ge
      (_root_.GD.N0232.N0720.N1135.d018316
        s candidate)) hcandidate
  · exact _root_.GD.N0232.N0720.N1201.d015334 m n s



theorem d018328
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1135.d018324 s ↔
      _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 := by
  constructor
  · exact _root_.GD.N0232.N0720.N1135.d018327 s
  · intro hgap ε hε
    obtain ⟨candidate, hcandidate⟩ :=
      _root_.GD.N0232.N0720.N1135.d018325 s ε hε
    rw [hgap, zero_add] at hcandidate
    exact ⟨candidate, hcandidate⟩




def d018329
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ k : ℕ, ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
    _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value ≤
      1 / ((k : ℝ) + 1)





def d018330
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ k : ℕ, ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
    ‖s.value‖ ^ 2 - _root_.GD.N0232.N0720.N1103.d018279 s candidate ≤
      1 / ((k : ℝ) + 1)

theorem d018331
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1135.d018329 s ↔
      _root_.GD.N0232.N0720.N1135.d018330 s := by
  unfold _root_.GD.N0232.N0720.N1135.d018329
    _root_.GD.N0232.N0720.N1135.d018330
  simp only [_root_.GD.N0232.N0720.N1135.d018317]


theorem d018332
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1135.d018329 s ↔
      _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 := by
  constructor
  · intro hcert
    choose candidate hcandidate using hcert
    have hcalibration : Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1131.d017154
          m n (candidate k) s.value) atTop (nhds 0) :=
      squeeze_zero
      (fun k ↦ _root_.GD.N0232.N0720.N1131.d017156
        m n (candidate k) s.value)
      hcandidate tendsto_one_div_add_atTop_nhds_zero_nat
    have hconstant : Tendsto
        (fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1201.d015333 m n s)
        atTop (nhds 0) :=
      squeeze_zero
        (fun _ ↦ _root_.GD.N0232.N0720.N1201.d015334 m n s)
        (fun k ↦ _root_.GD.N0232.N0720.N1135.d018316
          s (candidate k)) hcalibration
    exact tendsto_nhds_unique tendsto_const_nhds hconstant
  · intro hgap k
    have hpositive : 0 < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨candidate, hcandidate⟩ :=
      _root_.GD.N0232.N0720.N1135.d018325 s
        (1 / ((k : ℝ) + 1)) hpositive
    rw [hgap, zero_add] at hcandidate
    exact ⟨candidate, hcandidate.le⟩


theorem d018333
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1135.d018330 s ↔
      _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 := by
  rw [← _root_.GD.N0232.N0720.N1135.d018331,
    _root_.GD.N0232.N0720.N1135.d018332]



theorem d018334
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (¬ _root_.GD.N0232.N0720.N1135.d018329 s) ↔
      ∃ k : ℕ, ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
        1 / ((k : ℝ) + 1) <
          _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value := by
  unfold _root_.GD.N0232.N0720.N1135.d018329
  push Not
  rfl


theorem d018335
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate j) s.value) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 := by
  have hconstant : Tendsto
      (fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1201.d015333 m n s)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun _ ↦ _root_.GD.N0232.N0720.N1201.d015334 m n s)
      (fun j ↦ _root_.GD.N0232.N0720.N1135.d018316
        s (candidate j)) hcalibration
  exact tendsto_nhds_unique tendsto_const_nhds hconstant



theorem d018336
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate j) s.value) atTop (nhds 0)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j))
      atTop (nhds s.value) := by
  have hsq : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) - s.value‖ ^ 2)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ sq_nonneg
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) - s.value‖)
      (fun j ↦ _root_.GD.N0232.N0720.N1121.d018304
        m n (candidate j) s.value s.finiteRisk)
      hcalibration
  have hnorm : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) - s.value‖)
      atTop (nhds 0) := by
    have hsqrt := hsq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm





theorem d018337
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate j) s.value) atTop (nhds 0))
    (B : ℝ) :
    ∃ j, B < _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet := by
  have hconv : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j))
      atTop (nhds s.value) :=
    _root_.GD.N0232.N0720.N1135.d018336
      s candidate hcalibration
  by_contra hnot
  push Not at hnot
  have huniform : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) omega| ≤ B := by
    intro j
    filter_upwards [_root_.GD.N0232.N0720.N1054.d016444
        (m := m) (n := n) (candidate j).packet (candidate j).weight
          (candidate j).weight_nonneg] with omega hpacket
    exact hpacket.trans (hnot j)
  have hbound : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |s.value omega| ≤ B :=
    _root_.GD.N0232.N0720.N1054.d016447
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)) s.value B
      hconv huniform
  exact (_root_.GD.N0232.N0720.N1055.d017238 s.value B hbound)
    s.riskCharacter






theorem d018338
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (happrox : _root_.GD.N0232.N0720.N1135.d018324 s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact (_root_.GD.N0232.N0720.N1201.d015341
    m n hm hn).2
    ⟨s, hstrict,
      _root_.GD.N0232.N0720.N1135.d018327 s happrox⟩




theorem d018339
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1135.d018324 s := by
  rw [_root_.GD.N0232.N0720.N1201.d015341
    m n hm hn]
  simp only [_root_.GD.N0232.N0720.N1200.d015250]
  apply exists_congr
  intro s
  rw [and_congr_right]
  intro _
  exact
    (_root_.GD.N0232.N0720.N1135.d018328
      s).symm





theorem d018340
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1135.d018329 s := by
  rw [_root_.GD.N0232.N0720.N1201.d015341
    m n hm hn]
  simp only [_root_.GD.N0232.N0720.N1200.d015250]
  apply exists_congr
  intro s
  rw [and_congr_right]
  intro _
  exact
    (_root_.GD.N0232.N0720.N1135.d018332
      s).symm


theorem d018341
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1135.d018330 s := by
  rw [_root_.GD.N0232.N0720.N1201.d015341
    m n hm hn]
  simp only [_root_.GD.N0232.N0720.N1200.d015250]
  apply exists_congr
  intro s
  rw [and_congr_right]
  intro _
  exact
    (_root_.GD.N0232.N0720.N1135.d018333 s).symm


theorem d018342
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate j) s.value) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact (_root_.GD.N0232.N0720.N1201.d015341
    m n hm hn).2
    ⟨s, hstrict,
      _root_.GD.N0232.N0720.N1135.d018335
        s candidate hcalibration⟩




theorem d018343
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (hexact : _root_.GD.N0232.N0720.N1130.d017075 m n candidate = s.value) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply (_root_.GD.N0232.N0720.N1201.d015341
    m n hm hn).2
  refine ⟨s, hstrict, ?_⟩
  apply _root_.GD.N0232.N0720.N1135.d018320
    s candidate
  exact (_root_.GD.N0232.N0720.N1123.d018313
    m n candidate s.value s.finiteRisk).2 hexact




theorem d018344
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (happrox : _root_.GD.N0232.N0720.N1135.d018324
      (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact _root_.GD.N0232.N0720.N1135.d018338
    hm hn (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
      (_root_.GD.N0232.N0720.N1029.d015373 m n hm hn) happrox



theorem d018345
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hcert : _root_.GD.N0232.N0720.N1135.d018329
      (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply (_root_.GD.N0232.N0720.N1135.d018340
    hm hn).2
  exact ⟨_root_.GD.N0232.N0720.N1029.d015372 m n hm hn,
    _root_.GD.N0232.N0720.N1029.d015373 m n hm hn, hcert⟩






theorem d018346
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
        ε ≤ _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value := by
  have hgapNe : _root_.GD.N0232.N0720.N1201.d015333 m n s ≠ 0 := by
    intro hgap
    apply hno
    exact (_root_.GD.N0232.N0720.N1201.d015341
      m n hm hn).2 ⟨s, hstrict, hgap⟩
  have hgapPos : 0 < _root_.GD.N0232.N0720.N1201.d015333 m n s :=
    lt_of_le_of_ne (_root_.GD.N0232.N0720.N1201.d015334 m n s)
      (Ne.symm hgapNe)
  exact ⟨_root_.GD.N0232.N0720.N1201.d015333 m n s, hgapPos,
    fun candidate ↦
      _root_.GD.N0232.N0720.N1135.d018316 s candidate⟩




theorem d018347
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (¬ _root_.GD.N0232.N0720.N1159.d014661 m n) ↔
      ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) →
          ∃ k : ℕ, ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
            1 / ((k : ℝ) + 1) <
              _root_.GD.N0232.N0720.N1131.d017154
                m n candidate s.value := by
  constructor
  · intro hno s hstrict
    apply (_root_.GD.N0232.N0720.N1135.d018334
      s).1
    intro hcert
    apply hno
    exact
      (_root_.GD.N0232.N0720.N1135.d018340
        hm hn).2 ⟨s, hstrict, hcert⟩
  · intro hfloor hendpoint
    obtain ⟨s, hstrict, hcert⟩ :=
      (_root_.GD.N0232.N0720.N1135.d018340
        hm hn).1 hendpoint
    obtain ⟨k, hk⟩ := hfloor s hstrict
    obtain ⟨candidate, hcandidate⟩ := hcert k
    exact (not_lt_of_ge hcandidate) (hk candidate)

end

end N1135
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1135.d018316
#print axioms _root_.GD.N0232.N0720.N1135.d018317
#print axioms _root_.GD.N0232.N0720.N1135.d018318
#print axioms _root_.GD.N0232.N0720.N1135.d018326
#print axioms _root_.GD.N0232.N0720.N1135.d018321
#print axioms _root_.GD.N0232.N0720.N1135.d018322
#print axioms _root_.GD.N0232.N0720.N1135.d018323
#print axioms _root_.GD.N0232.N0720.N1135.d018327
#print axioms _root_.GD.N0232.N0720.N1135.d018328
#print axioms _root_.GD.N0232.N0720.N1135.d018332
#print axioms _root_.GD.N0232.N0720.N1135.d018333
#print axioms _root_.GD.N0232.N0720.N1135.d018336
#print axioms _root_.GD.N0232.N0720.N1135.d018337
#print axioms _root_.GD.N0232.N0720.N1135.d018338
#print axioms _root_.GD.N0232.N0720.N1135.d018340
#print axioms _root_.GD.N0232.N0720.N1135.d018341
#print axioms _root_.GD.N0232.N0720.N1135.d018343
#print axioms _root_.GD.N0232.N0720.N1135.d018344
#print axioms _root_.GD.N0232.N0720.N1135.d018346
#print axioms _root_.GD.N0232.N0720.N1135.d018347
