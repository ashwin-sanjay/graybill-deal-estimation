import GD.Module1030
import GD.Module0999
import GD.Module0989




























open Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1127

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0685
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1100
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1138
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1194
open _root_.GD.N0232.N0720.N1461

variable (m n : ℕ)





def d016543 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : ℝ :=
  ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2



def d016544
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) : ℝ :=
  ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega -
      _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n



def d016545
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) : ℝ :=
  ∑ i, weight i *
    ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
      (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal)




theorem d016546
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    ‖s.value‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s packet weight =
      _root_.GD.N0232.N0720.N1127.d016543 m n s +
        _root_.GD.N0232.N0720.N1127.d016544 m n s packet weight +
          _root_.GD.N0232.N0720.N1127.d016545 m n s packet weight := by
  have hexact :=
    _root_.GD.N0232.N0720.N1126.d016435
      s packet weight hweight (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  unfold _root_.GD.N0232.N0720.N1127.d016543 _root_.GD.N0232.N0720.N1127.d016544
    _root_.GD.N0232.N0720.N1127.d016545
  linarith

theorem d016547
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1127.d016543 m n s := by
  have hnorm := _root_.GD.N0232.N0720.N1194.d015818 m n s
  unfold _root_.GD.N0232.N0720.N1127.d016543
  nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1159.d014633 m n s.value),
    norm_nonneg s.value]

theorem d016548
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ _root_.GD.N0232.N0720.N1127.d016544 m n s packet weight := by
  unfold _root_.GD.N0232.N0720.N1127.d016544
  apply integral_nonneg
  intro omega
  exact mul_nonneg
    (le_trans zero_le_one
      (_root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
        (_root_.GD.N0232.N0720.N1126.d016419 packet) omega))
    (sq_nonneg _)

theorem d016549
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ _root_.GD.N0232.N0720.N1127.d016545 m n s packet weight := by
  unfold _root_.GD.N0232.N0720.N1127.d016545
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (hweight i)
  apply sub_nonneg.mpr
  exact ENNReal.toReal_mono (s.finiteRisk (packet i))
    ((_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1 (packet i))






theorem d016550
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    ‖s.value‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s packet weight =
      ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (s.value omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have hexact :=
    _root_.GD.N0232.N0720.N1126.d016435
      s packet weight hweight s.value
        (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
  have hslack :
      (∑ i, weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal)) = 0 := by simp
  rw [hslack] at hexact
  linarith



theorem d016551
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hgap : Tendsto
      (fun j ↦ ‖s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ ∫ omega,
        _root_.GD.N0232.N0720.N1126.d016415 (packet j) (weight j) omega *
          (s.value omega -
            _root_.GD.N0232.N0720.N1126.d016416 (packet j) (weight j) omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n)
      atTop (nhds 0) := by
  have heq :
      (fun j ↦ ‖s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j)) =
      (fun j ↦ ∫ omega,
        _root_.GD.N0232.N0720.N1126.d016415 (packet j) (weight j) omega *
          (s.value omega -
            _root_.GD.N0232.N0720.N1126.d016416 (packet j) (weight j) omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    funext j
    exact _root_.GD.N0232.N0720.N1127.d016550
      m n s (packet j) (weight j) (hweight j)
  rwa [heq] at hgap



theorem d016552
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hgap : Tendsto
      (fun j ↦ ‖s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (packet j) (weight j) (hweight j))
      atTop (nhds s.value) := by
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)
  have hcloseSq : Tendsto (fun j ↦ ‖s.value - r j‖ ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero (fun j ↦ sq_nonneg ‖s.value - r j‖)
      (fun j ↦ ?_) hgap
    have hreserve :=
      _root_.GD.N0232.N0720.N1126.d016436
        s (packet j) (weight j) (hweight j) s.value
          (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
    simpa only [r] using (show
      ‖s.value - r j‖ ^ 2 ≤
        ‖s.value‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j) by
          linarith)
  have hclose : Tendsto (fun j ↦ ‖r j - s.value‖)
      atTop (nhds 0) := by
    have hsqrt := hcloseSq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero,
      norm_sub_rev] using hsqrt
  have hr : Tendsto r atTop (nhds s.value) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hclose
  simpa only [r] using hr




theorem d016553
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hgap : Tendsto
      (fun j ↦ ‖s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    Tendsto (fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1127.d016543 m n s)
        atTop (nhds 0) ∧
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1127.d016544 m n s (packet j) (weight j))
        atTop (nhds 0) ∧
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1127.d016545 m n s (packet j) (weight j))
        atTop (nhds 0) := by
  have hdecomp (j : ℕ) :=
    _root_.GD.N0232.N0720.N1127.d016546
      m n s (packet j) (weight j) (hweight j)
  have hradiusNonneg := _root_.GD.N0232.N0720.N1127.d016547 m n s
  have hdistanceNonneg (j : ℕ) :=
    _root_.GD.N0232.N0720.N1127.d016548
      m n s (packet j) (weight j) (hweight j)
  have hslackNonneg (j : ℕ) :=
    _root_.GD.N0232.N0720.N1127.d016549
      m n s (packet j) (weight j) (hweight j)
  constructor
  · exact squeeze_zero (fun _ ↦ hradiusNonneg)
      (fun j ↦ by linarith [hdecomp j, hdistanceNonneg j,
        hslackNonneg j]) hgap
  constructor
  · exact squeeze_zero hdistanceNonneg
      (fun j ↦ by linarith [hdecomp j, hradiusNonneg,
        hslackNonneg j]) hgap
  · exact squeeze_zero hslackNonneg
      (fun j ↦ by linarith [hdecomp j, hradiusNonneg,
        hdistanceNonneg j]) hgap





theorem d016554
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hgap : Tendsto
      (fun j ↦ ‖s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  have htaxT :=
    (_root_.GD.N0232.N0720.N1127.d016553
      m n s packet weight hweight hgap).1
  have htaxZero : _root_.GD.N0232.N0720.N1127.d016543 m n s = 0 :=
    tendsto_nhds_unique tendsto_const_nhds htaxT
  have hnormSq : ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 = ‖s.value‖ ^ 2 := by
    unfold _root_.GD.N0232.N0720.N1127.d016543 at htaxZero
    linarith
  have htax := _root_.GD.N0230.N0685.d000512 (_root_.GD.N0232.N0720.N1100.d015487 m n s.value)
    (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
  simp only [sub_zero] at htax
  have hdist : ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ = 0 := by
    nlinarith [norm_nonneg
      (s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hdist)).symm





theorem d016555
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hne : _root_.GD.N0232.N0720.N1159.d014633 m n s.value ≠ s.value)
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) :
    ¬ Tendsto
      (fun j ↦ ‖s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0) := by
  intro hgap
  exact hne
    (_root_.GD.N0232.N0720.N1127.d016554
      m n s packet weight hweight hgap)










theorem d016556
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (houter : Tendsto
      (fun j ↦ Metric.infDist
        (_root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j))
        (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
      atTop (nhds 0))
    (hgap : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            (packet j) (weight j) (hweight j)‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)) -
          _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)) -
          _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)
  let epsilon : ℕ → ℝ := fun j ↦
    ‖r j‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j)
  apply _root_.GD.N0232.N0720.N1461.d015690
    m n hm hn s hstrict r epsilon
  · simpa only [r] using houter
  · intro j
    have hreserve :=
      _root_.GD.N0232.N0720.N1126.d016437
        s (packet j) (weight j) (hweight j)
    have hdistanceNonneg :
        0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value - r j‖ ^ 2 :=
      sq_nonneg _
    dsimp only [epsilon]
    linarith
  · simpa only [epsilon, r] using hgap
  · simpa only [r] using hscaleTwo
  · simpa only [r] using hshiftOneScaleThree







theorem d016557
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) :
    ¬ (Tendsto
          (fun j ↦ Metric.infDist
            (_root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j))
            (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦
            ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
                (packet j) (weight j) (hweight j)‖ ^ 2 -
              _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦
            ‖_root_.GD.N0232.N0720.N1146.d015228 m n
                (_root_.GD.N0232.N0720.N1126.d016426
                  (packet j) (weight j) (hweight j)) -
              _root_.GD.N0232.N0720.N1126.d016426
                (packet j) (weight j) (hweight j)‖)
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦
            ‖_root_.GD.N0232.N0720.N1146.d015229 m n
                (_root_.GD.N0232.N0720.N1126.d016426
                  (packet j) (weight j) (hweight j)) -
              _root_.GD.N0232.N0720.N1126.d016426
                (packet j) (weight j) (hweight j)‖)
          atTop (nhds 0)) := by
  rintro ⟨houter, hgap, htwo, hthree⟩
  exact hno
    (_root_.GD.N0232.N0720.N1127.d016556
      m n hm hn s hstrict packet weight hweight houter hgap htwo hthree)









theorem d016558
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hgap : Tendsto
      (fun j ↦ ‖s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)) -
          _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)) -
          _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n := fun _ ↦ s
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)
  apply _root_.GD.N0232.N0720.N1138.d015852
    m n hm hn seed
      (fun _ _ ↦ le_rfl) (by simpa [seed] using hstrict)
      r (fun _ ↦ 1)
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      (fun _ ↦ ‖s.value‖ ^ 2)
  · intro j
    norm_num
  · intro j
    simpa only [seed, r, one_mul] using
      (_root_.GD.N0232.N0720.N1126.d016437
        s (packet j) (weight j) (hweight j))
  · intro j
    have hnorm := _root_.GD.N0232.N0720.N1194.d015818 m n s
    dsimp only [seed]
    nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1159.d014633 m n s.value),
      norm_nonneg s.value]
  · exact hgap
  · exact hscaleTwo
  · exact hshiftOneScaleThree

end
end N1127
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1127.d016546
#print axioms _root_.GD.N0232.N0720.N1127.d016550
#print axioms _root_.GD.N0232.N0720.N1127.d016553
#print axioms _root_.GD.N0232.N0720.N1127.d016552
#print axioms _root_.GD.N0232.N0720.N1127.d016554
#print axioms _root_.GD.N0232.N0720.N1127.d016555
#print axioms _root_.GD.N0232.N0720.N1127.d016556
#print axioms _root_.GD.N0232.N0720.N1127.d016557
#print axioms _root_.GD.N0232.N0720.N1127.d016558
