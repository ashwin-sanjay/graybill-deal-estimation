import GD.Module1117
import GD.Module1031
import GD.Module0972






















open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1144

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1032
open _root_.GD.N0232.N0720.N1054
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1085
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0141
open _root_.GD.N0232.N0720.N1159

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)


noncomputable abbrev d017995
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) : _root_.GD.N0232.N0720.N1159.d014639 m n :=
  _root_.GD.N0232.N0720.N1082.d015397 m n hm hn U 1 zero_lt_one le_rfl



noncomputable abbrev d017996
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4)



theorem d017997
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1144.d017996 m n hm hn U ∈
      _root_.GD.N0232.N0720.N1159.d014630 m n (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U).value := by
  intro theta
  exact (_root_.GD.N0232.N0720.N1085.d015417
    m n hm hn U theta).le




theorem d017998
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1144.d017996 m n hm hn U ≠ 0 := by
  intro hzero
  have hrep :=
    _root_.GD.N0232.N0720.N1082.d015396
      m n hm hn U (5 / 4)
  have hunbounded :=
    _root_.GD.N0232.N0720.N1054.d016443
      (m := m) (n := n) (_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U) hrep 0
  apply hunbounded
  filter_upwards [Lp.coeFn_zero ℝ 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)] with omega hz
  rw [hzero, hz]
  norm_num



theorem d017999
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ / 16 ≤
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U).value).toReal -
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta
          (_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U)).toReal := by
  have hbound := _root_.GD.N0232.N0720.N1085.d015416
    m n hm hn U theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos
  have hbound' :
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U (5 / 4) omega -
              theta.location) -
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - theta.location) ≤
        -(_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ / 16) := by
    simpa only [_root_.GD.N0232.N0720.N1080.d014171] using hbound
  have hfullNonneg :
      0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - theta.location) :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hfiveNonneg :
      0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U (5 / 4) omega -
            theta.location) :=
    integral_nonneg fun _ ↦ sq_nonneg _
  simp only [_root_.GD.N0232.N0720.N1144.d017995, _root_.GD.N0232.N0720.N1144.d017996,
    _root_.GD.N0232.N0720.N1082.d015398, _root_.GD.N0232.N0720.N1082.d015389,
    ENNReal.toReal_ofReal hfullNonneg,
    ENNReal.toReal_ofReal hfiveNonneg]
  linarith [hbound']

variable {m n hm hn}
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem d018000
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 =
      ∫ omega, (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [← real_inner_self_eq_norm_sq
    (q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub q
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight),
    _root_.GD.N0232.N0720.N1126.d016427 packet weight hweight] with
      omega hsub hcompletion
  rw [hsub, Pi.sub_apply, hcompletion]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]


def d018001
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ) : ℝ :=
  ∑ i, weight i *
    (_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U (packet i).scale₁ (packet i).scale₂ / 16)

omit [DecidableEq I] in
theorem d018002
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ _root_.GD.N0232.N0720.N1144.d018001 U packet weight := by
  unfold _root_.GD.N0232.N0720.N1144.d018001
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hweight i)
    (div_nonneg
      (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U
        (packet i).scale₁_pos (packet i).scale₂_pos).le
      (by norm_num))




theorem d018003
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U -
        _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 +
        _root_.GD.N0232.N0720.N1144.d018001 U packet weight ≤
      ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
          packet weight := by
  let s := _root_.GD.N0232.N0720.N1144.d017995 m n hm hn U
  let q := _root_.GD.N0232.N0720.N1144.d017996 m n hm hn U
  have hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
    simpa only [s, q] using
      _root_.GD.N0232.N0720.N1144.d017997 m n hm hn U
  have hexact := _root_.GD.N0232.N0720.N1126.d016435
    s packet weight hweight q hq
  have hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s q hq
  have hweightedIntegrable : Integrable (fun omega ↦
      _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
      ) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    exact _root_.GD.N0230.N0617.d000185
      (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) (fun omega ↦ q omega) hweight
        (_root_.GD.N0232.N0720.N1126.d016419 packet)
        (_root_.GD.N0232.N0720.N1126.d016420 packet)
        (_root_.GD.N0232.N0720.N1126.d016421 packet)
        (Lp.memLp q).integrable_sq
        (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
          (packet i) q (hqFinite (packet i)))
  have hplainIntegrable : Integrable (fun omega ↦
      (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
      ) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply Integrable.mono' hweightedIntegrable
    · exact (((Lp.aestronglyMeasurable q).aemeasurable.sub
        (_root_.GD.N0232.N0720.N1126.d016423 packet weight).aemeasurable
        ).pow_const 2).aestronglyMeasurable
    · filter_upwards with omega
      have hsq : 0 ≤
          (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2 :=
        sq_nonneg _
      have hmass := _root_.GD.N0230.N0617.d000168
        weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
          (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
      change 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega at hmass
      rw [Real.norm_eq_abs, abs_of_nonneg hsq]
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hmass hsq)
  have hplainLeWeighted :
      (∫ omega,
          (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
        ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_mono hplainIntegrable hweightedIntegrable
    intro omega
    have hsq : 0 ≤
        (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2 :=
      sq_nonneg _
    have hmass := _root_.GD.N0230.N0617.d000168
      weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
        (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
    change 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega at hmass
    nlinarith
  have hdistance :
      ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 ≤
        ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [_root_.GD.N0232.N0720.N1144.d018000 packet weight hweight q]
    exact hplainLeWeighted
  have hslack : _root_.GD.N0232.N0720.N1144.d018001 U packet weight ≤
      ∑ i, weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal) := by
    unfold _root_.GD.N0232.N0720.N1144.d018001
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hweight i)
    simpa only [s, q] using
      _root_.GD.N0232.N0720.N1144.d017999
        m n hm hn U (packet i)
  linarith



theorem d018004
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1144.d018001 U packet weight ≤
      ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
          packet weight := by
  have hjoint :=
    _root_.GD.N0232.N0720.N1144.d018003
      U packet weight hweight
  nlinarith [sq_nonneg
    ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U -
      _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖]

omit [DecidableEq I] in


theorem d018005
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : ∃ i, 0 < weight i) :
    0 < _root_.GD.N0232.N0720.N1144.d018001 U packet weight := by
  obtain ⟨i, hi⟩ := hpositive
  unfold _root_.GD.N0232.N0720.N1144.d018001
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (hweight j)
      (div_nonneg
        (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U
          (packet j).scale₁_pos (packet j).scale₂_pos).le
        (by norm_num))
  · exact ⟨i, Finset.mem_univ i, mul_pos hi
      (div_pos
        (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U
          (packet i).scale₁_pos (packet i).scale₂_pos)
        (by norm_num))⟩



theorem d018006
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : ∃ i, 0 < weight i) :
    0 < ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
      _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
        packet weight := by
  exact (_root_.GD.N0232.N0720.N1144.d018005
    U packet weight hweight hpositive).trans_le
    (_root_.GD.N0232.N0720.N1144.d018004
      U packet weight hweight)





theorem d018007
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : I → _root_.GD.N0232.N0720.N1080.d014168) (weight : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    0 < ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
      _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
        packet weight := by
  by_cases hpositive : ∃ i, 0 < weight i
  · exact _root_.GD.N0232.N0720.N1144.d018006
      U packet weight hweight hpositive
  · have hzero : ∀ i, weight i = 0 := by
      intro i
      exact le_antisymm
        (le_of_not_gt (fun hi ↦ hpositive ⟨i, hi⟩)) (hweight i)
    have hreserve :
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
          packet weight = 0 := by
      unfold _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0230.N0617.d000186
      simp [_root_.GD.N0230.N0617.d000167, _root_.GD.N0230.N0617.d000164, hzero]
    rw [hreserve, sub_zero]
    exact sq_pos_of_pos
      (norm_pos_iff.mpr (_root_.GD.N0232.N0720.N1144.d017998 m n hm hn U))

variable {Krow : ℕ → Type*}
variable [∀ j, Fintype (Krow j)] [∀ j, DecidableEq (Krow j)]






theorem d018008
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : ∀ j, Krow j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Krow j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
          (packet j) (weight j)) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  refine _root_.GD.N0232.N0720.N1032.d017958
    (ι := Krow) hm hn (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U) ?_
      (_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U) ?_ ?_
      packet weight hweight htight
  · exact _root_.GD.N0232.N0720.N1082.d015399
      m n hm hn U 1 zero_lt_one le_rfl
  · exact _root_.GD.N0232.N0720.N1144.d017997
      m n hm hn U
  · exact _root_.GD.N0232.N0720.N1082.d015396
      m n hm hn U (5 / 4)

variable {J : Type*} [SemilatticeSup J] [Nonempty J]
variable {Irow : J → Type*}
variable [∀ j, Fintype (Irow j)] [∀ j, DecidableEq (Irow j)]

omit [Nonempty J] in



theorem d018009
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (packet : ∀ j, Irow j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Irow j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
          (packet j) (weight j)) atTop (nhds 0)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1144.d018001 U (packet j) (weight j))
      atTop (nhds 0) := by
  exact squeeze_zero
    (fun j ↦ _root_.GD.N0232.N0720.N1144.d018002 U
      (packet j) (weight j) (hweight j))
    (fun j ↦ _root_.GD.N0232.N0720.N1144.d018004
      U (packet j) (weight j) (hweight j))
    htight

end

end N1144
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1144.d017999
#print axioms _root_.GD.N0232.N0720.N1144.d018004
#print axioms _root_.GD.N0232.N0720.N1144.d018006
#print axioms _root_.GD.N0232.N0720.N1144.d018009
