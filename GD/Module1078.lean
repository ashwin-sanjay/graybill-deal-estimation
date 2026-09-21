import GD.Module1075





























open Filter MeasureTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1140

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0685
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1133
open _root_.GD.N0232.N0720.N1139
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1499

set_option linter.unusedSectionVars false

variable {m n k : ℕ}




def d017265
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1126.d016432 s packet weight -
    (delta : ℝ) * ∑ i, weight i



theorem d017266
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ) :
    _root_.GD.N0230.N0617.d000186 (_root_.GD.N0232.N0720.N1080.d014172 m n) weight
        (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
        (fun i ↦ _root_.GD.N0232.N0720.N1126.d016431 s packet i + (delta : ℝ)) =
      _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight := by
  unfold _root_.GD.N0232.N0720.N1140.d017265 _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0230.N0617.d000186
  have hsum :
      (∑ i, weight i *
          (_root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 -
            (_root_.GD.N0232.N0720.N1126.d016431 s packet i + (delta : ℝ)))) =
        (∑ i, weight i *
          (_root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet i)) -
          (delta : ℝ) * ∑ i, weight i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

private theorem d017267
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖q‖ ^ 2 = ∫ omega, (q omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [← real_inner_self_eq_norm_sq q, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with omega
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

private theorem d017268
    (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 =
      ∫ omega,
        (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
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




theorem d017269
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight +
        ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n ≤
      ‖q‖ ^ 2 := by
  have hqFinite :=
    _root_.GD.N0232.N0720.N1139.d017220
      s packet delta q hq
  have hconstraint :
      ∀ i, _root_.GD.N0232.N0720.N1139.d017221 s packet delta i q ≤ 0 :=
    (_root_.GD.N0232.N0720.N1139.d017223
      s packet delta q hqFinite).1 hq
  have hpenalty :
      ∑ i, weight i * _root_.GD.N0232.N0720.N1139.d017221 s packet delta i q ≤ 0 := by
    exact Finset.sum_nonpos fun i _ ↦
      mul_nonpos_of_nonneg_of_nonpos (hweight i) (hconstraint i)
  have hsquare :=
    _root_.GD.N0232.N0720.N1139.d017227
      s packet delta weight hweight q hqFinite
  unfold _root_.GD.N0232.N0720.N1139.d017226 at hsquare
  unfold _root_.GD.N0232.N0720.N1140.d017265
  linarith




theorem d017270
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight +
        ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 ≤
      ‖q‖ ^ 2 := by
  have hqFinite :=
    _root_.GD.N0232.N0720.N1139.d017220
      s packet delta q hq
  have hriskCap : ∀ i,
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016414 packet i) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
        _root_.GD.N0232.N0720.N1126.d016431 s packet i + (delta : ℝ) := by
    intro i
    change (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega *
        (q omega - (packet i).location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
      (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal + (delta : ℝ)
    rw [← _root_.GD.N0232.N0720.N1126.d016430
      (packet i) q (hqFinite i)]
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2
        ⟨s.finiteRisk (packet i), ENNReal.coe_ne_top⟩)
      (hq i)
    rw [ENNReal.toReal_add (s.finiteRisk (packet i)) ENNReal.coe_ne_top,
      ENNReal.coe_toReal] at hreal
    exact hreal
  have hreserve := _root_.GD.N0230.N0617.d000190
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet)
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016431 s packet i + (delta : ℝ))
      (fun omega ↦ q omega) hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)
      (_root_.GD.N0232.N0720.N1126.d016421 packet)
      (_root_.GD.N0232.N0720.N1126.d016422 packet)
      (Lp.aestronglyMeasurable q) (Lp.memLp q).integrable_sq
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
        (packet i) q (hqFinite i)) hriskCap
  rw [_root_.GD.N0232.N0720.N1140.d017266,
    ← _root_.GD.N0232.N0720.N1140.d017267 q] at hreserve
  change _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight +
      (∫ omega,
        (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤ ‖q‖ ^ 2 at hreserve
  rw [← _root_.GD.N0232.N0720.N1140.d017268
    packet weight hweight q] at hreserve
  exact hreserve




theorem d017271
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight +
        ‖q - _root_.GD.N0232.N0720.N1139.d017218 s packet delta‖ ^ 2 +
        ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          (_root_.GD.N0232.N0720.N1139.d017218 s packet delta omega -
            _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n ≤
      ‖q‖ ^ 2 := by
  let p := _root_.GD.N0232.N0720.N1139.d017218 s packet delta
  have hpWitness : _root_.GD.N0230.N0685.d000511 (_root_.GD.N0232.N0720.N1139.d017214 s packet delta) 0 p :=
    _root_.GD.N0232.N0720.N1139.d017219 s packet delta
  have hdual := _root_.GD.N0232.N0720.N1140.d017269
    s packet delta weight hweight p hpWitness.1
  have htax := _root_.GD.N0230.N0685.d000512 hpWitness hq
  simp only [sub_zero] at htax
  dsimp only [p] at hdual htax ⊢
  linarith




theorem d017272
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight +
        ‖q - _root_.GD.N0232.N0720.N1139.d017218 s packet delta‖ ^ 2 +
        ‖_root_.GD.N0232.N0720.N1139.d017218 s packet delta -
          _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 ≤
      ‖q‖ ^ 2 := by
  let p := _root_.GD.N0232.N0720.N1139.d017218 s packet delta
  have hpWitness : _root_.GD.N0230.N0685.d000511 (_root_.GD.N0232.N0720.N1139.d017214 s packet delta) 0 p :=
    _root_.GD.N0232.N0720.N1139.d017219 s packet delta
  have hdual := _root_.GD.N0232.N0720.N1140.d017270
    s packet delta weight hweight p hpWitness.1
  have htax := _root_.GD.N0230.N0685.d000512 hpWitness hq
  simp only [sub_zero] at htax
  dsimp only [p] at hdual htax ⊢
  linarith



theorem d017273
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    ‖q - _root_.GD.N0232.N0720.N1139.d017218 s packet delta‖ ^ 2 +
        ‖_root_.GD.N0232.N0720.N1139.d017218 s packet delta -
          _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 ≤
      ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight := by
  have h :=
    _root_.GD.N0232.N0720.N1140.d017272
      s packet delta weight hweight q hq
  linarith



theorem d017274
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    ‖_root_.GD.N0232.N0720.N1139.d017218 s packet delta -
        _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 ≤
      ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight := by
  have h := _root_.GD.N0232.N0720.N1140.d017273
    s packet delta weight hweight q hq
  nlinarith [sq_nonneg
    ‖q - _root_.GD.N0232.N0720.N1139.d017218 s packet delta‖]





theorem d017275
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hcompletion :
      _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight ∈
        _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    2 * ‖_root_.GD.N0232.N0720.N1139.d017218 s packet delta -
        _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight‖ ^ 2 -
        _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight := by
  have h := _root_.GD.N0232.N0720.N1140.d017273
    s packet delta weight hweight
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) hcompletion
  simpa only [norm_sub_rev, two_mul] using h



theorem d017276
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    ‖_root_.GD.N0232.N0720.N1139.d017218 s packet delta -
        _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ≤
      Real.sqrt
        (‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight) := by
  have hsq := _root_.GD.N0232.N0720.N1140.d017274
    s packet delta weight hweight q hq
  have hgapNonneg :
      0 ≤ ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1140.d017265 s packet delta weight :=
    (sq_nonneg _).trans hsq
  rw [← Real.sqrt_sq (norm_nonneg _), Real.sqrt_le_sqrt_iff hgapNonneg]
  exact hsq

end

end N1140
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1140.d017269
#print axioms _root_.GD.N0232.N0720.N1140.d017270
#print axioms _root_.GD.N0232.N0720.N1140.d017272
#print axioms _root_.GD.N0232.N0720.N1140.d017274
#print axioms _root_.GD.N0232.N0720.N1140.d017275
