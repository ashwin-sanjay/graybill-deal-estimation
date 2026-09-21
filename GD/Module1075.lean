import GD.Module0017
import GD.Module1074
import Mathlib.Analysis.Convex.Mul


























open Filter MeasureTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1139

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0614
open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0685
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1133
open _root_.GD.N0232.N0720.N1137
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159

variable {m n k : ℕ}




def d017211
    (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {q | ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≠ ⊤}


theorem d017212
    (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) :
    Convex ℝ (_root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet) := by
  intro q hq r hr a b ha hb hab i
  have hraw := _root_.GD.N0230.N0602.d000121
    (_root_.GD.N0232.N0720.N1080.d014173 m n (packet i))
    (packet i).location q r ha hb hab
  change _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) (a • q + b • r) ≤
    ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q +
      ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r at hraw
  have hrhs :
      ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q +
          ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq i),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hr i)⟩
  exact ne_top_of_le_ne_top hrhs hraw



theorem d017213
    (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) (i : Fin k) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet)
      (fun q ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal) := by
  refine ⟨_root_.GD.N0232.N0720.N1139.d017212 packet, ?_⟩
  intro q hq r hr a b ha hb hab
  have hraw := _root_.GD.N0230.N0602.d000121
    (_root_.GD.N0232.N0720.N1080.d014173 m n (packet i))
    (packet i).location q r ha hb hab
  change _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) (a • q + b • r) ≤
    ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q +
      ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r at hraw
  have hright :
      ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q +
          ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq i),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hr i)⟩
  have hreal := ENNReal.toReal_mono hright hraw
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq i))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hr i)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at hreal
  exact hreal



def d017214
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {q | ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≤
    _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value + (delta : ENNReal)}

theorem d017215
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) :
    IsClosed (_root_.GD.N0232.N0720.N1139.d017214 s packet delta) := by
  simpa [_root_.GD.N0232.N0720.N1139.d017214, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun i : Fin k ↦ _root_.GD.N0232.N0720.N1080.d014171 m n (packet i))
      (fun i : Fin k ↦ (packet i).location)
      (fun i : Fin k ↦
        _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value + (delta : ENNReal))
      (fun i : Fin k ↦
        _root_.GD.N0232.N0720.N1080.d014173 m n (packet i)))

theorem d017216
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) :
    Convex ℝ (_root_.GD.N0232.N0720.N1139.d017214 s packet delta) := by
  simpa [_root_.GD.N0232.N0720.N1139.d017214, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun i : Fin k ↦ _root_.GD.N0232.N0720.N1080.d014171 m n (packet i))
      (fun i : Fin k ↦ (packet i).location)
      (fun i : Fin k ↦
        _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value + (delta : ENNReal))
      (fun i : Fin k ↦
        _root_.GD.N0232.N0720.N1080.d014173 m n (packet i)))

theorem d017217
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) :
    (_root_.GD.N0232.N0720.N1139.d017214 s packet delta).Nonempty := by
  refine ⟨s.value, ?_⟩
  intro i
  exact le_add_of_nonneg_right bot_le


noncomputable def d017218
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  Classical.choose <| _root_.GD.N0230.N0685.d000521
    (_root_.GD.N0232.N0720.N1139.d017217 s packet delta)
    (_root_.GD.N0232.N0720.N1139.d017215 s packet delta).isComplete
    (_root_.GD.N0232.N0720.N1139.d017216 s packet delta) 0

theorem d017219
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) :
    _root_.GD.N0230.N0685.d000511 (_root_.GD.N0232.N0720.N1139.d017214 s packet delta) 0
      (_root_.GD.N0232.N0720.N1139.d017218 s packet delta) :=
  Classical.choose_spec <| _root_.GD.N0230.N0685.d000521
    (_root_.GD.N0232.N0720.N1139.d017217 s packet delta)
    (_root_.GD.N0232.N0720.N1139.d017215 s packet delta).isComplete
    (_root_.GD.N0232.N0720.N1139.d017216 s packet delta) 0


theorem d017220
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta) :
    q ∈ _root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet := by
  intro i
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨s.finiteRisk (packet i), ENNReal.coe_ne_top⟩)
    (hq i)





def d017221
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (i : Fin k)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal -
    (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ)

theorem d017222
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (i : Fin k) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet)
      (_root_.GD.N0232.N0720.N1139.d017221 s packet delta i) := by
  refine ⟨_root_.GD.N0232.N0720.N1139.d017212 packet, ?_⟩
  intro q hq r hr a b ha hb hab
  have hconv := (_root_.GD.N0232.N0720.N1139.d017213 packet i).2
    hq hr ha hb hab
  change
    (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) (a • q + b • r)).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ) ≤
      a * ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ)) +
        b * ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ))
  calc
    _ ≤ a * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal +
          b * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ) := by
      exact sub_le_sub_right
        (sub_le_sub_right hconv
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal) (delta : ℝ)
    _ = a * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal +
          b * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r).toReal -
          (a + b) * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
          (a + b) * (delta : ℝ) := by rw [hab]; ring
    _ = _ := by ring



theorem d017223
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : q ∈ _root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet) :
    q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta ↔
      ∀ i, _root_.GD.N0232.N0720.N1139.d017221 s packet delta i q ≤ 0 := by
  constructor
  · intro hq i
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2
        ⟨s.finiteRisk (packet i), ENNReal.coe_ne_top⟩)
      (hq i)
    rw [ENNReal.toReal_add (s.finiteRisk (packet i)) ENNReal.coe_ne_top]
      at hreal
    simpa [_root_.GD.N0232.N0720.N1139.d017221, ENNReal.coe_toReal, add_comm] using hreal
  · intro hconstraint i
    apply (ENNReal.toReal_le_toReal
      (hqFinite i)
      (ENNReal.add_ne_top.2
        ⟨s.finiteRisk (packet i), ENNReal.coe_ne_top⟩)).1
    rw [ENNReal.toReal_add (s.finiteRisk (packet i)) ENNReal.coe_ne_top]
    rw [ENNReal.coe_toReal]
    have hi := hconstraint i
    dsimp only [_root_.GD.N0232.N0720.N1139.d017221] at hi
    linarith

private theorem d017224
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖q‖ ^ 2 = ∫ omega, (q omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [← real_inner_self_eq_norm_sq q, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with omega
  simp only [RCLike.inner_apply, conj_trivial, pow_two]




theorem d017225
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : Fin k → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : q ∈ _root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet) :
    ‖q‖ ^ 2 -
        (_root_.GD.N0232.N0720.N1126.d016432 s packet weight +
          ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
            (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∑ i, weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal) := by
  have hexact :=
    _root_.GD.N0230.N0617.d000188
      (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) (_root_.GD.N0232.N0720.N1126.d016431 s packet)
        (fun omega ↦ q omega) hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
        (_root_.GD.N0232.N0720.N1126.d016420 packet)
        (_root_.GD.N0232.N0720.N1126.d016421 packet)
        (_root_.GD.N0232.N0720.N1126.d016422 packet)
        (Lp.memLp q).integrable_sq
        (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
          (packet i) q (hqFinite i))
  rw [← _root_.GD.N0232.N0720.N1139.d017224 q] at hexact
  have hriskEq (i : Fin k) :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016414 packet i) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal := by
    exact (_root_.GD.N0232.N0720.N1126.d016430
      (packet i) q (hqFinite i)).symm
  simp_rw [hriskEq] at hexact
  simpa only [_root_.GD.N0232.N0720.N1126.d016432, _root_.GD.N0232.N0720.N1126.d016415,
    _root_.GD.N0232.N0720.N1126.d016416, _root_.GD.N0232.N0720.N1126.d016431] using hexact


def d017226
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ‖q‖ ^ 2 + ∑ i, weight i *
    _root_.GD.N0232.N0720.N1139.d017221 s packet delta i q


theorem d017227
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (weight : Fin k → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : q ∈ _root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet) :
    _root_.GD.N0232.N0720.N1139.d017226 s packet delta weight q =
      _root_.GD.N0232.N0720.N1126.d016432 s packet weight -
        (delta : ℝ) * ∑ i, weight i +
          ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
            (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have hexact :=
    _root_.GD.N0232.N0720.N1139.d017225
      s packet weight hweight q hqFinite
  unfold _root_.GD.N0232.N0720.N1139.d017226 _root_.GD.N0232.N0720.N1139.d017221
  have hsum :
      (∑ i, weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ))) =
        -(∑ i, weight i *
          ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
            (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal)) -
          (delta : ℝ) * ∑ i, weight i := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  linarith

private theorem d017228
    (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet)
      (fun q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦ ‖q‖ ^ 2) := by
  have hnorm : ConvexOn ℝ Set.univ
      (fun q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦ ‖q‖) :=
    convexOn_univ_norm
  have hsq : ConvexOn ℝ Set.univ
      (fun q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦ ‖q‖ ^ (2 : ℕ)) := by
    exact hnorm.pow (fun q _ ↦ norm_nonneg q) 2
  exact hsq.subset (Set.subset_univ _)
    (_root_.GD.N0232.N0720.N1139.d017212 packet)










theorem d017229
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (hdelta : 0 < delta) :
    ∃ (weight : Fin k → ℝ) (hweight : ∀ i, 0 ≤ weight i),
      _root_.GD.N0232.N0720.N1139.d017218 s packet delta =
          _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight ∧
      _root_.GD.N0232.N0720.N1126.d016432 s packet weight =
        ‖_root_.GD.N0232.N0720.N1139.d017218 s packet delta‖ ^ 2 +
          (delta : ℝ) * ∑ i, weight i ∧
      ∑ i, weight i *
        _root_.GD.N0232.N0720.N1139.d017221 s packet delta i
          (_root_.GD.N0232.N0720.N1139.d017218 s packet delta) = 0 := by
  let D : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
    _root_.GD.N0232.N0720.N1139.d017211 (m := m) (n := n) packet
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1139.d017218 s packet delta
  have hpWitness :
      _root_.GD.N0230.N0685.d000511 (_root_.GD.N0232.N0720.N1139.d017214 s packet delta) 0 p :=
    _root_.GD.N0232.N0720.N1139.d017219 s packet delta
  have hpFinite : p ∈ D := by
    exact _root_.GD.N0232.N0720.N1139.d017220
      s packet delta p hpWitness.1
  have hobjective : ConvexOn ℝ D
      (fun q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦ ‖q‖ ^ 2) := by
    exact _root_.GD.N0232.N0720.N1139.d017228 packet
  have hlower : ∀ q ∈ D,
      (∀ i, _root_.GD.N0232.N0720.N1139.d017221 s packet delta i q ≤ 0) →
        ‖p‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    intro q hqFinite hqConstraint
    have hqCap : q ∈ _root_.GD.N0232.N0720.N1139.d017214 s packet delta :=
      (_root_.GD.N0232.N0720.N1139.d017223
        s packet delta q hqFinite).2 hqConstraint
    have htax := _root_.GD.N0230.N0685.d000512 hpWitness hqCap
    simp only [sub_zero] at htax
    linarith [sq_nonneg ‖q - p‖]
  have hslater : ∃ q ∈ D,
      ∀ i, _root_.GD.N0232.N0720.N1139.d017221 s packet delta i q < 0 := by
    refine ⟨s.value, ?_, ?_⟩
    · intro i
      exact s.finiteRisk (packet i)
    · intro i
      have hdeltaReal : 0 < (delta : ℝ) := NNReal.coe_pos.2 hdelta
      simp only [_root_.GD.N0232.N0720.N1139.d017221, sub_self, zero_sub]
      exact neg_lt_zero.mpr hdeltaReal
  obtain ⟨weight, hweight, hcertificate⟩ :=
    _root_.GD.N0230.N0614.d000150
      D (fun q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦ ‖q‖ ^ 2)
        (_root_.GD.N0232.N0720.N1139.d017221 s packet delta)
        (_root_.GD.N0232.N0720.N1139.d017212 packet) hobjective
        (fun i ↦ _root_.GD.N0232.N0720.N1139.d017222 s packet delta i)
        (‖p‖ ^ 2) hlower hslater
  let r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight
  have hrFinite : r ∈ D := by
    intro i
    exact _root_.GD.N0232.N0720.N1126.d016428 packet weight hweight
      (packet i)
  have hpCertificate :
      ‖p‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1139.d017226 s packet delta weight p := by
    exact hcertificate p hpFinite
  have hrCertificate :
      ‖p‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1139.d017226 s packet delta weight r := by
    exact hcertificate r hrFinite
  have hpConstraint :
      ∀ i, _root_.GD.N0232.N0720.N1139.d017221 s packet delta i p ≤ 0 :=
    (_root_.GD.N0232.N0720.N1139.d017223
      s packet delta p hpFinite).1 hpWitness.1
  have hpLagrangian_le :
      _root_.GD.N0232.N0720.N1139.d017226 s packet delta weight p ≤ ‖p‖ ^ 2 := by
    have hsum :
        (∑ i, weight i * _root_.GD.N0232.N0720.N1139.d017221 s packet delta i p) ≤ 0 := by
      exact Finset.sum_nonpos fun i _ ↦
        mul_nonpos_of_nonneg_of_nonpos (hweight i) (hpConstraint i)
    unfold _root_.GD.N0232.N0720.N1139.d017226
    linarith
  have hrDistanceZero :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (r omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [_root_.GD.N0232.N0720.N1126.d016427
      packet weight hweight] with omega homega
    dsimp only [r] at homega ⊢
    change _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight omega -
        _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2 = (0 : ℝ)
    rw [homega]
    ring
  have hpSquare :=
    _root_.GD.N0232.N0720.N1139.d017227
      s packet delta weight hweight p hpFinite
  have hrSquare :=
    _root_.GD.N0232.N0720.N1139.d017227
      s packet delta weight hweight r hrFinite
  have hpDistanceNonneg :
      0 ≤ ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (p omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_nonneg
    intro omega
    exact mul_nonneg
      (zero_le_one.trans
        (_root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
          hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) omega))
      (sq_nonneg _)
  have hrLagrangian_le_hpLagrangian :
      _root_.GD.N0232.N0720.N1139.d017226 s packet delta weight r ≤
        _root_.GD.N0232.N0720.N1139.d017226 s packet delta weight p := by
    rw [hpSquare, hrSquare, hrDistanceZero, add_zero]
    linarith
  have hrLagrangian_eq :
      _root_.GD.N0232.N0720.N1139.d017226 s packet delta weight r = ‖p‖ ^ 2 := by
    apply le_antisymm
    · exact hrLagrangian_le_hpLagrangian.trans hpLagrangian_le
    · exact hrCertificate
  have hpLagrangian_eq :
      _root_.GD.N0232.N0720.N1139.d017226 s packet delta weight p = ‖p‖ ^ 2 := by
    apply le_antisymm hpLagrangian_le
    exact hpCertificate
  have hpDistanceZero :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (p omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 0 := by
    rw [hpSquare] at hpLagrangian_eq
    rw [hrSquare, hrDistanceZero, add_zero] at hrLagrangian_eq
    linarith
  have hpDistanceIntegrable : Integrable
      (fun omega ↦ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (p omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    exact _root_.GD.N0230.N0617.d000185
      (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) (fun omega ↦ p omega)
        hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
        (_root_.GD.N0232.N0720.N1126.d016420 packet)
        (_root_.GD.N0232.N0720.N1126.d016421 packet)
        (Lp.memLp p).integrable_sq
        (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
          (packet i) p (hpFinite i))
  have hpDistanceZeroAE :
      (fun omega ↦ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (p omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2)
        =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun omega ↦ mul_nonneg
        (zero_le_one.trans
          (_root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
            hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) omega))
        (sq_nonneg _)) hpDistanceIntegrable).1 hpDistanceZero
  have hprojection : p = r := by
    apply Lp.ext
    filter_upwards [hpDistanceZeroAE,
      _root_.GD.N0232.N0720.N1126.d016427 packet weight hweight]
        with omega hzero hcompletion
    dsimp only [r] at hcompletion ⊢
    have hmass : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
      _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
    have hsq :
        (p omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2 = 0 := by
      change _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          (p omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2 = 0
        at hzero
      exact (mul_eq_zero.mp hzero).resolve_left
        (ne_of_gt (zero_lt_one.trans_le hmass))
    rw [hcompletion]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hreserve :
      _root_.GD.N0232.N0720.N1126.d016432 s packet weight =
        ‖p‖ ^ 2 + (delta : ℝ) * ∑ i, weight i := by
    rw [hrSquare, hrDistanceZero, add_zero] at hrLagrangian_eq
    linarith
  have hcomplementarity :
      ∑ i, weight i * _root_.GD.N0232.N0720.N1139.d017221 s packet delta i p = 0 := by
    unfold _root_.GD.N0232.N0720.N1139.d017226 at hpLagrangian_eq
    linarith
  refine ⟨weight, hweight, ?_, hreserve, hcomplementarity⟩
  simpa only [p, r] using hprojection






theorem d017230
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (hdelta : 0 < delta) :
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1130.d017075 m n candidate =
          _root_.GD.N0232.N0720.N1139.d017218 s packet delta ∧
      _root_.GD.N0232.N0720.N1130.d017075 m n candidate ∈
          _root_.GD.N0232.N0720.N1139.d017214 s packet delta ∧
      _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight =
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ ^ 2 +
          (delta : ℝ) * ∑ i, candidate.weight i ∧
      _root_.GD.N0232.N0720.N1130.d017077 m n s candidate = 0 := by
  obtain ⟨weight, hweight, hprojection, hreserve, _hcomplementarity⟩ :=
    _root_.GD.N0232.N0720.N1139.d017229
      s packet delta hdelta
  let candidate : _root_.GD.N0232.N0720.N1130.d017074 :=
    { width := k
      packet := packet
      weight := weight
      weight_nonneg := hweight }
  have hcompletion : _root_.GD.N0232.N0720.N1130.d017075 m n candidate =
      _root_.GD.N0232.N0720.N1139.d017218 s packet delta := by
    dsimp only [candidate, _root_.GD.N0232.N0720.N1130.d017075]
    exact hprojection.symm
  refine ⟨candidate, hcompletion, ?_, ?_, ?_⟩
  · rw [hcompletion]
    exact (_root_.GD.N0232.N0720.N1139.d017219
      s packet delta).1
  · simpa only [candidate, hcompletion] using hreserve
  · have hmass : 0 ≤ (delta : ℝ) * ∑ i, candidate.weight i := by
      exact mul_nonneg delta.coe_nonneg
        (Finset.sum_nonneg fun i _ ↦ candidate.weight_nonneg i)
    unfold _root_.GD.N0232.N0720.N1130.d017077
    rw [show _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight =
      ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ ^ 2 +
        (delta : ℝ) * ∑ i, candidate.weight i by
          simpa only [candidate, hcompletion] using hreserve]
    exact max_eq_right (by linarith)


def d017231 (N : ℕ) : Fin N → _root_.GD.N0232.N0720.N1080.d014168 :=
  fun i ↦ _root_.GD.N0232.N0720.N1133.d016566 i


def d017232
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1139.d017218 s (_root_.GD.N0232.N0720.N1139.d017231 N)
    (_root_.GD.N0232.N0720.N1137.d017205 N)

theorem d017233 (N : ℕ) :
    0 < _root_.GD.N0232.N0720.N1137.d017205 N := by
  apply NNReal.coe_pos.1
  simp only [_root_.GD.N0232.N0720.N1137.d017205, _root_.GD.N0232.N0720.N1137.d017203]
  exact one_div_pos.mpr (by positivity)



theorem d017234
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1130.d017075 m n candidate =
          _root_.GD.N0232.N0720.N1139.d017232 s N ∧
      (∀ i, i < N →
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i)
            (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i) s.value +
            _root_.GD.N0232.N0720.N1137.d017205 N) ∧
      _root_.GD.N0232.N0720.N1130.d017077 m n s candidate = 0 := by
  obtain ⟨candidate, hcompletion, hcap, _hreserve, hradial⟩ :=
    _root_.GD.N0232.N0720.N1139.d017230
      s (_root_.GD.N0232.N0720.N1139.d017231 N) (_root_.GD.N0232.N0720.N1137.d017205 N)
        (_root_.GD.N0232.N0720.N1139.d017233 N)
  refine ⟨candidate, ?_, ?_, hradial⟩
  · simpa only [_root_.GD.N0232.N0720.N1139.d017232] using hcompletion
  · intro i hi
    exact hcap ⟨i, hi⟩




def d017235
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ N : ℕ,
    ‖_root_.GD.N0232.N0720.N1146.d015228 m n
          (_root_.GD.N0232.N0720.N1139.d017232 s N) -
        _root_.GD.N0232.N0720.N1139.d017232 s N‖ ≤
      _root_.GD.N0232.N0720.N1137.d017203 N ∧
    ‖_root_.GD.N0232.N0720.N1146.d015229 m n
          (_root_.GD.N0232.N0720.N1139.d017232 s N) -
        _root_.GD.N0232.N0720.N1139.d017232 s N‖ ≤
      _root_.GD.N0232.N0720.N1137.d017203 N




theorem d017236
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hresidual : _root_.GD.N0232.N0720.N1139.d017235 s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1137.d017209
    hm hn s hstrict
  intro N
  obtain ⟨candidate, hcompletion, hcap, hradial⟩ :=
    _root_.GD.N0232.N0720.N1139.d017234 s N
  refine ⟨candidate, hcap, ?_, ?_, ?_⟩
  · rw [hradial]
    exact _root_.GD.N0232.N0720.N1137.d017204 N
  · unfold _root_.GD.N0232.N0720.N1130.d017078
    rw [hcompletion]
    exact (hresidual N).1
  · unfold _root_.GD.N0232.N0720.N1130.d017079
    rw [hcompletion]
    exact (hresidual N).2

end

end N1139
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1139.d017229
#print axioms _root_.GD.N0232.N0720.N1139.d017230
#print axioms _root_.GD.N0232.N0720.N1139.d017234
#print axioms _root_.GD.N0232.N0720.N1139.d017236
