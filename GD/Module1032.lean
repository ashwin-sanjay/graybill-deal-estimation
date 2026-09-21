import GD.Module0017
import GD.Module1030
import GD.Module0935
import Mathlib.Analysis.Convex.Mul

















open Filter MeasureTheory Set
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1116

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0614
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1143
open _root_.GD.N0232.N0720.N1159

variable {m n : ℕ}
variable {ι : Type*}


def d016450 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) d ≠ ⊤}


def d016451
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (i : ι)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) d).toReal -
    (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ)


theorem d016452 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) :
    Convex ℝ (_root_.GD.N0232.N0720.N1116.d016450 (m := m) (n := n) packet) := by
  intro p hp q hq a b ha hb hab i
  have hraw := _root_.GD.N0230.N0602.d000121
    (_root_.GD.N0232.N0720.N1080.d014173 m n (packet i))
    (packet i).location p q ha hb hab
  change _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) (a • p + b • q) ≤
    ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p +
      ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q at hraw
  have hright :
      ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p +
          ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≠ ⊤ :=
    ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp i),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq i)⟩
  exact ne_top_of_le_ne_top hright hraw



theorem d016453
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (i : ι) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1116.d016450 (m := m) (n := n) packet)
      (_root_.GD.N0232.N0720.N1116.d016451 s packet delta i) := by
  refine ⟨_root_.GD.N0232.N0720.N1116.d016452 packet, ?_⟩
  intro p hp q hq a b ha hb hab
  have hraw := _root_.GD.N0230.N0602.d000121
    (_root_.GD.N0232.N0720.N1080.d014173 m n (packet i))
    (packet i).location p q ha hb hab
  change _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) (a • p + b • q) ≤
    ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p +
      ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q at hraw
  have hap : ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp i)
  have hbq : ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq i)
  have hreal :
      (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) (a • p + b • q)).toReal ≤
        a * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p).toReal +
          b * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal := by
    have htoReal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hap, hbq⟩) hraw
    rw [ENNReal.toReal_add hap hbq,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at htoReal
    exact htoReal
  unfold _root_.GD.N0232.N0720.N1116.d016451
  change
    (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) (a • p + b • q)).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ) ≤
      a * ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ)) +
        b * ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ))
  calc
    (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) (a • p + b • q)).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ) ≤
        (a * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p).toReal +
          b * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal) -
            (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ) := by
      linarith
    _ = a * ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ)) +
        b * ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ)) := by
      calc
        a * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p).toReal +
              b * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal -
                (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal - (delta : ℝ) =
            a * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) p).toReal +
              b * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal -
                (a + b) *
                  ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal + (delta : ℝ)) := by
          rw [hab]
          ring
        _ = _ := by ring


theorem d016454
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) :
    ConvexOn ℝ (_root_.GD.N0232.N0720.N1116.d016450 (m := m) (n := n) packet)
      (fun d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦ ‖d‖ ^ 2) := by
  refine ⟨_root_.GD.N0232.N0720.N1116.d016452 packet, ?_⟩
  intro p hp q hq a b ha hb hab
  change ‖a • p + b • q‖ ^ 2 ≤ a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2
  have hnorm : ‖a • p + b • q‖ ≤ a * ‖p‖ + b * ‖q‖ := by
    calc
      ‖a • p + b • q‖ ≤ ‖a • p‖ + ‖b • q‖ := norm_add_le _ _
      _ = a * ‖p‖ + b * ‖q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
  have hweighted_nonneg : 0 ≤ a * ‖p‖ + b * ‖q‖ :=
    add_nonneg (mul_nonneg ha (norm_nonneg p))
      (mul_nonneg hb (norm_nonneg q))
  have hnormsq :
      ‖a • p + b • q‖ ^ 2 ≤ (a * ‖p‖ + b * ‖q‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hweighted_nonneg).2 hnorm
  have hJensen :
      (a * ‖p‖ + b * ‖q‖) ^ 2 ≤
        a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2 := by
    nlinarith [mul_nonneg ha hb, sq_nonneg (‖p‖ - ‖q‖)]
  exact hnormsq.trans hJensen

variable [Fintype ι] [DecidableEq ι]




theorem d016455
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1126.d016432 s packet weight =
      ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight‖ ^ 2 +
        ∑ i, weight i *
          ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i)
              (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
                packet weight hweight)).toReal -
            (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal) := by
  let r := _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
    packet weight hweight
  have hrFinite : _root_.GD.N0232.N0720.N1159.d014637 m n r :=
    _root_.GD.N0232.N0720.N1126.d016428 packet weight hweight
  have hexact :=
    _root_.GD.N0230.N0617.d000188
      (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) (_root_.GD.N0232.N0720.N1126.d016431 s packet)
      (fun omega ↦ r omega) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)
      (_root_.GD.N0232.N0720.N1126.d016421 packet)
      (_root_.GD.N0232.N0720.N1126.d016422 packet)
      (Lp.memLp r).integrable_sq
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
        (packet i) r (hrFinite (packet i)))
  have hnorm :
      (∫ omega, (r omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = ‖r‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq r, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with omega
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  have hrisk (i : ι) :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega *
          (r omega - _root_.GD.N0232.N0720.N1126.d016414 packet i) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r).toReal :=
    (_root_.GD.N0232.N0720.N1126.d016430
      (packet i) r (hrFinite (packet i))).symm
  have hcompletion :=
    _root_.GD.N0232.N0720.N1126.d016427 (m := m) (n := n)
      packet weight hweight
  have hdistance :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          (r omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hcompletion] with omega homega
    change _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
      (r omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2 =
        (0 : ℝ)
    rw [homega]
    ring
  rw [hnorm] at hexact
  simp_rw [hrisk] at hexact
  change
    ‖r‖ ^ 2 -
        (_root_.GD.N0232.N0720.N1126.d016432 s packet weight +
          ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
            (r omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∑ i, weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r).toReal) at hexact
  rw [hdistance, add_zero] at hexact
  have hneg :
      (∑ i, weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r).toReal)) =
      -(∑ i, weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hneg] at hexact
  dsimp only [r] at hexact ⊢
  linarith




theorem d016456
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {a : ℝ} (ha : a < ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) :
    ∃ (k : ℕ) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) (weight : Fin k → ℝ),
      (∀ i, 0 ≤ weight i) ∧
        a < _root_.GD.N0232.N0720.N1126.d016432 s packet weight := by
  classical
  let projectionEnergy := ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2
  let b : ℝ := (a + projectionEnergy) / 2
  have hab : a < b := by dsimp only [b, projectionEnergy]; linarith
  have hb : b < ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
    dsimp only [b, projectionEnergy]
    linarith
  obtain ⟨F, delta, hdelta, hforce⟩ :=
    _root_.GD.N0232.N0720.N1143.d014680 m n s hb
  let e : Fin F.card ≃ ↑F := (Finset.equivFin F).symm
  let packet : Fin F.card → _root_.GD.N0232.N0720.N1080.d014168 := fun i ↦ (e i).1
  let D := _root_.GD.N0232.N0720.N1116.d016450 (m := m) (n := n) packet
  let objective : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → ℝ := fun d ↦ ‖d‖ ^ 2
  let constraint : Fin F.card → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → ℝ :=
    fun i ↦ _root_.GD.N0232.N0720.N1116.d016451 s packet delta i
  have hD : Convex ℝ D := _root_.GD.N0232.N0720.N1116.d016452 packet
  have hobjective : ConvexOn ℝ D objective :=
    _root_.GD.N0232.N0720.N1116.d016454 packet
  have hconstraint : ∀ i, ConvexOn ℝ D (constraint i) := by
    intro i
    exact _root_.GD.N0232.N0720.N1116.d016453 s packet delta i
  have hlower : ∀ d ∈ D, (∀ i, constraint i d ≤ 0) →
      b ≤ objective d := by
    intro d hd hfeasible
    have hrelaxed : ∀ theta ∈ F,
        _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (delta : ENNReal) := by
      intro theta htheta
      let i : Fin F.card := e.symm ⟨theta, htheta⟩
      have hi := hfeasible i
      have hdfinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≠ ⊤ := by
        simpa [D, _root_.GD.N0232.N0720.N1116.d016450, packet, i] using hd i
      have hrightfinite :
          _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (delta : ENNReal) ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨s.finiteRisk theta, ENNReal.coe_ne_top⟩
      apply (ENNReal.toReal_le_toReal hdfinite hrightfinite).mp
      rw [ENNReal.toReal_add (s.finiteRisk theta) ENNReal.coe_ne_top]
      simpa [constraint, _root_.GD.N0232.N0720.N1116.d016451, packet, i,
        add_comm] using hi
    exact (hforce d hrelaxed).le
  have hslater : ∃ d ∈ D, ∀ i, constraint i d < 0 := by
    refine ⟨s.value, ?_, ?_⟩
    · intro i
      exact s.finiteRisk (packet i)
    · intro i
      have hdeltaReal : 0 < (delta : ℝ) := by exact_mod_cast hdelta
      simp [constraint, _root_.GD.N0232.N0720.N1116.d016451, hdeltaReal]
  obtain ⟨weight, hweight, hcertificate⟩ :=
    _root_.GD.N0230.N0614.d000150
      D objective constraint hD hobjective hconstraint b hlower hslater
  let r := _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
    packet weight hweight
  have hrD : r ∈ D := by
    intro i
    exact _root_.GD.N0232.N0720.N1126.d016428 packet weight hweight (packet i)
  have hbound := hcertificate r hrD
  have hreserve :=
    _root_.GD.N0232.N0720.N1116.d016455
      s packet weight hweight
  have hlagrangian_le :
      objective r + ∑ i, weight i * constraint i r ≤
        _root_.GD.N0232.N0720.N1126.d016432 s packet weight := by
    rw [hreserve]
    dsimp only [objective]
    dsimp only [r]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hweight i)
    dsimp only [constraint, _root_.GD.N0232.N0720.N1116.d016451]
    exact sub_le_self _ (NNReal.coe_nonneg delta)
  refine ⟨F.card, packet, weight, hweight, ?_⟩
  exact hab.trans_le (hbound.trans hlagrangian_le)




theorem d016457
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ∃ (width : ℕ → ℕ)
        (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
        (weight : ∀ j, Fin (width j) → ℝ),
      (∀ j i, 0 ≤ weight j i) ∧
        Tendsto
          (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
            _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
          atTop (nhds 0) := by
  classical
  have hexists : ∀ j : ℕ,
      ∃ (k : ℕ) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) (weight : Fin k → ℝ),
        (∀ i, 0 ≤ weight i) ∧
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
              1 / ((j : ℝ) + 1) <
            _root_.GD.N0232.N0720.N1126.d016432 s packet weight := by
    intro j
    apply _root_.GD.N0232.N0720.N1116.d016456
    have hpos : 0 < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  choose width packet weight hweight hlower using hexists
  refine ⟨width, packet, weight, hweight, ?_⟩
  have hgap_nonneg : ∀ j,
      0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j) := by
    intro j
    have hweak := _root_.GD.N0232.N0720.N1126.d016437
      s (packet j) (weight j) (hweight j)
    nlinarith [sq_nonneg
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value -
        _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          (packet j) (weight j) (hweight j)‖]
  have hgap_upper : ∀ j,
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j) ≤
        1 / ((j : ℝ) + 1) := by
    intro j
    linarith [hlower j]
  exact squeeze_zero hgap_nonneg hgap_upper
    tendsto_one_div_add_atTop_nhds_zero_nat

end

end N1116
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1116.d016455
#print axioms _root_.GD.N0232.N0720.N1116.d016456
#print axioms _root_.GD.N0232.N0720.N1116.d016457
