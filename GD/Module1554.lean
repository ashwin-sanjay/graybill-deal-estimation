import GD.Module0017
import GD.Module0935
import GD.Module1077
import GD.Module1065
import GD.Module0244










set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0720.N1473
noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1126 _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1142
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0584
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0712
open _root_.GD.N0230.N0614

variable (m n : ℕ)


theorem d024007
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    {a : ℝ} (ha : a < ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2) :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (delta : NNReal), 0 < delta ∧
      ∀ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        (∀ theta ∈ F,
          _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤
            _root_.GD.N0232.N0720.N1080.d014182 m n theta s + (delta : ENNReal)) →
          a < ‖d‖ ^ 2 := by
  classical
  by_cases ha0 : a < 0
  · refine ⟨∅, 1, by norm_num, ?_⟩
    intro d hd
    exact ha0.trans_le (sq_nonneg ‖d‖)
  · have ha_nonneg : 0 ≤ a := le_of_not_gt ha0
    obtain ⟨F, hF⟩ :=
      _root_.GD.N0232.N0720.N1142.d014678 m n s ha
    let H := _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)
    let r : ℝ := Real.sqrt a
    let K : Set (WeakSpace ℝ H) :=
      toWeakSpace ℝ H '' Metric.closedBall (0 : H) r
    let packet : ↑F → _root_.GD.N0232.N0720.N1080.d014168 := fun i ↦ i.1
    let weakRisk : ↑F → WeakSpace ℝ H → ENNReal := fun i ↦
      _root_.GD.N0230.N0712.d001258 (_root_.GD.N0232.N0720.N1080.d014172 m n)
        (_root_.GD.N0232.N0720.N1080.d014171 m n (packet i)) (packet i).location
    let cap : ↑F → ENNReal := fun i ↦
      _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s
    have hKcompact : IsCompact K := by
      exact _root_.GD.N0230.N0633.d001199 (H := H) r
    have hweakRisk : ∀ i, LowerSemicontinuous (weakRisk i) := by
      intro i
      exact _root_.GD.N0230.N0712.d001260
        (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n (packet i))
        (_root_.GD.N0232.N0720.N1080.d014173 m n (packet i))
        (packet i).location
    have hdisjoint :
        Disjoint K
          (⋂ i, (weakRisk i) ⁻¹' Set.Iic (cap i)) := by
      rw [Set.disjoint_left]
      intro w hwK hwcap
      obtain ⟨d, hdball, rfl⟩ := hwK
      have hdcap : ∀ theta ∈ F,
          _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s := by
        intro theta htheta
        let i : ↑F := ⟨theta, htheta⟩
        have hi := Set.mem_iInter.mp hwcap i
        simpa [weakRisk, cap, packet, _root_.GD.N0230.N0712.d001258, _root_.GD.N0232.N0720.N1080.d014182, H, i] using hi
      have hstrict := hF d hdcap
      have hnorm : ‖d‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hdball
      have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg a
      have hr_sq : r ^ 2 = a := Real.sq_sqrt ha_nonneg
      have hsq : ‖d‖ ^ 2 ≤ r ^ 2 := by
        nlinarith [norm_nonneg d]
      linarith
    obtain ⟨delta, hdelta, hrelaxed⟩ :=
      _root_.GD.N0230.N0584.d000065
        K hKcompact weakRisk cap hweakRisk hdisjoint
    refine ⟨F, delta, hdelta, ?_⟩
    intro d hdcap
    by_contra hnot
    push Not at hnot
    have hnorm : ‖d‖ ≤ r := by
      have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg a
      have hr_sq : r ^ 2 = a := Real.sq_sqrt ha_nonneg
      nlinarith [norm_nonneg d]
    have hdK : toWeakSpace ℝ H d ∈ K := by
      exact ⟨d, by simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm, rfl⟩
    have hdrelaxed :
        toWeakSpace ℝ H d ∈
          ⋂ i, (weakRisk i) ⁻¹'
            Set.Iic (cap i + (delta : ENNReal)) := by
      apply Set.mem_iInter.2
      intro i
      have hi := hdcap (packet i) i.2
      simpa [weakRisk, cap, packet, _root_.GD.N0230.N0712.d001258, _root_.GD.N0232.N0720.N1080.d014182, H] using hi
    exact Set.disjoint_left.mp hrelaxed hdK hdrelaxed




def d024008 (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n) packet weight -
    ∑ i, weight i * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s).toReal



theorem d024009
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s)
    {a : ℝ} (ha : a < ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2) :
    ∃ C : _root_.GD.N0232.N0720.N1130.d017074,
      a < _root_.GD.N0232.N0720.N1473.d024008 m n s C.packet C.weight := by
  classical
  let b : ℝ := (a + ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2) / 2
  have hab : a < b := by dsimp only [b]; linarith
  have hb : b < ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2 := by
    dsimp only [b]; linarith
  obtain ⟨F, delta, hdelta, hforce⟩ :=
    _root_.GD.N0232.N0720.N1473.d024007 m n s hb
  let e : Fin F.card ≃ ↑F := (Finset.equivFin F).symm
  let packet : Fin F.card → _root_.GD.N0232.N0720.N1080.d014168 := fun i ↦ (e i).1
  let D := _root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0720.N1080.d014182 m n)
  let objective : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → ℝ := fun d ↦ ‖d‖ ^ 2
  let constraint : Fin F.card → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → ℝ :=
    fun i d ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) d).toReal -
      (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s).toReal - (delta : ℝ)
  have hcombo : ∀ θ p q a b, 0 ≤ a → 0 ≤ b → a + b = 1 →
      _root_.GD.N0232.N0720.N1080.d014182 m n θ (a • p + b • q) ≤
        ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014182 m n θ p + ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014182 m n θ q := by
    intro θ p q a b ha hb hab
    exact _root_.GD.N0230.N0602.d000121
      (_root_.GD.N0232.N0720.N1080.d014173 m n θ) θ.location p q ha hb hab
  have hD : Convex ℝ D :=
    _root_.GD.N0230.N0632.d003533
      (_root_.GD.N0232.N0720.N1080.d014182 m n) hcombo
  have hobjective : ConvexOn ℝ D objective := by
    have h := _root_.GD.N0230.N0632.d003534
      (_root_.GD.N0232.N0720.N1080.d014182 m n) hcombo _root_.GD.N0232.N0720.N1080.d014169
    simpa only [_root_.GD.N0232.N0720.N1080.d014190, ENNReal.toReal_ofReal (sq_nonneg _),
      zero_sub, norm_neg, objective] using h
  have hconstraint : ∀ i, ConvexOn ℝ D (constraint i) := by
    intro i
    exact ((_root_.GD.N0230.N0632.d003534
      (_root_.GD.N0232.N0720.N1080.d014182 m n) hcombo (packet i)).sub (concaveOn_const _ hD)).sub
        (concaveOn_const _ hD)
  have hlower : ∀ d ∈ D, (∀ i, constraint i d ≤ 0) → b ≤ objective d := by
    intro d hd hfeasible
    have hrelaxed : ∀ θ ∈ F,
        _root_.GD.N0232.N0720.N1080.d014182 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ s + (delta : ENNReal) := by
      intro θ hθ
      let i : Fin F.card := e.symm ⟨θ, hθ⟩
      have hi := hfeasible i
      apply (ENNReal.toReal_le_toReal (hd θ)
        (ENNReal.add_ne_top.mpr ⟨hs θ, ENNReal.coe_ne_top⟩)).mp
      rw [ENNReal.toReal_add (hs θ) ENNReal.coe_ne_top]
      simpa [constraint, packet, i, add_comm] using hi
    exact (hforce d hrelaxed).le
  have hslater : ∃ d ∈ D, ∀ i, constraint i d < 0 := by
    refine ⟨s, hs, ?_⟩
    intro i
    have hdeltaReal : 0 < (delta : ℝ) := by exact_mod_cast hdelta
    simp [constraint, hdeltaReal]
  obtain ⟨weight, hweight, hcertificate⟩ :=
    _root_.GD.N0230.N0614.d000150
      D objective constraint hD hobjective hconstraint b hlower hslater
  let r := _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet weight hweight
  have hrD : r ∈ D := _root_.GD.N0232.N0720.N1126.d016428 packet weight hweight
  have hbound := hcertificate r hrD
  have hminimum := _root_.GD.N0232.N0720.N1125.d017257
    (m := m) (n := n) packet weight hweight
  have hlagrangian_le :
      objective r + ∑ i, weight i * constraint i r ≤
        _root_.GD.N0232.N0720.N1473.d024008 m n s packet weight := by
    unfold _root_.GD.N0232.N0720.N1473.d024008
    rw [← hminimum]
    simp only [_root_.GD.N0232.N0720.N1125.d017249]
    have hsum : (∑ i, weight i * constraint i r) ≤
        (∑ i, weight i * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) r).toReal) -
          ∑ i, weight i * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s).toReal := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro i hi
      dsimp only [constraint]
      have h := mul_nonneg (hweight i) (NNReal.coe_nonneg delta)
      nlinarith
    dsimp only [objective, r] at hsum ⊢
    linarith
  exact ⟨⟨F.card, packet, weight, hweight⟩,
    hab.trans_le (hbound.trans hlagrangian_le)⟩

end
end GD.N0232.N0720.N1473

#print axioms _root_.GD.N0232.N0720.N1473.d024009
