import GD.Module0766
import GD.Module0737
import GD.Module0148





































open Filter Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0821

noncomputable section

open _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0810
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0671

variable {k : ℕ} {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [MetricSpace W]





theorem d011675
    {traceP traceQ : W} {taxSeq : ℕ → ℝ}
    (charge : W → W → ℝ)
    (hchargeNonnegative : 0 ≤ charge traceP traceQ)
    (hchargeFaithful : charge traceP traceQ = 0 → traceP = traceQ)
    (hlower : ∀ r : ℝ, r < charge traceP traceQ →
      ∀ᶠ n in atTop, r ≤ taxSeq n)
    (hzero : Tendsto taxSeq atTop (nhds 0)) :
    traceP = traceQ := by
  by_cases hcharge : charge traceP traceQ = 0
  · exact hchargeFaithful hcharge
  · have hpos : 0 < charge traceP traceQ :=
      lt_of_le_of_ne hchargeNonnegative (Ne.symm hcharge)
    let r : ℝ := charge traceP traceQ / 2
    have hrpos : 0 < r := by
      dsimp [r]
      positivity
    have hrlt : r < charge traceP traceQ := by
      dsimp [r]
      linarith
    have hbelow : ∀ᶠ n in atTop, r ≤ taxSeq n := hlower r hrlt
    have habove : ∀ᶠ n in atTop, taxSeq n < r :=
      (tendsto_order.1 hzero).2 r hrpos
    obtain ⟨n, hnLower, hnUpper⟩ := (hbelow.and habove).exists
    exact False.elim ((not_lt_of_ge hnLower) hnUpper)




theorem d011676
    {traceP traceQ : W} {taxSeq : ℕ → ℝ}
    (hlower : ∀ r : ℝ, r < dist traceP traceQ ^ 2 →
      ∀ᶠ n in atTop, r ≤ taxSeq n)
    (hzero : Tendsto taxSeq atTop (nhds 0)) :
    traceP = traceQ := by
  apply _root_.GD.N0232.N0719.N0821.d011675
    (fun x y : W ↦ dist x y ^ 2)
  · exact sq_nonneg _
  · intro hzeroDist
    exact eq_of_dist_eq_zero (sq_eq_zero_iff.mp hzeroDist)
  · exact hlower
  · exact hzero




def d011677
    (active : Finset (Fin k))
    (tax : ∀ c : _root_.GD.N0232.N0719.N0809.d010964 k,
      _root_.GD.N0232.N0719.N0810.d011629 k c → V → V → ℝ)
    (trace : V → W) (p q : V) : Prop :=
  ∀ thetaSeq : ∀ depth : ℕ,
      _root_.GD.N0232.N0719.N0810.d011629 k (active, depth),
    Tendsto
        (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq depth).1)
        atTop (nhds 0) →
    ∀ r : ℝ, r < dist (trace p) (trace q) ^ 2 →
      ∀ᶠ depth in atTop,
        r ≤ tax (active, depth) (thetaSeq depth) p q






def d011678
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k))
    (trace : _root_.GD.N0232.N0719.N0816.d010975 k sizes → W)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : Prop :=
  _root_.GD.N0232.N0719.N0821.d011677 active
    (fun _c theta p q ↦
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
    trace p q





theorem d011679
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hpq : p ≠ q) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q := by
  let energy : ℝ≥0∞ :=
    _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)
  have hparameter := _root_.GD.N0232.N0719.N0859.d010814 k sizes theta
  have hreference :=
    (_root_.GD.N0232.N0719.d009183
      k sizes theta.location theta.scale theta.scale_pos).2
  have henergyPos : 0 < energy := by
    exact _root_.GD.N0230.N0671.d001651
      hparameter hreference hpq
  have hpTop : _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p ≠ ⊤ :=
    _root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hp theta
  have hqTop : _root_.GD.N0232.N0719.N0859.d010821 k sizes theta q ≠ ⊤ :=
    _root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hq theta
  have hpTop' :
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location p ≠ ⊤ := hpTop
  have hqTop' :
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location q ≠ ⊤ := hqTop
  have hEq := _root_.GD.N0230.N0670.d001647
    hparameter theta.location p q
  have henergyTop : energy ≠ ⊤ := by
    have hle : energy ≤
        ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117
              (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
              (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location p +
          ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117
              (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
              (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location q := by
      dsimp [energy]
      rw [← hEq]
      exact le_add_left le_rfl
    apply ne_top_of_le_ne_top _ hle
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpTop',
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqTop'⟩
  unfold _root_.GD.N0232.N0719.N0811.d011037
  exact div_pos
    (ENNReal.toReal_pos henergyPos.ne' henergyTop)
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta)






theorem d011680
    (active : Finset (Fin k))
    (tax : ∀ c : _root_.GD.N0232.N0719.N0809.d010964 k,
      _root_.GD.N0232.N0719.N0810.d011629 k c → V → V → ℝ)
    (trace : V → W) {p q : V}
    (hobservable : _root_.GD.N0232.N0719.N0821.d011677 active tax trace p q)
    (thetaSeq : ∀ depth : ℕ,
      _root_.GD.N0232.N0719.N0810.d011629 k (active, depth))
    (hface : Tendsto
      (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq depth).1)
      atTop (nhds 0))
    (hzero : Tendsto
      (fun depth ↦ tax (active, depth) (thetaSeq depth) p q)
      atTop (nhds 0)) :
    trace p = trace q := by
  exact _root_.GD.N0232.N0719.N0821.d011676
    (hobservable thetaSeq hface) hzero


theorem d011681
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k))
    (trace : _root_.GD.N0232.N0719.N0816.d010975 k sizes → W)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hobservable : _root_.GD.N0232.N0719.N0821.d011678
      k sizes hk hsizes active trace p q)
    (thetaSeq : ∀ depth : ℕ,
      _root_.GD.N0232.N0719.N0810.d011629 k (active, depth))
    (hface : Tendsto
      (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq depth).1)
      atTop (nhds 0))
    (hzero : Tendsto
      (fun depth ↦ _root_.GD.N0232.N0719.N0811.d011037
        k sizes hk hsizes (thetaSeq depth).1 p q)
      atTop (nhds 0)) :
    trace p = trace q := by
  exact _root_.GD.N0232.N0719.N0821.d011680
    active
    (fun _c theta p q ↦
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
    trace hobservable thetaSeq hface hzero







theorem d011682
    (hk0 : 0 < k)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, _root_.GD.N0232.N0719.N0810.d011629 k c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, _root_.GD.N0232.N0719.N0810.d011629 k c → V → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n,
      Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k (schedule n)) →
      ∀ d, d ∈ face n →
        IsLUB
          (Set.range
            (fun theta : _root_.GD.N0232.N0719.N0810.d011629 k (schedule n) ↦
              profile (schedule n) theta d))
          (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hq : ∀ n, q ∈ face n)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2)
    {active : Finset (Fin k)} (hactive : active.Nonempty)
    (trace : V → W)
    (hobservable : _root_.GD.N0232.N0719.N0821.d011677 active tax trace p q) :
    trace p = trace q := by
  obtain ⟨thetaSeq, hface, hzero⟩ :=
    _root_.GD.N0232.N0719.N0810.d011642
      hk0 schedule hschedule profile objective tax C face htower hconvex
      hSup hp hq hTaxNonnegative hExact hactive
  exact _root_.GD.N0232.N0719.N0821.d011680
    active tax trace hobservable thetaSeq hface hzero










theorem d011683
    (hk0 : 0 < k)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, _root_.GD.N0232.N0719.N0810.d011629 k c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, _root_.GD.N0232.N0719.N0810.d011629 k c → V → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n,
      Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k (schedule n)) →
      ∀ d, d ∈ face n →
        IsLUB
          (Set.range
            (fun theta : _root_.GD.N0232.N0719.N0810.d011629 k (schedule n) ↦
              profile (schedule n) theta d))
          (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hq : ∀ n, q ∈ face n)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2)
    (trace : Finset (Fin k) → V → W)
    (hobservable : ∀ active, active.Nonempty →
      _root_.GD.N0232.N0719.N0821.d011677 active tax (trace active) p q)
    (hjoint : (∀ active, active.Nonempty →
      trace active p = trace active q) → p = q) :
    p = q := by
  apply hjoint
  intro active hactive
  exact _root_.GD.N0232.N0719.N0821.d011682
    hk0 schedule hschedule profile objective tax C face htower hconvex
    hSup hp hq hTaxNonnegative hExact hactive (trace active)
    (hobservable active hactive)

end

end N0821
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0821.d011676
#print axioms _root_.GD.N0232.N0719.N0821.d011675
#print axioms _root_.GD.N0232.N0719.N0821.d011679
#print axioms _root_.GD.N0232.N0719.N0821.d011680
#print axioms _root_.GD.N0232.N0719.N0821.d011681
#print axioms _root_.GD.N0232.N0719.N0821.d011682
#print axioms _root_.GD.N0232.N0719.N0821.d011683
