import GD.Module0148
import GD.Module0067
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuity.Basic

























open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0230
namespace N0675

noncomputable section

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0671
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0625



section CommonSupport

variable {Omega Theta : Type*} [MeasurableSpace Omega]




def d001652
    {mu0 : Measure Omega} (mu : Measure Omega) (target : ℝ)
    (d : _root_.GD.N0230.N0602.d000116 mu0) : ℝ :=
  (_root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target d).toReal



def d001653
    {mu0 : Measure Omega} (mu : Measure Omega)
    (p q : _root_.GD.N0230.N0602.d000116 mu0) : ℝ :=
  (_root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal



theorem d001654
    {mu0 mu : Measure Omega} (hmu : mu ≪ mu0)
    (target : ℝ) (p q : _root_.GD.N0230.N0602.d000116 mu0)
    (hp : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target p ≠ ⊤)
    (hq : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target q ≠ ⊤) :
    _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0 (_root_.GD.N0230.N0670.d001646 p q) ≠ ⊤ := by
  have hEq :=
    _root_.GD.N0230.N0670.d001647 hmu target p q
  have hle :
      _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0 (_root_.GD.N0230.N0670.d001646 p q) ≤
        ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target p +
          ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target q := by
    rw [← hEq]
    exact le_add_left le_rfl
  apply ne_top_of_le_ne_top _ hle
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq⟩



theorem d001655
    {mu0 mu : Measure Omega} (hmu : mu ≪ mu0)
    (target : ℝ) (p q : _root_.GD.N0230.N0602.d000116 mu0)
    (hp : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target p ≠ ⊤)
    (hq : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target q ≠ ⊤) :
    _root_.GD.N0230.N0675.d001652 mu target (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0230.N0675.d001653 mu p q =
      (_root_.GD.N0230.N0675.d001652 mu target p +
        _root_.GD.N0230.N0675.d001652 mu target q) / 2 := by
  simpa [_root_.GD.N0230.N0675.d001652, _root_.GD.N0230.N0675.d001653] using
    _root_.GD.N0230.N0670.d001649
      hmu target p q hp hq



theorem d001656
    {mu0 mu : Measure Omega} (hmu : mu ≪ mu0) (hmu0 : mu0 ≪ mu)
    (target : ℝ) {p q : _root_.GD.N0230.N0602.d000116 mu0}
    (hp : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target p ≠ ⊤)
    (hq : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target q ≠ ⊤)
    (hpq : p ≠ q) :
    0 < _root_.GD.N0230.N0675.d001653 mu p q := by
  unfold _root_.GD.N0230.N0675.d001653
  exact ENNReal.toReal_pos
    (_root_.GD.N0230.N0671.d001651 hmu hmu0 hpq).ne'
    (_root_.GD.N0230.N0675.d001654
      hmu target p q hp hq)







theorem d001657
    {mu0 : Measure Omega}
    (mu : Theta → Measure Omega) (target : Theta → ℝ)
    (hmu : ∀ theta, mu theta ≪ mu0)
    (hmu0 : ∀ theta, mu0 ≪ mu theta)
    {p q : _root_.GD.N0230.N0602.d000116 mu0}
    (hp : ∀ theta,
      _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) (mu theta) (target theta) p ≠ ⊤)
    (hq : ∀ theta,
      _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) (mu theta) (target theta) q ≠ ⊤)
    (hweak : ∀ theta,
      _root_.GD.N0230.N0675.d001652 (mu theta) (target theta) q ≤
        _root_.GD.N0230.N0675.d001652 (mu theta) (target theta) p)
    (hpq : p ≠ q) :
    ∀ theta,
      _root_.GD.N0230.N0675.d001652 (mu theta) (target theta)
          (_root_.GD.N0230.N0718.d001528 p q) <
        _root_.GD.N0230.N0675.d001652 (mu theta) (target theta) p := by
  intro theta
  have hidentity := _root_.GD.N0230.N0675.d001655
    (hmu theta) (target theta) p q (hp theta) (hq theta)
  have htax := _root_.GD.N0230.N0675.d001656
    (hmu theta) (hmu0 theta) (target theta)
    (hp theta) (hq theta) hpq
  have hweakTheta := hweak theta
  linarith

end CommonSupport



section ReducedSelection

variable {Theta D : Type*}
variable [AddCommGroup D] [Module ℝ D]



def d001658 (objective : D → ℝ) (C : Set D) : Prop :=
  ∀ {p q}, p ∈ C → q ∈ C → p ≠ q →
    objective (_root_.GD.N0230.N0718.d001528 p q) <
      (objective p + objective q) / 2



def d001659 (objective : D → ℝ) (C : Set D) : Prop :=
  ∀ ⦃p q : D⦄, p ∈ C → q ∈ C →
    IsMinOn objective C p → IsMinOn objective C q → p = q



theorem d001660
    (objective : D → ℝ) (C : Set D)
    (hconvex : Convex ℝ C)
    (hmidpoint : _root_.GD.N0230.N0675.d001658 objective C) :
    _root_.GD.N0230.N0675.d001659 objective C := by
  intro p q hpC hqC hpMin hqMin
  by_contra hpq
  have hmidC : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
    unfold _root_.GD.N0230.N0718.d001528
    apply hconvex hpC hqC
    · norm_num
    · norm_num
    · norm_num
  have hpLe : objective p ≤ objective (_root_.GD.N0230.N0718.d001528 p q) :=
    hpMin hmidC
  have hqLe : objective q ≤ objective p := hqMin hpC
  have hEq : objective q = objective p := by
    exact le_antisymm hqLe (hpMin hqC)
  have hstrict := hmidpoint hpC hqC hpq
  rw [hEq] at hstrict
  linarith



theorem d001661
    (objective : D → ℝ) (C : Set D)
    (hstrict : StrictConvexOn ℝ C objective) :
    _root_.GD.N0230.N0675.d001658 objective C := by
  intro p q hpC hqC hpq
  have h := hstrict.2 hpC hqC hpq
      (show 0 < (1 / 2 : ℝ) from by norm_num)
      (show 0 < (1 / 2 : ℝ) from by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 from by norm_num)
  have hrhs :
      (objective p + objective q) / 2 =
        (1 / 2 : ℝ) * objective p + (1 / 2 : ℝ) * objective q := by
    ring
  rw [hrhs]
  simpa only [_root_.GD.N0230.N0718.d001528, smul_eq_mul] using h

variable [TopologicalSpace D]






theorem d001662
    (risk : Theta → D → ℝ)
    (objective : D → ℝ) (seed : D)
    (hcompact : IsCompact {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hlsc : LowerSemicontinuousOn objective
      {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hconvex : Convex ℝ {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hmidpoint : _root_.GD.N0230.N0675.d001658 objective
      {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hmono : _root_.GD.N0230.N0625.d000802 risk objective) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk seed star ∧
      IsMinOn objective {d : D | _root_.GD.N0230.N0556.d000030 risk seed d} star ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star := by
  let C : Set D := {d : D | _root_.GD.N0230.N0556.d000030 risk seed d}
  have hseedC : seed ∈ C := by
    exact _root_.GD.N0230.N0556.d000032 risk seed
  obtain ⟨star, hstarC, hstarMin⟩ :=
    hlsc.exists_isMinOn ⟨seed, hseedC⟩ hcompact
  have hrigid : _root_.GD.N0230.N0675.d001659 objective C :=
    _root_.GD.N0230.N0675.d001660 objective C hconvex hmidpoint
  have hunique : _root_.GD.N0230.N0625.d000801 objective C star := by
    refine ⟨hstarC, hstarMin, ?_⟩
    intro d hdC hdEq
    have hdMin : IsMinOn objective C d := by
      intro e heC
      rw [hdEq]
      exact hstarMin heC
    exact hrigid hdC hstarC hdMin hstarMin
  have hterminal : _root_.GD.N0230.N0630.d000786 risk star :=
    _root_.GD.N0230.N0625.d000809
      risk objective seed star hmono hunique
  exact ⟨star, hstarC, hstarMin, hterminal,
    _root_.GD.N0230.N0630.d000788 risk hterminal⟩



theorem d001663
    (risk : Theta → D → ℝ)
    (objective : D → ℝ) (seed : D)
    (hcompact : IsCompact {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hlsc : LowerSemicontinuousOn objective
      {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hstrict : StrictConvexOn ℝ
      {d : D | _root_.GD.N0230.N0556.d000030 risk seed d} objective)
    (hmono : _root_.GD.N0230.N0625.d000802 risk objective) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk seed star ∧
      IsMinOn objective {d : D | _root_.GD.N0230.N0556.d000030 risk seed d} star ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star := by
  exact _root_.GD.N0230.N0675.d001662
    risk objective seed hcompact hlsc hstrict.1
      (_root_.GD.N0230.N0675.d001661 objective _ hstrict) hmono




theorem d001664
    (risk : Theta → D → ℝ)
    (objective : D → ℝ) (baseline seed : D)
    (hseed : _root_.GD.N0230.N0630.d000785 risk seed baseline)
    (hcompact : IsCompact {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hlsc : LowerSemicontinuousOn objective
      {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hconvex : Convex ℝ {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hmidpoint : _root_.GD.N0230.N0675.d001658 objective
      {d : D | _root_.GD.N0230.N0556.d000030 risk seed d})
    (hmono : _root_.GD.N0230.N0625.d000802 risk objective) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk seed star ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      _root_.GD.N0230.N0630.d000785 risk star baseline := by
  obtain ⟨star, hstar, _hmin, hterminal, hadmissible⟩ :=
    _root_.GD.N0230.N0675.d001662
      risk objective seed hcompact hlsc hconvex hmidpoint hmono
  exact ⟨star, hstar, hterminal, hadmissible,
    _root_.GD.N0230.N0630.d000790 risk hstar hseed⟩

end ReducedSelection



section PurificationBridge

variable {Theta ReducedRule AmbientRule : Type*}











theorem d001665
    (reducedRisk : Theta → ReducedRule → ℝ)
    (ambientRisk : Theta → AmbientRule → ℝ)
    (lift : ReducedRule → AmbientRule)
    (purify : AmbientRule → ReducedRule)
    (star : ReducedRule)
    (hreduced : _root_.GD.N0230.N0630.d000786 reducedRisk star)
    (hpurifies : ∀ e : AmbientRule,
      _root_.GD.N0230.N0556.d000028 ambientRisk e (lift star) →
        _root_.GD.N0230.N0556.d000028 reducedRisk (purify e) star)
    (hequalityFaithful : ∀ e : AmbientRule,
      _root_.GD.N0230.N0556.d000028 ambientRisk e (lift star) →
        purify e = star → e = lift star) :
    _root_.GD.N0230.N0630.d000786 ambientRisk (lift star) := by
  intro e he
  exact hequalityFaithful e he (hreduced (purify e) (hpurifies e he))

end PurificationBridge

end

end N0675
end N0230
end GD

#print axioms _root_.GD.N0230.N0675.d001655
#print axioms _root_.GD.N0230.N0675.d001654
#print axioms _root_.GD.N0230.N0675.d001656
#print axioms _root_.GD.N0230.N0675.d001657
#print axioms _root_.GD.N0230.N0675.d001660
#print axioms _root_.GD.N0230.N0675.d001661
#print axioms _root_.GD.N0230.N0675.d001662
#print axioms _root_.GD.N0230.N0675.d001663
#print axioms _root_.GD.N0230.N0675.d001664
#print axioms _root_.GD.N0230.N0675.d001665
