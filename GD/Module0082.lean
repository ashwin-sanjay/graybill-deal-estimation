import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Separation.Connected
import GD.Module0007
import GD.Module0080























open Filter Set Topology

namespace GD
namespace N0230
namespace N0698

noncomputable section

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0695
open _root_.GD.N0230.N0582

variable {Θ Rule : Type*}





theorem d001086
    [TopologicalSpace Rule]
    (terminal : Set Rule) (P : Rule → Rule)
    (hgraph : IsClosed (_root_.GD.N0230.N0582.d000059 P))
    (hfix : ∀ d, P d = d ↔ d ∈ terminal) :
    IsClosed terminal := by
  have hset : terminal =
      (fun d : Rule ↦ (d, d)) ⁻¹' _root_.GD.N0230.N0582.d000059 P := by
    ext d
    change d ∈ terminal ↔ d = P d
    simpa only [eq_comm] using (hfix d).symm
  rw [hset]
  exact hgraph.preimage (continuous_id.prodMk continuous_id)








theorem d001087
    [TopologicalSpace Rule]
    (risk : Θ → Rule → ℝ) (P : Rule → Rule)
    (hgraph : IsClosed (_root_.GD.N0230.N0582.d000059 P))
    (hfix : ∀ d, P d = d ↔ _root_.GD.N0230.N0630.d000786 risk d) :
    IsClosed (_root_.GD.N0230.N0695.d001053 risk) := by
  apply _root_.GD.N0230.N0698.d001086
    (_root_.GD.N0230.N0695.d001053 risk) P hgraph
  intro d
  exact hfix d



theorem d001088
    [TopologicalSpace Rule] [T2Space Rule]
    (risk : Θ → Rule → ℝ) (P : Rule → Rule)
    (hP : Continuous P)
    (hfix : ∀ d, P d = d ↔ _root_.GD.N0230.N0630.d000786 risk d) :
    IsClosed (_root_.GD.N0230.N0695.d001053 risk) := by
  apply _root_.GD.N0230.N0698.d001087 risk P
  · exact isClosed_eq continuous_snd (hP.comp continuous_fst)
  · exact hfix




abbrev d001089 := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}


noncomputable instance d001090 : CompactSpace _root_.GD.N0230.N0698.d001089 :=
  isCompact_iff_compactSpace.mp isCompact_Icc


def d001091 (n : ℕ) : _root_.GD.N0230.N0698.d001089 :=
  ⟨1 / ((n : ℝ) + 1), by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · exact div_nonneg zero_le_one (by linarith)
    · exact (div_le_one (by linarith)).2 (by linarith)⟩

def d001092 : _root_.GD.N0230.N0698.d001089 := ⟨0, by norm_num⟩
def d001093 : _root_.GD.N0230.N0698.d001089 := ⟨1, by norm_num⟩



def d001094 (n : ℕ) (x : _root_.GD.N0230.N0698.d001089) : ℝ :=
  let t := (n : ℝ) + 1
  (x.1 - 1 / t) ^ 2 * (1 + t ^ 2 * (1 - x.1) ^ 2)


theorem d001095 (n : ℕ) :
    Continuous (_root_.GD.N0230.N0698.d001094 n) := by
  unfold _root_.GD.N0230.N0698.d001094
  fun_prop



theorem d001096 (n : ℕ) :
    _root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0698.d001094 (_root_.GD.N0230.N0698.d001091 n) := by
  intro e he
  let t : ℝ := (n : ℝ) + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hfactor : 0 < 1 + t ^ 2 * (1 - e.1) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (1 - e.1))]
  have hle :
      (e.1 - 1 / t) ^ 2 * (1 + t ^ 2 * (1 - e.1) ^ 2) ≤ 0 := by
    have hn := he n
    simpa [_root_.GD.N0230.N0698.d001094, _root_.GD.N0230.N0698.d001091, t] using hn
  have hnonneg :
      0 ≤ (e.1 - 1 / t) ^ 2 * (1 + t ^ 2 * (1 - e.1) ^ 2) :=
    mul_nonneg (sq_nonneg _) hfactor.le
  have hzero :
      (e.1 - 1 / t) ^ 2 * (1 + t ^ 2 * (1 - e.1) ^ 2) = 0 :=
    le_antisymm hle hnonneg
  have hsquare : (e.1 - 1 / t) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hfactor.ne'
  apply Subtype.ext
  dsimp [_root_.GD.N0230.N0698.d001091]
  nlinarith [sq_nonneg (e.1 - 1 / t)]



theorem d001097 :
    _root_.GD.N0230.N0556.d000028 _root_.GD.N0230.N0698.d001094 _root_.GD.N0230.N0698.d001093 _root_.GD.N0230.N0698.d001092 := by
  intro n
  let t : ℝ := (n : ℝ) + 1
  have ht : 1 ≤ t := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [t]
    linarith
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hinv_nonneg : 0 ≤ 1 / t := by positivity
  have hinv_le : 1 / t ≤ 1 := (div_le_one htpos).2 ht
  have hleft : (1 - 1 / t) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - 1 / t)]
  have hrightEq :
      (1 / t) ^ 2 * (1 + t ^ 2) = 1 + 1 / t ^ 2 := by
    field_simp [htpos.ne']
    <;> ring
  have hright : 1 ≤ (1 / t) ^ 2 * (1 + t ^ 2) := by
    rw [hrightEq]
    have hnonneg : 0 ≤ (1 : ℝ) / t ^ 2 := by positivity
    linarith
  have hmain :
      (1 - 1 / t) ^ 2 ≤ (1 / t) ^ 2 * (1 + t ^ 2) :=
    hleft.trans hright
  simpa [_root_.GD.N0230.N0698.d001094, _root_.GD.N0230.N0698.d001093, _root_.GD.N0230.N0698.d001092, t] using hmain


theorem d001098 :
    ¬ _root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0698.d001094 _root_.GD.N0230.N0698.d001092 := by
  intro h
  have heq := h _root_.GD.N0230.N0698.d001093 _root_.GD.N0230.N0698.d001097
  have hval := congrArg Subtype.val heq
  norm_num [_root_.GD.N0230.N0698.d001093, _root_.GD.N0230.N0698.d001092] at hval


theorem d001099 :
    Tendsto _root_.GD.N0230.N0698.d001091 atTop (𝓝 _root_.GD.N0230.N0698.d001092) := by
  rw [tendsto_subtype_rng]
  simpa [_root_.GD.N0230.N0698.d001091, _root_.GD.N0230.N0698.d001092] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))






theorem d001100 :
    ¬ IsClosed (_root_.GD.N0230.N0695.d001053 _root_.GD.N0230.N0698.d001094) := by
  intro hclosed
  have hmem : _root_.GD.N0230.N0698.d001092 ∈ _root_.GD.N0230.N0695.d001053 _root_.GD.N0230.N0698.d001094 :=
    hclosed.mem_of_tendsto _root_.GD.N0230.N0698.d001099
      (Eventually.of_forall fun n ↦ _root_.GD.N0230.N0698.d001096 n)
  exact _root_.GD.N0230.N0698.d001098 hmem



variable {G : Type*} [TopologicalSpace G] [ConnectedSpace G]
variable [TopologicalSpace Rule]






theorem d001101
    (terminal : Set Rule)
    (act : G → Rule → Rule) (d : Rule)
    (horbitIn : ∀ g, act g d ∈ terminal)
    (horbit : Continuous (fun g ↦ act g d))
    (hTotallyDisconnected : IsTotallyDisconnected terminal)
    (identity : G) (hidentity : act identity d = d) :
    ∀ g, act g d = d := by
  have hrangePreconnected :
      IsPreconnected (Set.range (fun g ↦ act g d)) :=
    isPreconnected_range horbit
  have hrangeSubset :
      Set.range (fun g ↦ act g d) ⊆ terminal := by
    rintro x ⟨g, rfl⟩
    exact horbitIn g
  have hrangeSubsingleton :
      (Set.range (fun g ↦ act g d)).Subsingleton :=
    hTotallyDisconnected _ hrangeSubset hrangePreconnected
  intro g
  have heq : act g d = act identity d :=
    hrangeSubsingleton ⟨g, rfl⟩ ⟨identity, rfl⟩
  exact heq.trans hidentity








theorem d001102
    (risk : Θ → Rule → ℝ)
    (act : G → Rule → Rule) (d : Rule)
    (hterminal : ∀ g, _root_.GD.N0230.N0630.d000786 risk (act g d))
    (horbit : Continuous (fun g ↦ act g d))
    (hTotallyDisconnected : IsTotallyDisconnected (_root_.GD.N0230.N0695.d001053 risk))
    (identity : G) (hidentity : act identity d = d) :
    ∀ g, act g d = d := by
  exact _root_.GD.N0230.N0698.d001101
    (_root_.GD.N0230.N0695.d001053 risk) act d hterminal horbit
      hTotallyDisconnected identity hidentity



theorem d001103
    (risk : Θ → Rule → ℝ)
    (act : G → Rule → Rule) (d : Rule)
    (hterminal : ∀ g, _root_.GD.N0230.N0630.d000786 risk (act g d))
    (horbitTerminal : Continuous (fun g ↦
      (⟨act g d, hterminal g⟩ : {x // _root_.GD.N0230.N0630.d000786 risk x})))
    [DiscreteTopology {x // _root_.GD.N0230.N0630.d000786 risk x}]
    (identity : G) (hidentity : act identity d = d) :
    ∀ g, act g d = d := by
  let orbitT : G → {x // _root_.GD.N0230.N0630.d000786 risk x} :=
    fun g ↦ ⟨act g d, hterminal g⟩
  have horbitPreconnected : IsPreconnected (Set.range orbitT) :=
    isPreconnected_range horbitTerminal
  haveI : PreconnectedSpace (Set.range orbitT) :=
    Subtype.preconnectedSpace horbitPreconnected
  haveI : DiscreteTopology (Set.range orbitT) := inferInstance
  have hrangeSubsingleton : Subsingleton (Set.range orbitT) :=
    PreconnectedSpace.trivial_of_discrete
  intro g
  have heq : orbitT g = orbitT identity := by
    exact congrArg Subtype.val
      (hrangeSubsingleton.elim
        (⟨orbitT g, ⟨g, rfl⟩⟩ : Set.range orbitT)
        (⟨orbitT identity, ⟨identity, rfl⟩⟩ : Set.range orbitT))
  exact (congrArg Subtype.val heq).trans hidentity

end

end N0698
end N0230
end GD

#print axioms _root_.GD.N0230.N0698.d001087
#print axioms _root_.GD.N0230.N0698.d001100
#print axioms _root_.GD.N0230.N0698.d001102
