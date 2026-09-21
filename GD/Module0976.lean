import GD.Module0975
import GD.Module0966
















open Filter

namespace GD
namespace N0232
namespace N0720
namespace N1161

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1100

variable (m n : ℕ)


def d015496
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s t : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015250 m n hm hn t ∧
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value t.value



def d015497
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s ∧
    ∃ η : ℝ, 0 < η ∧
      ∀ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t →
          η ≤ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) t



def d015498
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s →
      ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
          _root_.GD.N0232.N0720.N1161.d015497 m n hm hn t



def d015499
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s →
      0 < _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s →
        ∀ ε : ℝ, 0 < ε →
          ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
            _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
              _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) t < ε


theorem d015500
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {s t : _root_.GD.N0232.N0720.N1159.d014639 m n}
    (hs : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s)
    (hst : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value t.value) :
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn t := by
  intro theta
  exact lt_of_le_of_lt (hst theta) (hs theta)



theorem d015501
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s) :
    ¬ _root_.GD.N0232.N0720.N1161.d015497 m n hm hn s ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
          _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
            _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) t < ε := by
  classical
  constructor
  · intro hnot ε hε
    by_contra hsmall
    apply hnot
    refine ⟨hs, ε, hε, ?_⟩
    intro t ht
    exact le_of_not_gt fun hlt ↦ hsmall ⟨t, ht, hlt⟩
  · intro hsmall htrap
    obtain ⟨_hs, η, hη, hfloor⟩ := htrap
    obtain ⟨t, ht, hlt⟩ := hsmall η hη
    exact (not_lt_of_ge (hfloor t ht)) hlt




theorem d015502
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀)
    (hno : ∀ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s₀ t →
        ¬ _root_.GD.N0232.N0720.N1161.d015497 m n hm hn t) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  classical
  let DownSeed := {t : _root_.GD.N0232.N0720.N1159.d014639 m n //
    _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s₀ t}
  let start : DownSeed :=
    ⟨s₀, hs₀, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₀.value⟩
  have hnext : ∀ (u : DownSeed) (j : ℕ),
      ∃ v : DownSeed,
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) u.1.value v.1.value ∧
          _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) v.1 <
            1 / ((j : ℝ) + 1) := by
    intro u j
    have huStrict : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn u.1 := u.2.1
    have huNot : ¬ _root_.GD.N0232.N0720.N1161.d015497 m n hm hn u.1 :=
      hno u.1 u.2
    obtain ⟨v, hv, hvsmall⟩ :=
      (_root_.GD.N0232.N0720.N1161.d015501
        m n hm hn u.1 huStrict).1 huNot
        (1 / ((j : ℝ) + 1)) (by positivity)
    refine ⟨⟨v, hv.1, ?_⟩, hv.2, hvsmall⟩
    exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n) hv.2 u.2.2
  let next : DownSeed → ℕ → DownSeed :=
    fun u j ↦ Classical.choose (hnext u j)
  have next_spec (u : DownSeed) (j : ℕ) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) u.1.value (next u j).1.value ∧
        _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (next u j).1 <
          1 / ((j : ℝ) + 1) :=
    Classical.choose_spec (hnext u j)
  let chain : ℕ → DownSeed := fun j ↦
    Nat.rec start (fun depth current ↦ next current depth) j
  have chain_zero : (chain 0).1 = s₀ := rfl
  have chain_succ (j : ℕ) : chain (j + 1) = next (chain j) j := by
    simp only [chain, Nat.rec_add_one]
  have hdesc (j : ℕ) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (chain j).1.value (chain (j + 1)).1.value := by
    rw [chain_succ]
    exact (next_spec (chain j) j).1
  have hmasterShift : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n)
        (chain (j + 1)).1) atTop (nhds 0) := by
    apply squeeze_zero (g := fun j : ℕ ↦ 1 / ((j : ℝ) + 1))
    · intro j
      exact _root_.GD.N0232.N0720.N1482.d015170
        (m := m) (n := n) (chain (j + 1)).1
    · intro j
      rw [chain_succ]
      exact (next_spec (chain j) j).2.le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hmaster : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (chain j).1)
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).1 hmasterShift
  apply _root_.GD.N0232.N0720.N1100.d015493
    m n hm hn (fun j ↦ (chain j).1) hdesc hmaster
  rw [chain_zero]
  exact hs₀



theorem d015503
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdescent : _root_.GD.N0232.N0720.N1161.d015499 m n hm hn)
    (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  by_cases hzero :
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s₀ = 0
  · exact
      (_root_.GD.N0232.N0720.N1482.d015173
        (m := m) (n := n) hm hn).2 ⟨s₀, hs₀, hzero⟩
  · apply _root_.GD.N0232.N0720.N1161.d015502
      m n hm hn s₀ hs₀
    intro t ht htrap
    obtain ⟨htStrict, η, hη, hfloor⟩ := htrap
    have htNonneg := _root_.GD.N0232.N0720.N1482.d015170
      (m := m) (n := n) t
    have htPos : 0 < _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) t := by
      exact lt_of_lt_of_le hη
        (hfloor t ⟨htStrict, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value⟩)
    obtain ⟨u, hu, husmall⟩ := hdescent t htStrict htPos η hη
    exact (not_lt_of_ge (hfloor u hu)) husmall




theorem d015504
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      _root_.GD.N0232.N0720.N1161.d015498 m n hm hn := by
  classical
  constructor
  · intro hnot s hs
    by_contra hbarrier
    apply hnot
    apply _root_.GD.N0232.N0720.N1161.d015502
      m n hm hn s hs
    intro t ht htBarrier
    exact hbarrier ⟨t, ht, htBarrier⟩
  · intro hdense hendpoint
    obtain ⟨p, hpRep, hpStrict, hpTerminal⟩ :=
      (_root_.GD.N0232.N0720.N1159.d014664
        m n hm hn).1 hendpoint
    let s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n :=
      _root_.GD.N0232.N0720.N1159.d014657 m n hm hn p hpRep hpStrict
    have hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀ := by
      simpa only [_root_.GD.N0232.N0720.N1200.d015250, s₀,
        _root_.GD.N0232.N0720.N1159.d014657] using hpStrict
    obtain ⟨t, htBelow, htBarrier⟩ := hdense s₀ hs₀
    obtain ⟨htStrict, η, hη, hfloor⟩ := htBarrier
    have htValue : t.value = p := by
      apply hpTerminal t.value
      simpa only [s₀, _root_.GD.N0232.N0720.N1159.d014657, _root_.GD.N0230.N0608.d000673] using
        htBelow.2
    have htTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value := by
      simpa only [htValue] using hpTerminal
    have htProjection : _root_.GD.N0232.N0720.N1159.d014633 m n t.value = t.value :=
      (_root_.GD.N0232.N0720.N1159.d014635 m n t.value).2 htTerminal
    have htRep : _root_.GD.N0232.N0720.N1159.d014652 m n t.value := by
      simpa only [htValue] using hpRep
    have htAll : ∀ g,
        _root_.GD.N0232.N0720.N1159.d014647 m n t g = 0 := by
      apply (_root_.GD.N0232.N0720.N1159.d014656 m n hm hn t).2
      simpa only [htProjection] using htRep
    have htMaster :
        _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) t = 0 :=
      (_root_.GD.N0232.N0720.N1482.d015171
        (m := m) (n := n) t).2 htAll
    have hpositive : η ≤
        _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) t :=
      hfloor t ⟨htStrict, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value⟩
    rw [htMaster] at hpositive
    exact (not_lt_of_ge hpositive) hη

end
end N1161
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1161.d015501
#print axioms _root_.GD.N0232.N0720.N1161.d015502
#print axioms _root_.GD.N0232.N0720.N1161.d015503
#print axioms _root_.GD.N0232.N0720.N1161.d015504
