import GD.Module0995
import GD.Module0976



















open Filter

namespace GD
namespace N0232
namespace N0720
namespace N1160

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1099
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1161

variable (m n : ℕ)



def d015765
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s ∧
    ∃ η : ℝ, 0 < η ∧
      ∀ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t →
          η ≤ _root_.GD.N0232.N0720.N1477.d015749 m n t



def d015766
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s →
      ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
          _root_.GD.N0232.N0720.N1160.d015765 m n hm hn t



def d015767
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s →
      0 < _root_.GD.N0232.N0720.N1477.d015749 m n s →
        ∀ ε : ℝ, 0 < ε →
          ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
            _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
              _root_.GD.N0232.N0720.N1477.d015749 m n t < ε


theorem d015768
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1477.d015749 m n s := by
  unfold _root_.GD.N0232.N0720.N1477.d015749
  positivity



theorem d015769
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s) :
    ¬ _root_.GD.N0232.N0720.N1160.d015765 m n hm hn s ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
          _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
            _root_.GD.N0232.N0720.N1477.d015749 m n t < ε := by
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




theorem d015770
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀)
    (hno : ∀ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s₀ t →
        ¬ _root_.GD.N0232.N0720.N1160.d015765 m n hm hn t) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  classical
  let DownSeed := {t : _root_.GD.N0232.N0720.N1159.d014639 m n //
    _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s₀ t}
  let start : DownSeed :=
    ⟨s₀, hs₀, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₀.value⟩
  have hnext : ∀ (u : DownSeed) (j : ℕ),
      ∃ v : DownSeed,
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) u.1.value v.1.value ∧
          _root_.GD.N0232.N0720.N1477.d015749 m n v.1 <
            1 / ((j : ℝ) + 1) := by
    intro u j
    have huStrict : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn u.1 := u.2.1
    have huNot : ¬ _root_.GD.N0232.N0720.N1160.d015765 m n hm hn u.1 :=
      hno u.1 u.2
    obtain ⟨v, hv, hvsmall⟩ :=
      (_root_.GD.N0232.N0720.N1160.d015769
        m n hm hn u.1 huStrict).1 huNot
        (1 / ((j : ℝ) + 1)) (by positivity)
    refine ⟨⟨v, hv.1, ?_⟩, hv.2, hvsmall⟩
    exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n) hv.2 u.2.2
  let next : DownSeed → ℕ → DownSeed :=
    fun u j ↦ Classical.choose (hnext u j)
  have next_spec (u : DownSeed) (j : ℕ) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) u.1.value (next u j).1.value ∧
        _root_.GD.N0232.N0720.N1477.d015749 m n (next u j).1 <
          1 / ((j : ℝ) + 1) :=
    Classical.choose_spec (hnext u j)
  let chain : ℕ → DownSeed := fun j ↦
    Nat.rec start (fun depth current ↦ next current depth) j
  have chain_zero : (chain 0).1 = s₀ := rfl
  have chain_succ (j : ℕ) : chain (j + 1) = next (chain j) j := by
    simp only [chain]
  have hdesc (j : ℕ) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (chain j).1.value (chain (j + 1)).1.value := by
    rw [chain_succ]
    exact (next_spec (chain j) j).1
  have henergyShift : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (chain (j + 1)).1)
      atTop (nhds 0) := by
    apply squeeze_zero (g := fun j : ℕ ↦ 1 / ((j : ℝ) + 1))
    · intro j
      exact _root_.GD.N0232.N0720.N1160.d015768 m n (chain (j + 1)).1
    · intro j
      rw [chain_succ]
      exact (next_spec (chain j) j).2.le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have henergy : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (chain j).1)
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).1 henergyShift
  apply _root_.GD.N0232.N0720.N1099.d015762
    m n hm hn (fun j ↦ (chain j).1) hdesc henergy
  rw [chain_zero]
  exact hs₀



theorem d015771
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdescent : _root_.GD.N0232.N0720.N1160.d015767 m n hm hn)
    (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  by_cases hzero : _root_.GD.N0232.N0720.N1477.d015749 m n s₀ = 0
  · exact
      (_root_.GD.N0232.N0720.N1482.d015173
        (m := m) (n := n) hm hn).2
        ⟨s₀, hs₀,
          (_root_.GD.N0232.N0720.N1477.d015755
            m n s₀).2 hzero⟩
  · apply _root_.GD.N0232.N0720.N1160.d015770
      m n hm hn s₀ hs₀
    intro t ht htrap
    obtain ⟨htStrict, η, hη, hfloor⟩ := htrap
    have htPos : 0 < _root_.GD.N0232.N0720.N1477.d015749 m n t :=
      lt_of_lt_of_le hη
        (hfloor t ⟨htStrict, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value⟩)
    obtain ⟨u, hu, husmall⟩ := hdescent t htStrict htPos η hη
    exact (not_lt_of_ge (hfloor u hu)) husmall




theorem d015772
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      _root_.GD.N0232.N0720.N1160.d015766 m n hm hn := by
  classical
  constructor
  · intro hnot s hs
    by_contra hbarrier
    apply hnot
    apply _root_.GD.N0232.N0720.N1160.d015770
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
    have htEnergy : _root_.GD.N0232.N0720.N1477.d015749 m n t = 0 :=
      (_root_.GD.N0232.N0720.N1477.d015755
        m n t).1 htMaster
    have hpositive : η ≤ _root_.GD.N0232.N0720.N1477.d015749 m n t :=
      hfloor t ⟨htStrict, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value⟩
    rw [htEnergy] at hpositive
    exact (not_lt_of_ge hpositive) hη

end
end N1160
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1160.d015769
#print axioms _root_.GD.N0232.N0720.N1160.d015770
#print axioms _root_.GD.N0232.N0720.N1160.d015771
#print axioms _root_.GD.N0232.N0720.N1160.d015772
