import GD.Module0030



















open Filter

namespace GD
namespace N0230
namespace N0563

noncomputable section



def d000360
    {X : ℕ → Type*}
    (Legal : ∀ k, X k → Prop)
    (residual : ∀ k, X k → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k in atTop, ∃ x : X k, Legal k x ∧ residual k x < ε


def d000361
    {X : ℕ → Type*}
    (Legal : ∀ k, X k → Prop)
    (residual : ∀ k, X k → ℝ) : Prop :=
  ∃ x : ∀ k, X k,
    (∀ k, Legal k (x k)) ∧
    Tendsto (fun k ↦ residual k (x k)) atTop (nhds 0)






theorem d000362
    {X : ℕ → Type*}
    (Legal : ∀ k, X k → Prop)
    (residual : ∀ k, X k → ℝ)
    (hlegalNonempty : ∀ k, ∃ x : X k, Legal k x)
    (hresidualNonneg : ∀ k x, 0 ≤ residual k x) :
    _root_.GD.N0230.N0563.d000361 Legal residual ↔
      _root_.GD.N0230.N0563.d000360 Legal residual := by
  constructor
  · rintro ⟨x, hxLegal, hxZero⟩ ε hε
    have hsmall : ∀ᶠ k in atTop, residual k (x k) < ε :=
      (tendsto_order.1 hxZero).2 ε hε
    filter_upwards [hsmall] with k hk
    exact ⟨x k, hxLegal k, hk⟩
  · intro happrox
    classical
    let FeasibleLevel : ℕ → ℕ → Prop := fun k j ↦
      0 < j ∧ ∃ x : X k,
        Legal k x ∧ residual k x < 1 / (j : ℝ)
    let level : ℕ → ℕ := fun k ↦
      Nat.findGreatest (FeasibleLevel k) k
    have hlevel : Tendsto level atTop atTop := by
      refine tendsto_atTop.2 fun j ↦ ?_
      by_cases hj : j = 0
      · subst j
        exact Filter.Eventually.of_forall (fun _ ↦ Nat.zero_le _)
      · have hjPos : 0 < j := Nat.pos_of_ne_zero hj
        have htolerance : 0 < (1 / (j : ℝ)) := by positivity
        have hfeasible := happrox (1 / (j : ℝ)) htolerance
        filter_upwards [hfeasible, eventually_ge_atTop j] with k hkFeasible hjk
        apply Nat.le_findGreatest hjk
        exact ⟨hjPos, hkFeasible⟩
    have hchoice : ∀ k, ∃ x : X k,
        Legal k x ∧
          (0 < level k → residual k x < 1 / ((level k : ℕ) : ℝ)) := by
      intro k
      by_cases hk : 0 < level k
      · have hlevelFeasible : FeasibleLevel k (level k) := by
          exact Nat.findGreatest_of_ne_zero
            (P := FeasibleLevel k) (n := k) (m := level k)
            rfl (Nat.ne_of_gt hk)
        obtain ⟨x, hxLegal, hxResidual⟩ := hlevelFeasible.2
        exact ⟨x, hxLegal, fun _ ↦ hxResidual⟩
      · obtain ⟨x, hxLegal⟩ := hlegalNonempty k
        exact ⟨x, hxLegal, fun hkPos ↦ (hk hkPos).elim⟩
    choose x hxLegal hxBound using hchoice
    refine ⟨x, hxLegal, ?_⟩
    have hlevelPos : ∀ᶠ k in atTop, 0 < level k := by
      have hgeOne : ∀ᶠ k in atTop, 1 ≤ level k :=
        (tendsto_atTop.1 hlevel) 1
      exact hgeOne.mono (fun _ hk ↦ lt_of_lt_of_le Nat.zero_lt_one hk)
    have hupper : ∀ᶠ k in atTop,
        residual k (x k) ≤ 1 / ((level k : ℕ) : ℝ) := by
      filter_upwards [hlevelPos] with k hk
      exact (hxBound k hk).le
    have hlevelInv : Tendsto
        (fun k ↦ (1 : ℝ) / ((level k : ℕ) : ℝ))
        atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp hlevel
    exact squeeze_zero'
      (Filter.Eventually.of_forall (fun k ↦ hresidualNonneg k (x k)))
      hupper hlevelInv


def d000363
    {X : ℕ → Type*}
    (Legal : ∀ k, X k → Prop)
    (residual : ∀ k, X k → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∃ᶠ k in atTop, ∀ x : X k, Legal k x → ε ≤ residual k x




theorem d000364
    {X : ℕ → Type*}
    (Legal : ∀ k, X k → Prop)
    (residual : ∀ k, X k → ℝ)
    (hlegalNonempty : ∀ k, ∃ x : X k, Legal k x)
    (hresidualNonneg : ∀ k x, 0 ≤ residual k x) :
    (¬ _root_.GD.N0230.N0563.d000361 Legal residual) ↔
      _root_.GD.N0230.N0563.d000363 Legal residual := by
  rw [_root_.GD.N0230.N0563.d000362
    Legal residual hlegalNonempty hresidualNonneg]
  unfold _root_.GD.N0230.N0563.d000360 _root_.GD.N0230.N0563.d000363
  push Not
  rfl

#print axioms _root_.GD.N0230.N0563.d000362
#print axioms _root_.GD.N0230.N0563.d000364

end

end N0563
end N0230
end GD
