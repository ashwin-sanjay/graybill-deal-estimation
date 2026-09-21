import GD.Module0771





























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0824

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0810
open _root_.GD.N0232.N0719.N0818
open _root_.GD.N0232.N0719.N0823
open _root_.GD.N0230.N0643
open _root_.GD.N0230.N0554




def d011721
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) : Prop :=
  ∃ p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
    _root_.GD.N0230.N0643.d001717
        (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage)
        (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) p q ∧
      p ≠ q ∧
      ∀ i : ℕ, Nonempty (_root_.GD.N0232.N0719.N0818.d011655 k stage i) →
        ∀ epsilon : ℝ, 0 < epsilon →
          ∃ theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i,
            _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q < epsilon ∧
            _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p -
                _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p <
              2 * epsilon ∧
            _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i q -
                _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q <
              2 * epsilon



def d011722
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  ∃ p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
    p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
      q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
      p ≠ q ∧
      (∀ c : _root_.GD.N0232.N0719.N0809.d010964 k,
        _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes
            c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) p =
          _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes
            c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) q) ∧
      ∀ c : _root_.GD.N0232.N0719.N0809.d010964 k, Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k c) →
        ∀ epsilon : ℝ, 0 < epsilon →
          ∃ theta : _root_.GD.N0232.N0719.N0810.d011629 k c,
            _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q < epsilon ∧
            _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes
                  c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) p -
                _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p <
              2 * epsilon ∧
            _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes
                  c.1 (_root_.GD.N0232.N0719.N0815.d010938 c.2) q -
                _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q <
              2 * epsilon




theorem d011723
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) :
    ¬ _root_.GD.N0232.N0719.N0823.d011710 k sizes hk hsizes stage ↔
      _root_.GD.N0232.N0719.N0824.d011721 k sizes hk hsizes stage := by
  classical
  constructor
  · intro hfailure
    unfold _root_.GD.N0232.N0719.N0823.d011710 at hfailure
    push Not at hfailure
    obtain ⟨p, q, hclones, hpq, hcollapse⟩ := hfailure
    refine ⟨p, q, hclones, hpq, ?_⟩
    intro i hcollar epsilon hepsilon
    obtain ⟨theta, htotal⟩ := hcollapse i hcollar epsilon hepsilon
    have hupperP :
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p ≤
          _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p :=
      (_root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
        hclones.1 hcollar).1 ⟨theta, rfl⟩
    have hupperQ :
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q ≤
          _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i q :=
      (_root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
        hclones.2.1 hcollar).1 ⟨theta, rfl⟩
    have htaxNonnegative := _root_.GD.N0232.N0719.N0811.d011039
      k sizes hk hsizes theta.1 p q
    dsimp [_root_.GD.N0230.N0554.d001565] at htotal
    refine ⟨theta, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨p, q, hclones, hpq, hcollapse⟩ hseparate
    obtain ⟨i, hcollar, epsilon, hepsilon, hfloor⟩ :=
      hseparate p q hclones hpq
    obtain ⟨theta, htax, hpGap, hqGap⟩ :=
      hcollapse i hcollar (epsilon / 4) (by linarith)
    have hlower := hfloor theta
    dsimp [_root_.GD.N0230.N0554.d001565] at hlower
    linarith



theorem d011724
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hstage : _root_.GD.N0232.N0719.N0809.d010965 stage)
    (hescape : _root_.GD.N0232.N0719.N0824.d011721
      k sizes hk hsizes stage) :
    _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes := by
  obtain ⟨p, q, hclones, hpq, hcollapse⟩ := hescape
  refine ⟨p, q, hclones.1, hclones.2.1, hpq, ?_, ?_⟩
  · intro c
    obtain ⟨i, hi⟩ := hstage c
    have h := hclones.2.2 i
    simpa [_root_.GD.N0232.N0719.N0818.d011653, hi] using h
  · intro c hcollar epsilon hepsilon
    obtain ⟨i, hi⟩ := hstage c
    subst c
    simpa [_root_.GD.N0232.N0719.N0818.d011653] using
      hcollapse i hcollar epsilon hepsilon



theorem d011725
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hescape : _root_.GD.N0232.N0719.N0824.d011722
      k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0824.d011721 k sizes hk hsizes stage := by
  obtain ⟨p, q, hp, hq, hpq, hclones, hcollapse⟩ := hescape
  refine ⟨p, q, ⟨hp, hq, ?_⟩, hpq, ?_⟩
  · intro i
    exact hclones (stage i)
  · intro i hcollar epsilon hepsilon
    simpa [_root_.GD.N0232.N0719.N0818.d011653] using
      hcollapse (stage i) hcollar epsilon hepsilon






theorem d011726
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ¬ _root_.GD.N0232.N0719.N0823.d011711 k sizes hk hsizes ↔
      _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes := by
  constructor
  · intro hfailure
    apply _root_.GD.N0232.N0719.N0824.d011724
      k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k)
      (_root_.GD.N0232.N0719.N0809.d010967 k)
    exact
      (_root_.GD.N0232.N0719.N0824.d011723
        k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k)).1 hfailure
  · intro hescape hseparate
    have hsched := _root_.GD.N0232.N0719.N0824.d011725
      k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k) hescape
    exact
      (_root_.GD.N0232.N0719.N0824.d011723
        k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k)).2 hsched hseparate





theorem d011727
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hescape : _root_.GD.N0232.N0719.N0824.d011722
      k sizes hk hsizes) :
    ∃ p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
      p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
      q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
      p ≠ q ∧
      ∀ active : Finset (Fin k), active.Nonempty →
        ∃ thetaSeq : ∀ depth : ℕ,
            _root_.GD.N0232.N0719.N0810.d011629 k (active, depth),
          Tendsto
              (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq depth).1)
              atTop (nhds 0) ∧
            Tendsto
              (fun depth ↦ _root_.GD.N0232.N0719.N0811.d011037
                k sizes hk hsizes (thetaSeq depth).1 p q)
              atTop (nhds 0) ∧
            Tendsto
              (fun depth ↦
                _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active
                    (_root_.GD.N0232.N0719.N0815.d010938 depth) p -
                  _root_.GD.N0232.N0719.N0811.d011036
                    k sizes hk hsizes (thetaSeq depth).1 p)
              atTop (nhds 0) ∧
            Tendsto
              (fun depth ↦
                _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active
                    (_root_.GD.N0232.N0719.N0815.d010938 depth) q -
                  _root_.GD.N0232.N0719.N0811.d011036
                    k sizes hk hsizes (thetaSeq depth).1 q)
              atTop (nhds 0) := by
  obtain ⟨p, q, hp, hq, hpq, _hclones, hcollapse⟩ := hescape
  refine ⟨p, q, hp, hq, hpq, ?_⟩
  intro active hactive
  have hcollar : ∀ depth : ℕ,
      Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k (active, depth)) := fun depth ↦
    _root_.GD.N0232.N0719.N0810.d011635 hactive depth
  have hradiusPos : ∀ depth : ℕ, 0 < _root_.GD.N0232.N0719.N0815.d010938 depth := by
    intro depth
    unfold _root_.GD.N0232.N0719.N0815.d010938
    positivity
  choose thetaSeq htax hpGap hqGap using fun depth ↦
    hcollapse (active, depth) (hcollar depth)
      (_root_.GD.N0232.N0719.N0815.d010938 depth) (hradiusPos depth)
  have hradius : Tendsto _root_.GD.N0232.N0719.N0815.d010938 atTop (nhds 0) := by
    have hfun : _root_.GD.N0232.N0719.N0815.d010938 = (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) := by
      funext n
      simp [_root_.GD.N0232.N0719.N0815.d010938]
    rw [hfun]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨thetaSeq, ?_, ?_, ?_, ?_⟩
  · exact squeeze_zero
      (fun depth ↦ _root_.GD.N0232.N0719.N0810.d011632
        (by omega) active (thetaSeq depth).1)
      (fun depth ↦ (thetaSeq depth).2)
      hradius
  · exact squeeze_zero
      (fun depth ↦ _root_.GD.N0232.N0719.N0811.d011039
        k sizes hk hsizes (thetaSeq depth).1 p q)
      (fun depth ↦ (htax depth).le)
      hradius
  · have hgapNonnegative : ∀ depth,
        0 ≤ _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active
              (_root_.GD.N0232.N0719.N0815.d010938 depth) p -
            _root_.GD.N0232.N0719.N0811.d011036
              k sizes hk hsizes (thetaSeq depth).1 p := by
      intro depth
      have hupper :=
        (_root_.GD.N0232.N0719.N0812.d011048
          k sizes hk hsizes active (_root_.GD.N0232.N0719.N0815.d010938 depth)
          hp (hcollar depth)).1 ⟨thetaSeq depth, rfl⟩
      linarith
    exact squeeze_zero hgapNonnegative
      (fun depth ↦ (hpGap depth).le)
      (by simpa using hradius.const_mul (2 : ℝ))
  · have hgapNonnegative : ∀ depth,
        0 ≤ _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active
              (_root_.GD.N0232.N0719.N0815.d010938 depth) q -
            _root_.GD.N0232.N0719.N0811.d011036
              k sizes hk hsizes (thetaSeq depth).1 q := by
      intro depth
      have hupper :=
        (_root_.GD.N0232.N0719.N0812.d011048
          k sizes hk hsizes active (_root_.GD.N0232.N0719.N0815.d010938 depth)
          hq (hcollar depth)).1 ⟨thetaSeq depth, rfl⟩
      linarith
    exact squeeze_zero hgapNonnegative
      (fun depth ↦ (hqGap depth).le)
      (by simpa using hradius.const_mul (2 : ℝ))




theorem d011728
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0823.d011711 k sizes hk hsizes ∨
      ∃ p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
        p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
        q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
        p ≠ q ∧
        ∀ active : Finset (Fin k), active.Nonempty →
          ∃ thetaSeq : ∀ depth : ℕ,
              _root_.GD.N0232.N0719.N0810.d011629 k (active, depth),
            Tendsto
                (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active
                  (thetaSeq depth).1)
                atTop (nhds 0) ∧
              Tendsto
                (fun depth ↦ _root_.GD.N0232.N0719.N0811.d011037
                  k sizes hk hsizes (thetaSeq depth).1 p q)
                atTop (nhds 0) ∧
              Tendsto
                (fun depth ↦
                  _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active
                      (_root_.GD.N0232.N0719.N0815.d010938 depth) p -
                    _root_.GD.N0232.N0719.N0811.d011036
                      k sizes hk hsizes (thetaSeq depth).1 p)
                atTop (nhds 0) ∧
              Tendsto
                (fun depth ↦
                  _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active
                      (_root_.GD.N0232.N0719.N0815.d010938 depth) q -
                    _root_.GD.N0232.N0719.N0811.d011036
                      k sizes hk hsizes (thetaSeq depth).1 q)
                atTop (nhds 0) := by
  classical
  by_cases hresidual :
      _root_.GD.N0232.N0719.N0823.d011711 k sizes hk hsizes
  · exact Or.inl hresidual
  · exact Or.inr
      (_root_.GD.N0232.N0719.N0824.d011727
        k sizes hk hsizes
        ((_root_.GD.N0232.N0719.N0824.d011726
          k sizes hk hsizes).1 hresidual))

end

end N0824
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0824.d011723
#print axioms _root_.GD.N0232.N0719.N0824.d011726
#print axioms _root_.GD.N0232.N0719.N0824.d011727
#print axioms _root_.GD.N0232.N0719.N0824.d011728
