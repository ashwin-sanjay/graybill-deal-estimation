import GD.Module0774
import GD.Module0779



















open Filter Set

namespace GD
namespace N0232
namespace N0719
namespace N0822

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0810
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0819
open _root_.GD.N0232.N0719.N0820
open _root_.GD.N0232.N0719.N0847
open _root_.GD.N0232.N0719.N0951







def d011879
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : Prop :=
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



theorem d011880
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes ↔
      ∃ p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
        _root_.GD.N0232.N0719.N0822.d011879
          k sizes hk hsizes p q := by
  rfl


theorem d011881
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hescape : _root_.GD.N0232.N0719.N0822.d011879
      k sizes hk hsizes p q) :
    _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes := by
  exact ⟨p, q, hescape⟩




theorem d011882
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hescape : _root_.GD.N0232.N0719.N0822.d011879
      k sizes hk hsizes p q) :
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
  rcases hescape with ⟨hp, hq, hpq, _hclones, hcollapse⟩
  refine ⟨hp, hq, hpq, ?_⟩
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




theorem d011883
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hescape : _root_.GD.N0232.N0719.N0822.d011879
      k sizes hk hsizes p q) :
    ∃ (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) (depthSeq : ℕ → ℕ)
        (w : Fin k → ℝ) (active : Finset (Fin k)),
      _root_.GD.N0232.N0719.N0820.d011742 k sizes hk hsizes
        p q thetaSeq depthSeq w active := by
  classical
  obtain ⟨hp, hq, hpq, hfaces⟩ :=
    _root_.GD.N0232.N0719.N0822.d011882
      k sizes hk hsizes hescape
  have huniv : (Finset.univ : Finset (Fin k)).Nonempty := by
    exact ⟨⟨0, lt_of_lt_of_le (by omega : 0 < 3) hk⟩, Finset.mem_univ _⟩
  obtain ⟨collarSeq, _hfullMass, htax, hpGap, hqGap⟩ :=
    hfaces (Finset.univ : Finset (Fin k)) huniv
  let rawSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k := fun n ↦ (collarSeq n).1
  obtain ⟨w, active, phi, hw, hactiveEq, hactive, hphi,
      hweights, hinactive, hlower⟩ :=
    _root_.GD.N0232.N0719.N0819.d011738 (lt_of_lt_of_le (by omega : 0 < 3) hk)
      rawSeq
  refine ⟨rawSeq ∘ phi, phi, w, active,
    hp, hq, hpq, hw, hactiveEq, hactive, hphi,
    hweights, hinactive, hlower, ?_, ?_, ?_⟩
  · exact htax.comp hphi.tendsto_atTop
  · exact hpGap.comp hphi.tendsto_atTop
  · exact hqGap.comp hphi.tendsto_atTop



def d011884
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :=
  {z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes //
    z.1.p = p ∧ z.1.q = q}



theorem d011885
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hescape : _root_.GD.N0232.N0719.N0822.d011879
      k sizes hk hsizes p q) :
    Nonempty (_root_.GD.N0232.N0719.N0822.d011884
      k sizes hk hsizes p q) := by
  obtain ⟨thetaSeq, depthSeq, w, active, hspec⟩ :=
    _root_.GD.N0232.N0719.N0822.d011883
      k sizes hk hsizes hescape
  let data : _root_.GD.N0232.N0719.N0820.d011743 k sizes hk hsizes :=
    ⟨p, q, thetaSeq, depthSeq, w, active⟩
  let z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes :=
    ⟨data, hspec⟩
  exact ⟨⟨z, rfl, rfl⟩⟩





structure d011886
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) where
  p : _root_.GD.N0232.N0719.N0816.d010975 k sizes
  q : _root_.GD.N0232.N0719.N0816.d010975 k sizes
  completeEscape : _root_.GD.N0232.N0719.N0822.d011879
    k sizes hk hsizes p q
  localized : _root_.GD.N0232.N0719.N0822.d011884
    k sizes hk hsizes p q



theorem d011887
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hescape : _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes) :
    Nonempty (_root_.GD.N0232.N0719.N0822.d011886
      k sizes hk hsizes) := by
  rw [_root_.GD.N0232.N0719.N0822.d011880] at hescape
  obtain ⟨p, q, hpqEscape⟩ := hescape
  obtain ⟨localized⟩ :=
    _root_.GD.N0232.N0719.N0822.d011885
      k sizes hk hsizes hpqEscape
  exact ⟨⟨p, q, hpqEscape, localized⟩⟩



theorem d011888
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0822.d011886
      k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes :=
  _root_.GD.N0232.N0719.N0822.d011881 z.completeEscape



theorem d011889
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes ↔
      Nonempty (_root_.GD.N0232.N0719.N0822.d011886
        k sizes hk hsizes) := by
  constructor
  · exact _root_.GD.N0232.N0719.N0822.d011887
      k sizes hk hsizes
  · rintro ⟨z⟩
    exact _root_.GD.N0232.N0719.N0822.d011888 z



theorem d011890
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0822.d011886
      k sizes hk hsizes) :
    z.localized.1.1.active.card ≤ 2 ∨
      3 ≤ z.localized.1.1.active.card :=
  _root_.GD.N0232.N0719.N0819.d011739 z.localized.1.1.active







theorem d011891
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      Nonempty (_root_.GD.N0232.N0719.N0822.d011886
        k sizes hk hsizes) := by
  rcases _root_.GD.N0232.N0719.N0847.d011877
      k sizes hk hsizes with hterminal | hescape
  · exact Or.inl hterminal
  · exact Or.inr
      (_root_.GD.N0232.N0719.N0822.d011887
        k sizes hk hsizes hescape)





theorem d011892
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      (∃ z : _root_.GD.N0232.N0719.N0822.d011886
          k sizes hk hsizes,
        z.localized.1.1.active.card ≤ 2 ∨
          3 ≤ z.localized.1.1.active.card) := by
  rcases _root_.GD.N0232.N0719.N0822.d011891
      k sizes hk hsizes with hterminal | hsync
  · exact Or.inl hterminal
  · obtain ⟨z⟩ := hsync
    exact Or.inr ⟨z, _root_.GD.N0232.N0719.N0822.d011890 z⟩

end

end N0822
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0822.d011880
#print axioms _root_.GD.N0232.N0719.N0822.d011882
#print axioms _root_.GD.N0232.N0719.N0822.d011883
#print axioms _root_.GD.N0232.N0719.N0822.d011889
#print axioms _root_.GD.N0232.N0719.N0822.d011891
#print axioms _root_.GD.N0232.N0719.N0822.d011892
