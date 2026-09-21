import GD.Module0773










open Filter Set

namespace GD
namespace N0232
namespace N0719
namespace N0820

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0819
open _root_.GD.N0232.N0719.N0951


def d011742
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) (depthSeq : ℕ → ℕ)
    (w : Fin k → ℝ) (active : Finset (Fin k)) : Prop :=
  p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
  q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
  p ≠ q ∧
  _root_.GD.N0232.N0719.N0951.d003581 w ∧
  active = _root_.GD.N0232.N0719.N0819.d011733 w ∧
  active.Nonempty ∧
  StrictMono depthSeq ∧
  Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n)) atTop (nhds w) ∧
  Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq n)) atTop (nhds 0) ∧
  (∀ i, i ∈ active → ∀ᶠ n in atTop,
    w i / 2 ≤ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n) i) ∧
  Tendsto
    (fun n ↦ _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes (thetaSeq n) p q)
    atTop (nhds 0) ∧
  Tendsto
    (fun n ↦
      _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes Finset.univ
          (_root_.GD.N0232.N0719.N0815.d010938 (depthSeq n)) p -
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes (thetaSeq n) p)
    atTop (nhds 0) ∧
  Tendsto
    (fun n ↦
      _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes Finset.univ
          (_root_.GD.N0232.N0719.N0815.d010938 (depthSeq n)) q -
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes (thetaSeq n) q)
    atTop (nhds 0)




structure d011743
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) where
  p : _root_.GD.N0232.N0719.N0816.d010975 k sizes
  q : _root_.GD.N0232.N0719.N0816.d010975 k sizes
  thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k
  depthSeq : ℕ → ℕ
  w : Fin k → ℝ
  active : Finset (Fin k)



def d011744
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :=
  {z : _root_.GD.N0232.N0719.N0820.d011743 k sizes hk hsizes //
    _root_.GD.N0232.N0719.N0820.d011742 k sizes hk hsizes
      z.p z.q z.thetaSeq z.depthSeq z.w z.active}

namespace d011744

def d011745 {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0816.d010975 k sizes := z.1.p

def d011746 {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0816.d010975 k sizes := z.1.q

def d011747 {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    ℕ → _root_.GD.N0232.N0719.N0859.d010809 k := z.1.thetaSeq

def d011748 {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    ℕ → ℕ := z.1.depthSeq

def d011749 {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    Fin k → ℝ := z.1.w

def d011750 {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    Finset (Fin k) := z.1.active

theorem d011751 {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0820.d011742 k sizes hk hsizes
      z.1.p z.1.q z.1.thetaSeq z.1.depthSeq z.1.w z.1.active := z.2

end d011744

theorem d011752
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hescape : _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes) :
    Nonempty (_root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) := by
  obtain ⟨p, q, thetaSeq, depthSeq, w, active,
      hp, hq, hpq, hw, hactiveEq, hactive, _hrank, hdepth,
      hweights, hinactive, hlower, htax, hpGap, hqGap⟩ :=
    _root_.GD.N0232.N0719.N0819.d011741
      k sizes hk hsizes hescape
  exact ⟨⟨⟨p, q, thetaSeq, depthSeq, w, active⟩,
    hp, hq, hpq, hw, hactiveEq, hactive, hdepth,
    hweights, hinactive, hlower, htax, hpGap, hqGap⟩⟩



theorem d011753
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hescape : _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes) :
    (∃ z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes,
      z.1.active.card ≤ 2) ∨
    (∃ z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes,
      3 ≤ z.1.active.card) := by
  obtain ⟨z⟩ := _root_.GD.N0232.N0719.N0820.d011752
    k sizes hk hsizes hescape
  rcases _root_.GD.N0232.N0719.N0819.d011739 z.1.active with hlow | hinterior
  · exact Or.inl ⟨z, hlow⟩
  · exact Or.inr ⟨z, hinterior⟩

end


end N0820
end N0719
end N0232
end GD
