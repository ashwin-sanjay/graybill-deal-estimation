import GD.Module0774
import GD.Module0784


















open Filter Set

namespace GD
namespace N0232
namespace N0719
namespace N0817

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0232.N0719.N0819
open _root_.GD.N0232.N0719.N0820
open _root_.GD.N0232.N0719.N0959




theorem d011943
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes) :
    z.1.active = Finset.univ ↔ ∀ i, 0 < z.1.w i := by
  rcases z.2 with
    ⟨_hp, _hq, _hne, _hw, hactive, _hneActive, _hdepth,
      _hweights, _hinactive, _hlower, _htax, _hpGap, _hqGap⟩
  constructor
  · intro hfull i
    have hi : i ∈ z.1.active := by rw [hfull]; simp
    rw [hactive] at hi
    exact (_root_.GD.N0232.N0719.N0819.d011734 z.1.w i).1 hi
  · intro hpos
    rw [hactive]
    apply Finset.eq_univ_of_forall
    intro i
    exact (_root_.GD.N0232.N0719.N0819.d011734 z.1.w i).2 (hpos i)



def d011944
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) : _root_.GD.N0232.N0719.N0859.d010809 k :=
  _root_.GD.N0232.N0719.N0959.d011933 (by omega : 0 < k) z.1.w
    ((_root_.GD.N0232.N0719.N0817.d011943 z).1 hfull)

@[simp] theorem d011945
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    (_root_.GD.N0232.N0719.N0817.d011944 z hfull).location = 0 := by
  simp [_root_.GD.N0232.N0719.N0817.d011944]

@[simp] theorem d011946
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    _root_.GD.N0232.N0719.N0845.d010886 (_root_.GD.N0232.N0719.N0817.d011944 z hfull) = 1 := by
  exact _root_.GD.N0232.N0719.N0959.d011936
    (by omega : 0 < k) z.1.w
    ((_root_.GD.N0232.N0719.N0817.d011943 z).1 hfull)



theorem d011947
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    _root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0817.d011944 z hfull) = z.1.w := by
  rcases z.2 with
    ⟨_hp, _hq, _hne, hw, _hactive, _hneActive, _hdepth,
      _hweights, _hinactive, _hlower, _htax, _hpGap, _hqGap⟩
  exact _root_.GD.N0232.N0719.N0959.d011939
    (by omega : 0 < k) z.1.w
    ((_root_.GD.N0232.N0719.N0817.d011943 z).1 hfull) hw.2



theorem d011948
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hlocation : theta.location = 0)
    (htotalScale : _root_.GD.N0232.N0719.N0845.d010886 theta = 1)
    (hweight : _root_.GD.N0232.N0719.N0819.d011729 theta = z.1.w) :
    theta = _root_.GD.N0232.N0719.N0817.d011944 z hfull := by
  have htheta : _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta = theta :=
    (_root_.GD.N0232.N0719.N0845.d010895 (by omega : 0 < k) theta).2
      ⟨hlocation, htotalScale⟩
  have hlimit : _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k)
      (_root_.GD.N0232.N0719.N0817.d011944 z hfull) =
        _root_.GD.N0232.N0719.N0817.d011944 z hfull :=
    (_root_.GD.N0232.N0719.N0845.d010895 (by omega : 0 < k)
      (_root_.GD.N0232.N0719.N0817.d011944 z hfull)).2
      ⟨_root_.GD.N0232.N0719.N0817.d011945 z hfull,
        _root_.GD.N0232.N0719.N0817.d011946 z hfull⟩
  have hprojective : _root_.GD.N0232.N0719.N0819.d011729 theta =
      _root_.GD.N0232.N0719.N0819.d011729 (_root_.GD.N0232.N0719.N0817.d011944 z hfull) := by
    rw [hweight,
      _root_.GD.N0232.N0719.N0817.d011947 z hfull]
  have hnormalized := _root_.GD.N0232.N0719.N0959.d011930
    (by omega : 0 < k) hprojective
  rw [htheta, hlimit] at hnormalized
  exact hnormalized



theorem d011949
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hpos : ∀ i, 0 < z.1.w i) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) (z.1.thetaSeq n))
      atTop
      (nhds (_root_.GD.N0232.N0719.N0959.d011933
        (by omega : 0 < k) z.1.w hpos)) := by
  rcases z.2 with
    ⟨_hp, _hq, _hne, _hw, _hactive, _hneActive, _hdepth,
      hweights, _hinactive, _hlower, _htax, _hpGap, _hqGap⟩
  exact _root_.GD.N0232.N0719.N0959.d011942
    (by omega : 0 < k) z.1.thetaSeq z.1.w hweights hpos






theorem d011950
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) (z.1.thetaSeq n))
      atTop (nhds (_root_.GD.N0232.N0719.N0817.d011944 z hfull)) := by
  unfold _root_.GD.N0232.N0719.N0817.d011944
  exact _root_.GD.N0232.N0719.N0817.d011949 z
    ((_root_.GD.N0232.N0719.N0817.d011943 z).1 hfull)




theorem d011951
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    ∃ thetaLimit : _root_.GD.N0232.N0719.N0859.d010809 k,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) (z.1.thetaSeq n))
        atTop (nhds thetaLimit) := by
  exact ⟨_root_.GD.N0232.N0719.N0817.d011944 z hfull,
    _root_.GD.N0232.N0719.N0817.d011950 z hfull⟩








theorem d011952
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) (z.1.thetaSeq n))
        atTop (nhds (_root_.GD.N0232.N0719.N0817.d011944 z hfull)) ∧
      z.1.p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
      z.1.q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
      z.1.p ≠ z.1.q ∧
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0811.d011037
          k sizes hk hsizes (z.1.thetaSeq n) z.1.p z.1.q)
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦
          _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes Finset.univ
              (_root_.GD.N0232.N0719.N0815.d010938 (z.1.depthSeq n)) z.1.p -
            _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes (z.1.thetaSeq n) z.1.p)
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦
          _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes Finset.univ
              (_root_.GD.N0232.N0719.N0815.d010938 (z.1.depthSeq n)) z.1.q -
            _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes (z.1.thetaSeq n) z.1.q)
        atTop (nhds 0) := by
  rcases z.2 with
    ⟨hp, hq, hpq, _hw, _hactive, _hneActive, _hdepth,
      _hweights, _hinactive, _hlower, htax, hpGap, hqGap⟩
  exact ⟨_root_.GD.N0232.N0719.N0817.d011950 z hfull,
    hp, hq, hpq, htax, hpGap, hqGap⟩

end

end N0817
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0817.d011943
#print axioms _root_.GD.N0232.N0719.N0817.d011950
#print axioms _root_.GD.N0232.N0719.N0817.d011952
