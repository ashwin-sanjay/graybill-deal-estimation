import GD.Module0772
import GD.Module0251






















open Filter Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0819

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0951


def d011729
    {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0815.d010924 theta i / _root_.GD.N0232.N0719.N0815.d010926 theta


theorem d011730
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0951.d003581 (_root_.GD.N0232.N0719.N0819.d011729 theta) := by
  constructor
  · intro i
    exact div_nonneg (_root_.GD.N0232.N0719.N0815.d010925 theta i).le
      (_root_.GD.N0232.N0719.N0815.d010927 hk theta).le
  · unfold _root_.GD.N0232.N0719.N0819.d011729 _root_.GD.N0232.N0719.N0815.d010926
    rw [← Finset.sum_div]
    exact div_self (Finset.sum_pos
      (fun i _ ↦ _root_.GD.N0232.N0719.N0815.d010925 theta i)
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩).ne'


theorem d011731
    {k : ℕ} (hk : 0 < k)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0819.d011729
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      _root_.GD.N0232.N0719.N0819.d011729 theta := by
  funext i
  unfold _root_.GD.N0232.N0719.N0819.d011729
  rw [_root_.GD.N0232.N0719.N0815.d010929, _root_.GD.N0232.N0719.N0815.d010930]
  have hfactor : 1 / dilation ^ 2 ≠ 0 := by positivity
  exact mul_div_mul_left
    (_root_.GD.N0232.N0719.N0815.d010924 theta i) (_root_.GD.N0232.N0719.N0815.d010926 theta) hfactor


theorem d011732
    {k : ℕ} (hk : 0 < k) (active : Finset (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 active theta =
      ∑ i ∈ activeᶜ, _root_.GD.N0232.N0719.N0819.d011729 theta i := by
  unfold _root_.GD.N0232.N0719.N0815.d010928 _root_.GD.N0232.N0719.N0819.d011729
  rw [← Finset.sum_div]


def d011733 {k : ℕ} (w : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter (fun i ↦ 0 < w i)

@[simp] theorem d011734
    {k : ℕ} (w : Fin k → ℝ) (i : Fin k) :
    i ∈ _root_.GD.N0232.N0719.N0819.d011733 w ↔ 0 < w i := by
  simp [_root_.GD.N0232.N0719.N0819.d011733]


theorem d011735
    {k : ℕ} {w : Fin k → ℝ} (hw : _root_.GD.N0232.N0719.N0951.d003581 w) :
    (_root_.GD.N0232.N0719.N0819.d011733 w).Nonempty := by
  classical
  by_contra hempty
  have hzero : ∀ i, w i = 0 := by
    intro i
    have hnpos : ¬ 0 < w i := by
      intro hpos
      exact hempty ⟨i, (_root_.GD.N0232.N0719.N0819.d011734 w i).2 hpos⟩
    exact le_antisymm (le_of_not_gt hnpos) (hw.1 i)
  have : (∑ i, w i) = 0 := by simp [hzero]
  linarith [hw.2]


theorem d011736
    {k : ℕ} {w : Fin k → ℝ} (hw : _root_.GD.N0232.N0719.N0951.d003581 w)
    {i : Fin k} (hi : i ∈ (_root_.GD.N0232.N0719.N0819.d011733 w)ᶜ) :
    w i = 0 := by
  have hnpos : ¬ 0 < w i := by
    intro hpos
    have hmem : i ∈ _root_.GD.N0232.N0719.N0819.d011733 w :=
      (_root_.GD.N0232.N0719.N0819.d011734 w i).2 hpos
    exact (Finset.mem_compl.mp hi) hmem
  exact le_antisymm (le_of_not_gt hnpos) (hw.1 i)




theorem d011737
    {k : ℕ} {thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k} {w : Fin k → ℝ}
    (hconv : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n))
      atTop (nhds w)) :
    ∀ᶠ n in atTop, ∀ i ∈ _root_.GD.N0232.N0719.N0819.d011733 w,
      w i / 2 ≤ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n) i := by
  rw [Filter.eventually_all_finset]
  intro i hi
  have hwi : 0 < w i := (_root_.GD.N0232.N0719.N0819.d011734 w i).1 hi
  have hcoord : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n) i)
      atTop (nhds (w i)) := tendsto_pi_nhds.mp hconv i
  filter_upwards [(tendsto_order.1 hcoord).1 (w i / 2) (by linarith)] with n hn
  exact hn.le







theorem d011738
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) :
    ∃ (w : Fin k → ℝ) (active : Finset (Fin k))
        (φ : ℕ → ℕ),
      _root_.GD.N0232.N0719.N0951.d003581 w ∧
      active = _root_.GD.N0232.N0719.N0819.d011733 w ∧
      active.Nonempty ∧
      StrictMono φ ∧
      Tendsto
        ((fun n ↦ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n)) ∘ φ)
        atTop (nhds w) ∧
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq (φ n)))
        atTop (nhds 0) ∧
      ∀ i, i ∈ active →
        ∀ᶠ n in atTop,
          w i / 2 ≤ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq (φ n)) i := by
  classical
  let simplex : Set (Fin k → ℝ) :=
    {w | _root_.GD.N0232.N0719.N0951.d003581 w}
  have hmem : ∀ n,
      _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n) ∈ simplex := by
    intro n
    exact _root_.GD.N0232.N0719.N0819.d011730 hk (thetaSeq n)
  obtain ⟨w, hw, φ, hφ, hconv⟩ :=
    (_root_.GD.N0232.N0719.N0951.d003583 k).tendsto_subseq hmem
  let active := _root_.GD.N0232.N0719.N0819.d011733 w
  have hactive : active.Nonempty := _root_.GD.N0232.N0719.N0819.d011735 hw
  have hcoord : ∀ i,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq (φ n)) i)
        atTop (nhds (w i)) := by
    intro i
    exact tendsto_pi_nhds.mp hconv i
  have hinactive : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq (φ n)))
      atTop (nhds 0) := by
    rw [show (fun n ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq (φ n))) =
        (fun n ↦ ∑ i ∈ activeᶜ,
          _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq (φ n)) i) by
      funext n
      exact _root_.GD.N0232.N0719.N0819.d011732
        hk active (thetaSeq (φ n))]
    have hsum := tendsto_finsetSum activeᶜ (fun i hi ↦ hcoord i)
    have hzero : (∑ i ∈ activeᶜ, w i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact _root_.GD.N0232.N0719.N0819.d011736 hw hi
    simpa [hzero] using hsum
  have hlower : ∀ i, i ∈ active →
      ∀ᶠ n in atTop,
        w i / 2 ≤ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq (φ n)) i := by
    intro i hi
    have hwi : 0 < w i := by
      exact (_root_.GD.N0232.N0719.N0819.d011734 w i).1 hi
    have hhalf : w i / 2 < w i := by linarith
    filter_upwards [(tendsto_order.1 (hcoord i)).1 (w i / 2) hhalf] with n hn
    exact hn.le
  exact ⟨w, active, φ, hw, rfl, hactive, hφ, hconv,
    hinactive, hlower⟩



theorem d011739
    {k : ℕ} (active : Finset (Fin k)) :
    active.card ≤ 2 ∨ 3 ≤ active.card := by
  omega



theorem d011740
    {f : ℕ → ℝ} {phi : ℕ → ℕ}
    (hphi : StrictMono phi)
    (hf : Tendsto f atTop (nhds 0)) :
    Tendsto (f ∘ phi) atTop (nhds 0) := by
  exact hf.comp hphi.tendsto_atTop
















theorem d011741
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hescape : _root_.GD.N0232.N0719.N0824.d011722
      k sizes hk hsizes) :
    ∃ (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
        (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
        (depthSeq : ℕ → ℕ)
        (w : Fin k → ℝ) (active : Finset (Fin k)),
      p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
      q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes ∧
      p ≠ q ∧
      _root_.GD.N0232.N0719.N0951.d003581 w ∧
      active = _root_.GD.N0232.N0719.N0819.d011733 w ∧
      active.Nonempty ∧
      (active.card ≤ 2 ∨ 3 ≤ active.card) ∧
      StrictMono depthSeq ∧
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n))
        atTop (nhds w) ∧
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq n))
        atTop (nhds 0) ∧
      (∀ i, i ∈ active →
        ∀ᶠ n in atTop,
          w i / 2 ≤ _root_.GD.N0232.N0719.N0819.d011729 (thetaSeq n) i) ∧
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0719.N0811.d011037
          k sizes hk hsizes (thetaSeq n) p q)
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
        atTop (nhds 0) := by
  classical
  obtain ⟨p, q, hp, hq, hpq, hfaces⟩ :=
    _root_.GD.N0232.N0719.N0824.d011727
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
  refine ⟨p, q, (rawSeq ∘ phi), phi, w, active,
    hp, hq, hpq, hw, hactiveEq, hactive,
    _root_.GD.N0232.N0719.N0819.d011739 active, hphi, hweights, hinactive,
    hlower, ?_, ?_, ?_⟩
  · exact htax.comp hphi.tendsto_atTop
  · exact hpGap.comp hphi.tendsto_atTop
  · exact hqGap.comp hphi.tendsto_atTop

end

end N0819
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0819.d011730
#print axioms _root_.GD.N0232.N0719.N0819.d011731
#print axioms _root_.GD.N0232.N0719.N0819.d011738
#print axioms _root_.GD.N0232.N0719.N0819.d011739
#print axioms _root_.GD.N0232.N0719.N0819.d011741
