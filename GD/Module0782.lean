import GD.Module0696
import GD.Module0768
import GD.Module0769
import GD.Module0772
import GD.Module0749
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic



























open Filter Set MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace GD
namespace N0232
namespace N0719
namespace N0898

noncomputable section

open _root_.GD.N0232.N0719.N0863
open _root_.GD.N0232.N0719.N1002
open _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0810
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0821
open _root_.GD.N0232.N0719.N0814
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0823
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0865
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0671
open _root_.GD.N0230.N0591

variable {ι E V : Type*}
  [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MetricSpace V]


def d011900
    (response : V → ι → E) (p q : V) : ℝ :=
  _root_.GD.N0232.N0719.N0863.d010244 (fun i ↦ response p i - response q i)



def d011901
    (response : V → ι → E) : Prop :=
  ∀ p q : V,
    (∀ i j, response p i - response q i =
      response p j - response q j) →
    p = q


theorem d011902 (x : ι → E) :
    0 ≤ _root_.GD.N0232.N0719.N0863.d010244 x := by
  unfold _root_.GD.N0232.N0719.N0863.d010244 _root_.GD.N0232.N0719.N0863.d010243 _root_.GD.N0232.N0719.N0863.d010234
  exact Finset.sum_nonneg fun t _ ↦ by positivity



theorem d011903
    (hcard : 3 ≤ Fintype.card ι) (x : ι → E) :
    _root_.GD.N0232.N0719.N0863.d010244 x = 0 ↔ ∀ i j, x i = x j := by
  rw [_root_.GD.N0232.N0719.N0863.d010251]
  have hcoeff : (3 : ℝ) * ((Fintype.card ι - 2 : ℕ) : ℝ) ≠ 0 := by
    have hsub : 0 < Fintype.card ι - 2 := by omega
    positivity
  rw [mul_eq_zero]
  simp only [hcoeff, false_or]
  exact _root_.GD.N0234.N0736.d003284 x



theorem d011904
    (hcard : 3 ≤ Fintype.card ι)
    (response : V → ι → E) (p q : V) :
    _root_.GD.N0232.N0719.N0898.d011900 response p q = 0 ↔
      ∀ i j, response p i - response q i =
        response p j - response q j := by
  exact _root_.GD.N0232.N0719.N0898.d011903 hcard
    (fun i ↦ response p i - response q i)



theorem d011905
    (hcard : 3 ≤ Fintype.card ι)
    (response : V → ι → E) :
    _root_.GD.N0232.N0719.N0898.d011901 response ↔
      ∀ p q : V, _root_.GD.N0232.N0719.N0898.d011900 response p q = 0 → p = q := by
  constructor
  · intro hfaithful p q hzero
    exact hfaithful p q
      ((_root_.GD.N0232.N0719.N0898.d011904
        hcard response p q).1 hzero)
  · intro henergy p q hconsensus
    exact henergy p q
      ((_root_.GD.N0232.N0719.N0898.d011904
        hcard response p q).2 hconsensus)



variable {k : ℕ}




def d011906
    (active : Finset (Fin k))
    (tax : ∀ c : _root_.GD.N0232.N0719.N0809.d010964 k,
      _root_.GD.N0232.N0719.N0810.d011629 k c → V → V → ℝ)
    (response : V → ι → E) (p q : V) : Prop :=
  ∀ thetaSeq : ∀ depth : ℕ,
      _root_.GD.N0232.N0719.N0810.d011629 k (active, depth),
    Tendsto
        (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq depth).1)
        atTop (nhds 0) →
    ∀ r : ℝ, r < _root_.GD.N0232.N0719.N0898.d011900 response p q →
      ∀ᶠ depth in atTop,
        r ≤ tax (active, depth) (thetaSeq depth) p q










theorem d011907
    (hcard : 3 ≤ Fintype.card ι)
    (active : Finset (Fin k))
    (tax : ∀ c : _root_.GD.N0232.N0719.N0809.d010964 k,
      _root_.GD.N0232.N0719.N0810.d011629 k c → V → V → ℝ)
    (response : V → ι → E) {p q : V}
    (hfaithful : _root_.GD.N0232.N0719.N0898.d011901 response)
    (hobservable : _root_.GD.N0232.N0719.N0898.d011906
      active tax response p q)
    (thetaSeq : ∀ depth : ℕ,
      _root_.GD.N0232.N0719.N0810.d011629 k (active, depth))
    (hface : Tendsto
      (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq depth).1)
      atTop (nhds 0))
    (hzero : Tendsto
      (fun depth ↦ tax (active, depth) (thetaSeq depth) p q)
      atTop (nhds 0)) :
    p = q := by
  apply _root_.GD.N0232.N0719.N0821.d011675
    (fun x y : V ↦ _root_.GD.N0232.N0719.N0898.d011900 response x y)
  · exact _root_.GD.N0232.N0719.N0898.d011902
      (fun i ↦ response p i - response q i)
  · intro henergy
    exact hfaithful p q
      ((_root_.GD.N0232.N0719.N0898.d011904
        hcard response p q).1 henergy)
  · exact hobservable thetaSeq hface
  · exact hzero





def d011908
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k))
    (response : _root_.GD.N0232.N0719.N0816.d010975 k sizes → ι → E)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : Prop :=
  _root_.GD.N0232.N0719.N0898.d011906 active
    (fun _c theta p q ↦
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
    response p q


theorem d011909
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hcard : 3 ≤ Fintype.card ι)
    (active : Finset (Fin k))
    (response : _root_.GD.N0232.N0719.N0816.d010975 k sizes → ι → E)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hfaithful : _root_.GD.N0232.N0719.N0898.d011901 response)
    (hobservable : _root_.GD.N0232.N0719.N0898.d011908
      k sizes hk hsizes active response p q)
    (thetaSeq : ∀ depth : ℕ,
      _root_.GD.N0232.N0719.N0810.d011629 k (active, depth))
    (hface : Tendsto
      (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq depth).1)
      atTop (nhds 0))
    (hzero : Tendsto
      (fun depth ↦ _root_.GD.N0232.N0719.N0811.d011037
        k sizes hk hsizes (thetaSeq depth).1 p q)
      atTop (nhds 0)) :
    p = q := by
  exact _root_.GD.N0232.N0719.N0898.d011907
    hcard active
    (fun _c theta p q ↦
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
    response hfaithful hobservable thetaSeq hface hzero











theorem d011910
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hcard : 3 ≤ Fintype.card ι)
    (active : Finset (Fin k)) (hactive : active.Nonempty)
    (response : _root_.GD.N0232.N0719.N0816.d010975 k sizes → ι → E)
    (hfaithful : _root_.GD.N0232.N0719.N0898.d011901 response)
    (hobservable : ∀ p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
      p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes →
      q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes →
      _root_.GD.N0232.N0719.N0898.d011908
        k sizes hk hsizes active response p q) :
    _root_.GD.N0232.N0719.N0823.d011711
      k sizes hk hsizes := by
  by_contra hfailure
  have hescape : _root_.GD.N0232.N0719.N0824.d011722
      k sizes hk hsizes :=
    (_root_.GD.N0232.N0719.N0824.d011726
      k sizes hk hsizes).1 hfailure
  obtain ⟨p, q, hp, hq, hpq, thetaData⟩ :=
    _root_.GD.N0232.N0719.N0824.d011727
      k sizes hk hsizes hescape
  obtain ⟨thetaSeq, hface, hzero, _hpGap, _hqGap⟩ :=
    thetaData active hactive
  have heq : p = q :=
    _root_.GD.N0232.N0719.N0898.d011909
      k sizes hk hsizes hcard active response hfaithful
      (hobservable p q hp hq) thetaSeq hface hzero
  exact hpq heq




def d011911
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : ENNReal :=
  _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)




theorem d011912
    (k : ℕ) (sizes : Fin k → ℕ)
    (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    LowerSemicontinuous
      (fun theta : _root_.GD.N0232.N0719.N0859.d010809 k ↦
        _root_.GD.N0232.N0719.N0898.d011911 k sizes theta p q) := by
  exact _root_.GD.N0230.N0591.d000131
    (_root_.GD.N0232.N0719.d009182 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
    (_root_.GD.N0232.N0719.N0865.d011217 k sizes) (fun _theta ↦ 0)
    (_root_.GD.N0230.N0670.d001646 p q)
    (_root_.GD.N0232.N0719.N0865.d011220 k sizes)
    (_root_.GD.N0232.N0719.N0865.d011218 k sizes)
    (_root_.GD.N0232.N0719.N0865.d011219 k sizes)
    (_root_.GD.N0232.N0719.N0865.d011221 k sizes)
    continuous_const


theorem d011913
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0898.d011911 k sizes theta p q ≠ ⊤ := by
  have hmem := _root_.GD.N0232.N0719.N0814.d011691
    k sizes hk hsizes theta p q hp hq
  have hlt :
      (∫⁻ omega,
        ‖(_root_.GD.N0230.N0670.d001646 p q) omega‖ₑ ^
          (2 : ENNReal).toReal ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) < ⊤ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
      hmem.eLpNorm_lt_top
  unfold _root_.GD.N0232.N0719.N0898.d011911 _root_.GD.N0230.N0602.d000117
  apply ne_of_lt
  convert hlt using 1
  apply lintegral_congr
  intro omega
  simpa only [sub_zero, ENNReal.toReal_ofNat, enorm_eq_nnnorm] using
    (_root_.GD.N0232.N0719.N0814.d011685 ((_root_.GD.N0230.N0670.d001646 p q) omega)).symm



theorem d011914
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hpq : p ≠ q) :
    0 < _root_.GD.N0232.N0719.N0898.d011911 k sizes theta p q := by
  exact _root_.GD.N0230.N0671.d001651
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta)
    ((_root_.GD.N0232.N0719.d009183
      k sizes theta.location theta.scale theta.scale_pos).2)
    hpq














theorem d011915
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hpq : p ≠ q)
    (htheta : Tendsto thetaSeq atTop (nhds theta))
    (C : ℝ) (hC : 0 < C)
    (hcap : ∀ᶠ n in atTop,
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (thetaSeq n) ≤ C) :
    ¬ Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0811.d011037
        k sizes hk hsizes (thetaSeq n) p q)
      atTop (nhds 0) := by
  intro hzero
  let energy := _root_.GD.N0232.N0719.N0898.d011911 k sizes theta p q
  have henergyPos : 0 < energy :=
    _root_.GD.N0232.N0719.N0898.d011914
      k sizes hk hsizes theta hpq
  have henergyTop : energy ≠ ⊤ :=
    _root_.GD.N0232.N0719.N0898.d011913
      k sizes hk hsizes theta p q hp hq
  let r : ℝ := energy.toReal / 2
  have hrPos : 0 < r := by
    dsimp [r]
    exact half_pos (ENNReal.toReal_pos henergyPos.ne' henergyTop)
  have hrEnergy : ENNReal.ofReal r < energy := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal hrPos.le henergyTop]
    dsimp [r]
    linarith [ENNReal.toReal_pos henergyPos.ne' henergyTop]
  have heventEnergy : ∀ᶠ n in atTop,
      ENNReal.ofReal r <
        _root_.GD.N0232.N0719.N0898.d011911 k sizes (thetaSeq n) p q :=
    htheta.eventually
      ((_root_.GD.N0232.N0719.N0898.d011912
        k sizes p q) theta (ENNReal.ofReal r) hrEnergy)
  have htaxSmall : ∀ᶠ n in atTop,
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes (thetaSeq n) p q <
        r / C :=
    (tendsto_order.1 hzero).2 (r / C) (div_pos hrPos hC)
  obtain ⟨n, hnEnergy, hnCap, hnSmall⟩ :=
    (heventEnergy.and (hcap.and htaxSmall)).exists
  have hnTop : _root_.GD.N0232.N0719.N0898.d011911
      k sizes (thetaSeq n) p q ≠ ⊤ :=
    _root_.GD.N0232.N0719.N0898.d011913
      k sizes hk hsizes (thetaSeq n) p q hp hq
  have hrLt : r <
      (_root_.GD.N0232.N0719.N0898.d011911 k sizes (thetaSeq n) p q).toReal := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal hrPos.le hnTop).1 hnEnergy
  have hcapPos : 0 < _root_.GD.N0232.N0719.N0858.d010851
      k sizes hk hsizes (thetaSeq n) :=
    _root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes (thetaSeq n)
  have hlower : r / C ≤
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes (thetaSeq n) p q := by
    unfold _root_.GD.N0232.N0719.N0811.d011037 at hrLt ⊢
    exact (div_le_div_of_nonneg_left hrPos.le hcapPos hnCap).trans
      (div_le_div_of_nonneg_right hrLt.le hcapPos.le)
  exact (not_lt_of_ge hlower) hnSmall





theorem d011916 :
    _root_.GD.N0232.N0719.N1002.d010215 1 (-1) 0 = 0 ∧
      ¬ ((1 : ℝ) = -1 ∧ (1 : ℝ) = 0) := by
  constructor
  · rw [_root_.GD.N0232.N0719.N1002.d010225]
    right
    right
    norm_num
  · norm_num



def d011917 (p : ℝ × ℝ) : Fin 3 → ℝ :=
  fun _ ↦ p.1




theorem d011918 :
    ((0, 1) : ℝ × ℝ) ≠ (0, 0) ∧
      _root_.GD.N0232.N0719.N0898.d011900 _root_.GD.N0232.N0719.N0898.d011917
        ((0, 1) : ℝ × ℝ) (0, 0) = 0 := by
  constructor
  · norm_num
  · apply (_root_.GD.N0232.N0719.N0898.d011904
      (by decide : 3 ≤ Fintype.card (Fin 3))
      _root_.GD.N0232.N0719.N0898.d011917 ((0, 1) : ℝ × ℝ) (0, 0)).2
    intro i j
    rfl



theorem d011919 :
    ¬ _root_.GD.N0232.N0719.N0898.d011901 _root_.GD.N0232.N0719.N0898.d011917 := by
  intro hfaithful
  have heq := hfaithful ((0, 1) : ℝ × ℝ) (0, 0) (fun i j ↦ rfl)
  norm_num at heq

end

end N0898
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0898.d011903
#print axioms _root_.GD.N0232.N0719.N0898.d011905
#print axioms _root_.GD.N0232.N0719.N0898.d011907
#print axioms _root_.GD.N0232.N0719.N0898.d011910
#print axioms _root_.GD.N0232.N0719.N0898.d011912
#print axioms _root_.GD.N0232.N0719.N0898.d011915
#print axioms _root_.GD.N0232.N0719.N0898.d011916
#print axioms _root_.GD.N0232.N0719.N0898.d011918
