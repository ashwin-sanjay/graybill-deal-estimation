import GD.Module0153
import GD.Module0740
import GD.Module0766
import GD.Module0741
































open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0818

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0810
open _root_.GD.N0232.N0719.N0813
open _root_.GD.N0232.N0719.N0808
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0566
open _root_.GD.N0230.N0569
open _root_.GD.N0230.N0643
open _root_.GD.N0230.N0628
open _root_.GD.N0230.N0600
open _root_.GD.N0230.N0680



def d011648
    (k : ℕ) (sizes : Fin k → ℕ)
    (d : _root_.GD.N0232.N0719.N0816.d010976 k sizes) : _root_.GD.N0232.N0719.N0816.d010975 k sizes :=
  (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)).symm d

@[simp] theorem d011649
    (k : ℕ) (sizes : Fin k → ℕ) (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    _root_.GD.N0232.N0719.N0818.d011648 k sizes
      ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) d) = d := by
  simp [_root_.GD.N0232.N0719.N0818.d011648]

@[simp] theorem d011650
    (k : ℕ) (sizes : Fin k → ℕ) (d : _root_.GD.N0232.N0719.N0816.d010976 k sizes) :
    (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes))
      (_root_.GD.N0232.N0719.N0818.d011648 k sizes d) = d := by
  simp [_root_.GD.N0232.N0719.N0818.d011648]

@[simp] theorem d011651
    (k : ℕ) (sizes : Fin k → ℕ)
    (p q : _root_.GD.N0232.N0719.N0816.d010976 k sizes) :
    _root_.GD.N0232.N0719.N0818.d011648 k sizes (_root_.GD.N0230.N0718.d001528 p q) =
      _root_.GD.N0230.N0718.d001528 (_root_.GD.N0232.N0719.N0818.d011648 k sizes p)
        (_root_.GD.N0232.N0719.N0818.d011648 k sizes q) := by
  simp [_root_.GD.N0232.N0719.N0818.d011648, _root_.GD.N0230.N0718.d001528]

theorem d011652
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0816.d010976 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0818.d011648 k sizes d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  rcases hd with ⟨e, he, rfl⟩
  rw [_root_.GD.N0232.N0719.N0818.d011649]
  exact he


def d011653
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (i : ℕ) (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes
    (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) d



def d011654
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0816.d010976 k sizes) : ENNReal :=
  _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0818.d011648 k sizes d)


abbrev d011655
    (k : ℕ) (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) (i : ℕ) :=
  _root_.GD.N0232.N0719.N0810.d011629 k (stage i)






def d011656
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) : Prop :=
  _root_.GD.N0230.N0643.d001718
    (fun i ↦ _root_.GD.N0232.N0719.N0818.d011655 k stage i)
    (fun _ theta d ↦
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 d)
    (fun _ theta p q ↦
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
    (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage)
    (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)



def d011657
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  _root_.GD.N0232.N0719.N0818.d011656 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0809.d010966 k)




def d011658
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) : Prop :=
  _root_.GD.N0230.N0643.d001719
    (fun i ↦ _root_.GD.N0232.N0719.N0818.d011655 k stage i)
    (fun _ theta d ↦
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 d)
    (fun _ theta p q ↦
      _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
    (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage)
    (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)


def d011659
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  _root_.GD.N0232.N0719.N0818.d011658 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0809.d010966 k)











theorem d011660
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) :
    _root_.GD.N0232.N0719.N0818.d011656 k sizes hk hsizes stage ↔
      _root_.GD.N0232.N0719.N0818.d011658
        k sizes hk hsizes stage := by
  constructor
  · intro hmatched p q hclones hpq
    obtain ⟨i, eta, theta, _heta, hactive, htax⟩ :=
      hmatched p q hclones hpq
    refine ⟨i, theta, ?_⟩
    linarith
  · intro hbeats p q hclones hpq
    obtain ⟨i, theta, hbeatsTheta⟩ := hbeats p q hclones hpq
    have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
      unfold _root_.GD.N0230.N0718.d001528
      apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hclones.1 hclones.2.1
      · norm_num
      · norm_num
      · norm_num
    have hprofileLe :
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
            (_root_.GD.N0230.N0718.d001528 p q) ≤
          _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
            (_root_.GD.N0230.N0718.d001528 p q) :=
      (_root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
        hmid ⟨theta⟩).1 ⟨theta, rfl⟩
    have hinactivity : 0 ≤
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
              (_root_.GD.N0230.N0718.d001528 p q) -
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
              (_root_.GD.N0230.N0718.d001528 p q) := by
      linarith
    obtain ⟨eta, heta, hinactivityEta, hetaTax⟩ :=
      (_root_.GD.N0230.N0643.d001720 hinactivity).2 hbeatsTheta
    refine ⟨i, eta, theta, heta, ?_, hetaTax⟩
    linarith




theorem d011661
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon
          (_root_.GD.N0230.N0718.d001528 p q) ≤
      (_root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon p +
        _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon q) / 2 := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    unfold _root_.GD.N0230.N0718.d001528
    apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hp hq
    · norm_num
    · norm_num
    · norm_num
  unfold _root_.GD.N0232.N0719.N0816.d010978
  apply iSup_le
  intro theta
  have hreal :
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
          (_root_.GD.N0230.N0718.d001528 p q) ≤
        (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p +
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q) / 2 := by
    have htax := _root_.GD.N0232.N0719.N0811.d011039
      k sizes hk hsizes theta.1 p q
    have hexact := _root_.GD.N0232.N0719.N0811.d011040
      k sizes hk hsizes theta.1 hp hq
    linarith
  have hprofile :
      _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta.1
          (_root_.GD.N0230.N0718.d001528 p q) ≤
        (_root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta.1 p +
          _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta.1 q) / 2 := by
    rw [← _root_.GD.N0232.N0719.N0811.d011041
          k sizes hk hsizes theta.1 hmid,
        ← _root_.GD.N0232.N0719.N0811.d011041
          k sizes hk hsizes theta.1 hp,
        ← _root_.GD.N0232.N0719.N0811.d011041
          k sizes hk hsizes theta.1 hq]
    calc
      ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
            (_root_.GD.N0230.N0718.d001528 p q)) ≤
          ENNReal.ofReal
            ((_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p +
              _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q) / 2) :=
        ENNReal.ofReal_le_ofReal hreal
      _ =
          (ENNReal.ofReal
                (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p) +
            ENNReal.ofReal
                (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q)) / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [ENNReal.ofReal_add
          (_root_.GD.N0232.N0719.N0812.d011044
            k sizes hk hsizes theta.1 p)
          (_root_.GD.N0232.N0719.N0812.d011044
            k sizes hk hsizes theta.1 q)]
        norm_num
  calc
    _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta.1
          (_root_.GD.N0230.N0718.d001528 p q) ≤
        (_root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta.1 p +
          _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta.1 q) / 2 := hprofile
    _ ≤ ((⨆ eta : {eta : _root_.GD.N0232.N0719.N0859.d010809 k //
              _root_.GD.N0232.N0719.N0815.d010928 active eta ≤ epsilon},
            _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes eta.1 p) +
          (⨆ eta : {eta : _root_.GD.N0232.N0719.N0859.d010809 k //
              _root_.GD.N0232.N0719.N0815.d010928 active eta ≤ epsilon},
            _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes eta.1 q)) / 2 := by
      gcongr
      · exact le_iSup (fun eta : {eta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active eta ≤ epsilon} ↦
            _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes eta.1 p) theta
      · exact le_iSup (fun eta : {eta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active eta ≤ epsilon} ↦
            _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes eta.1 q) theta


theorem d011662
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0600.d001552 (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) := by
  intro p hp q hq
  rcases hp with ⟨p, hp, rfl⟩
  rcases hq with ⟨q, hq, rfl⟩
  refine ⟨_root_.GD.N0230.N0718.d001528 p q, ?_, ?_⟩
  · unfold _root_.GD.N0230.N0718.d001528
    apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hp hq
    · norm_num
    · norm_num
    · norm_num
  · simp [_root_.GD.N0230.N0718.d001528]



theorem d011663
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (i : ℕ) {p q : _root_.GD.N0232.N0719.N0816.d010976 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i
          (_root_.GD.N0230.N0718.d001528 p q) ≤
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i p +
        _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i q) / 2 := by
  simp only [_root_.GD.N0232.N0719.N0816.d010983]
  rw [
    _root_.GD.N0232.N0719.N0816.d010980,
    _root_.GD.N0232.N0719.N0816.d010980,
    _root_.GD.N0232.N0719.N0816.d010980]
  change
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes
          (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
          (_root_.GD.N0232.N0719.N0818.d011648 k sizes (_root_.GD.N0230.N0718.d001528 p q)) ≤
      (_root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes
            (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
            (_root_.GD.N0232.N0719.N0818.d011648 k sizes p) +
        _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes
            (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
            (_root_.GD.N0232.N0719.N0818.d011648 k sizes q)) / 2
  rw [_root_.GD.N0232.N0719.N0818.d011651]
  exact _root_.GD.N0232.N0719.N0818.d011661
    k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
    (_root_.GD.N0232.N0719.N0818.d011652
      k sizes hk hsizes hp)
    (_root_.GD.N0232.N0719.N0818.d011652
      k sizes hk hsizes hq)



theorem d011664
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) :
    ∀ i, _root_.GD.N0230.N0600.d001552
      (_root_.GD.N0230.N0566.d000753
        (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
        (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) i) := by
  intro i
  induction i with
  | zero =>
      simpa [_root_.GD.N0230.N0566.d000753] using
        _root_.GD.N0232.N0719.N0818.d011662 k sizes hk hsizes
  | succ i ih =>
      rw [_root_.GD.N0230.N0566.d000755]
      intro p hp q hq
      refine ⟨ih p hp.1 q hq.1, ?_⟩
      intro e he
      have hpqeq :
          _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i p =
            _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i q :=
        le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)
      calc
        _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i
              (_root_.GD.N0230.N0718.d001528 p q) ≤
            (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i p +
              _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i q) / 2 :=
          _root_.GD.N0232.N0719.N0818.d011663
            k sizes hk hsizes stage i
            ((_root_.GD.N0230.N0680.d001666
              (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
              (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
              (_root_.GD.N0230.N0566.d000753
                (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
                (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes))
              (_root_.GD.N0230.N0566.d000756
                (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
                (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)) i) hp.1)
            ((_root_.GD.N0230.N0680.d001666
              (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
              (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
              (_root_.GD.N0230.N0566.d000753
                (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
                (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes))
              (_root_.GD.N0230.N0566.d000756
                (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
                (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)) i) hq.1)
        _ = _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i p := by
          rw [hpqeq, _root_.GD.N0230.N0601.d001580]
        _ ≤ _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i e := hp.2 e he



theorem d011665
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hmatched : _root_.GD.N0232.N0719.N0818.d011656
      k sizes hk hsizes stage)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hclones : ∀ i,
      _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p =
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i q)
    (hpq : p ≠ q) :
    ∃ i,
      _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0230.N0718.d001528 p q) <
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p := by
  have hcloneOn : _root_.GD.N0230.N0643.d001717
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage)
      (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) p q := ⟨hp, hq, hclones⟩
  obtain ⟨i, eta, theta, heta, hactive, htax⟩ :=
    hmatched p q hcloneOn hpq
  refine ⟨i, ?_⟩
  have hupperP :
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p ≤
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p :=
    (_root_.GD.N0232.N0719.N0812.d011048
      k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) hp
      ⟨theta⟩).1 ⟨theta, rfl⟩
  have hupperQ :
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q ≤
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i q :=
    (_root_.GD.N0232.N0719.N0812.d011048
      k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) hq
      ⟨theta⟩).1 ⟨theta, rfl⟩
  have hexact := _root_.GD.N0232.N0719.N0811.d011040
    k sizes hk hsizes theta.1 hp hq
  have hqeq := hclones i
  unfold _root_.GD.N0232.N0719.N0818.d011653 at hactive hupperP hupperQ hqeq ⊢
  linarith



theorem d011666
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hmatched : _root_.GD.N0232.N0719.N0818.d011656
      k sizes hk hsizes stage)
    {p q : _root_.GD.N0232.N0719.N0816.d010976 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
    (hclones : ∀ i,
      _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i p =
        _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i q)
    (hpq : p ≠ q) :
    ∃ i,
      _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i
          (_root_.GD.N0230.N0718.d001528 p q) <
        _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i p := by
  let p' := _root_.GD.N0232.N0719.N0818.d011648 k sizes p
  let q' := _root_.GD.N0232.N0719.N0818.d011648 k sizes q
  have hp' : p' ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes :=
    _root_.GD.N0232.N0719.N0818.d011652
      k sizes hk hsizes hp
  have hq' : q' ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes :=
    _root_.GD.N0232.N0719.N0818.d011652
      k sizes hk hsizes hq
  have hpq' : p' ≠ q' := by
    intro heq
    apply hpq
    have hpback : (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p' = p := by
      simp [p', _root_.GD.N0232.N0719.N0818.d011648]
    have hqback : (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) q' = q := by
      simp [q', _root_.GD.N0232.N0719.N0818.d011648]
    rw [← hpback, ← hqback, heq]
  have hrealClones : ∀ i,
      _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p' =
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i q' := by
    intro i
    have h := congrArg ENNReal.toReal (hclones i)
    simp only [_root_.GD.N0232.N0719.N0816.d010983] at h
    rw [
      _root_.GD.N0232.N0719.N0816.d010980,
      _root_.GD.N0232.N0719.N0816.d010980] at h
    change
      _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0232.N0719.N0818.d011648 k sizes p) =
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0232.N0719.N0818.d011648 k sizes q) at h
    simpa [p', q'] using h
  obtain ⟨i, hi⟩ :=
    _root_.GD.N0232.N0719.N0818.d011665
      k sizes hk hsizes stage hmatched hp' hq' hrealClones hpq'
  refine ⟨i, ?_⟩
  have hmid' : _root_.GD.N0230.N0718.d001528 p' q' ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    unfold _root_.GD.N0230.N0718.d001528
    apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hp' hq'
    · norm_num
    · norm_num
    · norm_num
  have hrightPos :
      0 < _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p' :=
    (_root_.GD.N0232.N0719.N0808.d011054
      k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
      (_root_.GD.N0230.N0718.d001528 p' q')).trans_lt hi
  have hofReal :
      ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
            (_root_.GD.N0230.N0718.d001528 p' q')) <
        ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p') :=
    (ENNReal.ofReal_lt_ofReal_iff hrightPos).2 hi
  simp only [_root_.GD.N0232.N0719.N0816.d010983]
  rw [
    _root_.GD.N0232.N0719.N0816.d010980,
    _root_.GD.N0232.N0719.N0816.d010980]
  change
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes
          (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
          (_root_.GD.N0232.N0719.N0818.d011648 k sizes (_root_.GD.N0230.N0718.d001528 p q)) <
      _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes
        (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
        (_root_.GD.N0232.N0719.N0818.d011648 k sizes p)
  rw [_root_.GD.N0232.N0719.N0818.d011651,
    ← _root_.GD.N0232.N0719.N0808.d011053
      k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) hmid',
    ← _root_.GD.N0232.N0719.N0808.d011053
      k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) hp']
  exact hofReal



theorem d011667
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hmatched : _root_.GD.N0232.N0719.N0818.d011656
      k sizes hk hsizes stage)
    {p q : _root_.GD.N0232.N0719.N0816.d010976 k sizes}
    (hp : ∀ i, p ∈ _root_.GD.N0230.N0566.d000753
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
      (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) i)
    (hq : ∀ i, q ∈ _root_.GD.N0230.N0566.d000753
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
      (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) i) :
    q = p := by
  by_contra hqp
  have htower := _root_.GD.N0230.N0566.d000756
    (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
    (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
  have hclones : ∀ i,
      _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i q =
        _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage i p := by
    intro i
    have hqNext := hq (i + 1)
    have hpNext := hp (i + 1)
    rw [htower.2 i] at hqNext hpNext
    exact le_antisymm (hqNext.2 p (hp i)) (hpNext.2 q (hq i))
  obtain ⟨i, hgap⟩ :=
    _root_.GD.N0232.N0719.N0818.d011666
      k sizes hk hsizes stage hmatched
      ((_root_.GD.N0230.N0680.d001666
        (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
        (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
        (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)) htower 0) (hq 0))
      ((_root_.GD.N0230.N0680.d001666
        (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
        (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
        (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)) htower 0) (hp 0))
      hclones hqp
  have hmidFace : _root_.GD.N0230.N0718.d001528 q p ∈
      _root_.GD.N0230.N0566.d000753
        (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
        (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) i :=
    _root_.GD.N0232.N0719.N0818.d011664
      k sizes hk hsizes stage i q (hq i) p (hp i)
  have hqNext := hq (i + 1)
  rw [htower.2 i] at hqNext
  have hqMin := hqNext.2
  exact (not_lt_of_ge (hqMin _ hmidFace)) hgap




theorem d011668
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hmatched : _root_.GD.N0232.N0719.N0818.d011656
      k sizes hk hsizes stage) :
    ∃ p : _root_.GD.N0232.N0719.N0816.d010976 k sizes,
      _root_.GD.N0230.N0569.d001685
        (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)) p := by
  obtain ⟨p, hp, _hlex⟩ :=
    _root_.GD.N0230.N0566.d000757
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
      (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0813.d011059 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0813.d011060 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0816.d010984
        k sizes hk hsizes stage)
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact _root_.GD.N0232.N0719.N0818.d011667
    k sizes hk hsizes stage hmatched hp hq



theorem d011669
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0616.d000721
      (_root_.GD.N0232.N0719.N0818.d011654 k sizes)
      (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) := by
  intro d e hd hed
  refine ⟨_root_.GD.N0232.N0719.N0818.d011648 k sizes e, ?_, ?_⟩
  · intro theta
    exact (hed theta).trans
      ((_root_.GD.N0232.N0719.N0818.d011652
        k sizes hk hsizes hd) theta)
  · exact _root_.GD.N0232.N0719.N0818.d011650 k sizes e



theorem d011670
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) :
    _root_.GD.N0230.N0596.d000732
      (_root_.GD.N0232.N0719.N0818.d011654 k sizes)
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage) := by
  intro i e d hed
  simp only [_root_.GD.N0232.N0719.N0816.d010983]
  rw [_root_.GD.N0232.N0719.N0816.d010980,
    _root_.GD.N0232.N0719.N0816.d010980]
  unfold _root_.GD.N0232.N0719.N0816.d010978
  apply iSup_mono
  intro theta
  exact ENNReal.div_le_div_right (hed theta.1)
    (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta.1)













theorem d011671
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hmatched : _root_.GD.N0232.N0719.N0818.d011656
      k sizes hk hsizes stage) :
    ∃ p : _root_.GD.N0232.N0719.N0816.d010976 k sizes,
      _root_.GD.N0230.N0569.d001685
          (_root_.GD.N0230.N0566.d000753
            (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
            (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)) p ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0818.d011654 k sizes) p := by
  obtain ⟨p, hunique⟩ :=
    _root_.GD.N0232.N0719.N0818.d011668
      k sizes hk hsizes stage hmatched
  let objective := _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage
  let C := _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes
  let face := _root_.GD.N0230.N0566.d000753 objective C
  have htower : _root_.GD.N0230.N0583.d000745 objective C face :=
    _root_.GD.N0230.N0566.d000756 objective C
  have hlex : _root_.GD.N0230.N0596.d000730 objective C p :=
    _root_.GD.N0230.N0583.d000747 objective C face htower hunique.1
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hunique.1 hunique.2
  refine ⟨p, hunique, ?_⟩
  exact _root_.GD.N0230.N0596.d000733
    (_root_.GD.N0232.N0719.N0818.d011654 k sizes) objective C p
    (_root_.GD.N0232.N0719.N0818.d011669 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0818.d011670
      k sizes hk hsizes stage)
    hlex hfaithful



theorem d011672
    (k : ℕ) (sizes : Fin k → ℕ)
    {p : _root_.GD.N0232.N0719.N0816.d010976 k sizes}
    (hp : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0818.d011654 k sizes) p) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0818.d011648 k sizes p) := by
  intro e he
  have hweak : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0818.d011654 k sizes)
      ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) e) p := by
    intro theta
    change _root_.GD.N0232.N0719.N0859.d010821 k sizes theta e ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0818.d011648 k sizes p)
    exact he theta
  have heq := hp _ hweak
  have heq' := congrArg (_root_.GD.N0232.N0719.N0818.d011648 k sizes) heq
  exact heq'






theorem d011673
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hmatched : _root_.GD.N0232.N0719.N0818.d011657
      k sizes hk hsizes) :
    ∃ p : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
      _root_.GD.N0230.N0569.d001685
          (_root_.GD.N0230.N0566.d000753
            (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes
              (_root_.GD.N0232.N0719.N0809.d010966 k))
            (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes))
          ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p) ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p := by
  obtain ⟨p, hunique, hterminal⟩ :=
    _root_.GD.N0232.N0719.N0818.d011671
      k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k) hmatched
  refine ⟨_root_.GD.N0232.N0719.N0818.d011648 k sizes p, ?_, ?_⟩
  · simpa using hunique
  · exact _root_.GD.N0232.N0719.N0818.d011672
      k sizes hterminal


theorem d011674
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hbeats : _root_.GD.N0232.N0719.N0818.d011659
      k sizes hk hsizes) :
    ∃ p : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
      _root_.GD.N0230.N0569.d001685
          (_root_.GD.N0230.N0566.d000753
            (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes
              (_root_.GD.N0232.N0719.N0809.d010966 k))
            (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes))
          ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p) ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p := by
  exact _root_.GD.N0232.N0719.N0818.d011673
    k sizes hk hsizes
    ((_root_.GD.N0232.N0719.N0818.d011660
      k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k)).2 hbeats)

end

end N0818
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0818.d011661
#print axioms _root_.GD.N0232.N0719.N0818.d011660
#print axioms _root_.GD.N0232.N0719.N0818.d011664
#print axioms _root_.GD.N0232.N0719.N0818.d011665
#print axioms _root_.GD.N0232.N0719.N0818.d011666
#print axioms _root_.GD.N0232.N0719.N0818.d011667
#print axioms _root_.GD.N0232.N0719.N0818.d011668
#print axioms _root_.GD.N0232.N0719.N0818.d011669
#print axioms _root_.GD.N0232.N0719.N0818.d011670
#print axioms _root_.GD.N0232.N0719.N0818.d011671
#print axioms _root_.GD.N0232.N0719.N0818.d011672
#print axioms _root_.GD.N0232.N0719.N0818.d011673
#print axioms _root_.GD.N0232.N0719.N0818.d011674
