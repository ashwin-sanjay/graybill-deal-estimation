import GD.Module0154
import GD.Module0767























open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0823

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
open _root_.GD.N0232.N0719.N0818
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0566
open _root_.GD.N0230.N0569
open _root_.GD.N0230.N0628
open _root_.GD.N0230.N0600
open _root_.GD.N0230.N0680
open _root_.GD.N0230.N0643
open _root_.GD.N0230.N0554
open _root_.GD.N0230.N0651
open _root_.GD.N0230.N0705









def d011710
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) : Prop :=
  ∀ p q,
    _root_.GD.N0230.N0643.d001717
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage)
      (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) p q →
    p ≠ q →
    ∃ i : ℕ,
      Nonempty (_root_.GD.N0232.N0719.N0818.d011655 k stage i) ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ∀ theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i,
          epsilon ≤
            _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q +
              _root_.GD.N0230.N0554.d001565
                (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
                  _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1)
                (_root_.GD.N0232.N0719.N0818.d011653
                  k sizes hk hsizes stage i) theta p q



def d011711
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  _root_.GD.N0232.N0719.N0823.d011710 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0809.d010966 k)




def d011712
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) : Prop :=
  ∀ p q,
    _root_.GD.N0230.N0643.d001717
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage)
      (_root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) p q →
    p ≠ q →
    ∃ i : ℕ,
      Nonempty (_root_.GD.N0232.N0719.N0818.d011655 k stage i) ∧
      _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0230.N0718.d001528 p q) <
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p




theorem N1754.d011713
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hmatched : _root_.GD.N0232.N0719.N0818.d011656
      k sizes hk hsizes stage) :
    _root_.GD.N0232.N0719.N0823.d011710
      k sizes hk hsizes stage := by
  intro p q hclones hpq
  obtain ⟨i, eta, theta, heta, hactive, htax⟩ :=
    hmatched p q hclones hpq
  have hLUB : IsLUB
      (Set.range (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
          (_root_.GD.N0230.N0718.d001528 p q)))
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
        (_root_.GD.N0230.N0718.d001528 p q)) := by
    apply _root_.GD.N0232.N0719.N0812.d011048
      k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
    · unfold _root_.GD.N0230.N0718.d001528
      apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hclones.1 hclones.2.1
      · norm_num
      · norm_num
      · norm_num
    · exact ⟨theta⟩
  have hexact : ∀ theta' : _root_.GD.N0232.N0719.N0818.d011655 k stage i,
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta'.1
            (_root_.GD.N0230.N0718.d001528 p q) +
          _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta'.1 p q =
        (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta'.1 p +
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta'.1 q) / 2 := by
    intro theta'
    exact _root_.GD.N0232.N0719.N0811.d011040
      k sizes hk hsizes theta'.1 hclones.1 hclones.2.1
  have hstrict :
      _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0230.N0718.d001528 p q) <
        (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i p +
          _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i q) / 2 :=
    _root_.GD.N0230.N0643.d001723
      (_root_.GD.N0232.N0719.N0818.d011655 k stage i)
      (fun theta d ↦
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 d)
      (fun theta p q ↦
        _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i)
      p q
      (fun theta' ↦
        (_root_.GD.N0232.N0719.N0812.d011048
          k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
          hclones.1 ⟨theta⟩).1 ⟨theta', rfl⟩)
      (fun theta' ↦
        (_root_.GD.N0232.N0719.N0812.d011048
          k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
          hclones.2.1 ⟨theta⟩).1 ⟨theta', rfl⟩)
      hexact eta theta hactive htax
  have hdeficit : 0 < _root_.GD.N0230.N0554.d001563
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i) p q := by
    dsimp [_root_.GD.N0230.N0554.d001563]
    exact sub_pos.2 hstrict
  obtain ⟨epsilon, hepsilon, hfloor⟩ :=
    (_root_.GD.N0230.N0651.d001587
      (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1)
      (fun theta p q ↦
        _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i)
      p q hLUB hexact).1 hdeficit
  exact ⟨i, ⟨theta⟩, epsilon, hepsilon, hfloor⟩



theorem d011714
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hresidual : _root_.GD.N0232.N0719.N0823.d011710
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
  obtain ⟨i, hcollar, epsilon, hepsilon, hfloor⟩ :=
    hresidual p q ⟨hp, hq, hclones⟩ hpq
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    unfold _root_.GD.N0230.N0718.d001528
    apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hp hq
    · norm_num
    · norm_num
    · norm_num
  have hLUB : IsLUB
      (Set.range (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
          (_root_.GD.N0230.N0718.d001528 p q)))
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
        (_root_.GD.N0230.N0718.d001528 p q)) :=
    _root_.GD.N0232.N0719.N0812.d011048
      k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
      hmid hcollar
  have hexact : ∀ theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i,
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
            (_root_.GD.N0230.N0718.d001528 p q) +
          _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q =
        (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p +
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q) / 2 := by
    intro theta
    exact _root_.GD.N0232.N0719.N0811.d011040
      k sizes hk hsizes theta.1 hp hq
  have hdeficit : 0 < _root_.GD.N0230.N0554.d001563
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i) p q :=
    (_root_.GD.N0230.N0651.d001587
      (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1)
      (fun theta p q ↦
        _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
      (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i)
      p q hLUB hexact).2 ⟨epsilon, hepsilon, hfloor⟩
  refine ⟨i, ?_⟩
  dsimp [_root_.GD.N0230.N0554.d001563] at hdeficit
  rw [← hclones i] at hdeficit
  linarith




theorem d011715
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) :
    _root_.GD.N0232.N0719.N0823.d011710 k sizes hk hsizes stage ↔
      _root_.GD.N0232.N0719.N0823.d011712 k sizes hk hsizes stage := by
  constructor
  · intro hresidual p q hclones hpq
    obtain ⟨i, hcollar, epsilon, hepsilon, hfloor⟩ :=
      hresidual p q hclones hpq
    have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
      unfold _root_.GD.N0230.N0718.d001528
      apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
        hclones.1 hclones.2.1
      · norm_num
      · norm_num
      · norm_num
    have hLUB : IsLUB
        (Set.range (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
            (_root_.GD.N0230.N0718.d001528 p q)))
        (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0230.N0718.d001528 p q)) :=
      _root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
        hmid hcollar
    have hexact : ∀ theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i,
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
              (_root_.GD.N0230.N0718.d001528 p q) +
            _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q =
          (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p +
            _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q) / 2 := by
      intro theta
      exact _root_.GD.N0232.N0719.N0811.d011040
        k sizes hk hsizes theta.1 hclones.1 hclones.2.1
    have hdeficit : 0 < _root_.GD.N0230.N0554.d001563
        (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i) p q :=
      (_root_.GD.N0230.N0651.d001587
        (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1)
        (fun theta p q ↦
          _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
        (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i)
        p q hLUB hexact).2 ⟨epsilon, hepsilon, hfloor⟩
    refine ⟨i, hcollar, ?_⟩
    dsimp [_root_.GD.N0230.N0554.d001563] at hdeficit
    rw [← hclones.2.2 i] at hdeficit
    linarith
  · intro hstrict p q hclones hpq
    obtain ⟨i, hcollar, hgap⟩ := hstrict p q hclones hpq
    have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
      unfold _root_.GD.N0230.N0718.d001528
      apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
        hclones.1 hclones.2.1
      · norm_num
      · norm_num
      · norm_num
    have hLUB : IsLUB
        (Set.range (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
            (_root_.GD.N0230.N0718.d001528 p q)))
        (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0230.N0718.d001528 p q)) :=
      _root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
        hmid hcollar
    have hexact : ∀ theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i,
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
              (_root_.GD.N0230.N0718.d001528 p q) +
            _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q =
          (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p +
            _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q) / 2 := by
      intro theta
      exact _root_.GD.N0232.N0719.N0811.d011040
        k sizes hk hsizes theta.1 hclones.1 hclones.2.1
    have hdeficit : 0 < _root_.GD.N0230.N0554.d001563
        (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i) p q := by
      dsimp [_root_.GD.N0230.N0554.d001563]
      rw [← hclones.2.2 i]
      linarith
    obtain ⟨epsilon, hepsilon, hfloor⟩ :=
      (_root_.GD.N0230.N0651.d001587
        (fun theta : _root_.GD.N0232.N0719.N0818.d011655 k stage i ↦
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1)
        (fun theta p q ↦
          _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q)
        (_root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i)
        p q hLUB hexact).1 hdeficit
    exact ⟨i, hcollar, epsilon, hepsilon, hfloor⟩



theorem d011716
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hresidual : _root_.GD.N0232.N0719.N0823.d011710
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
    rw [_root_.GD.N0232.N0719.N0816.d010980,
      _root_.GD.N0232.N0719.N0816.d010980] at h
    change
      _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0232.N0719.N0818.d011648 k sizes p) =
        _root_.GD.N0232.N0719.N0818.d011653 k sizes hk hsizes stage i
          (_root_.GD.N0232.N0719.N0818.d011648 k sizes q) at h
    simpa [p', q'] using h
  obtain ⟨i, hi⟩ :=
    _root_.GD.N0232.N0719.N0823.d011714
      k sizes hk hsizes stage hresidual hp' hq' hrealClones hpq'
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
  rw [_root_.GD.N0232.N0719.N0816.d010980,
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



theorem d011717
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hresidual : _root_.GD.N0232.N0719.N0823.d011710
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
    _root_.GD.N0232.N0719.N0823.d011716
      k sizes hk hsizes stage hresidual
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
  exact (not_lt_of_ge (hqNext.2 _ hmidFace)) hgap



theorem d011718
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hresidual : _root_.GD.N0232.N0719.N0823.d011710
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
  exact _root_.GD.N0232.N0719.N0823.d011717
    k sizes hk hsizes stage hresidual hp hq







theorem d011719
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (hresidual : _root_.GD.N0232.N0719.N0823.d011710
      k sizes hk hsizes stage) :
    ∃ p : _root_.GD.N0232.N0719.N0816.d010976 k sizes,
      _root_.GD.N0230.N0569.d001685
          (_root_.GD.N0230.N0566.d000753
            (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
            (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)) p ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0818.d011654 k sizes) p := by
  obtain ⟨p, hunique⟩ :=
    _root_.GD.N0232.N0719.N0823.d011718
      k sizes hk hsizes stage hresidual
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




theorem d011720
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hresidual : _root_.GD.N0232.N0719.N0823.d011711
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
    _root_.GD.N0232.N0719.N0823.d011719
      k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k) hresidual
  refine ⟨_root_.GD.N0232.N0719.N0818.d011648 k sizes p, ?_, ?_⟩
  · simpa using hunique
  · exact _root_.GD.N0232.N0719.N0818.d011672
      k sizes hterminal

end

end N0823
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0823.N1754.d011713
#print axioms _root_.GD.N0232.N0719.N0823.d011714
#print axioms _root_.GD.N0232.N0719.N0823.d011715
#print axioms _root_.GD.N0232.N0719.N0823.d011716
#print axioms _root_.GD.N0232.N0719.N0823.d011717
#print axioms _root_.GD.N0232.N0719.N0823.d011719
#print axioms _root_.GD.N0232.N0719.N0823.d011720
