import GD.Module0919



























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1070

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0230.N0553
open _root_.GD.N0230.N0554
open _root_.GD.N0230.N0567
open _root_.GD.N0230.N0587
open _root_.GD.N0230.N0585
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0718
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn

noncomputable local instance : Nonempty _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨_root_.GD.N0232.N0720.N1080.d014169⟩






def d014384 : Prop :=
  ∀ p q,
    p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn →
    q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn →
    IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p →
    IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) q →
    ∀ k : _root_.GD.N0232.N0720.N1066.d014331 m n hm hn,
      k ∉ Set.range (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn)) →
      _root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) k p =
          _root_.GD.N0232.N0720.N1066.d014332 m n hm hn p →
      _root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) k q =
          _root_.GD.N0232.N0720.N1066.d014332 m n hm hn q →
      _root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) k p q = 0 →
      p = q





theorem d014385 :
    _root_.GD.N0230.N0553.d001612
        (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
        (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1070.d014384 m n hm hn := by
  constructor
  · intro hfull p q hp hq hpMin hqMin k hkBoundary hpActive hqActive hzero
    exact hfull p q hp hq hpMin hqMin k hpActive hqActive hzero
  · intro hboundary p q hp hq hpMin hqMin k hpActive hqActive hzero
    by_cases hk : k ∈ Set.range
        (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
    · obtain ⟨theta, rfl⟩ := hk
      exact _root_.GD.N0232.N0720.N1066.d014342
        m n hm hn theta hp hq hzero
    · exact hboundary p q hp hq hpMin hqMin k hk
        hpActive hqActive hzero






def d014386
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p q : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn)
    (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta) p q



theorem d014387
    (theta : _root_.GD.N0232.N0720.N1080.d014168) {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1070.d014386 m n hm hn theta p q =
      (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) 0
          (_root_.GD.N0230.N0670.d001646
            ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p)
            ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm q)) /
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal := by
  exact _root_.GD.N0232.N0720.N1066.d014341
    m n hm hn theta hp hq





def d014388
    (p q : _root_.GD.N0232.N0720.N1025.d014303 m n) : Prop :=
  ∃ thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168,
    Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1070.d014386 m n hm hn (thetaSeq j) p q)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1066.d014332 m n hm hn p -
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (thetaSeq j) p)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1066.d014332 m n hm hn q -
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn (thetaSeq j) q)
        atTop (nhds 0)







theorem d014389
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hpMin : IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p)
    (hqMin : IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) q) :
    _root_.GD.N0232.N0720.N1070.d014388 m n hm hn p q := by
  let F := _root_.GD.N0232.N0720.N1066.d014330 m n hm hn
  let profileTax : _root_.GD.N0232.N0720.N1080.d014168 → _root_.GD.N0232.N0720.N1025.d014303 m n →
      _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ :=
    fun theta x y ↦ _root_.GD.N0230.N0567.d001641 F (_root_.GD.N0230.N0567.d001626 F theta) x y
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014312 m n hm hn hp hq
      (by norm_num) (by norm_num) (by norm_num)
  have hLUB : IsLUB
      (Set.range (fun theta ↦
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q)))
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn (_root_.GD.N0230.N0718.d001528 p q)) := by
    exact _root_.GD.N0230.N0567.d001638 F hmid
  have hexact : ∀ theta,
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta (_root_.GD.N0230.N0718.d001528 p q) +
          profileTax theta p q =
        (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p +
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q) / 2 := by
    intro theta
    change F.profile theta (_root_.GD.N0230.N0718.d001528 p q) +
        profileTax theta p q =
      (F.profile theta p + F.profile theta q) / 2
    dsimp [profileTax]
    have h := _root_.GD.N0230.N0567.d001642 F
      (_root_.GD.N0230.N0567.d001626 F theta) p q
    rw [_root_.GD.N0230.N0567.d001633 F theta hmid,
      _root_.GD.N0230.N0567.d001633 F theta hp,
      _root_.GD.N0230.N0567.d001633 F theta hq] at h
    exact h
  have htax : ∀ theta, 0 ≤ profileTax theta p q := by
    intro theta
    exact _root_.GD.N0232.N0720.N1066.d014339 m n hm hn hp hq
      (_root_.GD.N0230.N0567.d001626 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) theta)
  have hupperP : ∀ theta,
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta p ≤
        _root_.GD.N0232.N0720.N1066.d014332 m n hm hn p := by
    intro theta
    exact (_root_.GD.N0230.N0567.d001638 F hp).1
      ⟨theta, rfl⟩
  have hupperQ : ∀ theta,
      _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta q ≤
        _root_.GD.N0232.N0720.N1066.d014332 m n hm hn q := by
    intro theta
    exact (_root_.GD.N0230.N0567.d001638 F hq).1
      ⟨theta, rfl⟩
  have hObjEq :
      _root_.GD.N0232.N0720.N1066.d014332 m n hm hn p =
        _root_.GD.N0232.N0720.N1066.d014332 m n hm hn q :=
    le_antisymm (hpMin hq) (hqMin hp)
  have hnonnegative :
      0 ≤ _root_.GD.N0230.N0554.d001563
        (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn) p q :=
    _root_.GD.N0230.N0587.d001593
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn) profileTax
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn) p q hLUB hexact htax
      hupperP hupperQ
  have hnonpositive :
      _root_.GD.N0230.N0554.d001563
        (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn) p q ≤ 0 := by
    unfold _root_.GD.N0230.N0554.d001563
    rw [hObjEq]
    have hminimum := hpMin hmid
    change _root_.GD.N0232.N0720.N1066.d014332 m n hm hn p ≤
      _root_.GD.N0232.N0720.N1066.d014332 m n hm hn (_root_.GD.N0230.N0718.d001528 p q) at hminimum
    linarith
  have hflat :
      _root_.GD.N0230.N0554.d001563
        (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn) p q = 0 :=
    le_antisymm hnonpositive hnonnegative
  obtain ⟨thetaSeq, htaxZero, hpSlackZero, hqSlackZero⟩ :=
    (_root_.GD.N0230.N0587.d001591
      (_root_.GD.N0232.N0720.N1066.d014327 m n hm hn) profileTax
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn) p q hLUB hexact htax
      hupperP hupperQ).1 hflat
  refine ⟨thetaSeq, ?_, hpSlackZero, hqSlackZero⟩
  simpa [_root_.GD.N0232.N0720.N1070.d014386, profileTax, F] using htaxZero




def d014390 : Prop :=
  ∀ p q,
    p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn →
    q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn →
    IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p →
    IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) q →
    _root_.GD.N0232.N0720.N1070.d014388 m n hm hn p q →
    p = q




theorem d014391
    (hfaithful :
      _root_.GD.N0232.N0720.N1070.d014390 m n hm hn) :
    _root_.GD.N0230.N0553.d001612
      (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  intro p q hp hq hpMin hqMin _k _hpActive _hqActive _hzero
  exact hfaithful p q hp hq hpMin hqMin
    (_root_.GD.N0232.N0720.N1070.d014389
      m n hm hn hp hq hpMin hqMin)






theorem d014392
    (hfaithful : _root_.GD.N0230.N0553.d001612
      (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)) :
    _root_.GD.N0232.N0720.N1070.d014390 m n hm hn := by
  have hrigid : _root_.GD.N0230.N0585.d001306
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
    apply _root_.GD.N0230.N0553.d001613
      (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    · exact _root_.GD.N0232.N0720.N1025.d014312 m n hm hn
    · intro d hd
      exact _root_.GD.N0230.N0567.d001639
        (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) hd
    · intro p hp q hq k
      exact _root_.GD.N0230.N0567.d001642
        (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) k p q
    · intro p hp q hq k
      exact _root_.GD.N0232.N0720.N1066.d014339 m n hm hn hp hq k
    · intro p hp q hq
      exact _root_.GD.N0230.N0587.d001594
        (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn) p q
        (fun k ↦ _root_.GD.N0230.N0567.d001642
          (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) k p q)
        (_root_.GD.N0230.N0567.d001634
          (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn) (_root_.GD.N0230.N0718.d001528 p q))
    · exact hfaithful
  intro p q hp hq hpMin hqMin _hcollapse
  exact hrigid hp hq hpMin hqMin





theorem d014393 :
    _root_.GD.N0230.N0553.d001612
        (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
        (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1070.d014390 m n hm hn := by
  exact ⟨
    _root_.GD.N0232.N0720.N1070.d014392
      m n hm hn,
    _root_.GD.N0232.N0720.N1070.d014391
      m n hm hn⟩





theorem d014394 :
    ¬ _root_.GD.N0232.N0720.N1070.d014390 m n hm hn ↔
      ∃ p q,
        p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ∧
        q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ∧
        IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
          (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p ∧
        IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
          (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) q ∧
        _root_.GD.N0232.N0720.N1070.d014388 m n hm hn p q ∧
        p ≠ q := by
  constructor
  · intro hnot
    unfold _root_.GD.N0232.N0720.N1070.d014390 at hnot
    push Not at hnot
    obtain ⟨p, q, hp, hq, hpMin, hqMin, hcollapse, hpq⟩ := hnot
    exact ⟨p, q, hp, hq, hpMin, hqMin, hcollapse, hpq⟩
  · rintro ⟨p, q, hp, hq, hpMin, hqMin, hcollapse, hpq⟩ hfaithful
    exact hpq (hfaithful p q hp hq hpMin hqMin hcollapse)





theorem
    d014395 :
    (¬ _root_.GD.N0230.N0553.d001612
      (_root_.GD.N0230.N0567.d001631 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0230.N0567.d001641 (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
      (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)) ↔
      ∃ p q,
        p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ∧
        q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ∧
        IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
          (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p ∧
        IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
          (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) q ∧
        _root_.GD.N0232.N0720.N1070.d014388 m n hm hn p q ∧
        p ≠ q := by
  rw [_root_.GD.N0232.N0720.N1070.d014393]
  exact _root_.GD.N0232.N0720.N1070.d014394 m n hm hn




theorem
    d014396
    (hfaithful :
      _root_.GD.N0232.N0720.N1070.d014390 m n hm hn) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0720.N1025.d014301) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0720.N1025.d014301) (y : ℝ) ↦ g • y) repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired <
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      (∀ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired) →
        ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] repaired) := by
  exact
    _root_.GD.N0232.N0720.N1066.d014351
      m n hm hn
      (_root_.GD.N0232.N0720.N1070.d014391
        m n hm hn hfaithful)



theorem
    d014397
    (hfaithful :
      _root_.GD.N0232.N0720.N1070.d014384 m n hm hn) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0720.N1025.d014301) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0720.N1025.d014301) (y : ℝ) ↦ g • y) repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired <
          _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      (∀ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
        Measurable d →
        (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n theta repaired) →
        ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] repaired) := by
  exact
    _root_.GD.N0232.N0720.N1066.d014351
      m n hm hn
      ((_root_.GD.N0232.N0720.N1070.d014385
        m n hm hn).2 hfaithful)

end

end N1070
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1070.d014385
#print axioms _root_.GD.N0232.N0720.N1070.d014387
#print axioms _root_.GD.N0232.N0720.N1070.d014389
#print axioms _root_.GD.N0232.N0720.N1070.d014391
#print axioms _root_.GD.N0232.N0720.N1070.d014392
#print axioms _root_.GD.N0232.N0720.N1070.d014393
#print axioms _root_.GD.N0232.N0720.N1070.d014394
#print axioms _root_.GD.N0232.N0720.N1070.d014395
#print axioms _root_.GD.N0232.N0720.N1070.d014396
#print axioms _root_.GD.N0232.N0720.N1070.d014397
