import GD.Module0729
import GD.Module0765
import GD.Module0134


































open Filter Set

namespace GD
namespace N0232
namespace N0719
namespace N0810

noncomputable section

open _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0870
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0580
open _root_.GD.N0230.N0718

variable {k : ℕ} {V Q : Type*}
variable [AddCommGroup V] [Module ℝ V]




variable (Theta : _root_.GD.N0232.N0719.N0809.d010964 k → Type*)


abbrev d011629 (k : ℕ) (c : _root_.GD.N0232.N0719.N0809.d010964 k) :=
  {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
    _root_.GD.N0232.N0719.N0815.d010928 c.1 theta ≤ _root_.GD.N0232.N0719.N0815.d010938 c.2}



theorem d011630
    {c : _root_.GD.N0232.N0719.N0809.d010964 k}
    (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0810.d011629 k c) :
    ∀ n, _root_.GD.N0232.N0719.N0815.d010928 c.1 (thetaSeq n).1 ≤ _root_.GD.N0232.N0719.N0815.d010938 c.2 := by
  intro n
  exact (thetaSeq n).2


@[simp] theorem d011631
    (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0815.d010928 (∅ : Finset (Fin k)) theta = 1 := by
  unfold _root_.GD.N0232.N0719.N0815.d010928
  change _root_.GD.N0232.N0719.N0815.d010926 theta / _root_.GD.N0232.N0719.N0815.d010926 theta = 1
  exact div_self (_root_.GD.N0232.N0719.N0815.d010927 hk theta).ne'


theorem d011632
    (hk : 0 < k) (active : Finset (Fin k)) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 ≤ _root_.GD.N0232.N0719.N0815.d010928 active theta := by
  unfold _root_.GD.N0232.N0719.N0815.d010928
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ ↦ (_root_.GD.N0232.N0719.N0815.d010925 theta i).le
  · exact (_root_.GD.N0232.N0719.N0815.d010927 hk theta).le


theorem d011633 (depth : ℕ) :
    _root_.GD.N0232.N0719.N0815.d010938 (depth + 1) < 1 := by
  unfold _root_.GD.N0232.N0719.N0815.d010938
  have hden : 0 < ((depth + 1 : ℕ) : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hden]
  norm_num
  positivity



theorem d011634
    (hk : 0 < k) (depth : ℕ) :
    ¬ Nonempty
      (_root_.GD.N0232.N0719.N0810.d011629 k
        ((∅ : Finset (Fin k)), depth + 1)) := by
  rintro ⟨theta⟩
  have hmem := theta.2
  rw [_root_.GD.N0232.N0719.N0810.d011631 hk] at hmem
  exact (not_le_of_gt (_root_.GD.N0232.N0719.N0810.d011633 depth)) hmem




theorem d011635
    {active : Finset (Fin k)} (hactive : active.Nonempty) (depth : ℕ) :
    Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k (active, depth)) := by
  have htend :=
    _root_.GD.N0232.N0719.N0870.d011607
      hactive (_root_.GD.N0232.N0719.N0859.d010810 k)
  have hradius : 0 < _root_.GD.N0232.N0719.N0815.d010938 depth := by
    unfold _root_.GD.N0232.N0719.N0815.d010938
    positivity
  have heventually : ∀ᶠ n in atTop,
      _root_.GD.N0232.N0719.N0815.d010928 active
          (_root_.GD.N0232.N0719.N0870.d011590 active (_root_.GD.N0232.N0719.N0859.d010810 k) n) <
        _root_.GD.N0232.N0719.N0815.d010938 depth :=
    (tendsto_order.1 htend).2 (_root_.GD.N0232.N0719.N0815.d010938 depth) hradius
  obtain ⟨n, hn⟩ := heventually.exists
  exact ⟨⟨_root_.GD.N0232.N0719.N0870.d011590 active (_root_.GD.N0232.N0719.N0859.d010810 k) n, hn.le⟩⟩




theorem d011636
    (hk : 0 < k) (active : Finset (Fin k)) (depth : ℕ) :
    Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k (active, depth)) ↔
      active.Nonempty ∨ depth = 0 := by
  constructor
  · intro h
    by_cases hactive : active.Nonempty
    · exact Or.inl hactive
    · right
      have hempty : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hactive
      subst active
      cases depth with
      | zero => rfl
      | succ depth =>
          exact False.elim
            (_root_.GD.N0232.N0719.N0810.d011634 hk depth h)
  · rintro (hactive | rfl)
    · exact _root_.GD.N0232.N0719.N0810.d011635 hactive depth
    · by_cases hactive : active.Nonempty
      · exact _root_.GD.N0232.N0719.N0810.d011635 hactive 0
      · have hempty : active = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hactive
        subst active
        refine ⟨⟨_root_.GD.N0232.N0719.N0859.d010810 k, ?_⟩⟩
        simp [_root_.GD.N0232.N0719.N0815.d010938, _root_.GD.N0232.N0719.N0810.d011631 hk]



def d011637
    (tax : ∀ c, Theta c → V → V → ℝ) (p q : V) : Prop :=
  p ≠ q ∧
    ∀ c : _root_.GD.N0232.N0719.N0809.d010964 k, Nonempty (Theta c) →
      ∃ thetaSeq : ℕ → Theta c,
      Tendsto (fun n ↦ tax c (thetaSeq n) p q) atTop (nhds 0)



theorem d011638
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    {p : V} (hp : ∀ n, p ∈ face n) (stage : ℕ) :
    IsMinOn (objective (schedule stage)) (face stage) p := by
  have hpSucc : p ∈ face (stage + 1) := hp (stage + 1)
  rw [htower.2 stage] at hpSucc
  exact hpSucc.2




theorem d011639
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (profile : ∀ c, Theta c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, Theta c → V → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n, Nonempty (Theta (schedule n)) → ∀ d, d ∈ face n →
      IsLUB
        (Set.range
          (fun theta : Theta (schedule n) ↦
            profile (schedule n) theta d))
        (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hq : ∀ n, q ∈ face n)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2)
    (stage : ℕ)
    (hTheta : Nonempty (Theta (schedule stage))) :
    objective (schedule stage) (_root_.GD.N0230.N0718.d001528 p q) =
      objective (schedule stage) p := by
  have hpMin :=
    _root_.GD.N0232.N0719.N0810.d011638 schedule objective C face htower hp stage
  have hqMin :=
    _root_.GD.N0232.N0719.N0810.d011638 schedule objective C face htower hq stage
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ face stage := by
    unfold _root_.GD.N0230.N0718.d001528
    apply hconvex stage (hp stage) (hq stage)
    · norm_num
    · norm_num
    · norm_num
  have hObjEq : objective (schedule stage) q =
      objective (schedule stage) p :=
    le_antisymm (hqMin (hp stage)) (hpMin (hq stage))
  apply le_antisymm
  · apply (hSup stage hTheta _ hmid).2
    rintro value ⟨theta, rfl⟩
    have hpBound : profile (schedule stage) theta p ≤
        objective (schedule stage) p :=
      (hSup stage hTheta p (hp stage)).1 ⟨theta, rfl⟩
    have hqBound : profile (schedule stage) theta q ≤
        objective (schedule stage) p := by
      rw [← hObjEq]
      exact (hSup stage hTheta q (hq stage)).1 ⟨theta, rfl⟩
    linarith [hExact (schedule stage) theta,
      hTaxNonnegative (schedule stage) theta]
  · exact hpMin hmid



theorem d011640
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, Theta c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, Theta c → V → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n, Nonempty (Theta (schedule n)) → ∀ d, d ∈ face n →
      IsLUB
        (Set.range
          (fun theta : Theta (schedule n) ↦
            profile (schedule n) theta d))
        (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hq : ∀ n, q ∈ face n)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2) :
    ∀ c : _root_.GD.N0232.N0719.N0809.d010964 k, Nonempty (Theta c) →
      objective c (_root_.GD.N0230.N0718.d001528 p q) = objective c p := by
  intro c hc
  obtain ⟨stage, hstage⟩ := hschedule c
  subst c
  exact _root_.GD.N0232.N0719.N0810.d011639
    Theta schedule profile objective tax C face htower hconvex hSup hp hq
    hTaxNonnegative hExact stage hc








theorem d011641
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, Theta c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, Theta c → V → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n, Nonempty (Theta (schedule n)) → ∀ d, d ∈ face n →
      IsLUB
        (Set.range
          (fun theta : Theta (schedule n) ↦
            profile (schedule n) theta d))
        (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hq : ∀ n, q ∈ face n)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2) :
    ∀ c : _root_.GD.N0232.N0719.N0809.d010964 k, Nonempty (Theta c) →
      ∃ thetaSeq : ℕ → Theta c,
      (∀ n : ℕ,
        objective c p - 1 / ((n : ℝ) + 1) <
          profile c (thetaSeq n) (_root_.GD.N0230.N0718.d001528 p q)) ∧
      Tendsto (fun n ↦ tax c (thetaSeq n) p q) atTop (nhds 0) ∧
      (∀ n : ℕ,
        objective c p - 2 * (1 / ((n : ℝ) + 1)) <
          profile c (thetaSeq n) p) ∧
      (∀ n : ℕ,
        objective c p - 2 * (1 / ((n : ℝ) + 1)) <
          profile c (thetaSeq n) q) := by
  intro c hc
  obtain ⟨stage, hstage⟩ := hschedule c
  subst c
  exact
    _root_.GD.N0230.N0718.d001533
      (face stage) (hconvex stage)
      (profile (schedule stage)) (objective (schedule stage))
      (tax (schedule stage))
      (hp stage) (hq stage)
      (_root_.GD.N0232.N0719.N0810.d011638 schedule objective C face htower hp stage)
      (_root_.GD.N0232.N0719.N0810.d011638 schedule objective C face htower hq stage)
      (hSup stage hc)
      (hTaxNonnegative (schedule stage))
      (hExact (schedule stage))








theorem d011642
    (hk0 : 0 < k)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, _root_.GD.N0232.N0719.N0810.d011629 k c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, _root_.GD.N0232.N0719.N0810.d011629 k c → V → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n,
      Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k (schedule n)) →
      ∀ d, d ∈ face n →
        IsLUB
          (Set.range
            (fun theta : _root_.GD.N0232.N0719.N0810.d011629 k (schedule n) ↦
              profile (schedule n) theta d))
          (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hq : ∀ n, q ∈ face n)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2)
    {active : Finset (Fin k)} (hactive : active.Nonempty) :
    ∃ thetaSeq : ∀ depth : ℕ,
        _root_.GD.N0232.N0719.N0810.d011629 k (active, depth),
      Tendsto
          (fun depth ↦ _root_.GD.N0232.N0719.N0815.d010928 active (thetaSeq depth).1)
          atTop (nhds 0) ∧
        Tendsto
          (fun depth ↦ tax (active, depth) (thetaSeq depth) p q)
          atTop (nhds 0) := by
  have hradiusPos : ∀ depth : ℕ, 0 < _root_.GD.N0232.N0719.N0815.d010938 depth := by
    intro depth
    unfold _root_.GD.N0232.N0719.N0815.d010938
    positivity
  have hsmall : ∀ depth : ℕ,
      ∃ theta : _root_.GD.N0232.N0719.N0810.d011629 k (active, depth),
        tax (active, depth) theta p q < _root_.GD.N0232.N0719.N0815.d010938 depth := by
    intro depth
    have hnonempty : Nonempty (_root_.GD.N0232.N0719.N0810.d011629 k (active, depth)) :=
      _root_.GD.N0232.N0719.N0810.d011635 hactive depth
    obtain ⟨innerSeq, _, htax, _, _⟩ :=
      _root_.GD.N0232.N0719.N0810.d011641
        (fun c ↦ _root_.GD.N0232.N0719.N0810.d011629 k c)
        schedule hschedule profile objective tax C face htower hconvex
        hSup hp hq hTaxNonnegative hExact (active, depth) hnonempty
    have heventually : ∀ᶠ n in atTop,
        tax (active, depth) (innerSeq n) p q < _root_.GD.N0232.N0719.N0815.d010938 depth :=
      (tendsto_order.1 htax).2 (_root_.GD.N0232.N0719.N0815.d010938 depth) (hradiusPos depth)
    obtain ⟨n, hn⟩ := heventually.exists
    exact ⟨innerSeq n, hn⟩
  choose thetaSeq hthetaSeq using hsmall
  have hradiusTendsto : Tendsto _root_.GD.N0232.N0719.N0815.d010938 atTop (nhds 0) := by
    have hfun : _root_.GD.N0232.N0719.N0815.d010938 = (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) := by
      funext n
      simp [_root_.GD.N0232.N0719.N0815.d010938]
    rw [hfun]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨thetaSeq, ?_, ?_⟩
  · exact squeeze_zero
      (fun depth ↦ _root_.GD.N0232.N0719.N0810.d011632 hk0 active (thetaSeq depth).1)
      (fun depth ↦ (thetaSeq depth).2)
      hradiusTendsto
  · exact squeeze_zero
      (fun depth ↦ hTaxNonnegative (active, depth) (thetaSeq depth))
      (fun depth ↦ (hthetaSeq depth).le)
      hradiusTendsto


theorem d011643
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, Theta c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, Theta c → V → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n, Nonempty (Theta (schedule n)) → ∀ d, d ∈ face n →
      IsLUB
        (Set.range
          (fun theta : Theta (schedule n) ↦
            profile (schedule n) theta d))
        (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hq : ∀ n, q ∈ face n)
    (hpq : p ≠ q)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2) :
    _root_.GD.N0232.N0719.N0810.d011637 Theta tax p q := by
  refine ⟨hpq, ?_⟩
  intro c hc
  obtain ⟨thetaSeq, _, htax, _, _⟩ :=
    _root_.GD.N0232.N0719.N0810.d011641
      Theta schedule hschedule profile objective tax C face htower hconvex
      hSup hp hq hTaxNonnegative hExact c hc
  exact ⟨thetaSeq, htax⟩





theorem d011644
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, Theta c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, Theta c → V → V → ℝ)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n, Nonempty (Theta (schedule n)) → ∀ d, d ∈ face n →
      IsLUB
        (Set.range
          (fun theta : Theta (schedule n) ↦
            profile (schedule n) theta d))
        (objective (schedule n) d))
    (hTaxNonnegative : ∀ p q, (∀ n, p ∈ face n) →
      (∀ n, q ∈ face n) →
      ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ p q, (∀ n, p ∈ face n) →
      (∀ n, q ∈ face n) →
      ∀ c theta,
        profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
          (profile c theta p + profile c theta q) / 2) :
    (∃ p q, (∀ n, p ∈ face n) ∧ (∀ n, q ∈ face n) ∧ p ≠ q) ↔
      ∃ p q, (∀ n, p ∈ face n) ∧ (∀ n, q ∈ face n) ∧
        _root_.GD.N0232.N0719.N0810.d011637 Theta tax p q := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq⟩
    refine ⟨p, q, hp, hq, ?_⟩
    exact _root_.GD.N0232.N0719.N0810.d011643
      Theta schedule hschedule profile objective tax C face htower hconvex
      hSup hp hq hpq (hTaxNonnegative p q hp hq) (hExact p q hp hq)
  · rintro ⟨p, q, hp, hq, hescape⟩
    exact ⟨p, q, hp, hq, hescape.1⟩












theorem d011645
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, Theta c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, Theta c → V → V → ℝ)
    (classMap : V → Q)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n, Nonempty (Theta (schedule n)) → ∀ d, d ∈ face n →
      IsLUB
        (Set.range
          (fun theta : Theta (schedule n) ↦
            profile (schedule n) theta d))
        (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hqC : q ∈ C)
    (hequal : ∀ c, objective c q = objective c p)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2)
    (hNoEscape : classMap p ≠ classMap q →
      ∃ c : _root_.GD.N0232.N0719.N0809.d010964 k,
        Nonempty (Theta c) ∧
        ∀ thetaSeq : ℕ → Theta c,
          ¬ Tendsto (fun n ↦ tax c (thetaSeq n) p q) atTop (nhds 0)) :
    classMap p = classMap q := by
  have hq : ∀ n, q ∈ face n :=
    _root_.GD.N0230.N0580.d001536
      (fun n ↦ objective (schedule n)) C face htower hp hqC
      (fun n ↦ hequal (schedule n))
  by_contra hpq
  obtain ⟨c, hc, hNoSequence⟩ := hNoEscape hpq
  obtain ⟨thetaSeq, _, htax, _, _⟩ :=
    _root_.GD.N0232.N0719.N0810.d011641
      Theta schedule hschedule profile objective tax C face htower hconvex
      hSup hp hq hTaxNonnegative hExact c hc
  exact hNoSequence thetaSeq htax


theorem d011646
    {Omega : Type*} [MeasurableSpace Omega]
    (mu0 : MeasureTheory.Measure Omega)
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, Theta c →
      _root_.GD.N0230.N0602.d000116 mu0 → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k →
      _root_.GD.N0230.N0602.d000116 mu0 → ℝ)
    (tax : ∀ c, Theta c →
      _root_.GD.N0230.N0602.d000116 mu0 →
      _root_.GD.N0230.N0602.d000116 mu0 → ℝ)
    (C : Set (_root_.GD.N0230.N0602.d000116 mu0))
    (face : ℕ →
      Set (_root_.GD.N0230.N0602.d000116 mu0))
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n, Nonempty (Theta (schedule n)) → ∀ d, d ∈ face n →
      IsLUB
        (Set.range
          (fun theta : Theta (schedule n) ↦
            profile (schedule n) theta d))
        (objective (schedule n) d))
    {p q : _root_.GD.N0230.N0602.d000116 mu0}
    (hp : ∀ n, p ∈ face n) (hqC : q ∈ C)
    (hequal : ∀ c, objective c q = objective c p)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2)
    (hNoEscape : p ≠ q →
      ∃ c : _root_.GD.N0232.N0719.N0809.d010964 k,
        Nonempty (Theta c) ∧
        ∀ thetaSeq : ℕ → Theta c,
          ¬ Tendsto (fun n ↦ tax c (thetaSeq n) p q) atTop (nhds 0)) :
    p = q := by
  exact _root_.GD.N0232.N0719.N0810.d011645
    Theta schedule hschedule profile objective tax id C face htower hconvex
    hSup hp hqC hequal hTaxNonnegative hExact hNoEscape





theorem d011647
    (schedule : ℕ → _root_.GD.N0232.N0719.N0809.d010964 k)
    (hschedule : _root_.GD.N0232.N0719.N0809.d010965 schedule)
    (profile : ∀ c, Theta c → V → ℝ)
    (objective : _root_.GD.N0232.N0719.N0809.d010964 k → V → ℝ)
    (tax : ∀ c, Theta c → V → V → ℝ)
    (classMap : V → Q)
    (C : Set V) (face : ℕ → Set V)
    (htower : _root_.GD.N0230.N0583.d000745 (fun n ↦ objective (schedule n)) C face)
    (hconvex : ∀ n, Convex ℝ (face n))
    (hSup : ∀ n, Nonempty (Theta (schedule n)) → ∀ d, d ∈ face n →
      IsLUB
        (Set.range
          (fun theta : Theta (schedule n) ↦
            profile (schedule n) theta d))
        (objective (schedule n) d))
    {p q : V}
    (hp : ∀ n, p ∈ face n) (hqC : q ∈ C)
    (hequal : ∀ c, objective c q = objective c p)
    (hTaxNonnegative : ∀ c theta, 0 ≤ tax c theta p q)
    (hExact : ∀ c theta,
      profile c theta (_root_.GD.N0230.N0718.d001528 p q) + tax c theta p q =
        (profile c theta p + profile c theta q) / 2)
    (hUniform : classMap p ≠ classMap q →
      ∃ (c : _root_.GD.N0232.N0719.N0809.d010964 k) (_hc : Nonempty (Theta c)) (epsilon : ℝ),
        0 < epsilon ∧
        ∀ theta : Theta c, epsilon ≤ tax c theta p q) :
    classMap p = classMap q := by
  apply _root_.GD.N0232.N0719.N0810.d011645
    Theta schedule hschedule profile objective tax classMap C face htower
    hconvex hSup hp hqC hequal hTaxNonnegative hExact
  intro hpq
  obtain ⟨c, hc, epsilon, hepsilon, hlower⟩ := hUniform hpq
  refine ⟨c, hc, ?_⟩
  intro thetaSeq hseq
  have heventually : ∀ᶠ n in atTop,
      tax c (thetaSeq n) p q < epsilon :=
    (tendsto_order.1 hseq).2 epsilon hepsilon
  obtain ⟨n, hn⟩ := heventually.exists
  exact (not_lt_of_ge (hlower (thetaSeq n))) hn

end

end N0810
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0810.d011638
#print axioms _root_.GD.N0232.N0719.N0810.d011630
#print axioms _root_.GD.N0232.N0719.N0810.d011631
#print axioms _root_.GD.N0232.N0719.N0810.d011634
#print axioms _root_.GD.N0232.N0719.N0810.d011635
#print axioms _root_.GD.N0232.N0719.N0810.d011636
#print axioms _root_.GD.N0232.N0719.N0810.d011639
#print axioms _root_.GD.N0232.N0719.N0810.d011640
#print axioms _root_.GD.N0232.N0719.N0810.d011641
#print axioms _root_.GD.N0232.N0719.N0810.d011642
#print axioms _root_.GD.N0232.N0719.N0810.d011643
#print axioms _root_.GD.N0232.N0719.N0810.d011644
#print axioms _root_.GD.N0232.N0719.N0810.d011645
#print axioms _root_.GD.N0232.N0719.N0810.d011646
#print axioms _root_.GD.N0232.N0719.N0810.d011647
