import Mathlib

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0077.N0315

noncomputable section

universe u v w

def d008178 {Θ : Type u} {D : Type v} (R : Θ → D → ℝ) (d e : D) : Prop :=
  ∀ θ, R θ d ≤ R θ e

def d008179 {Θ : Type u} {D : Type v} (R : Θ → D → ℝ) (d e : D) : Prop :=
  _root_.GD.N0077.N0315.d008178 R d e ∧ ∃ θ, R θ d < R θ e

def d008180 {Θ : Type u} {D : Type v}
    (R : Θ → D → ℝ) (d e : D) : Prop :=
  ∀ θ, R θ d < R θ e

def d008181 {Θ : Type u} {D : Type v} (C : Set D) (R : Θ → D → ℝ) (d : D) : Prop :=
  d ∈ C ∧ ¬ ∃ e ∈ C, _root_.GD.N0077.N0315.d008179 R e d

def d008182 {Θ : Type u} {D : Type v}
    (c : Θ → ℝ) (R : Θ → D → ℝ) : Θ → D → ℝ :=
  fun θ d => c θ * R θ d

def d008183 {Θ : Type u} {Ξ : Type w} {D : Type v}
    (ι : Ξ → Θ) (R : Θ → D → ℝ) : Ξ → D → ℝ :=
  fun ξ d => R (ι ξ) d

theorem d008184 {Θ : Type u} {D : Type v}
    (R : Θ → D → ℝ) (c : Θ → ℝ) (hc : ∀ θ, 0 < c θ) (d e : D) :
    _root_.GD.N0077.N0315.d008178 (_root_.GD.N0077.N0315.d008182 c R) d e ↔ _root_.GD.N0077.N0315.d008178 R d e := by
  unfold _root_.GD.N0077.N0315.d008178 _root_.GD.N0077.N0315.d008182
  exact forall_congr' fun θ => mul_le_mul_iff_right₀ (hc θ)

theorem d008185 {Θ : Type u} {D : Type v}
    (R : Θ → D → ℝ) (c : Θ → ℝ) (hc : ∀ θ, 0 < c θ) (d e : D) :
    _root_.GD.N0077.N0315.d008179 (_root_.GD.N0077.N0315.d008182 c R) d e ↔ _root_.GD.N0077.N0315.d008179 R d e := by
  unfold _root_.GD.N0077.N0315.d008179
  rw [_root_.GD.N0077.N0315.d008184 R c hc]
  apply and_congr_right
  intro _
  exact exists_congr fun θ => mul_lt_mul_iff_right₀ (hc θ)

theorem d008186 {Θ : Type u} {D : Type v}
    (R : Θ → D → ℝ) (c : Θ → ℝ) (hc : ∀ θ, 0 < c θ) (d e : D) :
    _root_.GD.N0077.N0315.d008180 (_root_.GD.N0077.N0315.d008182 c R) d e ↔
      _root_.GD.N0077.N0315.d008180 R d e := by
  unfold _root_.GD.N0077.N0315.d008180 _root_.GD.N0077.N0315.d008182
  exact forall_congr' fun θ => mul_lt_mul_iff_right₀ (hc θ)

theorem d008187 {Θ : Type u} {D : Type v}
    (C : Set D) (R : Θ → D → ℝ) (c : Θ → ℝ) (hc : ∀ θ, 0 < c θ) (d : D) :
    _root_.GD.N0077.N0315.d008181 C (_root_.GD.N0077.N0315.d008182 c R) d ↔ _root_.GD.N0077.N0315.d008181 C R d := by
  simp only [_root_.GD.N0077.N0315.d008181, _root_.GD.N0077.N0315.d008185 R c hc]

theorem d008188 {Θ : Type u} {Ξ : Type w} {D : Type v}
    (R : Θ → D → ℝ) (ι : Ξ → Θ) {d e : D}
    (h : _root_.GD.N0077.N0315.d008178 R d e) :
    _root_.GD.N0077.N0315.d008178 (_root_.GD.N0077.N0315.d008183 ι R) d e :=
  fun ξ => h (ι ξ)

theorem d008189 {Θ : Type u} {Ξ : Type w} {D : Type v}
    (R : Θ → D → ℝ) (ι : Ξ → Θ) {d e : D}
    (h : _root_.GD.N0077.N0315.d008180 R d e) :
    _root_.GD.N0077.N0315.d008180 (_root_.GD.N0077.N0315.d008183 ι R) d e :=
  fun ξ => h (ι ξ)

theorem d008190 {Θ : Type u} {Ξ : Type w} {D : Type v}
    (R : Θ → D → ℝ) (ι : Ξ → Θ) {d e : D} (h : _root_.GD.N0077.N0315.d008178 R d e) :
    _root_.GD.N0077.N0315.d008179 (_root_.GD.N0077.N0315.d008183 ι R) d e ↔ ∃ ξ, R (ι ξ) d < R (ι ξ) e :=
  ⟨fun hstrict => hstrict.2,
    fun hstrict => ⟨_root_.GD.N0077.N0315.d008188 R ι h, hstrict⟩⟩

theorem d008191
    {Θ : Type u} {Ξ : Type w} {D : Type v}
    (R : Θ → D → ℝ) (ι : Ξ → Θ) (hι : Function.Surjective ι) (d e : D) :
    _root_.GD.N0077.N0315.d008178 (_root_.GD.N0077.N0315.d008183 ι R) d e ↔ _root_.GD.N0077.N0315.d008178 R d e := by
  constructor
  · intro h θ
    obtain ⟨ξ, rfl⟩ := hι θ
    exact h ξ
  · exact _root_.GD.N0077.N0315.d008188 R ι

theorem d008192
    {Θ : Type u} {Ξ : Type w} {D : Type v}
    (R : Θ → D → ℝ) (ι : Ξ → Θ) (hι : Function.Surjective ι) (d e : D) :
    _root_.GD.N0077.N0315.d008179 (_root_.GD.N0077.N0315.d008183 ι R) d e ↔ _root_.GD.N0077.N0315.d008179 R d e := by
  constructor
  · rintro ⟨hweak, ξ, hstrict⟩
    exact ⟨(_root_.GD.N0077.N0315.d008191 R ι hι d e).mp hweak,
      ι ξ, hstrict⟩
  · rintro ⟨hweak, θ, hstrict⟩
    obtain ⟨ξ, rfl⟩ := hι θ
    exact ⟨_root_.GD.N0077.N0315.d008188 R ι hweak, ξ, hstrict⟩

theorem d008193
    {Θ : Type u} {Ξ : Type w} {D : Type v}
    (C : Set D) (R : Θ → D → ℝ) (ι : Ξ → Θ) (hι : Function.Surjective ι) (d : D) :
    _root_.GD.N0077.N0315.d008181 C (_root_.GD.N0077.N0315.d008183 ι R) d ↔ _root_.GD.N0077.N0315.d008181 C R d := by
  simp only [_root_.GD.N0077.N0315.d008181, _root_.GD.N0077.N0315.d008192 R ι hι]

theorem d008194
    {Θ : Type u} {Ξ : Type w} {D : Type v} [Nonempty Ξ]
    (C : Set D) (R : Θ → D → ℝ) (ι : Ξ → Θ) (d : D)
    (hstrictify : ∀ e ∈ C, _root_.GD.N0077.N0315.d008179 R e d →
      ∃ f ∈ C, _root_.GD.N0077.N0315.d008180 R f d)
    (hsub : _root_.GD.N0077.N0315.d008181 C (_root_.GD.N0077.N0315.d008183 ι R) d) : _root_.GD.N0077.N0315.d008181 C R d := by
  refine ⟨hsub.1, ?_⟩
  rintro ⟨e, he, hdom⟩
  obtain ⟨f, hf, hstrict⟩ := hstrictify e he hdom
  apply hsub.2
  refine ⟨f, hf, fun ξ => (hstrict (ι ξ)).le, Classical.arbitrary Ξ, ?_⟩
  exact hstrict _

theorem d008195
    {Θ : Type u} {Ξ : Type w} {D : Type v} [Nonempty Ξ]
    (C : Set D) (R : Θ → D → ℝ) (ι : Ξ → Θ) (d : D)
    (midpoint : D → D → D)
    (hclosed : ∀ e ∈ C, midpoint d e ∈ C)
    (hstrictify : ∀ e ∈ C, _root_.GD.N0077.N0315.d008179 R e d →
      _root_.GD.N0077.N0315.d008180 R (midpoint d e) d)
    (hsub : _root_.GD.N0077.N0315.d008181 C (_root_.GD.N0077.N0315.d008183 ι R) d) : _root_.GD.N0077.N0315.d008181 C R d := by
  apply _root_.GD.N0077.N0315.d008194 C R ι d _ hsub
  intro e he hdom
  exact ⟨midpoint d e, hclosed e he, hstrictify e he hdom⟩

structure d008196 (Θ : Type u) (Ω : Type v) [MeasurableSpace Ω] where
  law : Θ → Measure Ω
  probability : ∀ θ, IsProbabilityMeasure (law θ)
  target : Θ → ℝ

def d008196.d008197 {Θ : Type u} {Ω : Type v} [MeasurableSpace Ω]
    (E : _root_.GD.N0077.N0315.d008196 Θ Ω) (θ : Θ) (d : Ω → ℝ) : ℝ :=
  ∫ ω, (d ω - E.target θ) ^ 2 ∂ E.law θ

def d008198 (Ω : Type v) [MeasurableSpace Ω] : Set (Ω → ℝ) :=
  {d | Measurable d}

theorem d008199
    (Ω : Type v) [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] :
    _root_.GD.N0077.N0315.d008198 Ω = Set.univ := by
  ext d
  simp only [_root_.GD.N0077.N0315.d008198, mem_setOf_eq, mem_univ, iff_true]
  exact measurable_of_countable d

def d008200 (b : ℝ) : Bool → ℝ
  | false => 0
  | true => b

def d008201 (Ω : Type v) (a : ℝ) : Ω → ℝ := fun _ => a

def d008202 (b : ℝ) : _root_.GD.N0077.N0315.d008196 Bool Unit where
  law := fun _ => Measure.dirac ()
  probability := fun _ => inferInstance
  target := _root_.GD.N0077.N0315.d008200 b

@[simp] theorem d008203 (b : ℝ) (θ : Bool) (d : Unit → ℝ) :
    (_root_.GD.N0077.N0315.d008202 b).d008197 θ d = (d () - _root_.GD.N0077.N0315.d008200 b θ) ^ 2 := by
  simp [_root_.GD.N0077.N0315.d008196.d008197, _root_.GD.N0077.N0315.d008202]

theorem d008204 (b : ℝ) (θ : Bool) (d : Unit → ℝ) :
    Integrable (fun ω => (d ω - (_root_.GD.N0077.N0315.d008202 b).target θ) ^ 2)
      ((_root_.GD.N0077.N0315.d008202 b).law θ) := by
  change Integrable (fun ω : Unit => (d ω - _root_.GD.N0077.N0315.d008200 b θ) ^ 2) (Measure.dirac ())
  exact integrable_dirac (by finiteness)

def d008205 {D : Type v} (R : Bool → D → ℝ) (d : D) : ℝ :=
  max (R false d) (R true d)

def d008206 {D : Type v} (C : Set D) (R : Bool → D → ℝ) (d : D) : Prop :=
  d ∈ C ∧ ∀ e ∈ C, _root_.GD.N0077.N0315.d008205 R d ≤ _root_.GD.N0077.N0315.d008205 R e

theorem d008207 {D : Type v} (R : Bool → D → ℝ) (d : D) :
    IsLUB (Set.range fun θ => R θ d) (_root_.GD.N0077.N0315.d008205 R d) := by
  constructor
  · rintro _ ⟨θ, rfl⟩
    cases θ
    · exact le_max_left _ _
    · exact le_max_right _ _
  · intro b hb
    exact max_le (hb ⟨false, rfl⟩) (hb ⟨true, rfl⟩)

def d008208 : Bool → ℝ
  | false => 16
  | true => 1

theorem d008209 : ∀ θ, 0 < _root_.GD.N0077.N0315.d008208 θ := by
  intro θ
  cases θ <;> norm_num [_root_.GD.N0077.N0315.d008208]

theorem d008210 :
    _root_.GD.N0077.N0315.d008205 (_root_.GD.N0077.N0315.d008202 3).d008197 (_root_.GD.N0077.N0315.d008201 Unit 1) <
        _root_.GD.N0077.N0315.d008205 (_root_.GD.N0077.N0315.d008202 3).d008197 (_root_.GD.N0077.N0315.d008201 Unit 0) ∧
      _root_.GD.N0077.N0315.d008205 (_root_.GD.N0077.N0315.d008182 _root_.GD.N0077.N0315.d008208 (_root_.GD.N0077.N0315.d008202 3).d008197) (_root_.GD.N0077.N0315.d008201 Unit 0) <
        _root_.GD.N0077.N0315.d008205 (_root_.GD.N0077.N0315.d008182 _root_.GD.N0077.N0315.d008208 (_root_.GD.N0077.N0315.d008202 3).d008197) (_root_.GD.N0077.N0315.d008201 Unit 1) := by
  norm_num [_root_.GD.N0077.N0315.d008205, _root_.GD.N0077.N0315.d008182, _root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008208, _root_.GD.N0077.N0315.d008200]

theorem d008211 :
    _root_.GD.N0077.N0315.d008206 (_root_.GD.N0077.N0315.d008198 Unit) (_root_.GD.N0077.N0315.d008202 3).d008197
      (_root_.GD.N0077.N0315.d008201 Unit (3 / 2)) := by
  refine ⟨measurable_const, ?_⟩
  intro e _he
  have h : (9 / 4 : ℝ) ≤ max ((e ()) ^ 2) ((e () - 3) ^ 2) := by
    by_cases he : e () ≤ 3 / 2
    · apply le_trans _ (le_max_right _ _)
      nlinarith [sq_nonneg (e () - 3 / 2)]
    · apply le_trans _ (le_max_left _ _)
      nlinarith [sq_nonneg (e () - 3 / 2)]
  convert h using 1 <;> norm_num [_root_.GD.N0077.N0315.d008205, _root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008200]

theorem d008212 :
    _root_.GD.N0077.N0315.d008206 (_root_.GD.N0077.N0315.d008198 Unit) (_root_.GD.N0077.N0315.d008182 _root_.GD.N0077.N0315.d008208 (_root_.GD.N0077.N0315.d008202 3).d008197)
      (_root_.GD.N0077.N0315.d008201 Unit (3 / 5)) := by
  refine ⟨measurable_const, ?_⟩
  intro e _he
  have h : (144 / 25 : ℝ) ≤ max (16 * (e ()) ^ 2) ((e () - 3) ^ 2) := by
    by_cases he : e () ≤ 3 / 5
    · apply le_trans _ (le_max_right _ _)
      nlinarith [sq_nonneg (e () - 3 / 5)]
    · apply le_trans _ (le_max_left _ _)
      nlinarith [sq_nonneg (e () - 3 / 5)]
  convert h using 1 <;>
    norm_num [_root_.GD.N0077.N0315.d008205, _root_.GD.N0077.N0315.d008182, _root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008208, _root_.GD.N0077.N0315.d008200]

theorem d008213 :
    ¬ _root_.GD.N0077.N0315.d008206 (_root_.GD.N0077.N0315.d008198 Unit) (_root_.GD.N0077.N0315.d008182 _root_.GD.N0077.N0315.d008208 (_root_.GD.N0077.N0315.d008202 3).d008197)
      (_root_.GD.N0077.N0315.d008201 Unit (3 / 2)) := by
  intro h
  have hbad := h.2 (_root_.GD.N0077.N0315.d008201 Unit 0) measurable_const
  norm_num [_root_.GD.N0077.N0315.d008205, _root_.GD.N0077.N0315.d008182, _root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008208, _root_.GD.N0077.N0315.d008200] at hbad

def d008214 : Unit → Bool := fun _ => false
def d008215 : Unit → Bool := fun _ => true

theorem d008216 :
    _root_.GD.N0077.N0315.d008181 (_root_.GD.N0077.N0315.d008198 Unit) (_root_.GD.N0077.N0315.d008202 1).d008197 (_root_.GD.N0077.N0315.d008201 Unit 0) := by
  refine ⟨measurable_const, ?_⟩
  rintro ⟨e, _he, hweak, θ, hstrict⟩
  have he0 : e () = 0 := by
    have h := hweak false
    simp only [_root_.GD.N0077.N0315.d008203, _root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008200, sub_zero, zero_pow
      (by decide : 2 ≠ 0)] at h
    nlinarith [sq_nonneg (e ())]
  have heq : (_root_.GD.N0077.N0315.d008202 1).d008197 θ e =
      (_root_.GD.N0077.N0315.d008202 1).d008197 θ (_root_.GD.N0077.N0315.d008201 Unit 0) := by
    simp only [_root_.GD.N0077.N0315.d008203, he0, _root_.GD.N0077.N0315.d008201]
  exact (ne_of_lt hstrict) heq

theorem d008217 :
    ¬ _root_.GD.N0077.N0315.d008181 (_root_.GD.N0077.N0315.d008198 Unit)
      (_root_.GD.N0077.N0315.d008183 _root_.GD.N0077.N0315.d008215 (_root_.GD.N0077.N0315.d008202 1).d008197) (_root_.GD.N0077.N0315.d008201 Unit 0) := by
  intro h
  apply h.2
  refine ⟨_root_.GD.N0077.N0315.d008201 Unit 1, measurable_const, ?_, (), ?_⟩
  · intro ξ
    norm_num [_root_.GD.N0077.N0315.d008183, _root_.GD.N0077.N0315.d008215, _root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008200]
  · norm_num [_root_.GD.N0077.N0315.d008183, _root_.GD.N0077.N0315.d008215, _root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008200]

def d008218 : _root_.GD.N0077.N0315.d008196 Bool Bool where
  law := fun θ => Measure.dirac θ
  probability := fun _ => inferInstance
  target := _root_.GD.N0077.N0315.d008200 1

@[simp] theorem d008219 (θ : Bool) (d : Bool → ℝ) :
    _root_.GD.N0077.N0315.d008218.d008197 θ d = (d θ - _root_.GD.N0077.N0315.d008200 1 θ) ^ 2 := by
  simp [_root_.GD.N0077.N0315.d008196.d008197, _root_.GD.N0077.N0315.d008218]

theorem d008220 (θ : Bool) (d : Bool → ℝ) :
    Integrable (fun ω => (d ω - _root_.GD.N0077.N0315.d008218.target θ) ^ 2)
      (_root_.GD.N0077.N0315.d008218.law θ) := by
  change Integrable (fun ω : Bool => (d ω - _root_.GD.N0077.N0315.d008200 1 θ) ^ 2) (Measure.dirac θ)
  exact integrable_dirac (by finiteness)

theorem d008221 :
    _root_.GD.N0077.N0315.d008181 (_root_.GD.N0077.N0315.d008198 Bool)
      (_root_.GD.N0077.N0315.d008183 _root_.GD.N0077.N0315.d008214 _root_.GD.N0077.N0315.d008218.d008197) (_root_.GD.N0077.N0315.d008201 Bool 0) := by
  refine ⟨measurable_const, ?_⟩
  rintro ⟨e, _he, _hweak, ξ, hstrict⟩
  have hbad : (e false) ^ 2 < 0 := by
    simpa only [_root_.GD.N0077.N0315.d008183, _root_.GD.N0077.N0315.d008214, _root_.GD.N0077.N0315.d008219, _root_.GD.N0077.N0315.d008201,
      _root_.GD.N0077.N0315.d008200, sub_zero, zero_pow (by decide : 2 ≠ 0)] using hstrict
  exact (not_lt_of_ge (sq_nonneg (e false))) hbad

theorem d008222 :
    ¬ _root_.GD.N0077.N0315.d008181 (_root_.GD.N0077.N0315.d008198 Bool) _root_.GD.N0077.N0315.d008218.d008197 (_root_.GD.N0077.N0315.d008201 Bool 0) := by
  intro h
  apply h.2
  refine ⟨_root_.GD.N0077.N0315.d008200 1, measurable_of_countable _, ?_, true, ?_⟩
  · intro θ
    cases θ <;> norm_num [_root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008200]
  · norm_num [_root_.GD.N0077.N0315.d008201, _root_.GD.N0077.N0315.d008200]

structure d008223 : Prop where
  positive_scaling_preserves_order :
    ∀ (Θ D : Type) (R : Θ → D → ℝ) (c : Θ → ℝ),
      (∀ θ, 0 < c θ) → ∀ d e,
        (_root_.GD.N0077.N0315.d008178 (_root_.GD.N0077.N0315.d008182 c R) d e ↔ _root_.GD.N0077.N0315.d008178 R d e) ∧
        (_root_.GD.N0077.N0315.d008179 (_root_.GD.N0077.N0315.d008182 c R) d e ↔ _root_.GD.N0077.N0315.d008179 R d e) ∧
        (_root_.GD.N0077.N0315.d008180 (_root_.GD.N0077.N0315.d008182 c R) d e ↔
          _root_.GD.N0077.N0315.d008180 R d e)
  positive_scaling_preserves_admissibility :
    ∀ (Θ D : Type) (C : Set D) (R : Θ → D → ℝ) (c : Θ → ℝ),
      (∀ θ, 0 < c θ) → ∀ d,
        _root_.GD.N0077.N0315.d008181 C (_root_.GD.N0077.N0315.d008182 c R) d ↔ _root_.GD.N0077.N0315.d008181 C R d
  restriction_preserves_order :
    ∀ (Θ Ξ D : Type) (R : Θ → D → ℝ) (ι : Ξ → Θ) (d e : D),
      (_root_.GD.N0077.N0315.d008178 R d e → _root_.GD.N0077.N0315.d008178 (_root_.GD.N0077.N0315.d008183 ι R) d e) ∧
      (_root_.GD.N0077.N0315.d008180 R d e →
        _root_.GD.N0077.N0315.d008180 (_root_.GD.N0077.N0315.d008183 ι R) d e)
  squared_loss_minimax_reversal :
    (∀ θ, 0 < _root_.GD.N0077.N0315.d008208 θ) ∧
      _root_.GD.N0077.N0315.d008205 (_root_.GD.N0077.N0315.d008202 3).d008197 (_root_.GD.N0077.N0315.d008201 Unit 1) <
        _root_.GD.N0077.N0315.d008205 (_root_.GD.N0077.N0315.d008202 3).d008197 (_root_.GD.N0077.N0315.d008201 Unit 0) ∧
      _root_.GD.N0077.N0315.d008205 (_root_.GD.N0077.N0315.d008182 _root_.GD.N0077.N0315.d008208 (_root_.GD.N0077.N0315.d008202 3).d008197) (_root_.GD.N0077.N0315.d008201 Unit 0) <
        _root_.GD.N0077.N0315.d008205 (_root_.GD.N0077.N0315.d008182 _root_.GD.N0077.N0315.d008208 (_root_.GD.N0077.N0315.d008202 3).d008197) (_root_.GD.N0077.N0315.d008201 Unit 1)
  squared_loss_minimax_optimizer_changes :
    _root_.GD.N0077.N0315.d008206 (_root_.GD.N0077.N0315.d008198 Unit) (_root_.GD.N0077.N0315.d008202 3).d008197
      (_root_.GD.N0077.N0315.d008201 Unit (3 / 2)) ∧
    _root_.GD.N0077.N0315.d008206 (_root_.GD.N0077.N0315.d008198 Unit) (_root_.GD.N0077.N0315.d008182 _root_.GD.N0077.N0315.d008208 (_root_.GD.N0077.N0315.d008202 3).d008197)
      (_root_.GD.N0077.N0315.d008201 Unit (3 / 5)) ∧
    ¬ _root_.GD.N0077.N0315.d008206 (_root_.GD.N0077.N0315.d008198 Unit) (_root_.GD.N0077.N0315.d008182 _root_.GD.N0077.N0315.d008208 (_root_.GD.N0077.N0315.d008202 3).d008197)
      (_root_.GD.N0077.N0315.d008201 Unit (3 / 2))
  full_admissibility_need_not_restrict :
    _root_.GD.N0077.N0315.d008181 (_root_.GD.N0077.N0315.d008198 Unit) (_root_.GD.N0077.N0315.d008202 1).d008197 (_root_.GD.N0077.N0315.d008201 Unit 0) ∧
      ¬ _root_.GD.N0077.N0315.d008181 (_root_.GD.N0077.N0315.d008198 Unit)
        (_root_.GD.N0077.N0315.d008183 _root_.GD.N0077.N0315.d008215 (_root_.GD.N0077.N0315.d008202 1).d008197) (_root_.GD.N0077.N0315.d008201 Unit 0)
  submodel_admissibility_need_not_extend :
    _root_.GD.N0077.N0315.d008181 (_root_.GD.N0077.N0315.d008198 Bool)
      (_root_.GD.N0077.N0315.d008183 _root_.GD.N0077.N0315.d008214 _root_.GD.N0077.N0315.d008218.d008197) (_root_.GD.N0077.N0315.d008201 Bool 0) ∧
      ¬ _root_.GD.N0077.N0315.d008181 (_root_.GD.N0077.N0315.d008198 Bool) _root_.GD.N0077.N0315.d008218.d008197 (_root_.GD.N0077.N0315.d008201 Bool 0)
  full_competitor_classes :
    _root_.GD.N0077.N0315.d008198 Unit = Set.univ ∧ _root_.GD.N0077.N0315.d008198 Bool = Set.univ
  finite_squared_losses :
    (∀ (b : ℝ) (θ : Bool) (d : Unit → ℝ),
      Integrable (fun ω => (d ω - (_root_.GD.N0077.N0315.d008202 b).target θ) ^ 2)
      ((_root_.GD.N0077.N0315.d008202 b).law θ)) ∧
    (∀ (θ : Bool) (d : Bool → ℝ),
      Integrable (fun ω => (d ω - _root_.GD.N0077.N0315.d008218.target θ) ^ 2)
      (_root_.GD.N0077.N0315.d008218.law θ))

theorem d008224 : _root_.GD.N0077.N0315.d008223 where
  positive_scaling_preserves_order := fun _ _ R c hc d e =>
    ⟨_root_.GD.N0077.N0315.d008184 R c hc d e,
      _root_.GD.N0077.N0315.d008185 R c hc d e,
      _root_.GD.N0077.N0315.d008186 R c hc d e⟩
  positive_scaling_preserves_admissibility := fun _ _ C R c hc d =>
    _root_.GD.N0077.N0315.d008187 C R c hc d
  restriction_preserves_order := fun _ _ _ R ι _ _ =>
    ⟨_root_.GD.N0077.N0315.d008188 R ι, _root_.GD.N0077.N0315.d008189 R ι⟩
  squared_loss_minimax_reversal :=
    ⟨_root_.GD.N0077.N0315.d008209, _root_.GD.N0077.N0315.d008210⟩
  squared_loss_minimax_optimizer_changes :=
    ⟨_root_.GD.N0077.N0315.d008211, _root_.GD.N0077.N0315.d008212,
      _root_.GD.N0077.N0315.d008213⟩
  full_admissibility_need_not_restrict :=
    ⟨_root_.GD.N0077.N0315.d008216, _root_.GD.N0077.N0315.d008217⟩
  submodel_admissibility_need_not_extend :=
    ⟨_root_.GD.N0077.N0315.d008221, _root_.GD.N0077.N0315.d008222⟩
  full_competitor_classes :=
    ⟨_root_.GD.N0077.N0315.d008199 Unit, _root_.GD.N0077.N0315.d008199 Bool⟩
  finite_squared_losses :=
    ⟨_root_.GD.N0077.N0315.d008204, _root_.GD.N0077.N0315.d008220⟩

end
end GD.N0077.N0315

#print axioms _root_.GD.N0077.N0315.d008224
#print axioms _root_.GD.N0077.N0315.d008207
#print axioms _root_.GD.N0077.N0315.d008193
#print axioms _root_.GD.N0077.N0315.d008195
