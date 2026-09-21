import GD.Module0095
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option warningAsError true
















namespace GD.N0230.N0664

open Set Function
open _root_.GD.N0230.N0709 _root_.GD.N0230.N0710
open _root_.GD.N0230.N0703

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



def d001249 (C : Set (WeakSpace ℝ E))
    (f : WeakSpace ℝ E → WeakSpace ℝ E) (x : WeakSpace ℝ E) :
    WeakSpace ℝ E := by
  classical
  exact if x ∈ C then f x else x

theorem d001250
    {C : Set (WeakSpace ℝ E)} {f : WeakSpace ℝ E → WeakSpace ℝ E}
    {x : WeakSpace ℝ E} (hx : x ∈ C) :
    _root_.GD.N0230.N0664.d001249 C f x = f x := by
  simp [_root_.GD.N0230.N0664.d001249, hx]

theorem d001251
    {C : Set (WeakSpace ℝ E)} {f : WeakSpace ℝ E → WeakSpace ℝ E}
    {x : WeakSpace ℝ E} (hx : x ∉ C) :
    _root_.GD.N0230.N0664.d001249 C f x = x := by
  simp [_root_.GD.N0230.N0664.d001249, hx]

theorem d001252
    {C : Set (WeakSpace ℝ E)} {f : WeakSpace ℝ E → WeakSpace ℝ E}
    (hf : MapsTo f C C) : MapsTo (_root_.GD.N0230.N0664.d001249 C f) C C := by
  intro x hx
  simpa only [_root_.GD.N0230.N0664.d001250 hx] using hf hx

theorem d001253
    {C : Set (WeakSpace ℝ E)} {f : WeakSpace ℝ E → WeakSpace ℝ E}
    (hf : ContinuousOn f C) : ContinuousOn (_root_.GD.N0230.N0664.d001249 C f) C := by
  apply hf.congr
  intro x hx
  exact _root_.GD.N0230.N0664.d001250 hx

theorem d001254
    {C : Set (WeakSpace ℝ E)} {f : WeakSpace ℝ E → WeakSpace ℝ E}
    (hC : Convex ℝ C) (hf : _root_.GD.N0230.N0710.d001232 f C) :
    _root_.GD.N0230.N0710.d001232 (_root_.GD.N0230.N0664.d001249 C f) C := by
  intro x hx y hy a b ha hb hab
  rw [_root_.GD.N0230.N0664.d001250 (hC hx hy ha hb hab),
    _root_.GD.N0230.N0664.d001250 hx, _root_.GD.N0230.N0664.d001250 hy]
  exact hf hx hy ha hb hab



theorem d001255
    {T A : Type*}
    (inner : T → WeakSpace ℝ E → WeakSpace ℝ E)
    (outer : A → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hinnerC : ∀ t, MapsTo (inner t) C C)
    (hinnerContinuous : ∀ t, ContinuousOn (inner t) C)
    (hinnerAffine : ∀ t, _root_.GD.N0230.N0710.d001232 (inner t) C)
    (hinnerCommutes : ∀ t s x, x ∈ C →
      inner t (inner s x) = inner s (inner t x))
    (hnormal : ∀ a t, ∃ t', ∀ x, x ∈ C →
      inner t (outer a x) = outer a (inner t' x))
    (houterC : ∀ a, MapsTo (outer a) C C)
    (houterContinuous : ∀ a, ContinuousOn (outer a) C)
    (houterAffine : ∀ a, _root_.GD.N0230.N0710.d001232 (outer a) C)
    (houterCommutes : ∀ a b x, x ∈ C →
      outer a (outer b x) = outer b (outer a x)) :
    ∃ x, x ∈ C ∧ (∀ t, inner t x = x) ∧ ∀ a, outer a x = x := by
  classical
  let inner' := fun t ↦ _root_.GD.N0230.N0664.d001249 C (inner t)
  let outer' := fun a ↦ _root_.GD.N0230.N0664.d001249 C (outer a)
  have hinnerCommutes' : _root_.GD.N0230.N0703.d001148 inner' := by
    intro t s x
    by_cases hx : x ∈ C
    · simp only [inner', _root_.GD.N0230.N0664.d001250 hx,
        _root_.GD.N0230.N0664.d001250 (hinnerC s hx),
        _root_.GD.N0230.N0664.d001250 (hinnerC t hx)]
      exact hinnerCommutes t s x hx
    · simp [inner', _root_.GD.N0230.N0664.d001249, hx]
  have houterCommutes' : _root_.GD.N0230.N0703.d001148 outer' := by
    intro a b x
    by_cases hx : x ∈ C
    · simp only [outer', _root_.GD.N0230.N0664.d001250 hx,
        _root_.GD.N0230.N0664.d001250 (houterC b hx),
        _root_.GD.N0230.N0664.d001250 (houterC a hx)]
      exact houterCommutes a b x hx
    · simp [outer', _root_.GD.N0230.N0664.d001249, hx]
  have hnormal' : _root_.GD.N0230.N0703.d001147 outer' inner' := by
    intro a t
    obtain ⟨t', ht'⟩ := hnormal a t
    refine ⟨t', ?_⟩
    funext x
    by_cases hx : x ∈ C
    · simp only [comp_apply, inner', outer', _root_.GD.N0230.N0664.d001250 hx,
        _root_.GD.N0230.N0664.d001250 (houterC a hx),
        _root_.GD.N0230.N0664.d001250 (hinnerC t' hx)]
      exact ht' x hx
    · simp [inner', outer', _root_.GD.N0230.N0664.d001249, hx]
  obtain ⟨x, hx, hi, ho⟩ :=
    _root_.GD.N0230.N0710.d001248
      inner' outer' C hcompact hconvex hne hbounded
      (fun t ↦ _root_.GD.N0230.N0664.d001252 (hinnerC t))
      (fun t ↦ _root_.GD.N0230.N0664.d001253 (hinnerContinuous t))
      (fun t ↦ _root_.GD.N0230.N0664.d001254 hconvex (hinnerAffine t))
      hinnerCommutes' hnormal'
      (fun a ↦ _root_.GD.N0230.N0664.d001252 (houterC a))
      (fun a ↦ _root_.GD.N0230.N0664.d001253 (houterContinuous a))
      (fun a ↦ _root_.GD.N0230.N0664.d001254 hconvex (houterAffine a))
      houterCommutes'
  refine ⟨x, hx, ?_, ?_⟩
  · intro t
    simpa only [inner', _root_.GD.N0230.N0664.d001250 hx] using hi t
  · intro a
    simpa only [outer', _root_.GD.N0230.N0664.d001250 hx] using ho a




theorem d001256
    (act : ℝ → ℝ → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : ∀ b a, 0 < a → MapsTo (act b a) C C)
    (hcontinuous : ∀ b a, 0 < a → ContinuousOn (act b a) C)
    (haffine : ∀ b a, 0 < a → _root_.GD.N0230.N0710.d001232 (act b a) C)
    (hcomp : ∀ b a c s, 0 < a → 0 < s → ∀ x, x ∈ C →
      act b a (act c s x) = act (b + a * c) (a * s) x) :
    ∃ x, x ∈ C ∧ ∀ b a, 0 < a → act b a x = x := by
  let inner := fun b ↦ act b 1
  let outer := fun a : {a : ℝ // 0 < a} ↦ act 0 a.val
  have hiComm : ∀ b c x, x ∈ C →
      inner b (inner c x) = inner c (inner b x) := by
    intro b c x hx
    dsimp only [inner]
    rw [hcomp b 1 c 1 zero_lt_one zero_lt_one x hx,
      hcomp c 1 b 1 zero_lt_one zero_lt_one x hx]
    simp only [one_mul, add_comm]
  have hoComm : ∀ a b x, x ∈ C →
      outer a (outer b x) = outer b (outer a x) := by
    intro a b x hx
    dsimp only [outer]
    rw [hcomp 0 a.val 0 b.val a.property b.property x hx,
      hcomp 0 b.val 0 a.val b.property a.property x hx]
    simp only [mul_zero, add_zero, mul_comm]
  have hn : ∀ a b, ∃ b', ∀ x, x ∈ C →
      inner b (outer a x) = outer a (inner b' x) := by
    intro a b
    refine ⟨b / a.val, ?_⟩
    intro x hx
    dsimp only [inner, outer]
    rw [hcomp b 1 0 a.val zero_lt_one a.property x hx,
      hcomp 0 a.val (b / a.val) 1 a.property zero_lt_one x hx]
    have hcancel : a.val * (b / a.val) = b := by
      field_simp [ne_of_gt a.property]
    simp only [one_mul, mul_one, mul_zero, add_zero, zero_add, hcancel]
  obtain ⟨x, hx, hi, ho⟩ :=
    _root_.GD.N0230.N0664.d001255 inner outer C
      hcompact hconvex hne hbounded
      (fun b ↦ hmaps b 1 zero_lt_one)
      (fun b ↦ hcontinuous b 1 zero_lt_one)
      (fun b ↦ haffine b 1 zero_lt_one) hiComm hn
      (fun a ↦ hmaps 0 a.val a.property)
      (fun a ↦ hcontinuous 0 a.val a.property)
      (fun a ↦ haffine 0 a.val a.property) hoComm
  refine ⟨x, hx, ?_⟩
  intro b a ha
  have hdecomp := hcomp b 1 0 a zero_lt_one ha x hx
  simp only [one_mul, mul_zero, add_zero] at hdecomp
  have ho' : act 0 a x = x := ho ⟨a, ha⟩
  have hi' : act b 1 x = x := hi b
  rw [← hdecomp, ho', hi']



theorem d001257
    (act : ℝ → ℝ → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : ∀ b r, MapsTo (act b r) C C)
    (hcontinuous : ∀ b r, ContinuousOn (act b r) C)
    (haffine : ∀ b r, _root_.GD.N0230.N0710.d001232 (act b r) C)
    (hcomp : ∀ b r c s, ∀ x, x ∈ C →
      act b r (act c s x) = act (b + Real.exp r * c) (r + s) x) :
    ∃ x, x ∈ C ∧ ∀ b r, act b r x = x := by
  let act' := fun b a ↦ act b (Real.log a)
  have hcomp' : ∀ b a c s, 0 < a → 0 < s → ∀ x, x ∈ C →
      act' b a (act' c s x) = act' (b + a * c) (a * s) x := by
    intro b a c s ha hs x hx
    dsimp only [act']
    rw [hcomp b (Real.log a) c (Real.log s) x hx,
      Real.exp_log ha, Real.log_mul (ne_of_gt ha) (ne_of_gt hs)]
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001256
    act' C hcompact hconvex hne hbounded
    (fun b a _ ↦ hmaps b (Real.log a))
    (fun b a _ ↦ hcontinuous b (Real.log a))
    (fun b a _ ↦ haffine b (Real.log a)) hcomp'
  refine ⟨x, hx, ?_⟩
  intro b r
  simpa only [act', Real.log_exp] using hfix b (Real.exp r) (Real.exp_pos r)

end

end GD.N0230.N0664

#print axioms _root_.GD.N0230.N0664.d001255
#print axioms _root_.GD.N0230.N0664.d001256
#print axioms _root_.GD.N0230.N0664.d001257
