import GD.Module1260
import GD.Module0624
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option warningAsError true












open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0986

open _root_.GD.N0232.N0719.N0873 _root_.GD.N0232.N0719.N0982

noncomputable section

variable {k : ℕ}

abbrev d020359 (sizes : Fin k → ℕ) := _root_.GD.N0232.N0719.d009173 k sizes

def d020360 (sizes : Fin k → ℕ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (i : Fin k) : ℝ :=
  (∑ j, z i j) / (sizes i : ℝ)

def d020361 (sizes : Fin k → ℕ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (i : Fin k) : ℝ :=
  (∑ j, (z i j - _root_.GD.N0232.N0719.N0986.d020360 sizes z i) ^ 2) / (2 * (sizes i : ℝ))

def d020362 (sizes : Fin k → ℕ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) :=
  (_root_.GD.N0232.N0719.N0986.d020360 sizes z, _root_.GD.N0232.N0719.N0986.d020361 sizes z)

theorem d020363 (sizes : Fin k → ℕ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020360 sizes z i = _root_.GD.N0232.N0719.N0900.d009102 k sizes z i := by
  simp [_root_.GD.N0232.N0719.N0986.d020360, _root_.GD.N0232.N0719.N0900.d009102, _root_.GD.N0107.d009084,
    _root_.GD.N0126.d006420, _root_.GD.N0126.d006419]

theorem d020364 (sizes : Fin k → ℕ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020361 sizes z i = _root_.GD.N0126.d006422 (z i) /
      (2 * (sizes i : ℝ)) := by
  simp [_root_.GD.N0232.N0719.N0986.d020361, _root_.GD.N0232.N0719.N0986.d020360, _root_.GD.N0126.d006422,
    _root_.GD.N0126.d006421, _root_.GD.N0126.d006420,
    _root_.GD.N0126.d006419]

@[fun_prop] theorem d020365 (sizes : Fin k → ℕ) :
    Continuous (_root_.GD.N0232.N0719.N0986.d020362 sizes) := by
  unfold _root_.GD.N0232.N0719.N0986.d020362 _root_.GD.N0232.N0719.N0986.d020361 _root_.GD.N0232.N0719.N0986.d020360
  fun_prop

def d020366 {n : ℕ} (a b : Fin n) (y d : ℝ) : Fin n → ℝ :=
  fun j => y + (Pi.single a d : Fin n → ℝ) j - (Pi.single b d : Fin n → ℝ) j

theorem d020367 {n : ℕ} (a b : Fin n) (y d : ℝ) :
    ∑ j, _root_.GD.N0232.N0719.N0986.d020366 a b y d j = (n : ℝ) * y := by
  simp [_root_.GD.N0232.N0719.N0986.d020366, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem d020368 {n : ℕ} (a b : Fin n) (hab : a ≠ b) (y d : ℝ) :
    ∑ j, (_root_.GD.N0232.N0719.N0986.d020366 a b y d j - y) ^ 2 = 2 * d ^ 2 := by
  have heq (j : Fin n) : (_root_.GD.N0232.N0719.N0986.d020366 a b y d j - y) ^ 2 =
      (Pi.single a (d ^ 2) : Fin n → ℝ) j +
        (Pi.single b (d ^ 2) : Fin n → ℝ) j := by
    by_cases hja : j = a
    · subst j
      simp [_root_.GD.N0232.N0719.N0986.d020366, hab]
    · by_cases hjb : j = b
      · subst j
        simp [_root_.GD.N0232.N0719.N0986.d020366, Ne.symm hab]
      · simp [_root_.GD.N0232.N0719.N0986.d020366, hja, hjb]
  simp_rw [heq]
  simp [Finset.sum_add_distrib]
  ring

def d020369 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (i : Fin k) : Fin (sizes i) :=
  ⟨0, lt_of_lt_of_le (by norm_num) (hn i)⟩

def d020370 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (i : Fin k) : Fin (sizes i) :=
  ⟨1, lt_of_lt_of_le (by norm_num) (hn i)⟩

theorem d020371 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020369 sizes hn i ≠ _root_.GD.N0232.N0719.N0986.d020370 sizes hn i := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [_root_.GD.N0232.N0719.N0986.d020369, _root_.GD.N0232.N0719.N0986.d020370] at hv

def d020372 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : _root_.GD.N0232.N0719.N0986.d020359 sizes :=
  fun i => _root_.GD.N0232.N0719.N0986.d020366 (_root_.GD.N0232.N0719.N0986.d020369 sizes hn i) (_root_.GD.N0232.N0719.N0986.d020370 sizes hn i) (x.1 i)
    (Real.sqrt ((sizes i : ℝ) * x.2 i))

theorem d020373 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0232.N0719.N0986.d020372 sizes hn x) i = x.1 i := by
  have hnR : (sizes i : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < sizes i := lt_of_lt_of_le (by norm_num) (hn i)
    exact_mod_cast h.ne'
  unfold _root_.GD.N0232.N0719.N0986.d020360 _root_.GD.N0232.N0719.N0986.d020372
  rw [_root_.GD.N0232.N0719.N0986.d020367]
  exact mul_div_cancel_left₀ _ hnR

theorem d020374 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0982.d020342) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0232.N0719.N0986.d020372 sizes hn x) i = x.2 i := by
  have hnR : (sizes i : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < sizes i := lt_of_lt_of_le (by norm_num) (hn i)
    exact_mod_cast h.ne'
  unfold _root_.GD.N0232.N0719.N0986.d020361
  rw [_root_.GD.N0232.N0719.N0986.d020373]
  change (∑ j, (_root_.GD.N0232.N0719.N0986.d020366 (_root_.GD.N0232.N0719.N0986.d020369 sizes hn i) (_root_.GD.N0232.N0719.N0986.d020370 sizes hn i) (x.1 i)
    (Real.sqrt ((sizes i : ℝ) * x.2 i)) j - x.1 i) ^ 2) / _ = _
  rw [_root_.GD.N0232.N0719.N0986.d020368 _ _ (_root_.GD.N0232.N0719.N0986.d020371 sizes hn i),
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (hx i).le)]
  field_simp [hnR]


theorem d020375 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0982.d020342) :
    _root_.GD.N0232.N0719.N0986.d020362 sizes (_root_.GD.N0232.N0719.N0986.d020372 sizes hn x) = x := by
  apply Prod.ext
  · funext i
    exact _root_.GD.N0232.N0719.N0986.d020373 sizes hn x i
  · funext i
    exact _root_.GD.N0232.N0719.N0986.d020374 sizes hn hx i



theorem d020376 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    {F G : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) → ℝ} (hF : ContinuousOn F _root_.GD.N0232.N0719.N0982.d020342)
    (hG : ContinuousOn G _root_.GD.N0232.N0719.N0982.d020342)
    (hae : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0986.d020359 sizes)),
      _root_.GD.N0232.N0719.N0986.d020362 sizes z ∈ _root_.GD.N0232.N0719.N0982.d020342 → F (_root_.GD.N0232.N0719.N0986.d020362 sizes z) = G (_root_.GD.N0232.N0719.N0986.d020362 sizes z)) :
    EqOn F G _root_.GD.N0232.N0719.N0982.d020342 := by
  let U : Set (_root_.GD.N0232.N0719.N0986.d020359 sizes) := _root_.GD.N0232.N0719.N0986.d020362 sizes ⁻¹' _root_.GD.N0232.N0719.N0982.d020342
  have hU : IsOpen U := _root_.GD.N0232.N0719.N0982.d020343.preimage (_root_.GD.N0232.N0719.N0986.d020365 sizes)
  have heq : EqOn (F ∘ _root_.GD.N0232.N0719.N0986.d020362 sizes) (G ∘ _root_.GD.N0232.N0719.N0986.d020362 sizes) U :=
    (volume : Measure (_root_.GD.N0232.N0719.N0986.d020359 sizes)).eqOn_open_of_ae_eq
      ((ae_restrict_iff' hU.measurableSet).mpr hae) hU
      (hF.comp (_root_.GD.N0232.N0719.N0986.d020365 sizes).continuousOn (fun _ hz => hz))
      (hG.comp (_root_.GD.N0232.N0719.N0986.d020365 sizes).continuousOn (fun _ hz => hz))
  intro x hx
  have hr := _root_.GD.N0232.N0719.N0986.d020375 sizes hn hx
  have hu : _root_.GD.N0232.N0719.N0986.d020372 sizes hn x ∈ U := by
    change _root_.GD.N0232.N0719.N0986.d020362 sizes (_root_.GD.N0232.N0719.N0986.d020372 sizes hn x) ∈ _root_.GD.N0232.N0719.N0982.d020342
    rwa [hr]
  simpa only [Function.comp_apply, hr] using heq hu

end
end GD.N0232.N0719.N0986

#print axioms _root_.GD.N0232.N0719.N0986.d020364
#print axioms _root_.GD.N0232.N0719.N0986.d020375
#print axioms _root_.GD.N0232.N0719.N0986.d020376
