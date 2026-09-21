import GD.Module0654


























open MeasureTheory Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0868

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929




def d009664
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s action : ℝ) : ℝ :=
  ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
    _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
      (action -
        _root_.GD.N0232.N0719.N0928.d009405
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y) ^ 2



theorem d009665
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k ↦
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
          _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) y ^ 2)
      (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 k
  let evidence : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s
  let mean : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009405
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y
  let B : ℝ := ∑ i, |y i|
  have hevidence : Integrable evidence (volume.restrict S) := by
    simpa [IntegrableOn, evidence, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        hk shape y t s hshape ht hpower
  have hmeanSqMeas :
      AEStronglyMeasurable (fun q ↦ mean q ^ 2) (volume.restrict S) :=
    ((_root_.GD.N0232.N0719.N0929.d009649 hk y).pow 2).aestronglyMeasurable
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ abs_nonneg (y i)
  have hmeanSqBound :
      ∀ᵐ q ∂volume.restrict S, ‖mean q ^ 2‖ ≤ B ^ 2 := by
    apply (ae_restrict_iff'
      (_root_.GD.N0232.N0719.N0955.d009608 k)).2
    filter_upwards [] with q hq
    have hm := _root_.GD.N0232.N0719.N0929.d009650 hk y hq
    change |mean q ^ 2| ≤ B ^ 2
    rw [abs_sq]
    have hs := (sq_le_sq₀ (abs_nonneg (mean q)) hB).2 hm
    simpa only [sq_abs] using hs
  have hproduct := hevidence.bdd_mul hmeanSqMeas hmeanSqBound
  simpa [IntegrableOn, evidence, mean, S, mul_comm] using hproduct



theorem d009666
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s action : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k ↦
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
          (action -
            _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) y) ^ 2)
      (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 k
  let evidence : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s
  let mean : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009405
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y
  let B : ℝ := |action| + ∑ i, |y i|
  have hevidence : Integrable evidence (volume.restrict S) := by
    simpa [IntegrableOn, evidence, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        hk shape y t s hshape ht hpower
  have hsqMeas : AEStronglyMeasurable
      (fun q ↦ (action - mean q) ^ 2) (volume.restrict S) :=
    (continuous_const.sub
      (_root_.GD.N0232.N0719.N0929.d009649 hk y)).pow 2 |>.aestronglyMeasurable
  have hB : 0 ≤ B := add_nonneg (abs_nonneg action)
    (Finset.sum_nonneg fun i _ ↦ abs_nonneg (y i))
  have hsqBound :
      ∀ᵐ q ∂volume.restrict S, ‖(action - mean q) ^ 2‖ ≤ B ^ 2 := by
    apply (ae_restrict_iff'
      (_root_.GD.N0232.N0719.N0955.d009608 k)).2
    filter_upwards [] with q hq
    have hm := _root_.GD.N0232.N0719.N0929.d009650 hk y hq
    have hdiff : |action - mean q| ≤ B := by
      calc
        |action - mean q| ≤ |action| + |mean q| := abs_sub _ _
        _ ≤ |action| + ∑ i, |y i| :=
          add_le_add (le_refl |action|) hm
        _ = B := rfl
    change |(action - mean q) ^ 2| ≤ B ^ 2
    rw [abs_sq]
    have hs := (sq_le_sq₀ (abs_nonneg (action - mean q)) hB).2 hdiff
    simpa only [sq_abs] using hs
  have hproduct := hevidence.bdd_mul hsqMeas hsqBound
  simpa [IntegrableOn, evidence, mean, S, mul_comm] using hproduct


theorem d009667
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s action : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    _root_.GD.N0232.N0719.N0868.d009664 hk shape y t s action =
      action ^ 2 * _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s -
        2 * action * _root_.GD.N0232.N0719.N0929.d009652 hk shape y t s +
        ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
          _root_.GD.N0232.N0719.N0928.d009437 shape
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
            _root_.GD.N0232.N0719.N0928.d009405
                (_root_.GD.N0232.N0719.N0853.d009567 hk q) y ^ 2 := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 k
  let E : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s
  let M : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009405
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y
  have hE : Integrable E (volume.restrict S) := by
    simpa [IntegrableOn, E, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        hk shape y t s hshape ht hpower
  have hEM : Integrable (fun q ↦ E q * M q) (volume.restrict S) := by
    simpa [IntegrableOn, E, M, S] using
      _root_.GD.N0232.N0719.N0929.d009651
        hk shape y t s hshape ht hpower
  have hEM2 : Integrable (fun q ↦ E q * M q ^ 2)
      (volume.restrict S) := by
    simpa [IntegrableOn, E, M, S] using
      _root_.GD.N0232.N0719.N0868.d009665
        hk shape y t s hshape ht hpower
  unfold _root_.GD.N0232.N0719.N0868.d009664 _root_.GD.N0232.N0719.N0929.d009647 _root_.GD.N0232.N0719.N0929.d009652
  change
    (∫ q, E q * (action - M q) ^ 2 ∂volume.restrict S) = _
  have hpoint : (fun q ↦ E q * (action - M q) ^ 2) =
      fun q ↦ action ^ 2 * E q -
        (2 * action) * (E q * M q) + E q * M q ^ 2 := by
    funext q
    ring
  have hAE : Integrable (fun q ↦ action ^ 2 * E q)
      (volume.restrict S) := hE.const_mul _
  have hAEM : Integrable (fun q ↦ (2 * action) * (E q * M q))
      (volume.restrict S) := hEM.const_mul _
  have hfirst : Integrable
      (fun q ↦ action ^ 2 * E q - (2 * action) * (E q * M q))
      (volume.restrict S) := hAE.sub hAEM
  rw [hpoint]
  rw [integral_add hfirst hEM2, integral_sub hAE hAEM,
    integral_const_mul, integral_const_mul]






theorem d009668
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s action : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    _root_.GD.N0232.N0719.N0868.d009664 hk shape y t s action =
      _root_.GD.N0232.N0719.N0868.d009664 hk shape y t s
          (_root_.GD.N0232.N0719.N0929.d009653 hk shape y t s) +
        _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s *
          (action - _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s) ^ 2 := by
  let D := _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s
  let N := _root_.GD.N0232.N0719.N0929.d009652 hk shape y t s
  let Q := ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
    _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
      _root_.GD.N0232.N0719.N0928.d009405
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y ^ 2
  have hD : D ≠ 0 := by
    exact _root_.GD.N0232.N0719.N0929.d009654 hk shape y t s hshape ht hpower
  rw [_root_.GD.N0232.N0719.N0868.d009667
      hk shape y t s action hshape ht hpower,
    _root_.GD.N0232.N0719.N0868.d009667
      hk shape y t s
        (_root_.GD.N0232.N0719.N0929.d009653 hk shape y t s)
        hshape ht hpower]
  change action ^ 2 * D - 2 * action * N + Q =
    (N / D) ^ 2 * D - 2 * (N / D) * N + Q +
      D * (action - N / D) ^ 2
  field_simp [hD]
  ring


theorem d009669
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s action : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    _root_.GD.N0232.N0719.N0868.d009664 hk shape y t s action -
        _root_.GD.N0232.N0719.N0868.d009664 hk shape y t s
          (_root_.GD.N0232.N0719.N0929.d009653 hk shape y t s) =
      _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s *
        (action - _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s) ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0868.d009668
    hk shape y t s action hshape ht hpower]
  ring



theorem d009670
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s action : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hmin : _root_.GD.N0232.N0719.N0868.d009664 hk shape y t s action ≤
      _root_.GD.N0232.N0719.N0868.d009664 hk shape y t s
        (_root_.GD.N0232.N0719.N0929.d009653 hk shape y t s)) :
    action = _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s := by
  have hD := _root_.GD.N0232.N0719.N0929.d009648 hk shape y t s hshape ht hpower
  rw [_root_.GD.N0232.N0719.N0868.d009668
    hk shape y t s action hshape ht hpower] at hmin
  have hsquare :
      (action - _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s) ^ 2 = 0 := by
    nlinarith [sq_nonneg
      (action - _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)




theorem d009671
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    |_root_.GD.N0232.N0719.N0929.d009653 hk shape y t s| ≤ ∑ i, |y i| := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 k
  let E : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s
  let M : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009405
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y
  let B : ℝ := ∑ i, |y i|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ abs_nonneg (y i)
  have hE : Integrable E (volume.restrict S) := by
    simpa [IntegrableOn, E, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        hk shape y t s hshape ht hpower
  have hmajor : Integrable (fun q ↦ B * E q) (volume.restrict S) :=
    hE.const_mul B
  have hnorm :
      ‖∫ q, E q * M q ∂volume.restrict S‖ ≤
        ∫ q, B * E q ∂volume.restrict S := by
    apply norm_integral_le_of_norm_le hmajor
    apply (ae_restrict_iff'
      (_root_.GD.N0232.N0719.N0955.d009608 k)).2
    filter_upwards [] with q hq
    have hEp : 0 < E q := by
      exact _root_.GD.N0232.N0719.N0929.d009646
        hk shape y t s hshape ht hpower hq
    have hM := _root_.GD.N0232.N0719.N0929.d009650 hk y hq
    change |E q * M q| ≤ B * E q
    rw [abs_mul, abs_of_pos hEp]
    nlinarith
  have hD : 0 < _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s :=
    _root_.GD.N0232.N0719.N0929.d009648 hk shape y t s hshape ht hpower
  have hnum :
      |_root_.GD.N0232.N0719.N0929.d009652 hk shape y t s| ≤
        B * _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s := by
    simpa [_root_.GD.N0232.N0719.N0929.d009652, _root_.GD.N0232.N0719.N0929.d009647, E, M, S,
      Real.norm_eq_abs, integral_const_mul] using hnorm
  unfold _root_.GD.N0232.N0719.N0929.d009653
  rw [abs_div, abs_of_pos hD]
  exact (div_le_iff₀ hD).2 (by simpa [mul_comm] using hnum)




def d009672
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (cutoff : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ) : ℝ :=
  ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
    _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s * cutoff q


def d009673
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (cutoff : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ) : ℝ :=
  ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
    _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
      _root_.GD.N0232.N0719.N0928.d009405
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y * cutoff q


def d009674
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (cutoff : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0868.d009673 hk shape y t s cutoff /
    _root_.GD.N0232.N0719.N0868.d009672 hk shape y t s cutoff



def d009675
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (cutoff : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ) : ℝ :=
  ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
    _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
      (_root_.GD.N0232.N0719.N0928.d009405
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y -
        _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s) * cutoff q



theorem d009676
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (cutoff : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ)
    (hcutoff : IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k ↦
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s * cutoff q)
      (_root_.GD.N0232.N0719.N0955.d009607 k))
    (hmeanCutoff : IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k ↦
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
          _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) y * cutoff q)
      (_root_.GD.N0232.N0719.N0955.d009607 k)) :
    _root_.GD.N0232.N0719.N0868.d009675 hk shape y t s cutoff =
      _root_.GD.N0232.N0719.N0868.d009673 hk shape y t s cutoff -
        _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s *
          _root_.GD.N0232.N0719.N0868.d009672 hk shape y t s cutoff := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 k
  let E : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s
  let M : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009405
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y
  let a := _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s
  have hEc : Integrable (fun q ↦ E q * cutoff q) (volume.restrict S) := by
    simpa [IntegrableOn, E, S] using hcutoff
  have hEMc : Integrable (fun q ↦ E q * M q * cutoff q)
      (volume.restrict S) := by
    simpa [IntegrableOn, E, M, S] using hmeanCutoff
  unfold _root_.GD.N0232.N0719.N0868.d009675 _root_.GD.N0232.N0719.N0868.d009673
    _root_.GD.N0232.N0719.N0868.d009672
  change (∫ q, E q * (M q - a) * cutoff q ∂volume.restrict S) = _
  have hpoint : (fun q ↦ E q * (M q - a) * cutoff q) =
      fun q ↦ E q * M q * cutoff q - a * (E q * cutoff q) := by
    funext q
    ring
  rw [hpoint, integral_sub hEMc (hEc.const_mul a), integral_const_mul]


theorem d009677
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (cutoff : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ)
    (hcutoff : IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k ↦
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s * cutoff q)
      (_root_.GD.N0232.N0719.N0955.d009607 k))
    (hmeanCutoff : IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k ↦
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
          _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) y * cutoff q)
      (_root_.GD.N0232.N0719.N0955.d009607 k))
    (hmass : _root_.GD.N0232.N0719.N0868.d009672 hk shape y t s cutoff ≠ 0) :
    _root_.GD.N0232.N0719.N0868.d009674 hk shape y t s cutoff -
        _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s =
      _root_.GD.N0232.N0719.N0868.d009675 hk shape y t s cutoff /
        _root_.GD.N0232.N0719.N0868.d009672 hk shape y t s cutoff := by
  rw [_root_.GD.N0232.N0719.N0868.d009676
    hk shape y t s cutoff hcutoff hmeanCutoff]
  unfold _root_.GD.N0232.N0719.N0868.d009674
  field_simp [hmass]


theorem d009678
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (cutoff : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ)
    (hcutoff : IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k ↦
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s * cutoff q)
      (_root_.GD.N0232.N0719.N0955.d009607 k))
    (hmeanCutoff : IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k ↦
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
          _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) y * cutoff q)
      (_root_.GD.N0232.N0719.N0955.d009607 k))
    (hmass : _root_.GD.N0232.N0719.N0868.d009672 hk shape y t s cutoff ≠ 0) :
    _root_.GD.N0232.N0719.N0868.d009672 hk shape y t s cutoff *
        (_root_.GD.N0232.N0719.N0868.d009674 hk shape y t s cutoff -
          _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s) ^ 2 =
      _root_.GD.N0232.N0719.N0868.d009675 hk shape y t s cutoff ^ 2 /
        _root_.GD.N0232.N0719.N0868.d009672 hk shape y t s cutoff := by
  rw [_root_.GD.N0232.N0719.N0868.d009677
    hk shape y t s cutoff hcutoff hmeanCutoff hmass]
  field_simp [hmass]

end

end N0868
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0868.d009665
#print axioms _root_.GD.N0232.N0719.N0868.d009667
#print axioms _root_.GD.N0232.N0719.N0868.d009668
#print axioms _root_.GD.N0232.N0719.N0868.d009670
#print axioms _root_.GD.N0232.N0719.N0868.d009671
#print axioms _root_.GD.N0232.N0719.N0868.d009677
#print axioms _root_.GD.N0232.N0719.N0868.d009678
