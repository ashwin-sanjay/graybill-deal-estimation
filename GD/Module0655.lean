import GD.Module0654


















open MeasureTheory Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0866

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929


def d009655 {I : Type*} (b l : ℝ) (y : I → ℝ) : I → ℝ :=
  fun i => b + l * y i


def d009656 {I : Type*} (l : ℝ) (t : I → ℝ) : I → ℝ :=
  fun i => l ^ 2 * t i



theorem d009657
    {I : Type*} [Fintype I]
    (p y : I → ℝ) (b l : ℝ) (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0928.d009405 p (_root_.GD.N0232.N0719.N0866.d009655 b l y) =
      b + l * _root_.GD.N0232.N0719.N0928.d009405 p y := by
  unfold _root_.GD.N0232.N0719.N0928.d009405 _root_.GD.N0232.N0719.N0866.d009655
  calc
    (∑ i, p i * (b + l * y i)) =
        ∑ i, (p i * b + l * (p i * y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, p i * b) + ∑ i, l * (p i * y i) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, p i) * b + l * ∑ i, p i * y i := by
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = b + l * ∑ i, p i * y i := by rw [hsum, one_mul]


theorem d009658
    {I : Type*} [Fintype I]
    (p y : I → ℝ) (b l : ℝ) (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0928.d009406 p (_root_.GD.N0232.N0719.N0866.d009655 b l y) =
      l ^ 2 * _root_.GD.N0232.N0719.N0928.d009406 p y := by
  unfold _root_.GD.N0232.N0719.N0928.d009406
  rw [_root_.GD.N0232.N0719.N0866.d009657 p y b l hsum]
  calc
    (1 / 2 : ℝ) *
          ∑ i, p i * (_root_.GD.N0232.N0719.N0866.d009655 b l y i -
            (b + l * _root_.GD.N0232.N0719.N0928.d009405 p y)) ^ 2 =
        (1 / 2 : ℝ) *
          ∑ i, l ^ 2 *
            (p i * (y i - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      unfold _root_.GD.N0232.N0719.N0866.d009655
      ring
    _ = l ^ 2 *
          ((1 / 2 : ℝ) *
            ∑ i, p i * (y i - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2) := by
      rw [← Finset.mul_sum]
      ring



theorem d009659
    {I : Type*} [Fintype I]
    (shape p y t : I → ℝ) (b l : ℝ)
    (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0928.d009407 shape p (_root_.GD.N0232.N0719.N0866.d009655 b l y) (_root_.GD.N0232.N0719.N0866.d009656 l t) =
      l ^ 2 * _root_.GD.N0232.N0719.N0928.d009407 shape p y t := by
  unfold _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0866.d009656
  rw [_root_.GD.N0232.N0719.N0866.d009658 p y b l hsum]
  have hgamma :
      (∑ i, shape i * p i * (l ^ 2 * t i)) =
        l ^ 2 * ∑ i, shape i * p i * t i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hgamma]
  ring




theorem d009660
    {I : Type*} [Fintype I]
    (shape p y t : I → ℝ) (s b l : ℝ)
    (hl : 0 < l) (hsum : ∑ i, p i = 1)
    (henergy : 0 < _root_.GD.N0232.N0719.N0928.d009407 shape p y t) :
    _root_.GD.N0232.N0719.N0928.d009437 shape p
        (_root_.GD.N0232.N0719.N0866.d009655 b l y) (_root_.GD.N0232.N0719.N0866.d009656 l t) s =
      (l ^ 2) ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
        _root_.GD.N0232.N0719.N0928.d009437 shape p y t s := by
  unfold _root_.GD.N0232.N0719.N0928.d009437
  rw [_root_.GD.N0232.N0719.N0866.d009659 shape p y t b l hsum]
  rw [Real.mul_rpow (sq_nonneg l) henergy.le]
  ring


theorem d009661
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s b l : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hl : 0 < l) :
    _root_.GD.N0232.N0719.N0929.d009647 hk shape (_root_.GD.N0232.N0719.N0866.d009655 b l y) (_root_.GD.N0232.N0719.N0866.d009656 l t) s =
      (l ^ 2) ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
        _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s := by
  unfold _root_.GD.N0232.N0719.N0929.d009647
  rw [← integral_const_mul]
  apply setIntegral_congr_fun
    (_root_.GD.N0232.N0719.N0955.d009608 k)
  intro q hq
  have henergy :
      0 < _root_.GD.N0232.N0719.N0928.d009407 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t := by
    obtain ⟨c, hc, hfloor⟩ :=
      _root_.GD.N0232.N0719.N0929.d009644 hk shape t hshape ht
    have hge := _root_.GD.N0232.N0719.N0928.d009442 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t c
      (fun i => (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le)
      (_root_.GD.N0232.N0719.N0853.d009570 hk q)
      hfloor
    linarith
  exact _root_.GD.N0232.N0719.N0866.d009660 shape
    (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s b l hl
    (_root_.GD.N0232.N0719.N0853.d009570 hk q) henergy


theorem d009662
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s b l : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hl : 0 < l) :
    _root_.GD.N0232.N0719.N0929.d009652 hk shape
        (_root_.GD.N0232.N0719.N0866.d009655 b l y) (_root_.GD.N0232.N0719.N0866.d009656 l t) s =
      (l ^ 2) ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
        (b * _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s +
          l * _root_.GD.N0232.N0719.N0929.d009652 hk shape y t s) := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 k
  let A := (l ^ 2) ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s)
  let E : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q => _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s
  let M : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q => _root_.GD.N0232.N0719.N0928.d009405
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y
  have hE : Integrable E (volume.restrict S) := by
    simpa [IntegrableOn, E, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        hk shape y t s hshape ht hpower
  have hEM : Integrable (fun q => E q * M q) (volume.restrict S) := by
    simpa [IntegrableOn, E, M, S] using
      _root_.GD.N0232.N0719.N0929.d009651
        hk shape y t s hshape ht hpower
  have hAbE : Integrable (fun q => (A * b) * E q)
      (volume.restrict S) := hE.const_mul (A * b)
  have hAlEM : Integrable (fun q => (A * l) * (E q * M q))
      (volume.restrict S) := hEM.const_mul (A * l)
  unfold _root_.GD.N0232.N0719.N0929.d009652
  calc
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q)
            (_root_.GD.N0232.N0719.N0866.d009655 b l y) (_root_.GD.N0232.N0719.N0866.d009656 l t) s *
          _root_.GD.N0232.N0719.N0928.d009405
            (_root_.GD.N0232.N0719.N0853.d009567 hk q)
            (_root_.GD.N0232.N0719.N0866.d009655 b l y)) =
        ∫ q in S,
          ((A * b) * E q + (A * l) * (E q * M q)) := by
      apply setIntegral_congr_fun
        (_root_.GD.N0232.N0719.N0955.d009608 k)
      intro q hq
      have henergy :
          0 < _root_.GD.N0232.N0719.N0928.d009407 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t := by
        obtain ⟨c, hc, hfloor⟩ :=
          _root_.GD.N0232.N0719.N0929.d009644 hk shape t hshape ht
        have hge := _root_.GD.N0232.N0719.N0928.d009442 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t c
          (fun i => (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le)
          (_root_.GD.N0232.N0719.N0853.d009570 hk q)
          hfloor
        linarith
      change
        _root_.GD.N0232.N0719.N0928.d009437 shape
              (_root_.GD.N0232.N0719.N0853.d009567 hk q)
              (_root_.GD.N0232.N0719.N0866.d009655 b l y) (_root_.GD.N0232.N0719.N0866.d009656 l t) s *
            _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 hk q)
              (_root_.GD.N0232.N0719.N0866.d009655 b l y) =
          (A * b) * E q + (A * l) * (E q * M q)
      rw [_root_.GD.N0232.N0719.N0866.d009660 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s b l hl
        (_root_.GD.N0232.N0719.N0853.d009570 hk q) henergy,
        _root_.GD.N0232.N0719.N0866.d009657
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y b l
          (_root_.GD.N0232.N0719.N0853.d009570 hk q)]
      change A * E q * (b + l * M q) = _
      ring
    _ = (A * b) * (∫ q in S, E q) +
          (A * l) * (∫ q in S, E q * M q) := by
      change (∫ q, ((A * b) * E q + (A * l) * (E q * M q))
          ∂volume.restrict S) = _
      rw [integral_add hAbE hAlEM, integral_const_mul,
        integral_const_mul]
    _ = A *
        (b * _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s +
          l * _root_.GD.N0232.N0719.N0929.d009652 hk shape y t s) := by
      unfold _root_.GD.N0232.N0719.N0929.d009647 _root_.GD.N0232.N0719.N0929.d009652 A E M S
      ring




theorem d009663
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s b l : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hl : 0 < l) :
    _root_.GD.N0232.N0719.N0929.d009653 hk shape
        (_root_.GD.N0232.N0719.N0866.d009655 b l y) (_root_.GD.N0232.N0719.N0866.d009656 l t) s =
      b + l * _root_.GD.N0232.N0719.N0929.d009653 hk shape y t s := by
  let A := (l ^ 2) ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s)
  let D := _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s
  let N := _root_.GD.N0232.N0719.N0929.d009652 hk shape y t s
  have hA : 0 < A := by
    unfold A
    exact Real.rpow_pos_of_pos (sq_pos_of_pos hl) _
  have hD : 0 < D := by
    unfold D
    exact _root_.GD.N0232.N0719.N0929.d009648 hk shape y t s hshape ht hpower
  unfold _root_.GD.N0232.N0719.N0929.d009653
  rw [_root_.GD.N0232.N0719.N0866.d009662
      hk shape y t s b l hshape ht hpower hl,
    _root_.GD.N0232.N0719.N0866.d009661 hk shape y t s b l hshape ht hpower hl]
  change (A * (b * D + l * N)) / (A * D) = b + l * (N / D)
  field_simp [hA.ne', hD.ne']

end

end N0866
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0866.d009659
#print axioms _root_.GD.N0232.N0719.N0866.d009660
#print axioms _root_.GD.N0232.N0719.N0866.d009661
#print axioms _root_.GD.N0232.N0719.N0866.d009662
#print axioms _root_.GD.N0232.N0719.N0866.d009663
