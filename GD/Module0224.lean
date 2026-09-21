import GD.Module0032
























open scoped BigOperators

namespace GD
namespace N0233
namespace N0726

noncomputable section

open _root_.GD.N0230.N0657

variable {ι : Type*} [Fintype ι]


def d003174 (q : ι → ℝ) : ℝ :=
  ∑ i, q i


def d003175 (q f : ι → ℝ) : ℝ :=
  ∑ i, q i * f i


def d003176 (q target : ι → ℝ) : ℝ :=
  _root_.GD.N0233.N0726.d003175 q target / _root_.GD.N0233.N0726.d003174 q



def d003177
    (q target potential : ι → ℝ) : ℝ :=
  ∑ i, q i * (target i - _root_.GD.N0233.N0726.d003176 q target) * potential i



def d003178
    (q target potential : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i, ∑ j,
      q i * q j * (target i - target j) *
        (potential i - potential j)






theorem d003179
    (q target potential : ι → ℝ)
    (hMass : _root_.GD.N0233.N0726.d003174 q ≠ 0) :
    _root_.GD.N0233.N0726.d003174 q * _root_.GD.N0233.N0726.d003177 q target potential =
      _root_.GD.N0233.N0726.d003178 q target potential := by
  let w : ι → ℝ := fun i ↦ q i / _root_.GD.N0233.N0726.d003174 q
  have hsum : ∑ i, w i = 1 := by
    unfold w
    rw [← Finset.sum_div]
    exact div_self hMass
  have hmean :
      _root_.GD.N0230.N0657.d000372 w target = _root_.GD.N0233.N0726.d003176 q target := by
    unfold _root_.GD.N0230.N0657.d000372 _root_.GD.N0233.N0726.d003176 _root_.GD.N0233.N0726.d003175 w
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  have hcenter :
      _root_.GD.N0230.N0657.d000373 w target potential =
        _root_.GD.N0233.N0726.d003177 q target potential / _root_.GD.N0233.N0726.d003174 q := by
    rw [_root_.GD.N0230.N0657.d000374, hmean]
    unfold _root_.GD.N0233.N0726.d003177 w
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  have hterm : ∀ i j,
      w i * w j * (target i - target j) *
          (potential i - potential j) =
        (q i * q j * (target i - target j) *
          (potential i - potential j)) / _root_.GD.N0233.N0726.d003174 q ^ 2 := by
    intro i j
    unfold w
    field_simp [hMass]
  have hpair :
      (1 / 2 : ℝ) *
          ∑ i, ∑ j,
            w i * w j * (target i - target j) *
              (potential i - potential j) =
        _root_.GD.N0233.N0726.d003178 q target potential / _root_.GD.N0233.N0726.d003174 q ^ 2 := by
    unfold _root_.GD.N0233.N0726.d003178
    simp_rw [hterm]
    simp_rw [← Finset.sum_div]
    ring
  have hcov := _root_.GD.N0230.N0657.d000375
    w target potential hsum
  rw [hcenter, hpair] at hcov
  field_simp [hMass] at hcov
  simpa [mul_comm] using hcov

end

end N0726
end N0233
end GD

#print axioms _root_.GD.N0233.N0726.d003179
