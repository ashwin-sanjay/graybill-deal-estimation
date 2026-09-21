import GD.Module0024
import GD.Module0770
import GD.Module0749





















open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0719
namespace N0830

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0865
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0814
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0640
open _root_.GD.N0230.N0718



def d011754
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega /
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta

@[fun_prop]
theorem d011755
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measurable
      (_root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes theta) := by
  unfold _root_.GD.N0232.N0719.N0830.d011754
  fun_prop

theorem d011756
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes theta omega := by
  unfold _root_.GD.N0232.N0719.N0830.d011754
  exact div_nonneg
    (_root_.GD.N0232.N0719.N0865.d011219 k sizes theta omega)
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta).le



theorem d011757
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 < _root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega := by
  unfold _root_.GD.N0232.N0719.N0865.d011217 _root_.GD.N0232.N0719.N0865.d011216
    _root_.GD.N0232.N0719.N0932.d009219
    _root_.GD.N0232.N0719.N0932.d009190
    _root_.GD.N0232.N0719.N0932.d009213
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  apply ENNReal.ofReal_pos.mp
  rw [_root_.GD.N0232.N0719.N0932.d009207]
  exact _root_.GD.N0232.N0719.N0932.d009200
    theta.location (theta.scale i) (omega i j) (theta.scale_pos i).ne'

theorem d011758
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 < _root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes theta omega := by
  unfold _root_.GD.N0232.N0719.N0830.d011754
  exact div_pos
    (_root_.GD.N0232.N0719.N0830.d011757 k sizes theta omega)
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta)


def d011759
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (headLevel : ℕ) : ℝ≥0∞ :=
  _root_.GD.N0230.N0640.d000270 (_root_.GD.N0232.N0719.d009182 k sizes)
    (_root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes theta)
    (_root_.GD.N0230.N0670.d001646 p q) headLevel



def d011760
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : ℝ≥0∞ :=
  _root_.GD.N0230.N0640.d000272 (_root_.GD.N0232.N0719.d009182 k sizes)
    (_root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes theta)
    (_root_.GD.N0230.N0670.d001646 p q)



theorem d011761
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (h : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    _root_.GD.N0230.N0640.d000272 (_root_.GD.N0232.N0719.d009182 k sizes)
        (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta) h =
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 h := by
  have hrisk := _root_.GD.N0230.N0591.d000130
    (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta) 0 h
    (_root_.GD.N0232.N0719.N0865.d011220 k sizes theta)
    (_root_.GD.N0232.N0719.N0865.d011218 k sizes theta)
    (_root_.GD.N0232.N0719.N0865.d011219 k sizes theta)
  simpa [_root_.GD.N0230.N0640.d000272, _root_.GD.N0230.N0591.d000126] using hrisk.symm



theorem d011762
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    _root_.GD.N0232.N0719.N0830.d011760 k sizes hk hsizes theta p q =
      ENNReal.ofReal
          (1 / _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta) *
        _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) := by
  let C := _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta
  let w := _root_.GD.N0232.N0719.N0865.d011217 k sizes theta
  let h := _root_.GD.N0230.N0670.d001646 p q
  have hC : 0 < C := _root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta
  have hwmeas : Measurable w :=
    _root_.GD.N0232.N0719.N0865.d011218 k sizes theta
  have hintMeas : AEMeasurable
      (fun omega => ENNReal.ofReal (w omega * h omega ^ 2))
      (_root_.GD.N0232.N0719.d009182 k sizes) :=
    ((hwmeas.aemeasurable.mul
      ((Lp.aestronglyMeasurable h).aemeasurable.pow_const 2)).ennreal_ofReal)
  unfold _root_.GD.N0232.N0719.N0830.d011760 _root_.GD.N0230.N0640.d000272
    _root_.GD.N0232.N0719.N0830.d011754
  change (∫⁻ omega, ENNReal.ofReal
      ((w omega / C) * h omega ^ 2) ∂_root_.GD.N0232.N0719.d009182 k sizes) = _
  calc
    (∫⁻ omega, ENNReal.ofReal
        ((w omega / C) * h omega ^ 2) ∂_root_.GD.N0232.N0719.d009182 k sizes) =
        ∫⁻ omega, ENNReal.ofReal (1 / C) *
          ENNReal.ofReal (w omega * h omega ^ 2)
          ∂_root_.GD.N0232.N0719.d009182 k sizes := by
      apply lintegral_congr
      intro omega
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / C)]
      congr 1
      ring
    _ = ENNReal.ofReal (1 / C) *
        _root_.GD.N0230.N0640.d000272 (_root_.GD.N0232.N0719.d009182 k sizes) w h := by
      rw [lintegral_const_mul'' _ hintMeas]
      rfl
    _ = ENNReal.ofReal (1 / C) *
        _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 h := by
      rw [_root_.GD.N0232.N0719.N0830.d011761]


theorem d011763
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) ≠ ⊤ := by
  have hidentity := _root_.GD.N0230.N0670.d001647
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta)
    theta.location p q
  have htaxLe :
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) ≤
        ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p +
          ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0719.N0859.d010821 k sizes theta q := by
    calc
      _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) ≤
          _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0230.N0718.d001528 p q) +
            _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
              (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q) :=
        le_add_left le_rfl
      _ = _ := hidentity
  apply ne_top_of_le_ne_top _ htaxLe
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (_root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hp theta),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (_root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hq theta)⟩



theorem d011764
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0830.d011760 k sizes hk hsizes theta p q =
      ENNReal.ofReal
        (_root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q) := by
  let C := _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta
  let Q := _root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)
  have hC : 0 < C := _root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta
  have hQ : Q ≠ ⊤ :=
    _root_.GD.N0232.N0719.N0830.d011763 k sizes hk hsizes theta hp hq
  rw [_root_.GD.N0232.N0719.N0830.d011762]
  change ENNReal.ofReal (1 / C) * Q =
    ENNReal.ofReal (Q.toReal / C)
  calc
    ENNReal.ofReal (1 / C) * Q =
        ENNReal.ofReal (1 / C) * ENNReal.ofReal Q.toReal := by
      rw [ENNReal.ofReal_toReal hQ]
    _ = ENNReal.ofReal ((1 / C) * Q.toReal) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / C)]
    _ = ENNReal.ofReal (Q.toReal / C) := by
      congr 1
      ring



theorem d011765
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (headLevel : ℕ) :
    _root_.GD.N0232.N0719.N0830.d011759 k sizes hk hsizes theta p q headLevel ≤
      ENNReal.ofReal ((2 : ℝ) ^ headLevel) *
        ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q) := by
  unfold _root_.GD.N0232.N0719.N0830.d011759
  calc
    _root_.GD.N0230.N0640.d000270 (_root_.GD.N0232.N0719.d009182 k sizes)
        (_root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes theta)
        (_root_.GD.N0230.N0670.d001646 p q) headLevel ≤
      ENNReal.ofReal ((2 : ℝ) ^ headLevel) *
        _root_.GD.N0232.N0719.N0830.d011760 k sizes hk hsizes theta p q :=
      _root_.GD.N0230.N0640.d000274
        (_root_.GD.N0232.N0719.d009182 k sizes)
        (_root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes theta)
        (_root_.GD.N0232.N0719.N0830.d011755
          k sizes hk hsizes theta)
        (_root_.GD.N0232.N0719.N0830.d011756
          k sizes hk hsizes theta)
        (_root_.GD.N0230.N0670.d001646 p q) headLevel
    _ = _ := by
      rw [_root_.GD.N0232.N0719.N0830.d011764
        k sizes hk hsizes theta hp hq]



theorem d011766
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    Tendsto
      (fun headLevel =>
        _root_.GD.N0232.N0719.N0830.d011759 k sizes hk hsizes theta p q headLevel)
      atTop
      (nhds (_root_.GD.N0230.N0640.d000271
        (_root_.GD.N0232.N0719.d009182 k sizes) (_root_.GD.N0230.N0670.d001646 p q))) := by
  exact _root_.GD.N0230.N0640.d000275
    (_root_.GD.N0232.N0719.d009182 k sizes)
    (_root_.GD.N0232.N0719.N0830.d011754 k sizes hk hsizes theta)
    (_root_.GD.N0232.N0719.N0830.d011755
      k sizes hk hsizes theta)
    (Filter.Eventually.of_forall fun omega =>
      _root_.GD.N0232.N0719.N0830.d011758
        k sizes hk hsizes theta omega)
    (_root_.GD.N0230.N0670.d001646 p q)







theorem d011767
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (htax : Tendsto
      (fun j => _root_.GD.N0232.N0719.N0811.d011037
        k sizes hk hsizes (thetaSeq j) p q)
      atTop (nhds 0))
    (headLevel : ℕ) :
    Tendsto
      (fun j => _root_.GD.N0232.N0719.N0830.d011759
        k sizes hk hsizes (thetaSeq j) p q headLevel)
      atTop (nhds 0) := by
  have henergy : Tendsto
      (fun j => _root_.GD.N0232.N0719.N0830.d011760
        k sizes hk hsizes (thetaSeq j) p q)
      atTop (nhds 0) := by
    have hofReal : Tendsto
        (fun j => ENNReal.ofReal (_root_.GD.N0232.N0719.N0811.d011037
          k sizes hk hsizes (thetaSeq j) p q))
        atTop (nhds 0) := by
      have hcomp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp htax
      change Tendsto
        (fun j => ENNReal.ofReal (_root_.GD.N0232.N0719.N0811.d011037
          k sizes hk hsizes (thetaSeq j) p q))
        atTop (nhds (ENNReal.ofReal 0)) at hcomp
      simpa using hcomp
    simpa only [_root_.GD.N0232.N0719.N0830.d011764
      k sizes hk hsizes (hp := hp) (hq := hq), ENNReal.ofReal_zero] using hofReal
  exact _root_.GD.N0230.N0640.d000276
    (_root_.GD.N0232.N0719.d009182 k sizes)
    (fun j => _root_.GD.N0232.N0719.N0830.d011754
      k sizes hk hsizes (thetaSeq j))
    (fun j => _root_.GD.N0232.N0719.N0830.d011755
      k sizes hk hsizes (thetaSeq j))
    (fun j => _root_.GD.N0232.N0719.N0830.d011756
      k sizes hk hsizes (thetaSeq j))
    (_root_.GD.N0230.N0670.d001646 p q) headLevel henergy

end

end N0830
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0830.d011757
#print axioms _root_.GD.N0232.N0719.N0830.d011764
#print axioms _root_.GD.N0232.N0719.N0830.d011765
#print axioms _root_.GD.N0232.N0719.N0830.d011766
#print axioms _root_.GD.N0232.N0719.N0830.d011767
