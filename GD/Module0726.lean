import GD.Module0631
import GD.Module0720
import GD.Module0725

















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0845

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0804
open _root_.GD.N0232.N0719.N0837


theorem d010880
    {k : ℕ} {theta eta : _root_.GD.N0232.N0719.N0859.d010809 k}
    (hlocation : theta.location = eta.location)
    (hscale : ∀ i, theta.scale i = eta.scale i) :
    theta = eta := by
  cases theta with
  | mk thetaLocation thetaScale thetaPos =>
    cases eta with
    | mk etaLocation etaScale etaPos =>
      dsimp at hlocation hscale
      have hscale' : thetaScale = etaScale := funext hscale
      subst etaLocation
      subst etaScale
      rfl


def d010881
    {k : ℕ} (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := shift + dilation * theta.location
  scale := fun i ↦ dilation * theta.scale i
  scale_pos := fun i ↦ mul_pos hdilation (theta.scale_pos i)

@[simp] theorem d010882
    {k : ℕ} (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta).location =
      shift + dilation * theta.location := rfl

@[simp] theorem d010883
    {k : ℕ} (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta).scale i =
      dilation * theta.scale i := rfl


theorem d010884
    {k : ℕ}
    (shift₁ dilation₁ shift₂ dilation₂ : ℝ)
    (hdilation₁ : 0 < dilation₁) (hdilation₂ : 0 < dilation₂)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010881 shift₁ dilation₁ hdilation₁
        (_root_.GD.N0232.N0719.N0845.d010881 shift₂ dilation₂ hdilation₂ theta) =
      _root_.GD.N0232.N0719.N0845.d010881
        (shift₁ + dilation₁ * shift₂)
        (dilation₁ * dilation₂)
        (mul_pos hdilation₁ hdilation₂) theta := by
  apply _root_.GD.N0232.N0719.N0845.d010880
  · simp only [_root_.GD.N0232.N0719.N0845.d010882]
    ring
  · intro i
    simp only [_root_.GD.N0232.N0719.N0845.d010883]
    ring

@[simp] theorem d010885
    {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010881 0 1 zero_lt_one theta = theta := by
  apply _root_.GD.N0232.N0719.N0845.d010880
  · simp
  · intro i
    simp



def d010886 {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  ∑ i, theta.scale i

theorem d010887
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0845.d010886 theta := by
  let i : Fin k := ⟨0, hk⟩
  unfold _root_.GD.N0232.N0719.N0845.d010886
  exact Finset.sum_pos' (fun j _ ↦ (theta.scale_pos j).le)
    ⟨i, Finset.mem_univ i, theta.scale_pos i⟩

theorem d010888
    {k : ℕ} (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010886 (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      dilation * _root_.GD.N0232.N0719.N0845.d010886 theta := by
  unfold _root_.GD.N0232.N0719.N0845.d010886
  simp only [_root_.GD.N0232.N0719.N0845.d010883]
  exact (Finset.mul_sum _ _ _).symm



theorem d010889
    {k : ℕ} (hk : 0 < k)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta = theta ↔
      shift = 0 ∧ dilation = 1 := by
  constructor
  · intro hfix
    let i : Fin k := ⟨0, hk⟩
    have hscale := congrArg (fun p : _root_.GD.N0232.N0719.N0859.d010809 k ↦ p.scale i) hfix
    have hlocation := congrArg (_root_.GD.N0232.N0719.N0859.d010809.location (k := k)) hfix
    simp only [_root_.GD.N0232.N0719.N0845.d010883] at hscale
    simp only [_root_.GD.N0232.N0719.N0845.d010882] at hlocation
    have hdilation_one : dilation = 1 := by
      nlinarith [theta.scale_pos i]
    constructor
    · rw [hdilation_one] at hlocation
      linarith
    · exact hdilation_one
  · rintro ⟨rfl, rfl⟩
    exact _root_.GD.N0232.N0719.N0845.d010885 theta



noncomputable def d010890
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010809 k :=
  _root_.GD.N0232.N0719.N0845.d010881
    (-(theta.location / _root_.GD.N0232.N0719.N0845.d010886 theta))
    (_root_.GD.N0232.N0719.N0845.d010886 theta)⁻¹
    (inv_pos.mpr (_root_.GD.N0232.N0719.N0845.d010887 hk theta)) theta

@[simp] theorem d010891
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0232.N0719.N0845.d010890 hk theta).location = 0 := by
  unfold _root_.GD.N0232.N0719.N0845.d010890
  simp only [_root_.GD.N0232.N0719.N0845.d010882]
  field_simp [(_root_.GD.N0232.N0719.N0845.d010887 hk theta).ne']
  ring

@[simp] theorem d010892
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0845.d010890 hk theta).scale i =
      (_root_.GD.N0232.N0719.N0845.d010886 theta)⁻¹ * theta.scale i := rfl

@[simp] theorem d010893
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010886 (_root_.GD.N0232.N0719.N0845.d010890 hk theta) = 1 := by
  rw [_root_.GD.N0232.N0719.N0845.d010890, _root_.GD.N0232.N0719.N0845.d010888]
  exact inv_mul_cancel₀ (_root_.GD.N0232.N0719.N0845.d010887 hk theta).ne'


theorem d010894
    {k : ℕ} (hk : 0 < k)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010890 hk
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      _root_.GD.N0232.N0719.N0845.d010890 hk theta := by
  apply _root_.GD.N0232.N0719.N0845.d010880
  · simp
  · intro i
    simp only [_root_.GD.N0232.N0719.N0845.d010892, _root_.GD.N0232.N0719.N0845.d010883,
      _root_.GD.N0232.N0719.N0845.d010888]
    field_simp [hdilation.ne', (_root_.GD.N0232.N0719.N0845.d010887 hk theta).ne']


theorem d010895
    {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010890 hk theta = theta ↔
      theta.location = 0 ∧ _root_.GD.N0232.N0719.N0845.d010886 theta = 1 := by
  constructor
  · intro h
    constructor
    · have := congrArg (_root_.GD.N0232.N0719.N0859.d010809.location (k := k)) h
      simpa using this.symm
    · have := congrArg _root_.GD.N0232.N0719.N0845.d010886 h
      simpa using this.symm
  · rintro ⟨hlocation, hscale⟩
    apply _root_.GD.N0232.N0719.N0845.d010880
    · simpa [hlocation]
    · intro i
      simp [hscale]




theorem d010896
    {k : ℕ} (hk : 0 < k) (theta eta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (∃ (shift dilation : ℝ) (hdilation : 0 < dilation),
        _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta = eta) ↔
      _root_.GD.N0232.N0719.N0845.d010890 hk theta = _root_.GD.N0232.N0719.N0845.d010890 hk eta := by
  constructor
  · rintro ⟨shift, dilation, hdilation, rfl⟩
    exact (_root_.GD.N0232.N0719.N0845.d010894 hk shift dilation hdilation theta).symm
  · intro hnormalized
    have htheta : 0 < _root_.GD.N0232.N0719.N0845.d010886 theta := _root_.GD.N0232.N0719.N0845.d010887 hk theta
    have heta : 0 < _root_.GD.N0232.N0719.N0845.d010886 eta := _root_.GD.N0232.N0719.N0845.d010887 hk eta
    let dilation : ℝ := _root_.GD.N0232.N0719.N0845.d010886 eta / _root_.GD.N0232.N0719.N0845.d010886 theta
    let shift : ℝ := eta.location - dilation * theta.location
    have hdilation : 0 < dilation := div_pos heta htheta
    refine ⟨shift, dilation, hdilation, ?_⟩
    apply _root_.GD.N0232.N0719.N0845.d010880
    · simp only [_root_.GD.N0232.N0719.N0845.d010882]
      dsimp [shift]
      ring
    · intro i
      have hcoordinate := congrArg
          (fun p : _root_.GD.N0232.N0719.N0859.d010809 k ↦ p.scale i) hnormalized
      simp only [_root_.GD.N0232.N0719.N0845.d010892] at hcoordinate
      simp only [_root_.GD.N0232.N0719.N0845.d010883]
      dsimp [dilation]
      field_simp [htheta.ne', heta.ne'] at hcoordinate ⊢
      exact hcoordinate


theorem d010897
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      dilation ^ 2 * _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta := by
  have hk0 : 0 < k := by omega
  have hsizes0 : ∀ i, 0 < sizes i := fun i ↦
    lt_of_lt_of_le (by norm_num) (hsizes i)
  unfold _root_.GD.N0232.N0719.N0858.d010851 _root_.GD.N0232.N0719.N0859.d010812
    _root_.GD.N0232.N0719.N0859.d010815
  change
    _root_.GD.N0141.d006684
        (_root_.GD.N0232.N0719.d009176 k sizes
          (shift + dilation * theta.location)
          (fun i ↦ dilation * theta.scale i))
        (fun omega ↦
          _root_.GD.N0232.N0719.N0900.d009111 k sizes omega -
            (shift + dilation * theta.location)) +
      _root_.GD.N0232.N0719.N1024.d010727 k sizes hk *
        _root_.GD.N0232.N0719.N1024.d010712 k sizes hk
          (fun i ↦ dilation * theta.scale i) =
      dilation ^ 2 *
        (_root_.GD.N0141.d006684
            (_root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale)
            (fun omega ↦
              _root_.GD.N0232.N0719.N0900.d009111 k sizes omega - theta.location) +
          _root_.GD.N0232.N0719.N1024.d010727 k sizes hk *
            _root_.GD.N0232.N0719.N1024.d010712 k sizes hk theta.scale)
  rw [_root_.GD.N0232.N0719.N0804.d009189
    k sizes hk0 hsizes0 shift theta.location dilation hdilation.ne'
    theta.scale]
  rw [_root_.GD.N0232.N0719.N0837.d010744
    k sizes hk hsizes dilation hdilation.ne' theta.scale]
  ring


theorem d010898
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift : ℝ) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift 1 zero_lt_one theta) =
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta := by
  simpa using
    _root_.GD.N0232.N0719.N0845.d010897
      k sizes hk hsizes shift 1 zero_lt_one theta



noncomputable def d010899
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta / _root_.GD.N0232.N0719.N0845.d010886 theta ^ 2

theorem d010900
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010899 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      _root_.GD.N0232.N0719.N0845.d010899 k sizes hk hsizes theta := by
  unfold _root_.GD.N0232.N0719.N0845.d010899
  rw [_root_.GD.N0232.N0719.N0845.d010897
    k sizes hk hsizes shift dilation hdilation theta]
  rw [_root_.GD.N0232.N0719.N0845.d010888]
  field_simp [hdilation.ne',
    (_root_.GD.N0232.N0719.N0845.d010887 (by omega : 0 < k) theta).ne']



theorem d010901
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010899 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta) =
      _root_.GD.N0232.N0719.N0845.d010899 k sizes hk hsizes theta := by
  unfold _root_.GD.N0232.N0719.N0845.d010890
  exact _root_.GD.N0232.N0719.N0845.d010900
    k sizes hk hsizes
    (-(theta.location / _root_.GD.N0232.N0719.N0845.d010886 theta))
    (_root_.GD.N0232.N0719.N0845.d010886 theta)⁻¹
    (inv_pos.mpr (_root_.GD.N0232.N0719.N0845.d010887 (by omega : 0 < k) theta)) theta




theorem d010902
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta =
      _root_.GD.N0232.N0719.N0845.d010886 theta ^ 2 *
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
          (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta) := by
  have h := _root_.GD.N0232.N0719.N0845.d010901
    k sizes hk hsizes theta
  unfold _root_.GD.N0232.N0719.N0845.d010899 at h
  rw [_root_.GD.N0232.N0719.N0845.d010893] at h
  norm_num at h
  have hmul := (eq_div_iff
    (pow_ne_zero 2
      (_root_.GD.N0232.N0719.N0845.d010887 (by omega : 0 < k) theta).ne')).mp h
  simpa [mul_comm] using hmul.symm



theorem d010903
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) =
      ENNReal.ofReal (dilation ^ 2) *
        _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta := by
  unfold _root_.GD.N0232.N0719.N0858.d010852
  rw [_root_.GD.N0232.N0719.N0845.d010897
    k sizes hk hsizes shift dilation hdilation theta]
  exact ENNReal.ofReal_mul (sq_nonneg dilation)

theorem d010904
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift : ℝ) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift 1 zero_lt_one theta) =
      _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta := by
  simpa using
    _root_.GD.N0232.N0719.N0845.d010903
      k sizes hk hsizes shift 1 zero_lt_one theta


theorem d010905
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift₁ dilation₁ shift₂ dilation₂ : ℝ)
    (hdilation₁ : 0 < dilation₁) (hdilation₂ : 0 < dilation₂)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift₁ dilation₁ hdilation₁
          (_root_.GD.N0232.N0719.N0845.d010881 shift₂ dilation₂ hdilation₂ theta)) =
      (ENNReal.ofReal (dilation₁ ^ 2) *
          ENNReal.ofReal (dilation₂ ^ 2)) *
        _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta := by
  rw [_root_.GD.N0232.N0719.N0845.d010903
    k sizes hk hsizes shift₁ dilation₁ hdilation₁]
  rw [_root_.GD.N0232.N0719.N0845.d010903
    k sizes hk hsizes shift₂ dilation₂ hdilation₂]
  exact (mul_assoc _ _ _).symm

end

end N0845
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0845.d010884
#print axioms _root_.GD.N0232.N0719.N0845.d010889
#print axioms _root_.GD.N0232.N0719.N0845.d010894
#print axioms _root_.GD.N0232.N0719.N0845.d010897
#print axioms _root_.GD.N0232.N0719.N0845.d010900
#print axioms _root_.GD.N0232.N0719.N0845.d010902
#print axioms _root_.GD.N0232.N0719.N0845.d010903
#print axioms _root_.GD.N0232.N0719.N0845.d010905
