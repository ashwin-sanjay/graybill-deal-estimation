import Mathlib.Analysis.SpecialFunctions.Pow.Real






































namespace GD
namespace N0232
namespace N0720
namespace N1263

noncomputable section








def d002593 (a : ℝ) : ℝ :=
  a ^ 3



def d002594 (p sigma tau : ℝ) : ℝ :=
  (sigma * tau) ^ (-p)




def d002595 (sigma tau : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1263.d002594 2 sigma tau




def d002596 (sigma tau : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1263.d002594 (5 / 2 : ℝ) sigma tau






theorem d002597
    (p a sigma tau : ℝ) (ha : 0 < a) (hsigma : 0 < sigma)
    (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1263.d002594 p (a * sigma) (a * tau) =
      a ^ (-2 * p) * _root_.GD.N0232.N0720.N1263.d002594 p sigma tau := by
  unfold _root_.GD.N0232.N0720.N1263.d002594
  have hst : 0 ≤ sigma * tau := mul_nonneg hsigma.le htau.le
  have hfactor : (a * sigma) * (a * tau) = a ^ 2 * (sigma * tau) := by
    ring
  rw [hfactor, Real.mul_rpow (sq_nonneg a) hst]
  have hpowTwo : a ^ 2 = a ^ (2 : ℝ) :=
    (Real.rpow_two a).symm
  rw [hpowTwo, ← Real.rpow_mul ha.le]
  have hexponent : (2 : ℝ) * -p = -2 * p := by ring
  rw [hexponent]



theorem d002598
    (p a sigma tau : ℝ) (ha : 0 < a) (hsigma : 0 < sigma)
    (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1263.d002594 p (a * sigma) (a * tau) *
        _root_.GD.N0232.N0720.N1263.d002593 a =
      a ^ (3 - 2 * p) * _root_.GD.N0232.N0720.N1263.d002594 p sigma tau := by
  rw [_root_.GD.N0232.N0720.N1263.d002597 p a sigma tau ha hsigma htau]
  unfold _root_.GD.N0232.N0720.N1263.d002593
  have hpowThree : a ^ 3 = a ^ (3 : ℝ) :=
    (Real.rpow_natCast a 3).symm
  rw [hpowThree]
  calc
    (a ^ (-2 * p) * _root_.GD.N0232.N0720.N1263.d002594 p sigma tau) * a ^ (3 : ℝ) =
        (a ^ (-2 * p) * a ^ (3 : ℝ)) *
          _root_.GD.N0232.N0720.N1263.d002594 p sigma tau := by ring
    _ = a ^ ((-2 * p) + 3) * _root_.GD.N0232.N0720.N1263.d002594 p sigma tau := by
      rw [← Real.rpow_add ha]
    _ = a ^ (3 - 2 * p) * _root_.GD.N0232.N0720.N1263.d002594 p sigma tau := by
      have hexponent : (-2 * p) + 3 = 3 - 2 * p := by ring
      rw [hexponent]


theorem d002599
    (a sigma tau : ℝ) (ha : 0 < a) (hsigma : 0 < sigma)
    (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1263.d002595 (a * sigma) (a * tau) =
      a ^ (-(4 : ℝ)) * _root_.GD.N0232.N0720.N1263.d002595 sigma tau := by
  unfold _root_.GD.N0232.N0720.N1263.d002595
  rw [_root_.GD.N0232.N0720.N1263.d002597 (2 : ℝ) a sigma tau
    ha hsigma htau]
  congr 2
  norm_num



theorem d002600
    (a sigma tau : ℝ) (ha : 0 < a) (hsigma : 0 < sigma)
    (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1263.d002595 (a * sigma) (a * tau) *
        _root_.GD.N0232.N0720.N1263.d002593 a =
      a ^ (-(1 : ℝ)) * _root_.GD.N0232.N0720.N1263.d002595 sigma tau := by
  unfold _root_.GD.N0232.N0720.N1263.d002595
  rw [_root_.GD.N0232.N0720.N1263.d002598
    (2 : ℝ) a sigma tau ha hsigma htau]
  congr 2
  norm_num


theorem d002601
    (a sigma tau : ℝ) (ha : 0 < a) (hsigma : 0 < sigma)
    (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1263.d002596 (a * sigma) (a * tau) =
      a ^ (-(5 : ℝ)) * _root_.GD.N0232.N0720.N1263.d002596 sigma tau := by
  unfold _root_.GD.N0232.N0720.N1263.d002596
  rw [_root_.GD.N0232.N0720.N1263.d002597 (5 / 2 : ℝ) a sigma tau
    ha hsigma htau]
  congr 2
  norm_num



theorem d002602
    (a sigma tau : ℝ) (ha : 0 < a) (hsigma : 0 < sigma)
    (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1263.d002596 (a * sigma) (a * tau) *
        _root_.GD.N0232.N0720.N1263.d002593 a =
      a ^ (-(2 : ℝ)) * _root_.GD.N0232.N0720.N1263.d002596 sigma tau := by
  unfold _root_.GD.N0232.N0720.N1263.d002596
  rw [_root_.GD.N0232.N0720.N1263.d002598
    (5 / 2 : ℝ) a sigma tau ha hsigma htau]
  congr 2
  norm_num




def d002603 (mu eta : ℝ) : ℝ :=
  (eta - mu) ^ 2




theorem d002604
    (b a mu eta : ℝ) :
    _root_.GD.N0232.N0720.N1263.d002603 (b + a * mu) (b + a * eta) =
      a ^ 2 * _root_.GD.N0232.N0720.N1263.d002603 mu eta := by
  unfold _root_.GD.N0232.N0720.N1263.d002603
  ring



def d002605 (kappa : ℝ) : ℝ :=
  kappa + 2



theorem d002606
    (kappa a energy : ℝ) (ha : 0 < a) :
    a ^ kappa * (a ^ 2 * energy) =
      a ^ _root_.GD.N0232.N0720.N1263.d002605 kappa * energy := by
  unfold _root_.GD.N0232.N0720.N1263.d002605
  have hpowTwo : a ^ 2 = a ^ (2 : ℝ) :=
    (Real.rpow_two a).symm
  calc
    a ^ kappa * (a ^ 2 * energy) =
        (a ^ kappa * a ^ 2) * energy := by ring
    _ = (a ^ kappa * a ^ (2 : ℝ)) * energy := by rw [hpowTwo]
    _ = a ^ (kappa + 2) * energy := by rw [← Real.rpow_add ha]




theorem d002607 (kappa : ℝ) :
    _root_.GD.N0232.N0720.N1263.d002605 kappa = 0 ↔ kappa = -(2 : ℝ) := by
  unfold _root_.GD.N0232.N0720.N1263.d002605
  constructor <;> intro h
  · linarith
  · linarith



theorem d002608
    (a : ℝ) (_ha : 0 < a) :
    a ^ _root_.GD.N0232.N0720.N1263.d002605 (-(2 : ℝ)) = 1 := by
  simp [_root_.GD.N0232.N0720.N1263.d002605]



theorem d002609 :
    (-(1 : ℝ)) ≠ -(2 : ℝ) := by
  norm_num




theorem d002610
    (b a mu eta sigma tau : ℝ) (ha : 0 < a)
    (hsigma : 0 < sigma) (htau : 0 < tau) :
    (_root_.GD.N0232.N0720.N1263.d002595 (a * sigma) (a * tau) *
        _root_.GD.N0232.N0720.N1263.d002593 a) *
          _root_.GD.N0232.N0720.N1263.d002603 (b + a * mu) (b + a * eta) =
      a * (_root_.GD.N0232.N0720.N1263.d002595 sigma tau *
        _root_.GD.N0232.N0720.N1263.d002603 mu eta) := by
  rw [_root_.GD.N0232.N0720.N1263.d002600
    a sigma tau ha hsigma htau,
    _root_.GD.N0232.N0720.N1263.d002604]
  rw [Real.rpow_neg ha.le, Real.rpow_one]
  have ha0 : a ≠ 0 := ha.ne'
  field_simp





theorem d002611
    (b a mu eta sigma tau : ℝ) (ha : 0 < a)
    (hsigma : 0 < sigma) (htau : 0 < tau) :
    (_root_.GD.N0232.N0720.N1263.d002596 (a * sigma) (a * tau) *
        _root_.GD.N0232.N0720.N1263.d002593 a) *
          _root_.GD.N0232.N0720.N1263.d002603 (b + a * mu) (b + a * eta) =
      _root_.GD.N0232.N0720.N1263.d002596 sigma tau *
        _root_.GD.N0232.N0720.N1263.d002603 mu eta := by
  rw [_root_.GD.N0232.N0720.N1263.d002602
    a sigma tau ha hsigma htau,
    _root_.GD.N0232.N0720.N1263.d002604]
  rw [Real.rpow_neg ha.le, Real.rpow_two]
  have ha0 : a ≠ 0 := ha.ne'
  field_simp





structure d002612 (Q : Type*) where
  scale : ℝ
  quotient : Q


def d002613 {Q : Type*}
    (a : ℝ) (theta : _root_.GD.N0232.N0720.N1263.d002612 Q) :
    _root_.GD.N0232.N0720.N1263.d002612 Q :=
  ⟨a * theta.scale, theta.quotient⟩


def d002614 {Q : Type*}
    (kappa : ℝ) (f : _root_.GD.N0232.N0720.N1263.d002612 Q → ℝ) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ theta,
    f (_root_.GD.N0232.N0720.N1263.d002613 a theta) = a ^ kappa * f theta


def d002615 {Q : Type*}
    (f : _root_.GD.N0232.N0720.N1263.d002612 Q → ℝ) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ theta,
    f (_root_.GD.N0232.N0720.N1263.d002613 a theta) = f theta


theorem d002616
    {Q : Type*} (phi : Q → ℝ) :
    _root_.GD.N0232.N0720.N1263.d002615
      (fun theta : _root_.GD.N0232.N0720.N1263.d002612 Q ↦ phi theta.quotient) := by
  intro a ha theta
  rfl



theorem d002614.d002617
    {Q : Type*} {kappa : ℝ}
    {f u : _root_.GD.N0232.N0720.N1263.d002612 Q → ℝ}
    (hf : _root_.GD.N0232.N0720.N1263.d002614 kappa f)
    (hu : _root_.GD.N0232.N0720.N1263.d002615 u) :
    _root_.GD.N0232.N0720.N1263.d002614 kappa (fun theta ↦ u theta * f theta) := by
  intro a ha theta
  change u (_root_.GD.N0232.N0720.N1263.d002613 a theta) *
      f (_root_.GD.N0232.N0720.N1263.d002613 a theta) =
    a ^ kappa * (u theta * f theta)
  rw [hu a ha theta, hf a ha theta]
  ring



theorem d002618
    {Q : Type*} {kappa : ℝ}
    (phi : Q → ℝ) (f : _root_.GD.N0232.N0720.N1263.d002612 Q → ℝ)
    (hf : _root_.GD.N0232.N0720.N1263.d002614 kappa f) :
    _root_.GD.N0232.N0720.N1263.d002614 kappa
      (fun theta ↦ phi theta.quotient * f theta) := by
  exact hf.d002617 (_root_.GD.N0232.N0720.N1263.d002616 phi)

end

end N1263
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1263.d002597
#print axioms _root_.GD.N0232.N0720.N1263.d002600
#print axioms _root_.GD.N0232.N0720.N1263.d002602
#print axioms _root_.GD.N0232.N0720.N1263.d002604
#print axioms _root_.GD.N0232.N0720.N1263.d002607
#print axioms _root_.GD.N0232.N0720.N1263.d002610
#print axioms _root_.GD.N0232.N0720.N1263.d002611
#print axioms _root_.GD.N0232.N0720.N1263.d002618
