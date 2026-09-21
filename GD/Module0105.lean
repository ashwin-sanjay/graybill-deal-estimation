import GD.Module0104





























namespace GD
namespace N0230
namespace N0668

noncomputable section

open _root_.GD.N0230.N0673

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Theta : Type*}



def d001343 (lambda : ℝ) (r s : H) : H :=
  (1 - lambda) • r + lambda • s



theorem d001344
    (psi : Theta → H) (r s : H) (lambda : ℝ) (theta : Theta) :
    ‖_root_.GD.N0230.N0668.d001343 lambda r s - psi theta‖ ^ 2 -
        ‖s - psi theta‖ ^ 2 =
      (1 - lambda) *
        ((‖r - psi theta‖ ^ 2 - ‖s - psi theta‖ ^ 2) -
          lambda * ‖r - s‖ ^ 2) := by
  have hcomb : _root_.GD.N0230.N0668.d001343 lambda r s - psi theta =
      (1 - lambda) • (r - psi theta) +
        lambda • (s - psi theta) := by
    unfold _root_.GD.N0230.N0668.d001343
    rw [smul_sub, smul_sub]
    have hpsi : (1 - lambda) • psi theta + lambda • psi theta =
        psi theta := by
      rw [← add_smul]
      norm_num
    calc
      (1 - lambda) • r + lambda • s - psi theta =
          (1 - lambda) • r + lambda • s -
            ((1 - lambda) • psi theta + lambda • psi theta) := by
              rw [hpsi]
      _ = (1 - lambda) • r - (1 - lambda) • psi theta +
          (lambda • s - lambda • psi theta) := by abel
  have hdiff : r - psi theta - (s - psi theta) = r - s := by
    abel
  have hnorm := _root_.GD.N0230.N0673.d001332
    (r - psi theta) (s - psi theta) (1 - lambda)
  simp only [sub_sub_cancel] at hnorm
  rw [hcomb, hnorm, hdiff]
  ring



theorem d001345
    (psi : Theta → H) (r s : H) (lambda : ℝ)
    (hlambda : lambda ≤ 1)
    (hcriterion : ∀ theta,
      ‖r - psi theta‖ ^ 2 - ‖s - psi theta‖ ^ 2 ≤
        lambda * ‖r - s‖ ^ 2) :
    ∀ theta,
      ‖_root_.GD.N0230.N0668.d001343 lambda r s - psi theta‖ ^ 2 ≤
        ‖s - psi theta‖ ^ 2 := by
  intro theta
  rw [← sub_nonpos,
    _root_.GD.N0230.N0668.d001344 psi r s lambda theta]
  exact mul_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr hlambda) (sub_nonpos.mpr (hcriterion theta))


theorem d001346
    (psi : Theta → H) (r s : H) (lambda : ℝ)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1)
    (hcriterion : ∀ theta,
      ‖r - psi theta‖ ^ 2 - ‖s - psi theta‖ ^ 2 ≤
        lambda * ‖r - s‖ ^ 2) :
    ∀ theta,
      ‖_root_.GD.N0230.N0668.d001343 lambda r s - psi theta‖ ^ 2 ≤
        ‖s - psi theta‖ ^ 2 :=
  _root_.GD.N0230.N0668.d001345
    psi r s lambda hlambda.2 hcriterion




theorem d001347
    (excess tax : Theta → ℝ) (lambda : ℝ)
    (htax : ∀ theta, 0 < tax theta)
    (hratio : ∀ theta, excess theta / tax theta ≤ lambda) :
    ∀ theta, excess theta ≤ lambda * tax theta := by
  intro theta
  exact (div_le_iff₀ (htax theta)).mp (hratio theta)



theorem d001348
    (excess tax : Theta → ℝ) (lambda : ℝ)
    (htax : ∀ theta, 0 < tax theta) :
    (∀ theta, excess theta / tax theta ≤ lambda) ↔
      ∀ theta, excess theta ≤ lambda * tax theta := by
  constructor
  · exact _root_.GD.N0230.N0668.d001347 excess tax lambda htax
  · intro h theta
    exact (div_le_iff₀ (htax theta)).2 (h theta)




theorem d001349
    (excess tax : Theta → ℝ) (lambda : ℝ)
    (htax : ∀ theta, 0 ≤ tax theta)
    (hratio : ∀ theta, 0 < tax theta →
      excess theta / tax theta ≤ lambda)
    (hzero : ∀ theta, tax theta = 0 → excess theta ≤ 0) :
    ∀ theta, excess theta ≤ lambda * tax theta := by
  intro theta
  rcases (htax theta).eq_or_lt with htaxZero | htaxPos
  · calc
      excess theta ≤ 0 := hzero theta htaxZero.symm
      _ = lambda * tax theta := by rw [← htaxZero]; ring
  · exact (div_le_iff₀ htaxPos).mp (hratio theta htaxPos)




theorem d001350
    (psi : Theta → H) (r s : H) (lambda : ℝ)
    (hlambda : lambda ≤ 1) (hrs : r ≠ s)
    (hratio : ∀ theta,
      (‖r - psi theta‖ ^ 2 - ‖s - psi theta‖ ^ 2) /
          ‖r - s‖ ^ 2 ≤ lambda) :
    ∀ theta,
      ‖_root_.GD.N0230.N0668.d001343 lambda r s - psi theta‖ ^ 2 ≤
        ‖s - psi theta‖ ^ 2 := by
  have htax : 0 < ‖r - s‖ ^ 2 := by
    have hnorm : 0 < ‖r - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hrs)
    positivity
  apply _root_.GD.N0230.N0668.d001345
    psi r s lambda hlambda
  intro theta
  exact (div_le_iff₀ htax).mp (hratio theta)

end
end N0668
end N0230
end GD

#print axioms _root_.GD.N0230.N0668.d001344
#print axioms _root_.GD.N0230.N0668.d001345
#print axioms _root_.GD.N0230.N0668.d001348
#print axioms _root_.GD.N0230.N0668.d001349
#print axioms _root_.GD.N0230.N0668.d001350
