import GD.Module0134
import GD.Module0029
import GD.Module0767
import GD.Module0634

















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0849

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0813
open _root_.GD.N0232.N0719.N0818
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0107
open _root_.GD.N0230.N0655
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0566
open _root_.GD.N0230.N0569
open _root_.GD.N0230.N0580



def d011768
    (k : ℕ) (sizes : Fin k → ℕ)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  AEStronglyMeasurable.mk
    (fun omega ↦ p omega) (Lp.aestronglyMeasurable p)

theorem d011769
    (k : ℕ) (sizes : Fin k → ℕ)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    Measurable (_root_.GD.N0232.N0719.N0849.d011768 k sizes p) :=
  AEStronglyMeasurable.measurable_mk (Lp.aestronglyMeasurable p)

theorem d011770
    (k : ℕ) (sizes : Fin k → ℕ)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    _root_.GD.N0232.N0719.N0849.d011768 k sizes p =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
      (fun omega ↦ p omega) :=
  (Lp.aestronglyMeasurable p).ae_eq_mk.symm

theorem d011771
    (k : ℕ) (sizes : Fin k → ℕ)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    MemLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes p) 2
      (_root_.GD.N0232.N0719.d009182 k sizes) := by
  exact MemLp.ae_eq
    (_root_.GD.N0232.N0719.N0849.d011770 k sizes p).symm
    (Lp.memLp p)

theorem d011772
    (k : ℕ) (sizes : Fin k → ℕ)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    MemLp.toLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes p)
        (_root_.GD.N0232.N0719.N0849.d011771 k sizes p) = p := by
  calc
    MemLp.toLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes p)
        (_root_.GD.N0232.N0719.N0849.d011771 k sizes p) =
        MemLp.toLp (fun omega ↦ p omega) (Lp.memLp p) :=
      MemLp.toLp_congr
        (_root_.GD.N0232.N0719.N0849.d011771 k sizes p) (Lp.memLp p)
        (_root_.GD.N0232.N0719.N0849.d011770 k sizes p)
    _ = p := Lp.toLp_coeFn p (Lp.memLp p)





theorem d011773
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : MemLp d 2 (_root_.GD.N0232.N0719.d009182 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (show _root_.GD.N0232.N0719.N0816.d010975 k sizes from MemLp.toLp d hd) := by
  have hd' : MemLp d 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    simpa [_root_.GD.N0232.N0719.N0859.d010813] using hd
  have h := _root_.GD.N0232.N0719.N0859.d010841 k sizes theta d hd'
  simpa [_root_.GD.N0232.N0719.N0859.d010813] using h


theorem d011774
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d)
    (hfeasible : _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes d) :
    MemLp d 2 (_root_.GD.N0232.N0719.d009182 k sizes) := by
  have hdRisk_ne_top :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (hfeasible (_root_.GD.N0232.N0719.N0859.d010810 k))
    unfold _root_.GD.N0232.N0719.N0858.d010852
    exact ENNReal.ofReal_ne_top
  apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).2
  have hlin :
      (∫⁻ omega, ENNReal.ofReal (d omega ^ 2)
        ∂_root_.GD.N0232.N0719.d009182 k sizes) ≠ ⊤ := by
    simpa [_root_.GD.N0232.N0719.N0859.d010840, _root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0859.d010810, _root_.GD.N0232.N0719.d009182] using
      hdRisk_ne_top
  have hint :=
    integrable_toReal_of_lintegral_ne_top
      ((hd.pow_const 2).ennreal_ofReal.aemeasurable) hlin
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint



theorem d011775
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d)
    (hfeasible : _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes d) :
    MemLp.toLp d
        (_root_.GD.N0232.N0719.N0849.d011774 k sizes hk hsizes d hd hfeasible)
      ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
  intro theta
  let hdLp :=
    _root_.GD.N0232.N0719.N0849.d011774 k sizes hk hsizes d hd hfeasible
  calc
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (show _root_.GD.N0232.N0719.N0816.d010975 k sizes from MemLp.toLp d hdLp) =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d :=
      (_root_.GD.N0232.N0719.N0849.d011773 k sizes theta d hdLp).symm
    _ ≤ _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta := hfeasible theta


theorem d011776
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : MemLp d 2 (_root_.GD.N0232.N0719.d009182 k sizes)) :
    _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes active epsilon d =
      _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon
        (MemLp.toLp d hd) := by
  unfold _root_.GD.N0232.N0719.N0815.d010935 _root_.GD.N0232.N0719.N0816.d010978
  congr 1
  funext theta
  unfold _root_.GD.N0232.N0719.N0815.d010933 _root_.GD.N0232.N0719.N0816.d010977
  rw [_root_.GD.N0232.N0719.N0849.d011773 k sizes theta.1 d hd]









theorem d011777
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hunique :
      _root_.GD.N0230.N0569.d001685
        (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes))
        ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p)) :
    ∀ (shift dilation : ℝ), 0 < dilation →
      _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation
          (_root_.GD.N0232.N0719.N0849.d011768 k sizes p) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
        _root_.GD.N0232.N0719.N0849.d011768 k sizes p := by
  let objective := _root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage
  let C := _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes
  let face := _root_.GD.N0230.N0566.d000753 objective C
  have htower : _root_.GD.N0230.N0583.d000745 objective C face :=
    _root_.GD.N0230.N0566.d000756 objective C
  have hpWeakCap :
      (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p ∈ C := by
    rw [← htower.1]
    exact hunique.1 0
  have hpCap : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    have h := _root_.GD.N0232.N0719.N0818.d011652
      k sizes hk hsizes hpWeakCap
    simpa using h
  let d := _root_.GD.N0232.N0719.N0849.d011768 k sizes p
  have hdMeas : Measurable d :=
    _root_.GD.N0232.N0719.N0849.d011769 k sizes p
  have hdLp : MemLp d 2 (_root_.GD.N0232.N0719.d009182 k sizes) :=
    _root_.GD.N0232.N0719.N0849.d011771 k sizes p
  have hdp : MemLp.toLp d hdLp = p := by
    simpa [d] using _root_.GD.N0232.N0719.N0849.d011772 k sizes p
  have hdFeasible : _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes d := by
    intro theta
    calc
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d =
          _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
            (show _root_.GD.N0232.N0719.N0816.d010975 k sizes from MemLp.toLp d hdLp) :=
        _root_.GD.N0232.N0719.N0849.d011773 k sizes theta d hdLp
      _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p := congrArg (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta) hdp
      _ ≤ _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta := hpCap theta
  intro shift dilation hdilation
  let dg := _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d
  have hdgMeas : Measurable dg :=
    _root_.GD.N0232.N0719.N0842.d010912 k sizes shift dilation d hdMeas
  have hdgFeasible : _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes dg := by
    exact _root_.GD.N0232.N0719.N0842.d010922
      k sizes hk hsizes shift dilation hdilation d hdMeas hdFeasible
  let hdgLp : MemLp dg 2 (_root_.GD.N0232.N0719.d009182 k sizes) :=
    _root_.GD.N0232.N0719.N0849.d011774
      k sizes hk hsizes dg hdgMeas hdgFeasible
  let q : _root_.GD.N0232.N0719.N0816.d010975 k sizes := MemLp.toLp dg hdgLp
  have hqCap : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    exact _root_.GD.N0232.N0719.N0849.d011775
      k sizes hk hsizes dg hdgMeas hdgFeasible
  have hqWeakCap :
      (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) q ∈ C := by
    exact ⟨q, hqCap, rfl⟩
  have hobjectives : ∀ i,
      objective i ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) q) =
        objective i ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p) := by
    intro i
    change
      _root_.GD.N0232.N0719.N0816.d010979 k sizes hk hsizes
          (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
          ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) q) =
        _root_.GD.N0232.N0719.N0816.d010979 k sizes hk hsizes
          (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2)
          ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p)
    rw [_root_.GD.N0232.N0719.N0816.d010980,
      _root_.GD.N0232.N0719.N0816.d010980]
    simp only [LinearEquiv.symm_apply_apply]
    calc
      _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes
          (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) q =
          _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes
            (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) dg := by
              exact (_root_.GD.N0232.N0719.N0849.d011776
                k sizes hk hsizes (stage i).1
                (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) dg hdgLp).symm
      _ = _root_.GD.N0232.N0719.N0815.d010935 k sizes hk hsizes
            (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) d := by
              exact _root_.GD.N0232.N0719.N0815.d010937
                k sizes hk hsizes (stage i).1
                (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) shift dilation
                hdilation d hdMeas
      _ = _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes
            (stage i).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) p := by
              rw [_root_.GD.N0232.N0719.N0849.d011776
                k sizes hk hsizes (stage i).1
                (_root_.GD.N0232.N0719.N0815.d010938 (stage i).2) d hdLp, hdp]
  have hqSurvivor : ∀ i,
      (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) q ∈ face i :=
    _root_.GD.N0230.N0580.d001536
      objective C face htower hunique.1 hqWeakCap hobjectives
  have hqpWeak :
      (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) q =
        (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p :=
    hunique.2 _ hqSurvivor
  have hqp : q = p := by
    simpa using congrArg (_root_.GD.N0232.N0719.N0818.d011648 k sizes) hqpWeak
  have htoLp : MemLp.toLp dg hdgLp = MemLp.toLp d hdLp := by
    change q = MemLp.toLp d hdLp
    rw [hqp, hdp]
  exact (MemLp.toLp_eq_toLp_iff hdgLp hdLp).mp htoLp




theorem d011778
    (k : ℕ) (sizes : Fin k → ℕ)
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0232.N0719.N0842.d010907 k sizes
        g⁻¹.shift g⁻¹.d009239 omega = g • omega := by
  ext i j
  simp [_root_.GD.N0232.N0719.N0842.d010907, _root_.GD.N0232.N0719.N0842.d010906,
    _root_.GD.N0232.N0719.N0946.d009229.d009239, _root_.GD.N0232.N0719.N0900.d009095,
    _root_.GD.N0107.d009018]
  rw [Real.exp_neg, inv_inv]
  exact Or.inl rfl



theorem d011779
    (k : ℕ) (sizes : Fin k → ℕ)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hfixed : ∀ g : _root_.GD.N0230.N0655.d000349,
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 g.2 d =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes] d) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega ↦ d (g • omega)) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
        fun omega ↦ g • d omega := by
  intro g
  let inverseParameter : _root_.GD.N0230.N0655.d000349 :=
    (g⁻¹.shift, ⟨g⁻¹.d009239, g⁻¹.d009240⟩)
  filter_upwards [hfixed inverseParameter] with omega homega
  change _root_.GD.N0232.N0719.N0842.d010911 k sizes g⁻¹.shift g⁻¹.d009239 d omega =
      d omega at homega
  unfold _root_.GD.N0232.N0719.N0842.d010911 at homega
  rw [show _root_.GD.N0232.N0719.N0842.d010907 k sizes
      g⁻¹.shift g⁻¹.d009239 omega = g • omega from
        _root_.GD.N0232.N0719.N0849.d011778 k sizes g omega] at homega
  change
    -(Real.exp (-g.logScale) * g.shift) +
        Real.exp (-g.logScale) * d (g • omega) = d omega at homega
  change d (g • omega) = g.shift + Real.exp g.logScale * d omega
  rw [Real.exp_neg] at homega
  field_simp [Real.exp_ne_zero] at homega
  linarith







theorem d011780
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hunique :
      _root_.GD.N0230.N0569.d001685
        (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes))
        ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p)) :
    ∃ repaired : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable repaired ∧
      (∀ (location : ℝ) (scale : Fin k → ℝ),
        (∀ i, 0 < scale i) →
          repaired =ᵐ[_root_.GD.N0232.N0719.d009176 k sizes location scale]
            _root_.GD.N0232.N0719.N0849.d011768 k sizes p) ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229)
          (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) ↦
          g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired := by
  let d := _root_.GD.N0232.N0719.N0849.d011768 k sizes p
  have hdMeas : Measurable d :=
    _root_.GD.N0232.N0719.N0849.d011769 k sizes p
  have hfixed : ∀ g : _root_.GD.N0230.N0655.d000349,
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 g.2 d =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes] d := by
    intro g
    exact _root_.GD.N0232.N0719.N0849.d011777
      k sizes hk hsizes stage p hunique g.1 g.2 g.2.2
  have hcov : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega ↦ d (g • omega)) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
        fun omega ↦ g • d omega :=
    _root_.GD.N0232.N0719.N0849.d011779 k sizes d hfixed
  simpa [d] using
    (_root_.GD.N0232.N0719.N0946.d009262
      (k := k) (sizes := sizes)
      (lt_of_lt_of_le (by norm_num) hk)
      (fun i ↦ lt_of_lt_of_le (by norm_num) (hsizes i))
      d hdMeas hcov)








def d011781
    (k : ℕ) (sizes : Fin k → ℕ)
    (d : _root_.GD.N0232.N0719.N0815.d010956 k sizes) : Prop :=
  ∀ e : _root_.GD.N0232.N0719.N0815.d010956 k sizes,
    (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0815.d010957 k sizes theta e ≤
        _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d) →
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      e.1 =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] d.1


theorem d011782
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {d e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hde : d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] e) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e := by
  unfold _root_.GD.N0232.N0719.N0859.d010840
  apply lintegral_congr_ae
  filter_upwards [hde] with omega homega
  rw [homega]



theorem d011783
    (k : ℕ) (sizes : Fin k → ℕ)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hdeq : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] _root_.GD.N0232.N0719.N0849.d011768 k sizes p) :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p := by
  intro theta
  calc
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N0849.d011768 k sizes p) :=
      _root_.GD.N0232.N0719.N0849.d011782 k sizes theta (hdeq theta)
    _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
          (show _root_.GD.N0232.N0719.N0816.d010975 k sizes from
            MemLp.toLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes p)
              (_root_.GD.N0232.N0719.N0849.d011771 k sizes p)) :=
      _root_.GD.N0232.N0719.N0849.d011773 k sizes theta
        (_root_.GD.N0232.N0719.N0849.d011768 k sizes p)
        (_root_.GD.N0232.N0719.N0849.d011771 k sizes p)
    _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p := by
      exact congrArg (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta)
        (_root_.GD.N0232.N0719.N0849.d011772 k sizes p)



theorem d011784
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hpCap : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p)
    (d : _root_.GD.N0232.N0719.N0815.d010956 k sizes)
    (hdeq : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      d.1 =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] _root_.GD.N0232.N0719.N0849.d011768 k sizes p) :
    _root_.GD.N0232.N0719.N0849.d011781 k sizes d := by
  intro e hdom
  have hdFeasible : _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes d.1 := by
    intro theta
    rw [_root_.GD.N0232.N0719.N0849.d011783
      k sizes p d.1 hdeq theta]
    exact hpCap theta
  have heFeasible : _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes e.1 := by
    intro theta
    exact (hdom theta).trans (hdFeasible theta)
  have heLp : MemLp e.1 2 (_root_.GD.N0232.N0719.d009182 k sizes) :=
    _root_.GD.N0232.N0719.N0849.d011774
      k sizes hk hsizes e.1 e.2 heFeasible
  let q : _root_.GD.N0232.N0719.N0816.d010975 k sizes := MemLp.toLp e.1 heLp
  have hqdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) q p := by
    intro theta
    change _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (show _root_.GD.N0232.N0719.N0816.d010975 k sizes from MemLp.toLp e.1 heLp) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p
    calc
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
          (show _root_.GD.N0232.N0719.N0816.d010975 k sizes from MemLp.toLp e.1 heLp) =
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e.1 :=
        (_root_.GD.N0232.N0719.N0849.d011773 k sizes theta e.1 heLp).symm
      _ ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d.1 := hdom theta
      _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p :=
        _root_.GD.N0232.N0719.N0849.d011783
          k sizes p d.1 hdeq theta
  have hqp : q = p := hterminal q hqdom
  have heRef : e.1 =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
      _root_.GD.N0232.N0719.N0849.d011768 k sizes p := by
    have hcoe :
        (fun omega ↦ q omega) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes] e.1 := by
      simpa [q] using heLp.coeFn_toLp
    have hqpCoe :
        (fun omega ↦ q omega) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
          (fun omega ↦ p omega) := by
      rw [hqp]
    exact hcoe.symm.trans
      (hqpCoe.trans
        (_root_.GD.N0232.N0719.N0849.d011770 k sizes p).symm)
  have hedRef : e.1 =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes] d.1 :=
    heRef.trans (hdeq (_root_.GD.N0232.N0719.N0859.d010810 k)).symm
  intro theta
  exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le hedRef




theorem d011785
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hpCap : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hdeq : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] _root_.GD.N0232.N0719.N0849.d011768 k sizes p) :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  intro theta
  calc
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p :=
      _root_.GD.N0232.N0719.N0849.d011783
        k sizes p d hdeq theta
    _ ≤ _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta := hpCap theta
    _ < _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) :=
      _root_.GD.N0232.N0719.N0858.d010856 k sizes hk hsizes theta
    _ = _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes) :=
      (_root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes theta).symm














theorem d011786
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (p : _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (hunique :
      _root_.GD.N0230.N0569.d001685
        (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes))
        ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p))
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) p) :
    ∃ d : _root_.GD.N0232.N0719.N0815.d010956 k sizes,
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229)
          (omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes) ↦
          g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) d.1 ∧
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        d.1 =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] _root_.GD.N0232.N0719.N0849.d011768 k sizes p) ∧
      (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
      _root_.GD.N0232.N0719.N0849.d011781 k sizes d := by
  obtain ⟨repaired, hrepairedMeas, hrepairedAll, hrepairedEquiv⟩ :=
    _root_.GD.N0232.N0719.N0849.d011780
      k sizes hk hsizes stage p hunique
  let d : _root_.GD.N0232.N0719.N0815.d010956 k sizes := ⟨repaired, hrepairedMeas⟩
  have hdeq : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      d.1 =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] _root_.GD.N0232.N0719.N0849.d011768 k sizes p := by
    intro theta
    exact hrepairedAll theta.location theta.scale theta.scale_pos
  have hpWeakCap :
      (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)) p ∈
        _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes := by
    have htower := _root_.GD.N0230.N0566.d000756
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
      (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
    rw [← htower.1]
    exact hunique.1 0
  have hpCap : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    have h := _root_.GD.N0232.N0719.N0818.d011652
      k sizes hk hsizes hpWeakCap
    simpa using h
  refine ⟨d, hrepairedEquiv, hdeq, ?_, ?_⟩
  · exact _root_.GD.N0232.N0719.N0849.d011785
      k sizes hk hsizes p hpCap d.1 hdeq
  · exact _root_.GD.N0232.N0719.N0849.d011784
      k sizes hk hsizes p hpCap hterminal d hdeq

end

end N0849
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0849.d011777
#print axioms _root_.GD.N0232.N0719.N0849.d011786
