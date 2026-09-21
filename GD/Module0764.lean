import GD.Module0763
import Mathlib.MeasureTheory.Function.LpSpace.Basic












open MeasureTheory
open scoped ENNReal

namespace GD.N0232.N0719.N0871

noncomputable section

open _root_.GD.N0232.N0719.N0851
open _root_.GD.N0232.N0719.N1013
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608



def d011549 {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010809 k where
  location := theta.location
  scale := theta.scale ∘ sigma
  scale_pos := fun i => theta.scale_pos (sigma i)



theorem d011550
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k)) :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma)) := by
  refine ⟨(_root_.GD.N0232.N0719.N0851.d010783 sizes sigma).measurable, ?_⟩
  unfold _root_.GD.N0232.N0719.N0859.d010813
    _root_.GD.N0232.N0719.d009182
  have hconst : (fun _ : Fin k => (1 : ℝ)) ∘ sigma = fun _ => 1 := by
    funext i
    rfl
  simpa only [hconst] using
    (_root_.GD.N0232.N0719.N0851.d010786
      sizes sigma 0 (fun _ => 1))


theorem d011551
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
      (_root_.GD.N0232.N0719.N0859.d010812 k (sizes ∘ sigma)
        (_root_.GD.N0232.N0719.N0871.d011549 sigma theta)) := by
  refine ⟨(_root_.GD.N0232.N0719.N0851.d010783 sizes sigma).measurable, ?_⟩
  exact _root_.GD.N0232.N0719.N0851.d010786
    sizes sigma theta.location theta.scale



def d011552
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k)) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma)) →+
      _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  Lp.compMeasurePreserving
    (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)

theorem d011553
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma))) :
    ‖_root_.GD.N0232.N0719.N0871.d011552 sizes sigma d‖ = ‖d‖ := by
  exact Lp.norm_compMeasurePreserving d
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)


theorem d011554
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma))) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
        (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma d) =
      _root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma)
        (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) d := by
  have hcoeRef := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)
  have hcoe :
      (fun omega => _root_.GD.N0232.N0719.N0871.d011552 sizes sigma d omega) =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
        (fun omega => d (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega)) :=
    (_root_.GD.N0232.N0719.N0859.d010814
      k sizes theta).ae_le hcoeRef
  unfold _root_.GD.N0232.N0719.N0859.d010821 _root_.GD.N0230.N0602.d000117
  calc
    (∫⁻ omega,
        ENNReal.ofReal
          ((_root_.GD.N0232.N0719.N0871.d011552 sizes sigma d omega - theta.location) ^ 2)
        ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) =
        ∫⁻ omega,
          ENNReal.ofReal
            ((d (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega) -
              theta.location) ^ 2)
          ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta := by
      apply lintegral_congr_ae
      filter_upwards [hcoe] with omega homega
      rw [homega]
    _ =
        ∫⁻ omega,
          ENNReal.ofReal
            ((d omega - theta.location) ^ 2)
          ∂_root_.GD.N0232.N0719.N0859.d010812 k (sizes ∘ sigma)
            (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) := by
      exact (_root_.GD.N0232.N0719.N0871.d011551
        sizes sigma theta).lintegral_comp_emb
          (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma).measurableEmbedding
          (fun omega =>
            ENNReal.ofReal ((d omega - theta.location) ^ 2))



def d011555
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k)) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) →+
      _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma)) :=
  Lp.compMeasurePreserving
    (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma).symm
    (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
      (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma))

theorem d011556
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ‖_root_.GD.N0232.N0719.N0871.d011555 sizes sigma d‖ = ‖d‖ := by
  exact Lp.norm_compMeasurePreserving d
    (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
      (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma))

theorem d011557
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0871.d011552 sizes sigma (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma d) = d := by
  apply Lp.ext
  have hpull := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma d)
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)
  have hpush := Lp.coeFn_compMeasurePreserving d
    (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
      (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma))
  have hpushComp :=
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma).quasiMeasurePreserving.ae_eq_comp
      hpush
  filter_upwards [hpull, hpushComp] with omega hpullOmega hpushOmega
  calc
    _root_.GD.N0232.N0719.N0871.d011552 sizes sigma (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma d) omega =
        _root_.GD.N0232.N0719.N0871.d011555 sizes sigma d
          (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega) := by
      simpa only [_root_.GD.N0232.N0719.N0871.d011552, Function.comp_apply] using hpullOmega
    _ = d
          ((_root_.GD.N0232.N0719.N0851.d010783 sizes sigma).symm
            (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega)) := by
      simpa only [_root_.GD.N0232.N0719.N0871.d011555, Function.comp_apply] using hpushOmega
    _ = d omega := by simp

theorem d011558
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma))) :
    _root_.GD.N0232.N0719.N0871.d011555 sizes sigma (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma d) = d := by
  apply Lp.ext
  have hpush := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma d)
    (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
      (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma))
  have hpull := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)
  have hpullComp :=
    (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
      (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)).quasiMeasurePreserving.ae_eq_comp
      hpull
  filter_upwards [hpush, hpullComp] with omega hpushOmega hpullOmega
  calc
    _root_.GD.N0232.N0719.N0871.d011555 sizes sigma (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma d) omega =
        _root_.GD.N0232.N0719.N0871.d011552 sizes sigma d
          ((_root_.GD.N0232.N0719.N0851.d010783 sizes sigma).symm omega) := by
      simpa only [_root_.GD.N0232.N0719.N0871.d011555, Function.comp_apply] using hpushOmega
    _ = d
          (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma
            ((_root_.GD.N0232.N0719.N0851.d010783 sizes sigma).symm omega)) := by
      simpa only [_root_.GD.N0232.N0719.N0871.d011552, Function.comp_apply] using hpullOmega
    _ = d omega := by simp


theorem d011559
    {k : ℕ} (sizes : Fin k → ℕ)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0871.d011552 sizes (Equiv.refl (Fin k)) d = d := by
  apply Lp.ext
  have hpull := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0719.N0871.d011550 sizes
      (Equiv.refl (Fin k)))
  filter_upwards [hpull] with omega homega
  calc
    _root_.GD.N0232.N0719.N0871.d011552 sizes (Equiv.refl (Fin k)) d omega =
        d (_root_.GD.N0232.N0719.N0851.d010783 sizes (Equiv.refl (Fin k)) omega) := by
      exact homega
    _ = d omega := by
      congr 1




theorem d011560
    {k : ℕ} (sizes : Fin k → ℕ)
    (sigma tau : Equiv.Perm (Fin k))
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k
        ((sizes ∘ sigma) ∘ tau))) :
    _root_.GD.N0232.N0719.N0871.d011552 sizes sigma
        (_root_.GD.N0232.N0719.N0871.d011552 (sizes ∘ sigma) tau d) =
      _root_.GD.N0232.N0719.N0871.d011552 sizes (tau.trans sigma) d := by
  apply Lp.ext
  have houter := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0719.N0871.d011552 (sizes ∘ sigma) tau d)
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)
  have hinner := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0719.N0871.d011550 (sizes ∘ sigma) tau)
  have hinnerComp :=
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma).quasiMeasurePreserving.ae_eq_comp
      hinner
  have hcombined := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0719.N0871.d011550 sizes
      (tau.trans sigma))
  filter_upwards [houter, hinnerComp, hcombined] with
    omega houterOmega hinnerOmega hcombinedOmega
  calc
    _root_.GD.N0232.N0719.N0871.d011552 sizes sigma
        (_root_.GD.N0232.N0719.N0871.d011552 (sizes ∘ sigma) tau d) omega =
        _root_.GD.N0232.N0719.N0871.d011552 (sizes ∘ sigma) tau d
          (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega) := by
      simpa only [_root_.GD.N0232.N0719.N0871.d011552, Function.comp_apply] using houterOmega
    _ = d
        (_root_.GD.N0232.N0719.N0851.d010783 (sizes ∘ sigma) tau
          (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega)) := by
      simpa only [_root_.GD.N0232.N0719.N0871.d011552, Function.comp_apply] using hinnerOmega
    _ = d (_root_.GD.N0232.N0719.N0851.d010783 sizes (tau.trans sigma) omega) := by
      rfl
    _ = _root_.GD.N0232.N0719.N0871.d011552 sizes (tau.trans sigma) d omega := by
      exact hcombinedOmega.symm





def d011561
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k)) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma))
      ≃ₗᵢ[ℝ]
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) where
  toLinearEquiv :=
    { toFun := _root_.GD.N0232.N0719.N0871.d011552 sizes sigma
      invFun := _root_.GD.N0232.N0719.N0871.d011555 sizes sigma
      left_inv := _root_.GD.N0232.N0719.N0871.d011558 sizes sigma
      right_inv := _root_.GD.N0232.N0719.N0871.d011557 sizes sigma
      map_add' := (Lp.compMeasurePreservingₗ ℝ
        (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
        (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)).map_add
      map_smul' := (Lp.compMeasurePreservingₗ ℝ
        (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma)
        (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)).map_smul }
  norm_map' := _root_.GD.N0232.N0719.N0871.d011553 sizes sigma

@[simp]
theorem d011562
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma))) :
    _root_.GD.N0232.N0719.N0871.d011561 sizes sigma d = _root_.GD.N0232.N0719.N0871.d011552 sizes sigma d :=
  rfl

@[simp]
theorem d011563
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    (_root_.GD.N0232.N0719.N0871.d011561 sizes sigma).symm d =
      _root_.GD.N0232.N0719.N0871.d011555 sizes sigma d :=
  rfl



theorem d011564
    {k : ℕ} (sizes : Fin k → ℕ)
    (sigma tau : Equiv.Perm (Fin k))
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k
        ((sizes ∘ sigma) ∘ tau))) :
    _root_.GD.N0232.N0719.N0871.d011561 sizes sigma
        (_root_.GD.N0232.N0719.N0871.d011561 (sizes ∘ sigma) tau d) =
      _root_.GD.N0232.N0719.N0871.d011561 sizes (tau.trans sigma) d := by
  exact _root_.GD.N0232.N0719.N0871.d011560 sizes sigma tau d



theorem d011565
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma)
        (_root_.GD.N0232.N0719.N0871.d011549 sigma theta)
        (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma d) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d := by
  symm
  calc
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d =
        _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
          (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma
            (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma d)) := by
      rw [_root_.GD.N0232.N0719.N0871.d011557]
    _ = _root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma)
          (_root_.GD.N0232.N0719.N0871.d011549 sigma theta)
          (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma d) :=
      _root_.GD.N0232.N0719.N0871.d011554 sizes sigma theta
        (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma d)



theorem d011566
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0871.d011552 sizes sigma
        (_root_.GD.N0232.N0719.N1013.d011526 k (sizes ∘ sigma) hk
          (fun i => hsizes (sigma i))) =
      _root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes := by
  unfold _root_.GD.N0232.N0719.N0871.d011552 _root_.GD.N0232.N0719.N1013.d011526
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  filter_upwards with omega
  exact _root_.GD.N0232.N0719.N1013.d011522 k sizes hk sigma omega


def d011567 {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010809 k where
  location := theta.location
  scale := theta.scale ∘ sigma.symm
  scale_pos := fun i => theta.scale_pos (sigma.symm i)

@[simp]
theorem d011568
    {k : ℕ} (sigma : Equiv.Perm (Fin k))
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0871.d011549 sigma (_root_.GD.N0232.N0719.N0871.d011567 sigma theta) = theta := by
  rcases theta with ⟨location, scale, hscale⟩
  unfold _root_.GD.N0232.N0719.N0871.d011549 _root_.GD.N0232.N0719.N0871.d011567
  congr 1
  funext i
  simp [Function.comp_apply]



theorem d011569
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k (sizes ∘ sigma))) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma))
        (_root_.GD.N0232.N0719.N1013.d011526 k (sizes ∘ sigma) hk
          (fun i => hsizes (sigma i))) d ↔
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
        (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma d) := by
  constructor
  · intro hd theta
    rw [_root_.GD.N0232.N0719.N0871.d011554]
    calc
      _root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma)
          (_root_.GD.N0232.N0719.N0871.d011549 sigma theta) d ≤
          _root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma)
            (_root_.GD.N0232.N0719.N0871.d011549 sigma theta)
            (_root_.GD.N0232.N0719.N1013.d011526 k (sizes ∘ sigma) hk
              (fun i => hsizes (sigma i))) :=
        hd (_root_.GD.N0232.N0719.N0871.d011549 sigma theta)
      _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
            (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma
              (_root_.GD.N0232.N0719.N1013.d011526 k (sizes ∘ sigma) hk
                (fun i => hsizes (sigma i)))) := by
        symm
        exact _root_.GD.N0232.N0719.N0871.d011554 sizes sigma theta _
      _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
            (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) := by
        rw [_root_.GD.N0232.N0719.N0871.d011566]
  · intro hd thetaRel
    let theta := _root_.GD.N0232.N0719.N0871.d011567 sigma thetaRel
    have htheta : _root_.GD.N0232.N0719.N0871.d011549 sigma theta = thetaRel := by
      exact _root_.GD.N0232.N0719.N0871.d011568 sigma thetaRel
    rw [← htheta]
    rw [← _root_.GD.N0232.N0719.N0871.d011554]
    calc
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
          (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma d) ≤
          _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
            (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) := hd theta
      _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes theta
            (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma
              (_root_.GD.N0232.N0719.N1013.d011526 k (sizes ∘ sigma) hk
                (fun i => hsizes (sigma i)))) := by
        rw [_root_.GD.N0232.N0719.N0871.d011566]
      _ = _root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma)
            (_root_.GD.N0232.N0719.N0871.d011549 sigma theta)
            (_root_.GD.N0232.N0719.N1013.d011526 k (sizes ∘ sigma) hk
              (fun i => hsizes (sigma i))) :=
        _root_.GD.N0232.N0719.N0871.d011554 sizes sigma theta _





theorem d011570
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0871.d011552 sizes sigma
        (_root_.GD.N0232.N0719.N1013.d011532 k (sizes ∘ sigma) hk
          (fun i => hsizes (sigma i))) =
      _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes := by
  let starRel := _root_.GD.N0232.N0719.N1013.d011532 k (sizes ∘ sigma) hk
    (fun i => hsizes (sigma i))
  let star := _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes
  have hstarRel :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma))
        (_root_.GD.N0232.N0719.N1013.d011526 k (sizes ∘ sigma) hk
          (fun i => hsizes (sigma i))) starRel :=
    (_root_.GD.N0232.N0719.N1013.d011533 k (sizes ∘ sigma) hk
      (fun i => hsizes (sigma i))).1
  have hpullFeasible :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
        (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes)
        (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma starRel) :=
    (_root_.GD.N0232.N0719.N0871.d011569 sizes sigma hk hsizes starRel).1 hstarRel
  have hstar :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
        (_root_.GD.N0232.N0719.N1013.d011526 k sizes hk hsizes) star :=
    (_root_.GD.N0232.N0719.N1013.d011533 k sizes hk hsizes).1
  have hpushFeasible :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k (sizes ∘ sigma))
        (_root_.GD.N0232.N0719.N1013.d011526 k (sizes ∘ sigma) hk
          (fun i => hsizes (sigma i)))
        (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma star) := by
    apply (_root_.GD.N0232.N0719.N0871.d011569 sizes sigma hk hsizes _).2
    simpa [_root_.GD.N0232.N0719.N0871.d011557] using hstar
  have htaxRel := _root_.GD.N0232.N0719.N1013.d011534
    k (sizes ∘ sigma) hk (fun i => hsizes (sigma i))
    (_root_.GD.N0232.N0719.N0871.d011555 sizes sigma star) hpushFeasible
  have hnormRel_le : ‖starRel‖ ^ 2 ≤ ‖star‖ ^ 2 := by
    rw [_root_.GD.N0232.N0719.N0871.d011556] at htaxRel
    nlinarith [sq_nonneg
      ‖_root_.GD.N0232.N0719.N0871.d011555 sizes sigma star - starRel‖]
  have htax := _root_.GD.N0232.N0719.N1013.d011534
    k sizes hk hsizes (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma starRel)
    hpullFeasible
  have hdist_nonpos :
      ‖_root_.GD.N0232.N0719.N0871.d011552 sizes sigma starRel - star‖ ^ 2 ≤ 0 := by
    rw [_root_.GD.N0232.N0719.N0871.d011553] at htax
    exact htax.trans (sub_nonpos.mpr hnormRel_le)
  have hnorm_zero :
      ‖_root_.GD.N0232.N0719.N0871.d011552 sizes sigma starRel - star‖ = 0 := by
    nlinarith [norm_nonneg
      (_root_.GD.N0232.N0719.N0871.d011552 sizes sigma starRel - star)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)




theorem d011571
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0871.d011561 sizes sigma
        (_root_.GD.N0232.N0719.N1013.d011532 k (sizes ∘ sigma) hk
          (fun i => hsizes (sigma i))) =
      _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes := by
  exact _root_.GD.N0232.N0719.N0871.d011570 sizes sigma hk hsizes



theorem d011572
    {k : ℕ} (sizes : Fin k → ℕ)
    (sigma tau : Equiv.Perm (Fin k))
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0871.d011561 sizes sigma
        (_root_.GD.N0232.N0719.N0871.d011561 (sizes ∘ sigma) tau
          (_root_.GD.N0232.N0719.N1013.d011532 k ((sizes ∘ sigma) ∘ tau) hk
            (fun i => hsizes (sigma (tau i))))) =
      _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes := by
  rw [_root_.GD.N0232.N0719.N0871.d011571
    (sizes ∘ sigma) tau hk (fun i => hsizes (sigma i))]
  exact _root_.GD.N0232.N0719.N0871.d011571 sizes sigma hk hsizes




theorem d011573
    {k n : ℕ} (sigma : Equiv.Perm (Fin k))
    (hk : 3 ≤ k) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0719.N0871.d011561 (fun _ : Fin k => n) sigma
        (_root_.GD.N0232.N0719.N1013.d011532 k (fun _ : Fin k => n) hk (fun _ => hn)) =
      _root_.GD.N0232.N0719.N1013.d011532 k (fun _ : Fin k => n) hk (fun _ => hn) := by
  exact _root_.GD.N0232.N0719.N0871.d011571
    (fun _ : Fin k => n) sigma hk (fun _ => hn)








theorem d011574
    {k : ℕ} (sizes : Fin k → ℕ) (sigma : Equiv.Perm (Fin k))
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (fun omega : _root_.GD.N0232.N0719.N0859.d010811 k sizes =>
      _root_.GD.N0232.N0719.N1013.d011537 k (sizes ∘ sigma) hk
        (fun i => hsizes (sigma i))
        (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega)) =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
      _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes := by
  let starRel := _root_.GD.N0232.N0719.N1013.d011532 k (sizes ∘ sigma) hk
    (fun i => hsizes (sigma i))
  have hrel := _root_.GD.N0232.N0719.N1013.d011539
    k (sizes ∘ sigma) hk (fun i => hsizes (sigma i))
    (_root_.GD.N0232.N0719.N0871.d011549 sigma theta)
  have hrelComp :=
    (_root_.GD.N0232.N0719.N0871.d011551 sizes sigma theta).quasiMeasurePreserving.ae_eq_comp
      hrel
  have hsource := _root_.GD.N0232.N0719.N1013.d011539
    k sizes hk hsizes theta
  have hcoeRef := Lp.coeFn_compMeasurePreserving starRel
    (_root_.GD.N0232.N0719.N0871.d011550 sizes sigma)
  have hcoe :=
    (_root_.GD.N0232.N0719.N0859.d010814
      k sizes theta).ae_le hcoeRef
  have hnatural := _root_.GD.N0232.N0719.N0871.d011570
    sizes sigma hk hsizes
  filter_upwards [hrelComp, hsource, hcoe] with omega
    hrelOmega hsourceOmega hcoeOmega
  calc
    _root_.GD.N0232.N0719.N1013.d011537 k (sizes ∘ sigma) hk
          (fun i => hsizes (sigma i))
          (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega) =
        starRel (_root_.GD.N0232.N0719.N0851.d010783 sizes sigma omega) := hrelOmega
    _ = _root_.GD.N0232.N0719.N0871.d011552 sizes sigma starRel omega := hcoeOmega.symm
    _ = _root_.GD.N0232.N0719.N1013.d011532 k sizes hk hsizes omega := by rw [hnatural]
    _ = _root_.GD.N0232.N0719.N1013.d011537 k sizes hk hsizes omega := hsourceOmega.symm


end

end GD.N0232.N0719.N0871
