import GD.Module0640

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0954

noncomputable section




def d009479 {n : ℕ} (shape : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  ∑ i, shape i



def d009480 {n : ℕ}
    (shape rate : _root_.GD.N0232.N0719.N0953.d003306 n)
    (t : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  ∏ i, gammaPDFReal (shape i) (rate i) (t i)


def d009481 {n : ℕ}
    (shape rate : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  ∏ i, (rate i) ^ (shape i) / Real.Gamma (shape i)



def d009482 {n : ℕ}
    (shape : _root_.GD.N0232.N0719.N0953.d003306 n)
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  ∏ i,
    (_root_.GD.N0232.N0719.N0953.d003334 x i) ^ (-(shape i + 1))


def d009483 {n : ℕ}
    (shape rate : _root_.GD.N0232.N0719.N0953.d003306 n)
    (x : _root_.GD.N0232.N0719.N0953.d003306 n) : ℝ :=
  _root_.GD.N0232.N0719.N0954.d009481 shape rate *
    (_root_.GD.N0232.N0719.N0953.d003308 x) ^ (_root_.GD.N0232.N0719.N0954.d009479 shape - 1) *
    Real.exp (-(_root_.GD.N0232.N0719.N0953.d003308 x * _root_.GD.N0232.N0719.N0953.d003337 rate x)) *
    _root_.GD.N0232.N0719.N0954.d009482 shape x



theorem d009484
    {a ω p : ℝ} (hω : 0 < ω) (hp : 0 < p) :
    (ω / p) ^ (a - 1) * (ω / p ^ 2) =
      ω ^ a * p ^ (-(a + 1)) := by
  rw [Real.div_rpow hω.le hp.le,
    Real.rpow_sub hω a 1, Real.rpow_one,
    Real.rpow_sub hp a 1, Real.rpow_one,
    Real.rpow_neg hp.le (a + 1),
    Real.rpow_add hp a 1, Real.rpow_one]
  field_simp [ne_of_gt hω, ne_of_gt hp,
    ne_of_gt (Real.rpow_pos_of_pos hω a),
    ne_of_gt (Real.rpow_pos_of_pos hp a)]



theorem d009485
    {n : ℕ} {x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    ((∏ i, (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)) /
        (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2) =
      (∏ i : _root_.GD.N0232.N0719.N0953.d003305 n,
          _root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003334 x i) ^ 2) /
        _root_.GD.N0232.N0719.N0953.d003308 x := by
  rw [Fintype.prod_sum_type]
  simp only [_root_.GD.N0232.N0719.N0953.d003334]
  rw [Fin.prod_univ_one]
  have hω : _root_.GD.N0232.N0719.N0953.d003308 x ≠ 0 := ne_of_gt hx.1
  field_simp [hω, ne_of_gt hx.2.2] <;> ring



theorem d009486
    {n : ℕ} (shape : _root_.GD.N0232.N0719.N0953.d003306 n)
    {x : _root_.GD.N0232.N0719.N0953.d003306 n} (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    (∏ i : _root_.GD.N0232.N0719.N0953.d003305 n,
        (_root_.GD.N0232.N0719.N0953.d003315 x i) ^ (shape i - 1)) *
        ((∏ i, (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)) /
          (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2) =
      (_root_.GD.N0232.N0719.N0953.d003308 x) ^ (_root_.GD.N0232.N0719.N0954.d009479 shape - 1) *
        _root_.GD.N0232.N0719.N0954.d009482 shape x := by
  have hω : 0 < _root_.GD.N0232.N0719.N0953.d003308 x := hx.1
  have hp :
      ∀ i : _root_.GD.N0232.N0719.N0953.d003305 n, 0 < _root_.GD.N0232.N0719.N0953.d003334 x i :=
    fun i => _root_.GD.N0232.N0719.N0953.d003336 hx i
  rw [_root_.GD.N0232.N0719.N0954.d009485 hx]
  rw [← mul_div_assoc]
  rw [← Finset.prod_mul_distrib]
  have hcoordinate :
      ∀ i : _root_.GD.N0232.N0719.N0953.d003305 n,
        _root_.GD.N0232.N0719.N0953.d003315 x i ^ (shape i - 1) *
            (_root_.GD.N0232.N0719.N0953.d003308 x / _root_.GD.N0232.N0719.N0953.d003334 x i ^ 2) =
          _root_.GD.N0232.N0719.N0953.d003308 x ^ shape i *
            _root_.GD.N0232.N0719.N0953.d003334 x i ^ (-(shape i + 1)) := by
    intro i
    cases i with
    | inl i =>
        simpa [_root_.GD.N0232.N0719.N0953.d003315, _root_.GD.N0232.N0719.N0953.d003334] using
          _root_.GD.N0232.N0719.N0954.d009484
            (a := shape (Sum.inl i)) hω (hp (Sum.inl i))
    | inr i =>
        fin_cases i
        simpa [_root_.GD.N0232.N0719.N0953.d003315, _root_.GD.N0232.N0719.N0953.d003334] using
          _root_.GD.N0232.N0719.N0954.d009484
            (a := shape (Sum.inr 0)) hω (hp (Sum.inr 0))
  simp_rw [hcoordinate]
  rw [Finset.prod_mul_distrib]
  have hrpowSum :
      ∏ i : _root_.GD.N0232.N0719.N0953.d003305 n, _root_.GD.N0232.N0719.N0953.d003308 x ^ shape i =
        _root_.GD.N0232.N0719.N0953.d003308 x ^ _root_.GD.N0232.N0719.N0954.d009479 shape := by
    symm
    simpa [_root_.GD.N0232.N0719.N0954.d009479] using
      (Real.rpow_sum_of_pos hω shape
        (Finset.univ : Finset (_root_.GD.N0232.N0719.N0953.d003305 n)))
  rw [hrpowSum]
  unfold _root_.GD.N0232.N0719.N0954.d009482
  rw [Real.rpow_sub hω (_root_.GD.N0232.N0719.N0954.d009479 shape) 1, Real.rpow_one]
  field_simp [ne_of_gt hω,
    ne_of_gt (Real.rpow_pos_of_pos hω (_root_.GD.N0232.N0719.N0954.d009479 shape))]


theorem d009487
    {n : ℕ} (rate : _root_.GD.N0232.N0719.N0953.d003306 n)
    {x : _root_.GD.N0232.N0719.N0953.d003306 n} :
    (∏ i : _root_.GD.N0232.N0719.N0953.d003305 n,
        Real.exp (-(rate i * _root_.GD.N0232.N0719.N0953.d003315 x i))) =
      Real.exp (-(_root_.GD.N0232.N0719.N0953.d003308 x * _root_.GD.N0232.N0719.N0953.d003337 rate x)) := by
  rw [← Real.exp_sum]
  congr 1
  have hmass := _root_.GD.N0232.N0719.N0953.d003339 rate x
  calc
    (∑ i : _root_.GD.N0232.N0719.N0953.d003305 n,
        -(rate i * _root_.GD.N0232.N0719.N0953.d003315 x i)) =
        -((∑ i, rate (Sum.inl i) * _root_.GD.N0232.N0719.N0953.d003315 x (Sum.inl i)) +
          rate (Sum.inr 0) * _root_.GD.N0232.N0719.N0953.d003315 x (Sum.inr 0)) := by
            rw [Fintype.sum_sum_type]
            simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
            rw [Finset.sum_neg_distrib]
            ring
    _ = -(_root_.GD.N0232.N0719.N0953.d003308 x * _root_.GD.N0232.N0719.N0953.d003337 rate x) := by
      rw [hmass]



theorem d009488
    {n : ℕ} {shape rate x : _root_.GD.N0232.N0719.N0953.d003306 n}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 n) :
    _root_.GD.N0232.N0719.N0954.d009480 shape rate (_root_.GD.N0232.N0719.N0953.d003315 x) *
        ((∏ i, (_root_.GD.N0232.N0719.N0953.d003308 x / (_root_.GD.N0232.N0719.N0953.d003307 x i) ^ 2)) /
          (_root_.GD.N0232.N0719.N0953.d003309 x) ^ 2) =
      _root_.GD.N0232.N0719.N0954.d009483 shape rate x := by
  have hsource := _root_.GD.N0232.N0719.N0953.d003322 hx
  unfold _root_.GD.N0232.N0719.N0954.d009480 _root_.GD.N0232.N0719.N0954.d009483
    _root_.GD.N0232.N0719.N0954.d009481
  have hpdf :
      ∀ i : _root_.GD.N0232.N0719.N0953.d003305 n,
        gammaPDFReal (shape i) (rate i) (_root_.GD.N0232.N0719.N0953.d003315 x i) =
          ((rate i) ^ (shape i) / Real.Gamma (shape i)) *
            (_root_.GD.N0232.N0719.N0953.d003315 x i) ^ (shape i - 1) *
            Real.exp (-(rate i * _root_.GD.N0232.N0719.N0953.d003315 x i)) := by
    intro i
    simp only [gammaPDFReal, if_pos (hsource i).le]
  simp_rw [hpdf]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  calc
    ((∏ i, rate i ^ shape i / Real.Gamma (shape i)) *
          (∏ i, _root_.GD.N0232.N0719.N0953.d003315 x i ^ (shape i - 1)) *
          (∏ i, Real.exp (-(rate i * _root_.GD.N0232.N0719.N0953.d003315 x i)))) *
        ((∏ i, _root_.GD.N0232.N0719.N0953.d003308 x / _root_.GD.N0232.N0719.N0953.d003307 x i ^ 2) /
          _root_.GD.N0232.N0719.N0953.d003309 x ^ 2) =
        (∏ i, rate i ^ shape i / Real.Gamma (shape i)) *
          ((∏ i, _root_.GD.N0232.N0719.N0953.d003315 x i ^ (shape i - 1)) *
            ((∏ i, _root_.GD.N0232.N0719.N0953.d003308 x / _root_.GD.N0232.N0719.N0953.d003307 x i ^ 2) /
              _root_.GD.N0232.N0719.N0953.d003309 x ^ 2)) *
          (∏ i, Real.exp (-(rate i * _root_.GD.N0232.N0719.N0953.d003315 x i))) := by
            ring
    _ =
        (∏ i, rate i ^ shape i / Real.Gamma (shape i)) *
          (_root_.GD.N0232.N0719.N0953.d003308 x ^ (_root_.GD.N0232.N0719.N0954.d009479 shape - 1) *
            _root_.GD.N0232.N0719.N0954.d009482 shape x) *
          Real.exp (-(_root_.GD.N0232.N0719.N0953.d003308 x * _root_.GD.N0232.N0719.N0953.d003337 rate x)) := by
            rw [_root_.GD.N0232.N0719.N0954.d009486 shape hx,
              _root_.GD.N0232.N0719.N0954.d009487 rate]
    _ = _ := by
      ring








theorem d009489
    {n : ℕ} (shape rate : _root_.GD.N0232.N0719.N0953.d003306 n)
    (G : _root_.GD.N0232.N0719.N0953.d003306 n → ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i) :
    (∫ t in _root_.GD.N0232.N0719.N0953.d003310 n,
        G t * _root_.GD.N0232.N0719.N0954.d009480 shape rate t) =
      ∫ x in _root_.GD.N0232.N0719.N0953.d003311 n,
        G (_root_.GD.N0232.N0719.N0953.d003315 x) *
          _root_.GD.N0232.N0719.N0954.d009483 shape rate x := by
  rw [_root_.GD.N0232.N0719.N0953.d003361]
  apply setIntegral_congr_fun (_root_.GD.N0232.N0719.N0953.d003333 n)
  intro x hx
  simp only
  rw [← _root_.GD.N0232.N0719.N0954.d009488
      hshape hrate hx]
  ring

theorem d009490
    {k : ℕ} (hk : 0 < k)
    (shape rate : Fin k → ℝ)
    (u : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)) :
    _root_.GD.N0232.N0719.N0954.d009343 shape rate
        (_root_.GD.N0232.N0719.N0954.d009345 k hk u) =
      _root_.GD.N0232.N0719.N0954.d009480
        (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
        (_root_.GD.N0232.N0719.N0954.d009350 hk rate) u := by
  unfold _root_.GD.N0232.N0719.N0954.d009343 _root_.GD.N0232.N0719.N0954.d009480
    _root_.GD.N0232.N0719.N0954.d009350
  symm
  apply Fintype.prod_equiv (_root_.GD.N0232.N0719.N0954.d009344 k hk)
  intro i
  simp [_root_.GD.N0232.N0719.N0954.d009345,
    MeasurableEquiv.piCongrLeft_apply_apply]











theorem d009491
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (G : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) → ℝ) :
    (∫ t, G (_root_.GD.N0232.N0719.N0954.d009347 hk t)
        ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate) =
      ∫ x in _root_.GD.N0232.N0719.N0953.d003311 (k - 1),
        G x *
          _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
            (_root_.GD.N0232.N0719.N0954.d009350 hk rate) x := by
  rw [_root_.GD.N0232.N0719.N0954.d009364
    hshape hrate]
  let e := _root_.GD.N0232.N0719.N0954.d009345 k hk
  have hvolume :
      MeasurePreserving e
        (volume : Measure (_root_.GD.N0232.N0719.N0953.d003306 (k - 1)))
        (volume : Measure (Fin k → ℝ)) :=
    volume_measurePreserving_piCongrLeft
      (fun _ : Fin k => ℝ) (_root_.GD.N0232.N0719.N0954.d009344 k hk)
  rw [← hvolume.integral_comp']
  simp only [e, _root_.GD.N0232.N0719.N0954.d009347, _root_.GD.N0232.N0719.N0954.d009346,
    MeasurableEquiv.symm_apply_apply]
  simp_rw [_root_.GD.N0232.N0719.N0954.d009490
    hk shape rate]
  have hae_nonzero :
      ∀ᵐ u : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) ∂volume,
        ∀ i, u i ≠ 0 := by
    apply ae_all_iff.2
    intro i
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ => volume) i 0
  have hzero :
      ∀ᵐ u : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) ∂volume,
        u ∉ _root_.GD.N0232.N0719.N0953.d003310 (k - 1) →
          _root_.GD.N0232.N0719.N0954.d009480
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk rate) u *
            G (_root_.GD.N0232.N0719.N0953.d003314 u) = 0 := by
    filter_upwards [hae_nonzero] with u hu hnot
    change ¬ ∀ i : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
      0 < u i at hnot
    have hnot' : ∃ i, ¬ 0 < u i :=
      not_forall.mp hnot
    obtain ⟨i, hi⟩ := hnot'
    have hineg : u i < 0 :=
      lt_of_le_of_ne (not_lt.mp hi) (hu i)
    have hpdfzero :
        gammaPDFReal
          (_root_.GD.N0232.N0719.N0954.d009350 hk shape i)
          (_root_.GD.N0232.N0719.N0954.d009350 hk rate i) (u i) = 0 := by
      simp [gammaPDFReal, not_le.mpr hineg]
    unfold _root_.GD.N0232.N0719.N0954.d009480
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hpdfzero,
      zero_mul]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hzero]
  let shapeC := _root_.GD.N0232.N0719.N0954.d009350 hk shape
  let rateC := _root_.GD.N0232.N0719.N0954.d009350 hk rate
  have htransport :=
    _root_.GD.N0232.N0719.N0954.d009489
      (shape := shapeC) (rate := rateC)
      (fun u => G (_root_.GD.N0232.N0719.N0953.d003314 u))
      (fun i => hshape (_root_.GD.N0232.N0719.N0954.d009344 k hk i))
      (fun i => hrate (_root_.GD.N0232.N0719.N0954.d009344 k hk i))
  calc
    (∫ u in _root_.GD.N0232.N0719.N0953.d003310 (k - 1),
        _root_.GD.N0232.N0719.N0954.d009480 shapeC rateC u *
          G (_root_.GD.N0232.N0719.N0953.d003314 u)) =
        ∫ u in _root_.GD.N0232.N0719.N0953.d003310 (k - 1),
          G (_root_.GD.N0232.N0719.N0953.d003314 u) *
            _root_.GD.N0232.N0719.N0954.d009480 shapeC rateC u := by
      apply setIntegral_congr_fun (_root_.GD.N0232.N0719.N0953.d003332 _)
      intro u _
      ring
    _ = ∫ x in _root_.GD.N0232.N0719.N0953.d003311 (k - 1),
          G (_root_.GD.N0232.N0719.N0953.d003314 (_root_.GD.N0232.N0719.N0953.d003315 x)) *
            _root_.GD.N0232.N0719.N0954.d009483 shapeC rateC x :=
      htransport
    _ = ∫ x in _root_.GD.N0232.N0719.N0953.d003311 (k - 1),
          G x * _root_.GD.N0232.N0719.N0954.d009483 shapeC rateC x := by
      apply setIntegral_congr_fun (_root_.GD.N0232.N0719.N0953.d003333 _)
      intro x hx
      simp only
      rw [_root_.GD.N0232.N0719.N0953.d003326 hx]

end

end GD.N0232.N0719.N0954
