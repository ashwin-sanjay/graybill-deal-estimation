import GD.Module0412
import GD.Module0416

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0140

noncomputable section


def d006650 (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)


def d006651 {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∑ i, x i ^ 2

theorem d006652 {d : ℕ} :
    Measurable (_root_.GD.N0140.d006651 (d := d)) := by
  unfold _root_.GD.N0140.d006651
  fun_prop



theorem d006653
    {d : ℕ} (i : Fin d) :
    (_root_.GD.N0140.d006650 d).map (fun x ↦ x i ^ 2) =
      _root_.GD.N0121.d006346 1 := by
  letI : ∀ _ : Fin d, IsProbabilityMeasure (gaussianReal 0 1) :=
    fun _ ↦ inferInstance
  have heval :
      (_root_.GD.N0140.d006650 d).map (Function.eval i) =
        gaussianReal 0 1 := by
    unfold _root_.GD.N0140.d006650
    exact (measurePreserving_eval
      (fun _ : Fin d ↦ gaussianReal 0 1) i).map_eq
  calc
    (_root_.GD.N0140.d006650 d).map (fun x ↦ x i ^ 2) =
        (((_root_.GD.N0140.d006650 d).map (Function.eval i)).map
          (fun z : ℝ ↦ z ^ 2)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ = (gaussianReal 0 1).map (fun z : ℝ ↦ z ^ 2) := by
          rw [heval]
    _ = _root_.GD.N0121.d006346 1 :=
      _root_.GD.N0121.d006355



theorem d006654 (d : ℕ) :
    iIndepFun (fun i (x : Fin d → ℝ) ↦ x i ^ 2)
      (_root_.GD.N0140.d006650 d) := by
  exact iIndepFun_pi
    (μ := fun _ : Fin d ↦ gaussianReal 0 1)
    (X := fun _ : Fin d ↦ fun z : ℝ ↦ z ^ 2)
    (fun _ ↦ by fun_prop)


theorem d006655
    {d : ℕ} {t : ℝ} (ht : t < 1 / 2) :
    mgf _root_.GD.N0140.d006651 (_root_.GD.N0140.d006650 d) t =
      ((1 / 2 : ℝ) / (1 / 2 - t)) ^ ((d : ℝ) / 2) := by
  letI : ∀ i : Fin d, IsProbabilityMeasure (gaussianReal 0 1) :=
    fun _ ↦ inferInstance
  letI : IsProbabilityMeasure (_root_.GD.N0140.d006650 d) := by
    unfold _root_.GD.N0140.d006650
    infer_instance
  have hind := _root_.GD.N0140.d006654 d
  have hsum := hind.mgf_sum
    (fun _ : Fin d ↦
      (show Measurable (fun x : Fin d → ℝ ↦ x _ ^ 2) by
        exact (measurable_pi_apply _).pow_const 2))
    Finset.univ (t := t)
  have hcoord (i : Fin d) :
      mgf (fun x : Fin d → ℝ ↦ x i ^ 2)
          (_root_.GD.N0140.d006650 d) t =
        mgf id (_root_.GD.N0121.d006346 1) t := by
    rw [← mgf_id_map
      (μ := _root_.GD.N0140.d006650 d)
      (X := fun x : Fin d → ℝ ↦ x i ^ 2)
      ((measurable_pi_apply i).pow_const 2).aemeasurable]
    rw [_root_.GD.N0140.d006653 i]
  rw [show mgf _root_.GD.N0140.d006651 (_root_.GD.N0140.d006650 d) t =
      ∏ i : Fin d,
        mgf (fun x : Fin d → ℝ ↦ x i ^ 2)
          (_root_.GD.N0140.d006650 d) t by
    have hfun :
        (∑ i : Fin d, fun x : Fin d → ℝ ↦ x i ^ 2) =
          fun x : Fin d → ℝ ↦ ∑ i, x i ^ 2 := by
      funext x
      simp only [Finset.sum_apply]
    change mgf (fun x : Fin d → ℝ ↦ ∑ i, x i ^ 2)
      (_root_.GD.N0140.d006650 d) t = _
    rw [← hfun]
    exact hsum]
  simp_rw [hcoord]
  unfold _root_.GD.N0121.d006346
  norm_num only [Nat.cast_one]
  rw [_root_.GD.N0121.d006347
    (a := (1 : ℝ) / 2) (r := 1 / 2) (t := t)
    (by norm_num) (by norm_num) ht]
  rw [Finset.prod_const, Finset.card_univ]
  simp only [Fintype.card_fin]
  let u : ℝ := (1 / 2 : ℝ) / (1 / 2 - t)
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  change (u ^ ((1 : ℝ) / 2)) ^ d = u ^ ((d : ℝ) / 2)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
  congr 1
  ring




theorem d006656
    (d : ℕ) (hd : 0 < d) :
    (_root_.GD.N0140.d006650 d).map _root_.GD.N0140.d006651 =
      _root_.GD.N0121.d006346 d := by
  letI : ∀ i : Fin d, IsProbabilityMeasure (gaussianReal 0 1) :=
    fun _ ↦ inferInstance
  letI : IsProbabilityMeasure (_root_.GD.N0140.d006650 d) := by
    unfold _root_.GD.N0140.d006650
    infer_instance
  letI : IsProbabilityMeasure
      (_root_.GD.N0121.d006346 d) := by
    unfold _root_.GD.N0121.d006346
    exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have hmap := _root_.GD.N0114.d006372
    (μ := _root_.GD.N0140.d006650 d)
    (ν := _root_.GD.N0121.d006346 d)
    (X := _root_.GD.N0140.d006651) (Y := id) (ε := 1 / 4)
    (by norm_num) _root_.GD.N0140.d006652 measurable_id
    (by
      intro t ht
      have htr : t < 1 / 2 := by linarith [ht.2]
      exact mgf_pos_iff.mp (by
        rw [_root_.GD.N0140.d006655 htr]
        positivity))
    (by
      intro t ht
      have htr : t < 1 / 2 := by linarith [ht.2]
      exact mgf_pos_iff.mp (by
        unfold _root_.GD.N0121.d006346
        rw [_root_.GD.N0121.d006347
          (by positivity) (by norm_num) htr]
        positivity))
    (by
      intro t ht
      have htr : t < 1 / 2 := by linarith [ht.2]
      rw [_root_.GD.N0140.d006655 htr]
      unfold _root_.GD.N0121.d006346
      rw [_root_.GD.N0121.d006347
        (by positivity) (by norm_num) htr])
  simpa using hmap





theorem d006657
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} (hd : 0 < d)
    (R : Ω → Fin d → ℝ) (S : Ω → ℝ)
    (hR : Measurable R)
    (hRlaw : P.map R = _root_.GD.N0140.d006650 d)
    (hS : ∀ ω, S ω = _root_.GD.N0140.d006651 (R ω)) :
    P.map S = _root_.GD.N0121.d006346 d := by
  calc
    P.map S = P.map (fun ω ↦ _root_.GD.N0140.d006651 (R ω)) := by
      congr 1
      funext ω
      exact hS ω
    _ = (P.map R).map _root_.GD.N0140.d006651 := by
      rw [Measure.map_map _root_.GD.N0140.d006652 hR]
      rfl
    _ = (_root_.GD.N0140.d006650 d).map _root_.GD.N0140.d006651 := by
      rw [hRlaw]
    _ = _root_.GD.N0121.d006346 d :=
      _root_.GD.N0140.d006656 d hd




theorem d006658
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) {d : ℕ} (hd : 0 < d)
    (R : Ω → Fin d → ℝ)
    (hR : Measurable R)
    (hRlaw : P.map R = _root_.GD.N0140.d006650 d)
    (hRSS : ∀ ω,
      _root_.GD.N0126.d006422 (fun i ↦ X i ω) =
        _root_.GD.N0140.d006651 (R ω)) :
    P.map (fun ω ↦
      _root_.GD.N0126.d006422 (fun i ↦ X i ω)) =
      _root_.GD.N0121.d006346 d := by
  exact _root_.GD.N0140.d006657
    hd R
    (fun ω ↦ _root_.GD.N0126.d006422 (fun i ↦ X i ω))
    hR hRlaw hRSS





theorem d006659
    {ι Ω : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [MeasurableSpace Ω]
    {P : Measure Ω} {X : ι → Ω → ℝ} {v : ℝ}
    {d : ℕ} (hd : 0 < d)
    (hGaussian : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (hcov : ∀ i j, cov[X i, X j; P] = if i = j then v else 0)
    (R : Ω → Fin d → ℝ)
    (hR : Measurable R)
    (hRlaw : P.map R = _root_.GD.N0140.d006650 d)
    (hRSS : ∀ ω,
      _root_.GD.N0126.d006422 (fun i ↦ X i ω) =
        _root_.GD.N0140.d006651 (R ω)) :
    IndepFun (_root_.GD.N0126.d006435 X)
        (fun ω ↦ _root_.GD.N0126.d006422 (fun i ↦ X i ω)) P
      ∧
    P.map (fun ω ↦
        _root_.GD.N0126.d006422 (fun i ↦ X i ω)) =
      _root_.GD.N0121.d006346 d := by
  letI : IsProbabilityMeasure P := hGaussian.isProbabilityMeasure
  exact ⟨
    _root_.GD.N0126.d006441
      (v := v) hGaussian (fun i j ↦ by
        rw [hcov i j]
        by_cases hij : i = j <;> simp [hij]),
    _root_.GD.N0140.d006658
      X hd R hR hRlaw hRSS⟩

end

end GD.N0140
