import GD.Module0426

















open MeasureTheory ProbabilityTheory WithLp Module
open scoped RealInnerProductSpace BigOperators

namespace GD.N0139

noncomputable section

section GaussianMarginal

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]


private noncomputable def d006660 :
    F →ₗᵢ[ℝ] WithLp 2 (E × F) where
  toLinearMap :=
    (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap.comp
      (LinearMap.inr ℝ E F)
  norm_map' y := by
    exact WithLp.norm_toLp_snd 2 E F y



private lemma d006661 (L : StrongDual ℝ F) :
    ‖L.comp (WithLp.sndL 2 ℝ E F)‖ = ‖L‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) ?_
    intro x
    calc
      ‖L ((WithLp.sndL 2 ℝ E F) x)‖
          ≤ ‖L‖ * ‖(WithLp.sndL 2 ℝ E F) x‖ := L.le_opNorm _
      _ ≤ ‖L‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E x) (norm_nonneg L)
  · let j := _root_.GD.N0139.d006660 (E := E) (F := F)
    have hcomp :
        (L.comp (WithLp.sndL 2 ℝ E F)).comp
            j.toContinuousLinearMap = L := by
      ext y
      rfl
    have hj : ‖j.toContinuousLinearMap‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro y
      simp [j, _root_.GD.N0139.d006660]
    calc
      ‖L‖ =
          ‖(L.comp (WithLp.sndL 2 ℝ E F)).comp
            j.toContinuousLinearMap‖ := by rw [hcomp]
      _ ≤ ‖L.comp (WithLp.sndL 2 ℝ E F)‖ *
          ‖j.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L.comp (WithLp.sndL 2 ℝ E F)‖ * 1 :=
        mul_le_mul_of_nonneg_left hj
          (ContinuousLinearMap.opNorm_nonneg
            (L.comp (WithLp.sndL 2 ℝ E F)))
      _ = ‖L.comp (WithLp.sndL 2 ℝ E F)‖ := mul_one _



theorem d006662 :
    (stdGaussian (WithLp 2 (E × F))).map
        (fun x : WithLp 2 (E × F) => x.snd) =
      stdGaussian F := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [show (fun x : WithLp 2 (E × F) => x.snd) =
      WithLp.sndL 2 ℝ E F from rfl]
  rw [charFunDual_map]
  simp [charFunDual_stdGaussian, _root_.GD.N0139.d006661]



theorem d006663 {ι : Type*} [Fintype ι] :
    (stdGaussian (EuclideanSpace ℝ ι)).map
        (fun x : EuclideanSpace ℝ ι => x.ofLp) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map]
  · have hfun :
        (fun x : ι → ℝ => (WithLp.toLp 2 x).ofLp) = id := by
          rfl
    change Measure.map (fun x : ι → ℝ => (WithLp.toLp 2 x).ofLp)
      (Measure.pi fun _ : ι => gaussianReal 0 1) =
        Measure.pi fun _ : ι => gaussianReal 0 1
    rw [hfun, Measure.map_id]
  · fun_prop
  · fun_prop

end GaussianMarginal

section AbstractCoordinates

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]



noncomputable def d006664
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (b : OrthonormalBasis ι ℝ Kᗮ) (x : E) : ι → ℝ :=
  (b.repr (Kᗮ.orthogonalProjectionOnto x)).ofLp

theorem d006665
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (b : OrthonormalBasis ι ℝ Kᗮ) :
    Measurable (_root_.GD.N0139.d006664 K b) := by
  unfold _root_.GD.N0139.d006664
  fun_prop



theorem d006666
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    (stdGaussian E).map Kᗮ.orthogonalProjectionOnto =
      stdGaussian Kᗮ := by
  calc
    (stdGaussian E).map Kᗮ.orthogonalProjectionOnto =
        ((stdGaussian E).map K.orthogonalDecomposition).map
          (fun x : WithLp 2 (K × Kᗮ) => x.snd) := by
            rw [Measure.map_map]
            · apply Measure.map_congr
              filter_upwards with x
              exact K.snd_orthogonalDecomposition_apply x |>.symm
            · fun_prop
            · fun_prop
    _ = (stdGaussian (WithLp 2 (K × Kᗮ))).map
          (fun x : WithLp 2 (K × Kᗮ) => x.snd) := by
            rw [stdGaussian_map]
    _ = stdGaussian Kᗮ := _root_.GD.N0139.d006662



theorem d006667
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (b : OrthonormalBasis ι ℝ Kᗮ) :
    (stdGaussian E).map (_root_.GD.N0139.d006664 K b) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  calc
    (stdGaussian E).map (_root_.GD.N0139.d006664 K b) =
        (((stdGaussian E).map Kᗮ.orthogonalProjectionOnto).map b.repr).map
          (fun x : EuclideanSpace ℝ ι => x.ofLp) := by
            rw [Measure.map_map, Measure.map_map]
            · rfl
            all_goals fun_prop
    _ = ((stdGaussian Kᗮ).map b.repr).map
          (fun x : EuclideanSpace ℝ ι => x.ofLp) := by
            rw [_root_.GD.N0139.d006666]
    _ = (stdGaussian (EuclideanSpace ℝ ι)).map
          (fun x : EuclideanSpace ℝ ι => x.ofLp) := by
            rw [stdGaussian_map]
    _ = Measure.pi (fun _ : ι => gaussianReal 0 1) :=
      _root_.GD.N0139.d006663


theorem d006668
    (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (b : OrthonormalBasis ι ℝ Kᗮ) (x : E) :
    ∑ i, (_root_.GD.N0139.d006664 K b x i) ^ 2 =
      ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2 := by
  simp only [_root_.GD.N0139.d006664]
  rw [← EuclideanSpace.real_norm_sq_eq]
  exact congrArg (fun t : ℝ => t ^ 2) (b.repr.norm_map _)

end AbstractCoordinates

section FiniteSample


def d006669 (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))

theorem d006670 {n : ℕ} (hn : 0 < n) :
    _root_.GD.N0139.d006669 n ≠ 0 := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  have hi := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp i) h
  simpa [_root_.GD.N0139.d006669] using hi



noncomputable def d006671 (n : ℕ) (hn : 0 < n) :
    OrthonormalBasis (Fin (n - 1)) ℝ (ℝ ∙ _root_.GD.N0139.d006669 n)ᗮ := by
  letI : Fact
      (finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  exact OrthonormalBasis.fromOrthogonalSpanSingleton
    (n - 1) (_root_.GD.N0139.d006670 hn)



noncomputable def d006672
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) : Fin (n - 1) → ℝ :=
  _root_.GD.N0139.d006664 (ℝ ∙ _root_.GD.N0139.d006669 n) (_root_.GD.N0139.d006671 n hn)
    (WithLp.toLp 2 x)

theorem d006673 (n : ℕ) (hn : 0 < n) :
    Measurable (_root_.GD.N0139.d006672 n hn) := by
  unfold _root_.GD.N0139.d006672
  exact (_root_.GD.N0139.d006665 _ _).comp (by fun_prop)



theorem d006674
    (n : ℕ) (hn : 0 < n) :
    (_root_.GD.N0140.d006650 n).map
        (_root_.GD.N0139.d006672 n hn) =
      _root_.GD.N0140.d006650 (n - 1) := by
  calc
    (_root_.GD.N0140.d006650 n).map
        (_root_.GD.N0139.d006672 n hn) =
      ((_root_.GD.N0140.d006650 n).map
        (WithLp.toLp 2)).map
          (_root_.GD.N0139.d006664 (ℝ ∙ _root_.GD.N0139.d006669 n)
            (_root_.GD.N0139.d006671 n hn)) := by
        rw [Measure.map_map]
        · rfl
        · exact _root_.GD.N0139.d006665 _ _
        · fun_prop
    _ = (stdGaussian (EuclideanSpace ℝ (Fin n))).map
          (_root_.GD.N0139.d006664 (ℝ ∙ _root_.GD.N0139.d006669 n)
            (_root_.GD.N0139.d006671 n hn)) := by
        have hstd :
            (_root_.GD.N0140.d006650 n).map
                (WithLp.toLp 2) =
              stdGaussian (EuclideanSpace ℝ (Fin n)) := by
          simpa [_root_.GD.N0140.d006650] using
            (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin n))
        rw [hstd]
    _ = _root_.GD.N0140.d006650 (n - 1) := by
        exact _root_.GD.N0139.d006667 _ _


def d006675 (n : ℕ) (x : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (_root_.GD.N0126.d006421 x)

private theorem d006676
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    _root_.GD.N0139.d006675 n x ∈ (ℝ ∙ _root_.GD.N0139.d006669 n)ᗮ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [_root_.GD.N0139.d006675, _root_.GD.N0139.d006669, WithLp.ofLp_toLp, star_trivial,
    dotProduct]
  change ∑ i, _root_.GD.N0126.d006421 x i * 1 = 0
  simpa using _root_.GD.N0126.d006425 x

private theorem d006677
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    WithLp.toLp 2 (fun _ : Fin n => _root_.GD.N0126.d006420 x) ∈
      ℝ ∙ _root_.GD.N0139.d006669 n := by
  rw [Submodule.mem_span_singleton]
  refine ⟨_root_.GD.N0126.d006420 x, ?_⟩
  ext i
  simp [_root_.GD.N0139.d006669]

private theorem d006678
    (n : ℕ) (x : Fin n → ℝ) :
    WithLp.toLp 2 x =
      WithLp.toLp 2
          (fun _ : Fin n => _root_.GD.N0126.d006420 x) +
        _root_.GD.N0139.d006675 n x := by
  ext i
  simp [_root_.GD.N0139.d006675, _root_.GD.N0126.d006421]



theorem d006679
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    (ℝ ∙ _root_.GD.N0139.d006669 n)ᗮ.orthogonalProjectionOnto
        (WithLp.toLp 2 x) =
      ⟨_root_.GD.N0139.d006675 n x, _root_.GD.N0139.d006676 n hn x⟩ := by
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := ℝ ∙ _root_.GD.N0139.d006669 n
  let m : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun _ : Fin n => _root_.GD.N0126.d006420 x)
  let r : EuclideanSpace ℝ (Fin n) := _root_.GD.N0139.d006675 n x
  have hm : m ∈ K := _root_.GD.N0139.d006677 n hn x
  have hr : r ∈ Kᗮ := _root_.GD.N0139.d006676 n hn x
  have hsplit : WithLp.toLp 2 x = m + r :=
    _root_.GD.N0139.d006678 n x
  rw [hsplit, map_add]
  rw [K.orthogonalProjectionOnto_orthogonal_apply_eq_zero hm]
  simpa [K, r] using
    (Kᗮ.orthogonalProjectionOnto_mem_subspace_eq_self ⟨r, hr⟩)



theorem d006680
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    _root_.GD.N0140.d006651 (_root_.GD.N0139.d006672 n hn x) =
      _root_.GD.N0126.d006422 x := by
  unfold _root_.GD.N0140.d006651 _root_.GD.N0139.d006672
  rw [_root_.GD.N0139.d006668]
  rw [_root_.GD.N0139.d006679 n hn x]
  change ‖_root_.GD.N0139.d006675 n x‖ ^ 2 =
    _root_.GD.N0126.d006422 x
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl




theorem d006681
    (n : ℕ) (hn : 2 ≤ n) :
    (_root_.GD.N0140.d006650 n).map
        _root_.GD.N0126.d006422 =
      _root_.GD.N0121.d006346 (n - 1) := by
  letI : ∀ _ : Fin n, IsProbabilityMeasure (gaussianReal 0 1) :=
    fun _ => inferInstance
  letI : IsProbabilityMeasure
      (_root_.GD.N0140.d006650 n) := by
    unfold _root_.GD.N0140.d006650
    infer_instance
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hd : 0 < n - 1 := by omega
  exact _root_.GD.N0140.d006657
    hd (_root_.GD.N0139.d006672 n hn0)
    _root_.GD.N0126.d006422
    (_root_.GD.N0139.d006673 n hn0)
    (_root_.GD.N0139.d006674 n hn0)
    (fun x => (_root_.GD.N0139.d006680 n hn0 x).symm)

end FiniteSample

end

end GD.N0139
