import GD.Module0312
import GD.Module1243











open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1390

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1372
open _root_.GD.N0232.N0720.N1371 _root_.GD.N0232.N0720.N1373
open _root_.GD.N0232.N0720.N1388 _root_.GD.N0232.N0720.N1389 _root_.GD.N0232.N0720.N1387
open _root_.GD.N0232.N0720.N1381 _root_.GD.N0232.N0720.N1392
open _root_.GD.N0232.N0720.N1401 _root_.GD.N0232.N0720.N1398
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1437
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556

noncomputable section

private theorem d020158 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : Measure.QuasiMeasurePreserving f μ ν) {p : β → Prop}
    (hp : ∀ᵐ y ∂ν, p y) : ∀ᵐ x ∂μ, p (f x) :=
  hf.ae hp



theorem d020159
    (f : ℕ → _root_.GD.N0232.N0720.N1393.d004492 → ℝ) (hf : ∀ n, _root_.GD.N0238.N0753.d004397 (f n))
    (h : _root_.GD.N0232.N0720.N1393.d004493 → ℝ)
    (hlim : ∀ᵐ (u : _root_.GD.N0232.N0720.N1393.d004493) ∂_root_.GD.N0232.N0720.N1393.d004494,
      Tendsto (fun n ↦ f n u) atTop (𝓝 (h u))) :
    ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1393.d004492),
      Tendsto (fun n ↦ f n x) atTop (𝓝 (_root_.GD.N0232.N0720.N1393.d004496 h x)) := by
  have hfst : ∀ᵐ (p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ)) ∂_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3),
      Tendsto (fun n ↦ f n (p.1 : _root_.GD.N0232.N0720.N1393.d004492)) atTop (𝓝 (h p.1)) :=
    _root_.GD.N0232.N0720.N1390.d020158 (Measure.quasiMeasurePreserving_fst
      (μ := _root_.GD.N0232.N0720.N1393.d004494) (ν := Measure.volumeIoiPow 3)) hlim
  have hprod : ∀ᵐ p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ∂_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3),
      Tendsto (fun n ↦ f n (((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492).symm p).1))
        atTop (𝓝 (_root_.GD.N0232.N0720.N1393.d004496 h (((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492).symm p).1))) := by
    filter_upwards [hfst] with p hp
    simp only [homeomorphUnitSphereProd_symm_apply_coe, _root_.GD.N0232.N0720.N1393.d004499]
    have heq : (fun n ↦ f n (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1393.d004492))) =
        (fun n ↦ p.2.1 * f n p.1) := by
      funext n
      simpa only [smul_eq_mul] using hf n p.2.1 p.2.2 (p.1 : _root_.GD.N0232.N0720.N1393.d004492)
    rw [heq]
    exact tendsto_const_nhds.mul hp
  have hpolar := (volume : Measure _root_.GD.N0232.N0720.N1393.d004492).measurePreserving_homeomorphUnitSphereProd
  have hsub : ∀ᵐ x : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492) ∂volume.comap Subtype.val,
      Tendsto (fun n ↦ f n x.1) atTop (𝓝 (_root_.GD.N0232.N0720.N1393.d004496 h x.1)) := by
    have hp := _root_.GD.N0232.N0720.N1390.d020158 hpolar.quasiMeasurePreserving (by
      simpa only [finrank_euclideanSpace_fin, Nat.reduceSub, _root_.GD.N0232.N0720.N1393.d004494] using hprod)
    simpa only [Homeomorph.symm_apply_apply] using hp
  have hr : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1393.d004492).restrict ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492),
      Tendsto (fun n ↦ f n x) atTop (𝓝 (_root_.GD.N0232.N0720.N1393.d004496 h x)) :=
    (ae_restrict_iff_subtype (μ := (volume : Measure _root_.GD.N0232.N0720.N1393.d004492))
      (p := fun x : _root_.GD.N0232.N0720.N1393.d004492 ↦
        Tendsto (fun n ↦ f n x) atTop (𝓝 (_root_.GD.N0232.N0720.N1393.d004496 h x)))
      (measurableSet_singleton (0 : _root_.GD.N0232.N0720.N1393.d004492)).compl).2 hsub
  simpa only [restrict_compl_singleton] using hr

theorem d020160 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (hg : ∀ p, g p ∈ Icc (0 : ℝ) 1) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1401.d020150 g x ∈ Icc (min (x 0) (x 2)) (max (x 0) (x 2)) := by
  let a := g (_root_.GD.N0232.N0720.N1437.d002996 (x 1 ^ 2) (x 3 ^ 2),
    _root_.GD.N0232.N0720.N1437.d002997 (x 0) (x 2) (x 1 ^ 2) (x 3 ^ 2))
  have ha : 0 ≤ a := (hg _).1
  have ha1 : 0 ≤ 1 - a := sub_nonneg.mpr (hg _).2
  change min (x 0) (x 2) ≤ x 2 + (x 0 - x 2) * a ∧
    x 2 + (x 0 - x 2) * a ≤ max (x 0) (x 2)
  constructor
  · have hX := mul_nonneg (sub_nonneg.mpr (min_le_left (x 0) (x 2))) ha
    have hY := mul_nonneg (sub_nonneg.mpr (min_le_right (x 0) (x 2))) ha1
    nlinarith
  · have hX := mul_nonneg (sub_nonneg.mpr (le_max_left (x 0) (x 2))) ha
    have hY := mul_nonneg (sub_nonneg.mpr (le_max_right (x 0) (x 2))) ha1
    nlinarith

theorem d020161
    {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ∃ h : _root_.GD.N0232.N0720.N1393.d004495, _root_.GD.N0230.N0556.d000031 _root_.GD.N0232.N0720.N1372.d004546 h ∧
      _root_.GD.N0232.N0720.N1393.d004496 h =ᵐ[(volume : Measure _root_.GD.N0232.N0720.N1393.d004492)]
        _root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) := by
  let g := _root_.GD.N0232.N0720.N1398.d019601 d
  let f := _root_.GD.N0232.N0720.N1401.d020150 g
  have hf : Measurable f :=
    _root_.GD.N0232.N0720.N1401.d020151 (_root_.GD.N0232.N0720.N1398.d019602 hd.1)
  have hhom : _root_.GD.N0238.N0753.d004397 f := _root_.GD.N0232.N0720.N1401.d020152 g
  have hbound : ∀ u : _root_.GD.N0232.N0720.N1393.d004493, ‖f u‖ ≤ 3 :=
    _root_.GD.N0232.N0720.N1401.d020153 g (_root_.GD.N0232.N0720.N1398.d019603 d)
  have hrep : ∀ θ : _root_.GD.N0232.N0720.N1387.d014682,
      f ∘ _root_.GD.N0232.N0720.N1389.d012529 =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 θ] d := by
    intro θ
    simpa only [Function.comp_def, f, _root_.GD.N0232.N0720.N1401.d020156, g] using
      (_root_.GD.N0232.N0720.N1398.d019606 hd θ).symm
  exact ⟨_root_.GD.N0232.N0720.N1381.d014708 f hf 3 hbound,
    _root_.GD.N0232.N0720.N1392.d014714 hd f hf hhom 3 hbound hrep,
    _root_.GD.N0232.N0720.N1381.d014710 f hf hhom 3 hbound⟩




theorem d020162
    {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ∃ (m : ℕ → ℕ) (p : ∀ j, Option (Fin (m j)) → _root_.GD.N0232.N0720.N1373.d004629)
      (a : ∀ j, Option (Fin (m j)) → ℝ) (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629),
      (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = 1) ∧
      (∀ j, (ν j : Measure _root_.GD.N0232.N0720.N1373.d004629) =
        ∑ i, ENNReal.ofReal (a j i) • Measure.dirac (p j i)) ∧
      (∀ j i, (p j i).2.1 ∈ Ioo (0 : ℝ) 1) ∧
      (∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1393.d004492),
        Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1373.d004645 (ν j : Measure _root_.GD.N0232.N0720.N1373.d004629) x) atTop
          (𝓝 (_root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) x))) ∧
      (∀ x : _root_.GD.N0232.N0720.N1393.d004492, _root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) x ∈
        Icc (min (x 0) (x 2)) (max (x 0) (x 2))) := by
  obtain ⟨h, hadm, hcoordinate⟩ := _root_.GD.N0232.N0720.N1390.d020161 hd
  obtain ⟨w, ns, hw, _hns, hlim⟩ := _root_.GD.N0232.N0720.N1371.d004627 h hadm
  let q : ∀ j, Option (Fin (ns j)) → _root_.GD.N0232.N0720.N1372.d004518 :=
    fun j ↦ _root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i)
  let v : ∀ j, Option (Fin (ns j)) → ℝ := fun j ↦ _root_.GD.N0232.N0720.N1371.d004600 (w (ns j))
  have hv : ∀ j i, 0 ≤ v j i := fun j ↦ _root_.GD.N0232.N0720.N1371.d004601 _ (hw (ns j))
  have hp : ∀ j, ∃ i, 0 < v j i := fun j ↦ _root_.GD.N0232.N0720.N1371.d004602 _
  let ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629 :=
    fun j ↦ _root_.GD.N0232.N0720.N1373.d004640 (q j) (v j) (hv j) (hp j)
  have hlim' : ∀ᵐ (u : _root_.GD.N0232.N0720.N1393.d004493) ∂_root_.GD.N0232.N0720.N1393.d004494,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1373.d004646 (q j) (v j) u) atTop (𝓝 (h u)) := by
    simpa only [_root_.GD.N0232.N0720.N1373.d004646, _root_.GD.N0232.N0720.N1373.d004633, _root_.GD.N0232.N0720.N1373.d004631, _root_.GD.N0232.N0720.N1373.d004632,
      _root_.GD.N0232.N0720.N1373.d004630, q, v] using hlim
  have hraw := _root_.GD.N0232.N0720.N1390.d020159
    (fun j ↦ _root_.GD.N0232.N0720.N1373.d004646 (q j) (v j))
    (fun j ↦ _root_.GD.N0232.N0720.N1373.d004650 (q j) (v j)) h hlim'
  refine ⟨ns, (fun j i ↦ _root_.GD.N0232.N0720.N1373.d004630 (q j i)),
    (fun j ↦ _root_.GD.N0232.N0720.N1373.d004637 (q j) (v j)), ν,
    (fun j i ↦ _root_.GD.N0232.N0720.N1373.d004638 (q j) (v j) (hv j) (hp j) i),
    (fun j ↦ _root_.GD.N0232.N0720.N1373.d004639 (q j) (v j) (hv j) (hp j)),
    (fun _ ↦ rfl), (fun j i ↦ (q j i).2.2), ?_, ?_⟩
  · filter_upwards [hraw, hcoordinate] with x hx heq
    simp only [ν, _root_.GD.N0232.N0720.N1373.d004647]
    rwa [heq] at hx
  · exact _root_.GD.N0232.N0720.N1390.d020160 _ (_root_.GD.N0232.N0720.N1398.d019603 d)

end

end GD.N0232.N0720.N1390

#print axioms _root_.GD.N0232.N0720.N1390.d020159
#print axioms _root_.GD.N0232.N0720.N1390.d020162
