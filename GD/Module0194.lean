import Mathlib















open MeasureTheory

namespace GD.N0232.N0720.N1278

noncomputable section



theorem d002662
    {x p h k L C theta gamma D : ℝ}
    (hgamma : 0 < gamma) (hk : 0 < k) (hh : 0 < h)
    (hD : gamma * k * h ≤ D) :
    (x * (L * p + theta * C * h)) ^ 2 / D ≤
      (2 / gamma) *
        ((L ^ 2 / k) * (x ^ 2 * p ^ 2 / h) +
          (C ^ 2 / k) * (theta ^ 2 * x ^ 2 * h)) := by
  have hfloor : 0 < gamma * k * h := by positivity
  have hDpos : 0 < D := hfloor.trans_le hD
  have hsquare :
      (x * (L * p + theta * C * h)) ^ 2 ≤
        2 * (x * (L * p)) ^ 2 + 2 * (x * (theta * C * h)) ^ 2 := by
    nlinarith [sq_nonneg (x * (L * p) - x * (theta * C * h))]
  calc
    (x * (L * p + theta * C * h)) ^ 2 / D ≤
        (2 * (x * (L * p)) ^ 2 +
          2 * (x * (theta * C * h)) ^ 2) / D :=
      div_le_div_of_nonneg_right hsquare hDpos.le
    _ ≤ (2 * (x * (L * p)) ^ 2 +
          2 * (x * (theta * C * h)) ^ 2) / (gamma * k * h) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hfloor
      · exact hD
    _ = (2 / gamma) *
        ((L ^ 2 / k) * (x ^ 2 * p ^ 2 / h) +
          (C ^ 2 / k) * (theta ^ 2 * x ^ 2 * h)) := by
      field_simp [hgamma.ne', hk.ne', hh.ne']








theorem d002663
    {X R : Type*} [MeasurableSpace X] [MeasurableSpace R]
    {μ : Measure X} {ν : Measure R}
    [SFinite μ] [SFinite ν]
    {perspective locationN locationB : X × R → ℝ}
    {locN locB : X → ℝ} {ancN ancB : R → ℝ}
    {gamma : ℝ}
    (hPerspective : Integrable perspective (μ.prod ν))
    (hLocationN : Integrable locN μ)
    (hLocationB : Integrable locB μ)
    (hAncillaryN : Integrable ancN ν)
    (hAncillaryB : Integrable ancB ν)
    (hN : ∀ z, locationN z = locN z.1 * ancN z.2)
    (hB : ∀ z, locationB z = locB z.1 * ancB z.2)
    (hMajor : ∀ z, perspective z ≤
      (2 / gamma) * (locationN z + locationB z)) :
    (∫ z, perspective z ∂(μ.prod ν)) ≤
      (2 / gamma) *
        ((∫ x, locN x ∂μ) * (∫ r, ancN r ∂ν) +
          (∫ x, locB x ∂μ) * (∫ r, ancB r ∂ν)) := by
  have hProdN : Integrable (fun z : X × R => locN z.1 * ancN z.2) (μ.prod ν) :=
    hLocationN.mul_prod hAncillaryN
  have hProdB : Integrable (fun z : X × R => locB z.1 * ancB z.2) (μ.prod ν) :=
    hLocationB.mul_prod hAncillaryB
  have hLocationN' : Integrable locationN (μ.prod ν) := by
    rw [show locationN = (fun z => locN z.1 * ancN z.2) from funext hN]
    exact hProdN
  have hLocationB' : Integrable locationB (μ.prod ν) := by
    rw [show locationB = (fun z => locB z.1 * ancB z.2) from funext hB]
    exact hProdB
  have hMajorInt : Integrable
      (fun z => (2 / gamma) * (locationN z + locationB z)) (μ.prod ν) :=
    (hLocationN'.add hLocationB').const_mul _
  calc
    (∫ z, perspective z ∂(μ.prod ν)) ≤
        ∫ z, (2 / gamma) * (locationN z + locationB z) ∂(μ.prod ν) := by
      exact integral_mono hPerspective hMajorInt hMajor
    _ = (2 / gamma) *
        ((∫ z, locationN z ∂(μ.prod ν)) +
          ∫ z, locationB z ∂(μ.prod ν)) := by
      rw [integral_const_mul, integral_add hLocationN' hLocationB']
    _ = (2 / gamma) *
        ((∫ x, locN x ∂μ) * (∫ r, ancN r ∂ν) +
          (∫ x, locB x ∂μ) * (∫ r, ancB r ∂ν)) := by
      rw [show (∫ z, locationN z ∂(μ.prod ν)) =
          ∫ z, locN z.1 * ancN z.2 ∂(μ.prod ν) by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hN,
        show (∫ z, locationB z ∂(μ.prod ν)) =
          ∫ z, locB z.1 * ancB z.2 ∂(μ.prod ν) by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hB,
        integral_prod_mul, integral_prod_mul]




theorem d002664
    {X R : Type*} [MeasurableSpace X] [MeasurableSpace R]
    {μ : Measure X} {ν : Measure R} [SFinite μ] [SFinite ν]
    {coord p h : X → ℝ} {k L C : R → ℝ}
    {D : X × R → ℝ} {theta gamma : ℝ}
    (hgamma : 0 < gamma)
    (hk : ∀ r, 0 < k r) (hh : ∀ x, 0 < h x)
    (hD : ∀ z, gamma * k z.2 * h z.1 ≤ D z)
    (hPerspective : Integrable
      (fun z : X × R =>
        (coord z.1 * (L z.2 * p z.1 + theta * C z.2 * h z.1)) ^ 2 /
          D z) (μ.prod ν))
    (hLocN : Integrable (fun x => coord x ^ 2 * p x ^ 2 / h x) μ)
    (hLocB : Integrable (fun x => theta ^ 2 * coord x ^ 2 * h x) μ)
    (hAncN : Integrable (fun r => L r ^ 2 / k r) ν)
    (hAncB : Integrable (fun r => C r ^ 2 / k r) ν) :
    (∫ z : X × R,
      (coord z.1 * (L z.2 * p z.1 + theta * C z.2 * h z.1)) ^ 2 /
        D z ∂(μ.prod ν)) ≤
      (2 / gamma) *
        ((∫ x, coord x ^ 2 * p x ^ 2 / h x ∂μ) *
            (∫ r, L r ^ 2 / k r ∂ν) +
          (∫ x, theta ^ 2 * coord x ^ 2 * h x ∂μ) *
            (∫ r, C r ^ 2 / k r ∂ν)) := by
  apply _root_.GD.N0232.N0720.N1278.d002663
      (perspective := fun z : X × R =>
        (coord z.1 * (L z.2 * p z.1 + theta * C z.2 * h z.1)) ^ 2 / D z)
      (locationN := fun z : X × R =>
        (coord z.1 ^ 2 * p z.1 ^ 2 / h z.1) * (L z.2 ^ 2 / k z.2))
      (locationB := fun z : X × R =>
        (theta ^ 2 * coord z.1 ^ 2 * h z.1) * (C z.2 ^ 2 / k z.2))
      (locN := fun x => coord x ^ 2 * p x ^ 2 / h x)
      (locB := fun x => theta ^ 2 * coord x ^ 2 * h x)
      (ancN := fun r => L r ^ 2 / k r)
      (ancB := fun r => C r ^ 2 / k r)
      hPerspective hLocN hLocB hAncN hAncB
  · intro z
    rfl
  · intro z
    rfl
  · intro z
    have hpoint := _root_.GD.N0232.N0720.N1278.d002662
      (x := coord z.1) (p := p z.1) (h := h z.1)
      (k := k z.2) (L := L z.2) (C := C z.2)
      (theta := theta) (gamma := gamma) (D := D z)
      hgamma (hk z.2) (hh z.1) (hD z)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hpoint




theorem d002665
    {X R : Type*} [MeasurableSpace X] [MeasurableSpace R]
    {μ : Measure X} {ν : Measure R} [SFinite μ] [SFinite ν]
    {coord p h : X → ℝ} {k L C : R → ℝ}
    {D : X × R → ℝ} {theta gamma : ℝ}
    (hgamma : 0 < gamma)
    (hk : ∀ r, 0 < k r) (hh : ∀ x, 0 < h x)
    (hD : ∀ z, gamma * k z.2 * h z.1 ≤ D z)
    (hPerspectiveMeas : AEStronglyMeasurable
      (fun z : X × R =>
        (coord z.1 * (L z.2 * p z.1 + theta * C z.2 * h z.1)) ^ 2 /
          D z) (μ.prod ν))
    (hLocN : Integrable (fun x => coord x ^ 2 * p x ^ 2 / h x) μ)
    (hLocB : Integrable (fun x => theta ^ 2 * coord x ^ 2 * h x) μ)
    (hAncN : Integrable (fun r => L r ^ 2 / k r) ν)
    (hAncB : Integrable (fun r => C r ^ 2 / k r) ν) :
    (∫ z : X × R,
      (coord z.1 * (L z.2 * p z.1 + theta * C z.2 * h z.1)) ^ 2 /
        D z ∂(μ.prod ν)) ≤
      (2 / gamma) *
        ((∫ x, coord x ^ 2 * p x ^ 2 / h x ∂μ) *
            (∫ r, L r ^ 2 / k r ∂ν) +
          (∫ x, theta ^ 2 * coord x ^ 2 * h x ∂μ) *
            (∫ r, C r ^ 2 / k r ∂ν)) := by
  let perspective : X × R → ℝ := fun z =>
    (coord z.1 * (L z.2 * p z.1 + theta * C z.2 * h z.1)) ^ 2 / D z
  let major : X × R → ℝ := fun z =>
    (2 / gamma) *
      ((coord z.1 ^ 2 * p z.1 ^ 2 / h z.1) * (L z.2 ^ 2 / k z.2) +
        (theta ^ 2 * coord z.1 ^ 2 * h z.1) * (C z.2 ^ 2 / k z.2))
  have hProdN : Integrable
      (fun z : X × R =>
        (coord z.1 ^ 2 * p z.1 ^ 2 / h z.1) * (L z.2 ^ 2 / k z.2))
      (μ.prod ν) := hLocN.mul_prod hAncN
  have hProdB : Integrable
      (fun z : X × R =>
        (theta ^ 2 * coord z.1 ^ 2 * h z.1) * (C z.2 ^ 2 / k z.2))
      (μ.prod ν) := hLocB.mul_prod hAncB
  have hMajorInt : Integrable major (μ.prod ν) := by
    dsimp [major]
    exact (hProdN.add hProdB).const_mul _
  have hMajorPoint : ∀ z, perspective z ≤ major z := by
    intro z
    dsimp [perspective, major]
    have hpoint := _root_.GD.N0232.N0720.N1278.d002662
      (x := coord z.1) (p := p z.1) (h := h z.1)
      (k := k z.2) (L := L z.2) (C := C z.2)
      (theta := theta) (gamma := gamma) (D := D z)
      hgamma (hk z.2) (hh z.1) (hD z)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hpoint
  have hPerspectiveNonneg : ∀ z, 0 ≤ perspective z := by
    intro z
    have hfloor : 0 < gamma * k z.2 * h z.1 :=
      mul_pos (mul_pos hgamma (hk z.2)) (hh z.1)
    have hDpos : 0 < D z := hfloor.trans_le (hD z)
    dsimp [perspective]
    positivity
  have hPerspectiveInt : Integrable perspective (μ.prod ν) := by
    apply hMajorInt.mono_nonneg hPerspectiveMeas
    · exact Filter.Eventually.of_forall hPerspectiveNonneg
    · exact Filter.Eventually.of_forall hMajorPoint
  exact _root_.GD.N0232.N0720.N1278.d002664
    hgamma hk hh hD (by simpa [perspective] using hPerspectiveInt)
    hLocN hLocB hAncN hAncB

end

end GD.N0232.N0720.N1278

#print axioms _root_.GD.N0232.N0720.N1278.d002662
#print axioms _root_.GD.N0232.N0720.N1278.d002663
#print axioms _root_.GD.N0232.N0720.N1278.d002664
#print axioms _root_.GD.N0232.N0720.N1278.d002665
