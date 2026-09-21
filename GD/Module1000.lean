import GD.Module0823
import GD.Module0955
import Mathlib.MeasureTheory.Constructions.Polish.Basic































open Function MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1486

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1498
open _root_.GD.N0232.N0720.N1034




attribute [local instance] Measure.Subtype.measureSpace

noncomputable local instance d015855 :
    SigmaFinite (volume : Measure (Set.Ioi (0 : ℝ))) := by
  apply SigmaFinite.of_map (volume : Measure (Set.Ioi (0 : ℝ)))
    measurable_subtype_coe.aemeasurable
  rw [MeasurableSet.map_coe_volume measurableSet_Ioi]
  infer_instance




abbrev d015856 :=
  ℝ × (Set.Ioi (0 : ℝ) × Set.Ioo (0 : ℝ) 1)


def d015857 (q : Set.Ioi (0 : ℝ)) : ℝ :=
  (q : ℝ) ^ (-(5 / 2 : ℝ))



theorem d015858 :
    _root_.GD.N0232.N0720.N1034.d012428 (4 : ℝ) = 5 / 2 := by
  norm_num [_root_.GD.N0232.N0720.N1034.d012428]

theorem d015859
    (q : Set.Ioi (0 : ℝ)) :
    _root_.GD.N0232.N0720.N1486.d015857 q =
      (q : ℝ) ^ (-_root_.GD.N0232.N0720.N1034.d012428 (4 : ℝ)) := by
  unfold _root_.GD.N0232.N0720.N1486.d015857
  rw [_root_.GD.N0232.N0720.N1486.d015858]


def d015860
    (q : Set.Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0232.N0720.N1486.d015857 q)

private theorem d015861 (p : ℝ) :
    Measurable (fun x : ℝ ↦ x ^ p) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const fun x hx ↦ Or.inl hx

@[fun_prop]
theorem d015862 :
    Measurable _root_.GD.N0232.N0720.N1486.d015857 := by
  exact
    (_root_.GD.N0232.N0720.N1486.d015861 (-(5 / 2 : ℝ))).comp
      measurable_subtype_coe

@[fun_prop]
theorem d015863 :
    Measurable _root_.GD.N0232.N0720.N1486.d015860 := by
  exact _root_.GD.N0232.N0720.N1486.d015862.ennreal_ofReal

theorem d015864
    (q : Set.Ioi (0 : ℝ)) :
    0 < _root_.GD.N0232.N0720.N1486.d015857 q := by
  exact Real.rpow_pos_of_pos q.property _

theorem d015865
    (q : Set.Ioi (0 : ℝ)) :
    _root_.GD.N0232.N0720.N1486.d015860 q ≠ ∞ := by
  exact ENNReal.ofReal_ne_top




def d015866 : Measure (Set.Ioi (0 : ℝ)) :=
  volume.withDensity _root_.GD.N0232.N0720.N1486.d015860


theorem d015867
    {s : Set (Set.Ioi (0 : ℝ))} (hs : MeasurableSet s) :
    _root_.GD.N0232.N0720.N1486.d015866 s =
      ∫⁻ q in s, _root_.GD.N0232.N0720.N1486.d015860 q ∂volume := by
  rw [_root_.GD.N0232.N0720.N1486.d015866, withDensity_apply _ hs]


noncomputable instance d015868 :
    SigmaFinite _root_.GD.N0232.N0720.N1486.d015866 := by
  unfold _root_.GD.N0232.N0720.N1486.d015866 _root_.GD.N0232.N0720.N1486.d015860
  infer_instance



theorem d015869 :
    ¬ IntegrableOn (fun q : ℝ ↦ q ^ (-(5 / 2 : ℝ)))
        (Set.Ioi (0 : ℝ)) := by
  exact not_integrableOn_Ioi_rpow (-(5 / 2 : ℝ))


def d015870
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) :
    Measure _root_.GD.N0232.N0720.N1486.d015856 :=
  volume.prod (_root_.GD.N0232.N0720.N1486.d015866.prod rho)


noncomputable instance d015871
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho] :
    SigmaFinite (_root_.GD.N0232.N0720.N1486.d015870 rho) := by
  unfold _root_.GD.N0232.N0720.N1486.d015870
  infer_instance




theorem d015872
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SFinite rho] :
    _root_.GD.N0232.N0720.N1486.d015870 rho =
      (volume.prod (volume.prod rho)).withDensity
        (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦
          _root_.GD.N0232.N0720.N1486.d015860 theta.2.1) := by
  unfold _root_.GD.N0232.N0720.N1486.d015870 _root_.GD.N0232.N0720.N1486.d015866
  calc
    volume.prod
          ((volume.withDensity _root_.GD.N0232.N0720.N1486.d015860).prod rho) =
        volume.prod
          ((volume.prod rho).withDensity
            (fun qz ↦ _root_.GD.N0232.N0720.N1486.d015860 qz.1)) := by
      rw [prod_withDensity_left
        _root_.GD.N0232.N0720.N1486.d015863]
    _ = (volume.prod (volume.prod rho)).withDensity
          (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦
            _root_.GD.N0232.N0720.N1486.d015860 theta.2.1) := by
      exact prod_withDensity_right
        (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Set.Ioi (0 : ℝ))).prod rho)
        (_root_.GD.N0232.N0720.N1486.d015863.comp measurable_fst)




def d015873
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (theta : _root_.GD.N0232.N0720.N1486.d015856) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := theta.1
  scale₁ := _root_.GD.N0232.N0720.N1498.d012567 m theta.2.1 theta.2.2
  scale₂ := _root_.GD.N0232.N0720.N1498.d012568 n theta.2.1 theta.2.2
  scale₁_pos :=
    _root_.GD.N0232.N0720.N1498.d012569 hm theta.2.1.property theta.2.2.property.1
  scale₂_pos :=
    _root_.GD.N0232.N0720.N1498.d012570 hn theta.2.1.property theta.2.2.property.2

@[simp] theorem d015874
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (theta : _root_.GD.N0232.N0720.N1486.d015856) :
    (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn theta).location = theta.1 := rfl

@[simp] theorem d015875
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (theta : _root_.GD.N0232.N0720.N1486.d015856) :
    (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn theta).scale₁ =
      _root_.GD.N0232.N0720.N1498.d012567 m theta.2.1 theta.2.2 := rfl

@[simp] theorem d015876
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (theta : _root_.GD.N0232.N0720.N1486.d015856) :
    (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn theta).scale₂ =
      _root_.GD.N0232.N0720.N1498.d012568 n theta.2.1 theta.2.2 := rfl

@[fun_prop]
theorem d015877
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Continuous (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn) := by
  apply (_root_.GD.N0232.N0720.N1499.d014996.comp_continuous_iff).mp
  change Continuous (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦
    (theta.1,
      (_root_.GD.N0232.N0720.N1498.d012567 m theta.2.1 theta.2.2,
        _root_.GD.N0232.N0720.N1498.d012568 n theta.2.1 theta.2.2)))
  have hq : Continuous
      (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦ (theta.2.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hz : Continuous
      (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦ (theta.2.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hscale₁ : Continuous (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦
      _root_.GD.N0232.N0720.N1498.d012567 m theta.2.1 theta.2.2) := by
    unfold _root_.GD.N0232.N0720.N1498.d012567
    exact Real.continuous_sqrt.comp
      ((continuous_const.mul hq).div hz
        (fun theta ↦ theta.2.2.property.1.ne'))
  have hscale₂ : Continuous (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦
      _root_.GD.N0232.N0720.N1498.d012568 n theta.2.1 theta.2.2) := by
    unfold _root_.GD.N0232.N0720.N1498.d012568
    exact Real.continuous_sqrt.comp
      ((continuous_const.mul hq).div (continuous_const.sub hz)
        (fun theta ↦ (sub_pos.mpr theta.2.2.property.2).ne'))
  exact continuous_fst.prodMk (hscale₁.prodMk hscale₂)


theorem d015878
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn) := by
  intro theta eta heq
  have hlocation : theta.1 = eta.1 :=
    congrArg _root_.GD.N0232.N0720.N1080.d014168.location heq
  have hscale₁ := congrArg _root_.GD.N0232.N0720.N1080.d014168.scale₁ heq
  have hscale₂ := congrArg _root_.GD.N0232.N0720.N1080.d014168.scale₂ heq
  change _root_.GD.N0232.N0720.N1498.d012567 m theta.2.1 theta.2.2 =
    _root_.GD.N0232.N0720.N1498.d012567 m eta.2.1 eta.2.2 at hscale₁
  change _root_.GD.N0232.N0720.N1498.d012568 n theta.2.1 theta.2.2 =
    _root_.GD.N0232.N0720.N1498.d012568 n eta.2.1 eta.2.2 at hscale₂
  have hprecision₁ :
      (theta.2.2 : ℝ) / (theta.2.1 : ℝ) =
        (eta.2.2 : ℝ) / (eta.2.1 : ℝ) := by
    calc
      (theta.2.2 : ℝ) / (theta.2.1 : ℝ) =
          (m : ℝ) /
            _root_.GD.N0232.N0720.N1498.d012567 m theta.2.1 theta.2.2 ^ 2 :=
        (_root_.GD.N0232.N0720.N1498.d012573 hm
          theta.2.1.property theta.2.2.property.1).symm
      _ = (m : ℝ) /
            _root_.GD.N0232.N0720.N1498.d012567 m eta.2.1 eta.2.2 ^ 2 := by
        rw [hscale₁]
      _ = (eta.2.2 : ℝ) / (eta.2.1 : ℝ) :=
        _root_.GD.N0232.N0720.N1498.d012573 hm
          eta.2.1.property eta.2.2.property.1
  have hprecision₂ :
      (1 - (theta.2.2 : ℝ)) / (theta.2.1 : ℝ) =
        (1 - (eta.2.2 : ℝ)) / (eta.2.1 : ℝ) := by
    calc
      (1 - (theta.2.2 : ℝ)) / (theta.2.1 : ℝ) =
          (n : ℝ) /
            _root_.GD.N0232.N0720.N1498.d012568 n theta.2.1 theta.2.2 ^ 2 :=
        (_root_.GD.N0232.N0720.N1498.d012574 hn
          theta.2.1.property theta.2.2.property.2).symm
      _ = (n : ℝ) /
            _root_.GD.N0232.N0720.N1498.d012568 n eta.2.1 eta.2.2 ^ 2 := by
        rw [hscale₂]
      _ = (1 - (eta.2.2 : ℝ)) / (eta.2.1 : ℝ) :=
        _root_.GD.N0232.N0720.N1498.d012574 hn
          eta.2.1.property eta.2.2.property.2
  have hinverse : (theta.2.1 : ℝ)⁻¹ = (eta.2.1 : ℝ)⁻¹ := by
    calc
      (theta.2.1 : ℝ)⁻¹ =
          (theta.2.2 : ℝ) / (theta.2.1 : ℝ) +
            (1 - (theta.2.2 : ℝ)) / (theta.2.1 : ℝ) := by ring
      _ = (eta.2.2 : ℝ) / (eta.2.1 : ℝ) +
            (1 - (eta.2.2 : ℝ)) / (eta.2.1 : ℝ) := by
        rw [hprecision₁, hprecision₂]
      _ = (eta.2.1 : ℝ)⁻¹ := by ring
  have hq : (theta.2.1 : ℝ) = (eta.2.1 : ℝ) :=
    inv_injective hinverse
  have hz : (theta.2.2 : ℝ) = (eta.2.2 : ℝ) := by
    rw [hq] at hprecision₁
    exact (div_left_inj' (ne_of_gt eta.2.1.property)).mp hprecision₁
  apply Prod.ext
  · exact hlocation
  · apply Prod.ext
    · exact Subtype.ext hq
    · exact Subtype.ext hz




def d015879 (m : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  (m : ℝ) / theta.scale₁ ^ 2


def d015880 (n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  (n : ℝ) / theta.scale₂ ^ 2


def d015881
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0232.N0720.N1486.d015879 m theta +
    _root_.GD.N0232.N0720.N1486.d015880 n theta

theorem d015882
    {m : ℕ} (hm : 0 < m) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1486.d015879 m theta := by
  unfold _root_.GD.N0232.N0720.N1486.d015879
  exact div_pos (Nat.cast_pos.mpr hm) (sq_pos_of_pos theta.scale₁_pos)

theorem d015883
    {n : ℕ} (hn : 0 < n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1486.d015880 n theta := by
  unfold _root_.GD.N0232.N0720.N1486.d015880
  exact div_pos (Nat.cast_pos.mpr hn) (sq_pos_of_pos theta.scale₂_pos)

theorem d015884
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1486.d015881 m n theta := by
  unfold _root_.GD.N0232.N0720.N1486.d015881
  exact add_pos
    (_root_.GD.N0232.N0720.N1486.d015882 hm theta)
    (_root_.GD.N0232.N0720.N1486.d015883 hn theta)



def d015885
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  (_root_.GD.N0232.N0720.N1486.d015881 m n theta)⁻¹



def d015886
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0232.N0720.N1486.d015879 m theta /
    _root_.GD.N0232.N0720.N1486.d015881 m n theta

theorem d015887
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1486.d015885 m n theta := by
  unfold _root_.GD.N0232.N0720.N1486.d015885
  exact inv_pos.mpr (_root_.GD.N0232.N0720.N1486.d015884 hm hn theta)

theorem d015888
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1486.d015886 m n theta ∈ Set.Ioo (0 : ℝ) 1 := by
  have hfirst := _root_.GD.N0232.N0720.N1486.d015882 hm theta
  have hsecond := _root_.GD.N0232.N0720.N1486.d015883 hn theta
  have htotal := _root_.GD.N0232.N0720.N1486.d015884 hm hn theta
  constructor
  · exact div_pos hfirst htotal
  · unfold _root_.GD.N0232.N0720.N1486.d015886
    rw [div_lt_one htotal]
    unfold _root_.GD.N0232.N0720.N1486.d015881
    linarith



def d015889
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1486.d015856 :=
  (theta.location,
    (⟨_root_.GD.N0232.N0720.N1486.d015885 m n theta,
        _root_.GD.N0232.N0720.N1486.d015887 hm hn theta⟩,
      ⟨_root_.GD.N0232.N0720.N1486.d015886 m n theta,
        _root_.GD.N0232.N0720.N1486.d015888 hm hn theta⟩))


theorem d015890
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (m : ℝ) * _root_.GD.N0232.N0720.N1486.d015885 m n theta /
        _root_.GD.N0232.N0720.N1486.d015886 m n theta =
      theta.scale₁ ^ 2 := by
  let A := _root_.GD.N0232.N0720.N1486.d015879 m theta
  let B := _root_.GD.N0232.N0720.N1486.d015880 n theta
  have hA : A ≠ 0 := by
    exact (_root_.GD.N0232.N0720.N1486.d015882 hm theta).ne'
  have hAB : A + B ≠ 0 := by
    exact (_root_.GD.N0232.N0720.N1486.d015884 hm hn theta).ne'
  change (m : ℝ) * (A + B)⁻¹ / (A / (A + B)) = theta.scale₁ ^ 2
  calc
    (m : ℝ) * (A + B)⁻¹ / (A / (A + B)) = (m : ℝ) / A := by
      field_simp [hA, hAB]
    _ = theta.scale₁ ^ 2 := by
      unfold A _root_.GD.N0232.N0720.N1486.d015879
      field_simp [Nat.cast_ne_zero.mpr hm.ne', theta.scale₁_pos.ne']


theorem d015891
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (n : ℝ) * _root_.GD.N0232.N0720.N1486.d015885 m n theta /
        (1 - _root_.GD.N0232.N0720.N1486.d015886 m n theta) =
      theta.scale₂ ^ 2 := by
  let A := _root_.GD.N0232.N0720.N1486.d015879 m theta
  let B := _root_.GD.N0232.N0720.N1486.d015880 n theta
  have hB : B ≠ 0 := by
    exact (_root_.GD.N0232.N0720.N1486.d015883 hn theta).ne'
  have hAB : A + B ≠ 0 := by
    exact (_root_.GD.N0232.N0720.N1486.d015884 hm hn theta).ne'
  have honeSub : 1 - A / (A + B) = B / (A + B) := by
    field_simp [hAB]
    ring
  change
    (n : ℝ) * (A + B)⁻¹ / (1 - A / (A + B)) = theta.scale₂ ^ 2
  rw [honeSub]
  calc
    (n : ℝ) * (A + B)⁻¹ / (B / (A + B)) = (n : ℝ) / B := by
      field_simp [hB, hAB]
    _ = theta.scale₂ ^ 2 := by
      unfold B _root_.GD.N0232.N0720.N1486.d015880
      field_simp [Nat.cast_ne_zero.mpr hn.ne', theta.scale₂_pos.ne']



theorem d015892
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1486.d015873 m n hm hn
        (_root_.GD.N0232.N0720.N1486.d015889 m n hm hn theta) = theta := by
  apply _root_.GD.N0232.N0720.N1499.d014994
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change
        Real.sqrt
            ((m : ℝ) * _root_.GD.N0232.N0720.N1486.d015885 m n theta /
              _root_.GD.N0232.N0720.N1486.d015886 m n theta) =
          theta.scale₁
      rw [_root_.GD.N0232.N0720.N1486.d015890 hm hn theta,
        Real.sqrt_sq_eq_abs, abs_of_pos theta.scale₁_pos]
    · change
        Real.sqrt
            ((n : ℝ) * _root_.GD.N0232.N0720.N1486.d015885 m n theta /
              (1 - _root_.GD.N0232.N0720.N1486.d015886 m n theta)) =
          theta.scale₂
      rw [_root_.GD.N0232.N0720.N1486.d015891 hm hn theta,
        Real.sqrt_sq_eq_abs, abs_of_pos theta.scale₂_pos]



theorem d015893
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Function.Surjective (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn) := by
  intro theta
  exact ⟨_root_.GD.N0232.N0720.N1486.d015889 m n hm hn theta,
    _root_.GD.N0232.N0720.N1486.d015892
      m n hm hn theta⟩


theorem d015894
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (theta : _root_.GD.N0232.N0720.N1486.d015856) :
    _root_.GD.N0232.N0720.N1486.d015889 m n hm hn
        (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn theta) = theta := by
  apply _root_.GD.N0232.N0720.N1486.d015878 m n hm hn
  exact _root_.GD.N0232.N0720.N1486.d015892
    m n hm hn (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn theta)



theorem d015895
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Function.Bijective (_root_.GD.N0232.N0720.N1486.d015873 m n hm hn) :=
  ⟨_root_.GD.N0232.N0720.N1486.d015878 m n hm hn,
    _root_.GD.N0232.N0720.N1486.d015893 m n hm hn⟩



def d015896
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    _root_.GD.N0232.N0720.N1486.d015856 ≃ _root_.GD.N0232.N0720.N1080.d014168 where
  toFun := _root_.GD.N0232.N0720.N1486.d015873 m n hm hn
  invFun := _root_.GD.N0232.N0720.N1486.d015889 m n hm hn
  left_inv :=
    _root_.GD.N0232.N0720.N1486.d015894 m n hm hn
  right_inv :=
    _root_.GD.N0232.N0720.N1486.d015892 m n hm hn


abbrev d015897 :=
  ℝ × (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ))






def d015898
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    _root_.GD.N0232.N0720.N1486.d015856 → _root_.GD.N0232.N0720.N1486.d015897 :=
  fun theta ↦
    let p := _root_.GD.N0232.N0720.N1486.d015873 m n hm hn theta
    (p.location, (⟨p.scale₁, p.scale₁_pos⟩, ⟨p.scale₂, p.scale₂_pos⟩))

@[fun_prop]
theorem d015899
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Continuous (_root_.GD.N0232.N0720.N1486.d015898 m n hm hn) := by
  let p := _root_.GD.N0232.N0720.N1486.d015873 m n hm hn
  have hp : Continuous p :=
    _root_.GD.N0232.N0720.N1486.d015877 m n hm hn
  have hlocation : Continuous (fun theta ↦ (p theta).location) :=
    _root_.GD.N0232.N0720.N1499.d014998.comp hp
  have hscale₁ : Continuous
      (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦
        (⟨(p theta).scale₁, (p theta).scale₁_pos⟩ : Set.Ioi (0 : ℝ))) :=
    (_root_.GD.N0232.N0720.N1499.d014999.comp hp).subtype_mk
      (fun theta ↦ (p theta).scale₁_pos)
  have hscale₂ : Continuous
      (fun theta : _root_.GD.N0232.N0720.N1486.d015856 ↦
        (⟨(p theta).scale₂, (p theta).scale₂_pos⟩ : Set.Ioi (0 : ℝ))) :=
    (_root_.GD.N0232.N0720.N1499.d015000.comp hp).subtype_mk
      (fun theta ↦ (p theta).scale₂_pos)
  exact hlocation.prodMk (hscale₁.prodMk hscale₂)

@[fun_prop]
theorem d015900
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Measurable (_root_.GD.N0232.N0720.N1486.d015898 m n hm hn) :=
  (_root_.GD.N0232.N0720.N1486.d015899 m n hm hn).measurable

theorem d015901
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Function.Injective
      (_root_.GD.N0232.N0720.N1486.d015898 m n hm hn) := by
  intro theta eta heq
  apply _root_.GD.N0232.N0720.N1486.d015878 m n hm hn
  apply _root_.GD.N0232.N0720.N1499.d014994
  have hlocation := congrArg
    (fun x : _root_.GD.N0232.N0720.N1486.d015897 ↦ x.1) heq
  have hscale₁ := congrArg
    (fun x : _root_.GD.N0232.N0720.N1486.d015897 ↦ (x.2.1 : ℝ)) heq
  have hscale₂ := congrArg
    (fun x : _root_.GD.N0232.N0720.N1486.d015897 ↦ (x.2.2 : ℝ)) heq
  apply Prod.ext
  · change theta.1 = eta.1
    exact hlocation
  · apply Prod.ext
    · change _root_.GD.N0232.N0720.N1498.d012567 m theta.2.1 theta.2.2 =
        _root_.GD.N0232.N0720.N1498.d012567 m eta.2.1 eta.2.2
      exact hscale₁
    · change _root_.GD.N0232.N0720.N1498.d012568 n theta.2.1 theta.2.2 =
        _root_.GD.N0232.N0720.N1498.d012568 n eta.2.1 eta.2.2
      exact hscale₂



theorem d015902
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    MeasurableEmbedding
      (_root_.GD.N0232.N0720.N1486.d015898 m n hm hn) := by
  letI : PolishSpace (Set.Ioi (0 : ℝ)) := isOpen_Ioi.polishSpace
  letI : PolishSpace (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo.polishSpace
  exact
    (_root_.GD.N0232.N0720.N1486.d015899 m n hm hn).measurableEmbedding
        (_root_.GD.N0232.N0720.N1486.d015901 m n hm hn)





def d015903
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) :
    Measure _root_.GD.N0232.N0720.N1486.d015897 :=
  (_root_.GD.N0232.N0720.N1486.d015870 rho).map
    (_root_.GD.N0232.N0720.N1486.d015898 m n hm hn)


noncomputable instance d015904
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho] :
    SigmaFinite (_root_.GD.N0232.N0720.N1486.d015903 m n hm hn rho) := by
  unfold _root_.GD.N0232.N0720.N1486.d015903
  exact
    (_root_.GD.N0232.N0720.N1486.d015902
      m n hm hn).sigmaFinite_map

end

end N1486
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1486.d015872
#print axioms _root_.GD.N0232.N0720.N1486.d015902
