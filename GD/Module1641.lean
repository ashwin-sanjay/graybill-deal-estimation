import GD.Module1640

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0079.N0320

noncomputable section

open _root_.GD.N0230.N0642
open _root_.GD.N0230.N0642.d001800


theorem d028014 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (a b : ℝ) :
    (∫ y : ℝ, y ∂μ.map (fun x : ℝ => a * x + b)) = a * (∫ x : ℝ, x ∂μ) + b := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_add (hμ.const_mul a) (integrable_const b)]
  rw [integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]

variable {X : Type*} [MeasurableSpace X]



theorem d028015 (q : _root_.GD.N0230.N0642.d001800 X) (T : X → X)
    (a b : ℝ)
    (h : ∀ x, q.kernel (T x) = (q.kernel x).map (fun y : ℝ => a * y + b)) :
    ∀ x, q.d001802 (T x) = a * q.d001802 x + b := by
  intro x
  letI : IsProbabilityMeasure (q.kernel x) := q.isMarkov.isProbabilityMeasure x
  rw [_root_.GD.N0230.N0642.d001800.d001805, h x, _root_.GD.N0230.N0642.d001800.d001805]
  exact _root_.GD.N0079.N0320.d028014 _ ((q.memLp_id x).integrable (by norm_num)) a b


theorem d028016 (q : _root_.GD.N0230.N0642.d001800 X) (μ : Measure X)
    (T : X → X) (a b : ℝ)
    (h : ∀ᵐ x ∂μ, q.kernel (T x) = (q.kernel x).map (fun y : ℝ => a * y + b)) :
    (fun x => q.d001802 (T x)) =ᵐ[μ] (fun x => a * q.d001802 x + b) := by
  filter_upwards [h] with x hx
  letI : IsProbabilityMeasure (q.kernel x) := q.isMarkov.isProbabilityMeasure x
  rw [_root_.GD.N0230.N0642.d001800.d001805, hx, _root_.GD.N0230.N0642.d001800.d001805]
  exact _root_.GD.N0079.N0320.d028014 _ ((q.memLp_id x).integrable (by norm_num)) a b

open _root_.GD.N0074
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0845 _root_.GD.N0232.N0719.N0900

variable (k : ℕ) (sizes : Fin k → ℕ)

abbrev d028017 := _root_.GD.N0232.N0719.N0900.d009094 k sizes

theorem d028018
    (r : _root_.GD.N0230.N0642.d001800 (_root_.GD.N0079.N0320.d028017 k sizes)) (b a : ℝ)
    (x y : _root_.GD.N0079.N0320.d028017 k sizes)
    (hcov : r.kernel y = Measure.map (fun z : ℝ => b + a * z) (r.kernel x)) :
    r.d001802 y = b + a * r.d001802 x := by
  letI : IsProbabilityMeasure (r.kernel x) := r.isMarkov.isProbabilityMeasure x
  rw [r.d001805, hcov, r.d001805]
  simpa only [add_comm] using
    _root_.GD.N0079.N0320.d028014 (r.kernel x) ((r.memLp_id x).integrable (by norm_num)) a b

theorem d028019
    (r : _root_.GD.N0230.N0642.d001800 (_root_.GD.N0079.N0320.d028017 k sizes)) (b a : ℝ)
    (hcov : ∀ x, r.kernel (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) =
      Measure.map (fun z : ℝ => b + a * z) (r.kernel x)) (x : _root_.GD.N0079.N0320.d028017 k sizes) :
    r.d001802 (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) = b + a * r.d001802 x :=
  _root_.GD.N0079.N0320.d028018 k sizes r b a x _ (hcov x)

theorem d028020
    (r : _root_.GD.N0230.N0642.d001800 (_root_.GD.N0079.N0320.d028017 k sizes)) (b a : ℝ) (ha : 0 < a)
    (hcov : ∀ x, r.kernel (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) =
      Measure.map (fun z : ℝ => b + a * z) (r.kernel x)) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes b a r.d001802 = r.d001802 := by
  funext x
  have h := _root_.GD.N0079.N0320.d028019 k sizes r b a hcov
    (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x)
  rw [_root_.GD.N0232.N0719.N0842.d010910 k sizes b a (ne_of_gt ha)] at h
  exact h.symm

theorem d028021
    (f : _root_.GD.N0079.N0320.d028017 k sizes → ℝ)
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ))
    (b a : ℝ) (ha : 0 < a) (hfixed : _root_.GD.N0232.N0719.N0842.d010911 k sizes b a f = f) :
    _root_.GD.N0074.d027955 k sizes b a ha (_root_.GD.N0074.d027958 k sizes f hf) = _root_.GD.N0074.d027958 k sizes f hf := by
  apply Subtype.ext
  apply Lp.ext
  have hre := _root_.GD.N0074.d027959 k sizes f hf (_root_.GD.N0232.N0719.N0859.d010810 k)
  have hcomp := (_root_.GD.N0074.d027957 k sizes b a ha).ae_eq hre
  filter_upwards [_root_.GD.N0074.d027956 k sizes b a ha (_root_.GD.N0074.d027958 k sizes f hf) (_root_.GD.N0232.N0719.N0859.d010810 k),
    hre, hcomp] with x htrans hraw hinverse
  calc
    (_root_.GD.N0074.d027955 k sizes b a ha (_root_.GD.N0074.d027958 k sizes f hf)).val x =
        _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (_root_.GD.N0074.d027958 k sizes f hf).val x := htrans
    _ = _root_.GD.N0232.N0719.N0842.d010911 k sizes b a f x := by
      unfold _root_.GD.N0232.N0719.N0842.d010911
      exact congrArg (fun z : ℝ => b + a * z) hinverse
    _ = f x := congrFun hfixed x
    _ = (_root_.GD.N0074.d027958 k sizes f hf).val x := hraw.symm

theorem d028022
    (hsizes : ∀ i, 2 ≤ sizes i)
    (r : _root_.GD.N0230.N0642.d001800 (_root_.GD.N0079.N0320.d028017 k sizes))
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp r.d001802 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ))
    (b a : ℝ) (ha : 0 < a)
    (hcov : ∀ x, r.kernel (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) =
      Measure.map (fun z : ℝ => b + a * z) (r.kernel x)) :
    _root_.GD.N0074.d027955 k sizes b a ha
        (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0074.d027958 k sizes r.d001802 hf)).val =
      (_root_.GD.N0074.d023620 k sizes hsizes (_root_.GD.N0074.d027958 k sizes r.d001802 hf)).val := by
  rw [← _root_.GD.N0074.d027964 k sizes hsizes a ha b,
    _root_.GD.N0079.N0320.d028021 k sizes r.d001802 hf b a ha
      (_root_.GD.N0079.N0320.d028020 k sizes r b a ha hcov)]

theorem d028023
    (κ : Kernel (_root_.GD.N0079.N0320.d028017 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 ≠ ∞)
    (b a : ℝ) (ha : 0 < a)
    (hcov : ∀ x, κ (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) =
      Measure.map (fun z : ℝ => b + a * z) (κ x)) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802
      =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 := by
  have hgood := _root_.GD.N0230.N0642.d001800.d001830 κ
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 hfinite
  have hgoodInv := (_root_.GD.N0074.d027957 k sizes b a ha).ae hgood
  filter_upwards [hgood, hgoodInv] with x hx hix
  have he : (_root_.GD.N0230.N0642.d001800.d001834 κ 0).kernel x =
      Measure.map (fun z : ℝ => b + a * z)
        ((_root_.GD.N0230.N0642.d001800.d001834 κ 0).kernel (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x)) := by
    change _root_.GD.N0230.N0642.d001800.d001831 κ 0 x =
      Measure.map (fun z : ℝ => b + a * z)
        (_root_.GD.N0230.N0642.d001800.d001831 κ 0 (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x))
    rw [_root_.GD.N0230.N0642.d001800.d001832 κ 0 hx,
      _root_.GD.N0230.N0642.d001800.d001832 κ 0 hix]
    have H := hcov (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x)
    rw [_root_.GD.N0232.N0719.N0842.d010910 k sizes b a (ne_of_gt ha)] at H
    exact H
  exact (_root_.GD.N0079.N0320.d028018 k sizes (_root_.GD.N0230.N0642.d001800.d001834 κ 0) b a
    (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x) x he).symm

theorem d028024
    (hsizes : ∀ i, 2 ≤ sizes i)
    (κ : Kernel (_root_.GD.N0079.N0320.d028017 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞)
    (b a : ℝ) (ha : 0 < a)
    (hcov : ∀ x, κ (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) =
      Measure.map (fun z : ℝ => b + a * z) (κ x)) :
    _root_.GD.N0074.d027955 k sizes b a ha
        (_root_.GD.N0074.d023620 k sizes hsizes
          (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val =
      (_root_.GD.N0074.d023620 k sizes hsizes
        (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val := by
  let d := _root_.GD.N0079.N0321.d028006 k sizes κ hfinite
  have hd : _root_.GD.N0074.d027955 k sizes b a ha d = d := by
    apply Subtype.ext
    apply Lp.ext
    have hre := _root_.GD.N0079.N0321.d028007 k sizes κ hfinite (_root_.GD.N0232.N0719.N0859.d010810 k)
    have hcomp := (_root_.GD.N0074.d027957 k sizes b a ha).ae_eq hre
    have hmean := _root_.GD.N0079.N0320.d028023 k sizes κ
      (hfinite (_root_.GD.N0232.N0719.N0859.d010810 k)) b a ha hcov
    filter_upwards [_root_.GD.N0074.d027956 k sizes b a ha d (_root_.GD.N0232.N0719.N0859.d010810 k), hre, hcomp, hmean]
      with x htrans hraw hinverse hfixed
    calc
      (_root_.GD.N0074.d027955 k sizes b a ha d).val x = _root_.GD.N0232.N0719.N0842.d010911 k sizes b a d.val x := htrans
      _ = _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 x := by
        unfold _root_.GD.N0232.N0719.N0842.d010911
        exact congrArg (fun z : ℝ => b + a * z) hinverse
      _ = (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 x := hfixed
      _ = d.val x := hraw.symm
  rw [← _root_.GD.N0074.d027964 k sizes hsizes a ha b, hd]

theorem d028025
    (κ : Kernel (_root_.GD.N0079.N0320.d028017 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 ≠ ∞)
    (b a : ℝ) (ha : 0 < a)
    (hcov : ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes,
      κ (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) =
        Measure.map (fun z : ℝ => b + a * z) (κ x)) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802
      =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 := by
  have hgood := _root_.GD.N0230.N0642.d001800.d001830 κ
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) 0 hfinite
  have hgoodInv := (_root_.GD.N0074.d027957 k sizes b a ha).ae hgood
  have hcovInv := (_root_.GD.N0074.d027957 k sizes b a ha).ae hcov
  filter_upwards [hgood, hgoodInv, hcovInv] with x hx hix hcx
  have he : (_root_.GD.N0230.N0642.d001800.d001834 κ 0).kernel x =
      Measure.map (fun z : ℝ => b + a * z)
        ((_root_.GD.N0230.N0642.d001800.d001834 κ 0).kernel (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x)) := by
    change _root_.GD.N0230.N0642.d001800.d001831 κ 0 x =
      Measure.map (fun z : ℝ => b + a * z)
        (_root_.GD.N0230.N0642.d001800.d001831 κ 0 (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x))
    rw [_root_.GD.N0230.N0642.d001800.d001832 κ 0 hx,
      _root_.GD.N0230.N0642.d001800.d001832 κ 0 hix]
    rw [_root_.GD.N0232.N0719.N0842.d010910 k sizes b a (ne_of_gt ha)] at hcx
    exact hcx
  exact (_root_.GD.N0079.N0320.d028018 k sizes (_root_.GD.N0230.N0642.d001800.d001834 κ 0) b a
    (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x) x he).symm

theorem d028026
    (hsizes : ∀ i, 2 ≤ sizes i)
    (κ : Kernel (_root_.GD.N0079.N0320.d028017 k sizes) ℝ) [IsMarkovKernel κ]
    (hfinite : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location ≠ ∞)
    (b a : ℝ) (ha : 0 < a)
    (hcov : ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes,
      κ (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) =
        Measure.map (fun z : ℝ => b + a * z) (κ x)) :
    _root_.GD.N0074.d027955 k sizes b a ha
        (_root_.GD.N0074.d023620 k sizes hsizes
          (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val =
      (_root_.GD.N0074.d023620 k sizes hsizes
        (_root_.GD.N0079.N0321.d028006 k sizes κ hfinite)).val := by
  let d := _root_.GD.N0079.N0321.d028006 k sizes κ hfinite
  have hd : _root_.GD.N0074.d027955 k sizes b a ha d = d := by
    apply Subtype.ext
    apply Lp.ext
    have hre := _root_.GD.N0079.N0321.d028007 k sizes κ hfinite (_root_.GD.N0232.N0719.N0859.d010810 k)
    have hcomp := (_root_.GD.N0074.d027957 k sizes b a ha).ae_eq hre
    have hmean := _root_.GD.N0079.N0320.d028025 k sizes κ
      (hfinite (_root_.GD.N0232.N0719.N0859.d010810 k)) b a ha hcov
    filter_upwards [_root_.GD.N0074.d027956 k sizes b a ha d (_root_.GD.N0232.N0719.N0859.d010810 k), hre, hcomp, hmean]
      with x htrans hraw hinverse hfixed
    calc
      (_root_.GD.N0074.d027955 k sizes b a ha d).val x = _root_.GD.N0232.N0719.N0842.d010911 k sizes b a d.val x := htrans
      _ = _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 x := by
        unfold _root_.GD.N0232.N0719.N0842.d010911
        exact congrArg (fun z : ℝ => b + a * z) hinverse
      _ = (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001802 x := hfixed
      _ = d.val x := hraw.symm
  rw [← _root_.GD.N0074.d027964 k sizes hsizes a ha b, hd]

#print axioms _root_.GD.N0079.N0320.d028014
#print axioms _root_.GD.N0079.N0320.d028015
#print axioms _root_.GD.N0079.N0320.d028016
#print axioms _root_.GD.N0079.N0320.d028018
#print axioms _root_.GD.N0079.N0320.d028019
#print axioms _root_.GD.N0079.N0320.d028020
#print axioms _root_.GD.N0079.N0320.d028021
#print axioms _root_.GD.N0079.N0320.d028022
#print axioms _root_.GD.N0079.N0320.d028023
#print axioms _root_.GD.N0079.N0320.d028024
#print axioms _root_.GD.N0079.N0320.d028025
#print axioms _root_.GD.N0079.N0320.d028026

end
end GD.N0079.N0320
