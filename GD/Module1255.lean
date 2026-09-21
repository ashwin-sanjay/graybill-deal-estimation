import GD.Module1254

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0987

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1290 _root_.GD.N0232.N0720.N1368
open _root_.GD.N0232.N0720.N1352 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1264

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]


def d020293 (i : I) (A B : ℝ) : I → ℝ := fun j => if j = i then A else B

theorem d020294 (p : I → ℝ) (hsum : ∑ j, p j = 1)
    (i : I) (A B : ℝ) :
    (∑ j, p j * _root_.GD.N0232.N0719.N0987.d020293 i A B j) = p i * A + (1 - p i) * B := by
  have heq : ∀ j, p j * _root_.GD.N0232.N0719.N0987.d020293 i A B j =
      p j * B + if j = i then p j * (A - B) else 0 := by
    intro j
    by_cases hj : j = i
    · simp [_root_.GD.N0232.N0719.N0987.d020293, hj]
      ring
    · simp [_root_.GD.N0232.N0719.N0987.d020293, hj]
  simp_rw [heq]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
  simp
  ring


def d020295 (p y r : I → ℝ) : ℝ :=
  (∑ j, p j * r j) + ((∑ j, p j * y j ^ 2) - (∑ j, p j * y j) ^ 2) / 2


def d020296 (i : I) (x : _root_.GD.N0232.N0720.N1352.d002739) : (I → ℝ) × (I → ℝ) :=
  (_root_.GD.N0232.N0719.N0987.d020293 i (x 0) (x 1), _root_.GD.N0232.N0719.N0987.d020293 i (x 2) (x 3))

theorem d020297 (p : I → ℝ) (hsum : ∑ j, p j = 1)
    (i : I) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0719.N0987.d020295 p (_root_.GD.N0232.N0719.N0987.d020296 i x).1 (_root_.GD.N0232.N0719.N0987.d020296 i x).2 =
      x 3 * (1 - p i) + x 2 * p i +
        (_root_.GD.N0232.N0720.N1352.d002742 x ^ 2 / 2) * p i * (1 - p i) := by
  have hsquare : ∀ j, _root_.GD.N0232.N0719.N0987.d020293 i (x 0) (x 1) j ^ 2 =
      _root_.GD.N0232.N0719.N0987.d020293 i (x 0 ^ 2) (x 1 ^ 2) j := by
    intro j
    by_cases hj : j = i <;> simp [_root_.GD.N0232.N0719.N0987.d020293, hj]
  simp only [_root_.GD.N0232.N0719.N0987.d020295, _root_.GD.N0232.N0719.N0987.d020296, hsquare, _root_.GD.N0232.N0719.N0987.d020294 p hsum]
  unfold _root_.GD.N0232.N0720.N1352.d002742
  ring

def d020298 (q : ℝ) (mu : Measure Ω) (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131)
    (x : (I → ℝ) × (I → ℝ)) : ℝ :=
  (∫ z, (∑ j, (t j z : ℝ) * x.1 j) *
    (_root_.GD.N0232.N0719.N0987.d020295 (fun j => (t j z : ℝ)) x.1 x.2) ^ (-q) ∂mu) /
  (∫ z, (_root_.GD.N0232.N0719.N0987.d020295 (fun j => (t j z : ℝ)) x.1 x.2) ^ (-q) ∂mu)



theorem d020299 (q : ℝ) (mu : Measure Ω)
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ j, Measurable (t j))
    (hsum : ∀ᵐ z ∂mu, ∑ j, (t j z : ℝ) = 1)
    (i : I) (x : _root_.GD.N0232.N0720.N1352.d002739) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (hphi : Measurable phi) :
    (∫ z, phi (t i z) *
      (_root_.GD.N0232.N0719.N0987.d020295 (fun j => (t j z : ℝ)) (_root_.GD.N0232.N0719.N0987.d020296 i x).1 (_root_.GD.N0232.N0719.N0987.d020296 i x).2) ^ (-q) ∂mu) =
    ∫ s, phi s * (_root_.GD.N0232.N0720.N1368.d020208 (x 3) (x 2) (_root_.GD.N0232.N0720.N1352.d002742 x ^ 2 / 2) s) ^ (-q)
      ∂Measure.map (t i) mu := by
  rw [integral_map (ht i).aemeasurable
    (show AEStronglyMeasurable
      (fun s : _root_.GD.N0232.N0720.N1290.d004131 => phi s *
        (_root_.GD.N0232.N0720.N1368.d020208 (x 3) (x 2) (_root_.GD.N0232.N0720.N1352.d002742 x ^ 2 / 2) s) ^ (-q))
        (Measure.map (t i) mu) from (by unfold _root_.GD.N0232.N0720.N1368.d020208; fun_prop))]
  apply integral_congr_ae
  filter_upwards [hsum] with z hz
  rw [_root_.GD.N0232.N0719.N0987.d020297 _ hz]
  rfl



theorem d020300 (q : ℝ) (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ j, Measurable (t j))
    (hsum : ∀ᵐ z ∂mu, ∑ j, (t j z : ℝ) = 1)
    (i : I) {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    _root_.GD.N0232.N0719.N0987.d020298 q mu t (_root_.GD.N0232.N0719.N0987.d020296 i x) =
      x 1 + (x 0 - x 1) * _root_.GD.N0232.N0720.N1368.d020209 q (Measure.map (t i) mu)
        (x 3) (x 2) (_root_.GD.N0232.N0720.N1352.d002742 x ^ 2 / 2) := by
  let nu := Measure.map (t i) mu
  letI : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map (ht i).aemeasurable
  let P := _root_.GD.N0232.N0720.N1368.d020208 (x 3) (x 2) (_root_.GD.N0232.N0720.N1352.d002742 x ^ 2 / 2)
  have hP : Continuous P := by unfold P _root_.GD.N0232.N0720.N1368.d020208; fun_prop
  have hpos : ∀ s, 0 < P s := by
    intro s
    exact _root_.GD.N0232.N0720.N1292.d004159 (_root_.GD.N0232.N0720.N1264.d020246 (_root_.GD.N0232.N0720.N1264.d020252 hx)) s
  have hmass := _root_.GD.N0232.N0720.N1290.d004135 q continuous_const hP hpos nu
    (phi := fun _ => (1 : ℝ))
  simp only [one_mul] at hmass
  have hmom := _root_.GD.N0232.N0720.N1290.d004135 q continuous_subtype_val hP hpos nu
  have hden : 0 < _root_.GD.N0232.N0720.N1290.d004139 q P nu := _root_.GD.N0232.N0720.N1290.d004146 q P hP hpos nu
  have hnum :
      (∫ z, (∑ j, (t j z : ℝ) * (_root_.GD.N0232.N0719.N0987.d020296 i x).1 j) *
        _root_.GD.N0232.N0719.N0987.d020295 (fun j => (t j z : ℝ)) (_root_.GD.N0232.N0719.N0987.d020296 i x).1 (_root_.GD.N0232.N0719.N0987.d020296 i x).2 ^ (-q) ∂mu) =
      x 1 * _root_.GD.N0232.N0720.N1290.d004139 q P nu + (x 0 - x 1) *
        (∫ s, (s : ℝ) * P s ^ (-q) ∂nu) := by
    have heq :
        (∫ z, (∑ j, (t j z : ℝ) * (_root_.GD.N0232.N0719.N0987.d020296 i x).1 j) *
          _root_.GD.N0232.N0719.N0987.d020295 (fun j => (t j z : ℝ)) (_root_.GD.N0232.N0719.N0987.d020296 i x).1 (_root_.GD.N0232.N0719.N0987.d020296 i x).2 ^ (-q) ∂mu) =
        ∫ z, (x 1 + (x 0 - x 1) * (t i z : ℝ)) *
          _root_.GD.N0232.N0719.N0987.d020295 (fun j => (t j z : ℝ)) (_root_.GD.N0232.N0719.N0987.d020296 i x).1 (_root_.GD.N0232.N0719.N0987.d020296 i x).2 ^ (-q) ∂mu := by
      apply integral_congr_ae
      filter_upwards [hsum] with z hz
      dsimp only [_root_.GD.N0232.N0719.N0987.d020296]
      rw [_root_.GD.N0232.N0719.N0987.d020294 _ hz]
      ring
    rw [heq, _root_.GD.N0232.N0719.N0987.d020299 q mu t ht hsum i x
      (fun s : _root_.GD.N0232.N0720.N1290.d004131 => x 1 + (x 0 - x 1) * (s : ℝ)) (by fun_prop)]
    change (∫ s, (x 1 + (x 0 - x 1) * (s : ℝ)) * P s ^ (-q) ∂nu) = _
    have heq' : (fun s : _root_.GD.N0232.N0720.N1290.d004131 => (x 1 + (x 0 - x 1) * (s : ℝ)) * P s ^ (-q)) =
        fun s => x 1 * P s ^ (-q) + (x 0 - x 1) * ((s : ℝ) * P s ^ (-q)) := by
      funext s
      ring
    rw [heq', integral_add (hmass.const_mul _) (hmom.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  unfold _root_.GD.N0232.N0719.N0987.d020298
  rw [hnum]
  have hd := _root_.GD.N0232.N0719.N0987.d020299 q mu t ht hsum i x (fun _ => 1) measurable_const
  simp only [one_mul] at hd
  rw [hd]
  change (_ + _) / _root_.GD.N0232.N0720.N1290.d004139 q P nu = x 1 + (x 0 - x 1) * _root_.GD.N0232.N0720.N1290.d004140 q P nu
  unfold _root_.GD.N0232.N0720.N1290.d004140
  field_simp [hden.ne']



theorem d020301 (D : ℕ) (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ j, Measurable (t j))
    (hsum : ∀ᵐ z ∂mu, ∑ j, (t j z : ℝ) = 1)
    (i : I) {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    _root_.GD.N0232.N0719.N0987.d020298 ((D : ℝ) / 2) mu t (_root_.GD.N0232.N0719.N0987.d020296 i x) =
      _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1308.d020280 D (Measure.map (t i) mu) ∘
        _root_.GD.N0232.N0720.N1351.d002814) x := by
  rw [_root_.GD.N0232.N0719.N0987.d020300 _ mu t ht hsum i hx]
  simp only [_root_.GD.N0232.N0720.N1352.d002804, Function.comp_apply,
    _root_.GD.N0232.N0720.N1308.d020280, _root_.GD.N0232.N0720.N1292.d004162, _root_.GD.N0232.N0720.N1292.d004161,
    _root_.GD.N0232.N0720.N1264.d020244, _root_.GD.N0232.N0720.N1351.d002814,
    _root_.GD.N0232.N0720.N1292.d004153, _root_.GD.N0232.N0720.N1368.d020209, _root_.GD.N0232.N0720.N1290.d004140, _root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1368.d020208,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, one_mul]
  unfold _root_.GD.N0232.N0720.N1352.d002742
  ring

end
end GD.N0232.N0719.N0987

#print axioms _root_.GD.N0232.N0719.N0987.d020301
