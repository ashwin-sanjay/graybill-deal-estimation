import GD.Module0280
import GD.Module1252












open MeasureTheory Set
open scoped ContDiff

namespace GD.N0232.N0720.N1264

noncomputable section

open _root_.GD.N0232.N0720.N1290 _root_.GD.N0232.N0720.N1368
open _root_.GD.N0232.N0720.N1352 _root_.GD.N0232.N0720.N1351
open _root_.GD.N0232.N0720.N1270 _root_.GD.N0232.N0720.N1292

def d020244 (p : _root_.GD.N0232.N0720.N1351.d002812) : _root_.GD.N0232.N0720.N1351.d002812 :=
  ![p 1, p 0, p 2]

theorem d020245 : ContDiff ℝ ∞ _root_.GD.N0232.N0720.N1264.d020244 := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [_root_.GD.N0232.N0720.N1264.d020244] <;> fun_prop

theorem d020246 {p : _root_.GD.N0232.N0720.N1351.d002812} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) :
    _root_.GD.N0232.N0720.N1264.d020244 p ∈ _root_.GD.N0232.N0720.N1292.d004155 := by
  change 0 < min (p 1) (p 0) + min (p 2) 0
  change 0 < min (p 0) (p 1) + min (p 2) 0 at hp
  simpa only [min_comm] using hp

theorem d020247 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)
    (p : _root_.GD.N0232.N0720.N1351.d002812) :
    _root_.GD.N0232.N0720.N1292.d004162 q (fun _ ↦ 1) mu p = _root_.GD.N0232.N0720.N1290.d004139 q (_root_.GD.N0232.N0720.N1292.d004153 p) mu := by
  simp only [_root_.GD.N0232.N0720.N1292.d004162, _root_.GD.N0232.N0720.N1292.d004161, _root_.GD.N0232.N0720.N1290.d004139, one_mul]

theorem d020248 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    {p : _root_.GD.N0232.N0720.N1351.d002812} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) :
    0 < _root_.GD.N0232.N0720.N1292.d004162 q (fun _ ↦ 1) mu p := by
  rw [_root_.GD.N0232.N0720.N1264.d020247]
  exact _root_.GD.N0232.N0720.N1290.d004146 q (_root_.GD.N0232.N0720.N1292.d004153 p) (by unfold _root_.GD.N0232.N0720.N1292.d004153; fun_prop)
    (_root_.GD.N0232.N0720.N1292.d004159 hp) mu

theorem d020249 (q : ℝ) {phi psi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ}
    (hphi : Continuous phi) (hpsi : Continuous psi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {p : _root_.GD.N0232.N0720.N1351.d002812} (hp : p ∈ _root_.GD.N0232.N0720.N1292.d004155) :
    _root_.GD.N0232.N0720.N1292.d004162 q (fun t ↦ phi t - psi t) mu p =
      _root_.GD.N0232.N0720.N1292.d004162 q phi mu p - _root_.GD.N0232.N0720.N1292.d004162 q psi mu p := by
  unfold _root_.GD.N0232.N0720.N1292.d004162
  have heq : _root_.GD.N0232.N0720.N1292.d004161 q (fun t ↦ phi t - psi t) p =
      fun t ↦ _root_.GD.N0232.N0720.N1292.d004161 q phi p t - _root_.GD.N0232.N0720.N1292.d004161 q psi p t := by
    funext t
    simp only [_root_.GD.N0232.N0720.N1292.d004161, sub_mul]
  rw [heq, integral_sub (_root_.GD.N0232.N0720.N1292.d004164 q hphi mu hp)
    (_root_.GD.N0232.N0720.N1292.d004164 q hpsi mu hp)]

theorem d020250 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)
    (p : _root_.GD.N0232.N0720.N1351.d002812) :
    _root_.GD.N0232.N0720.N1270.d020230 mu p = 1 - _root_.GD.N0232.N0720.N1292.d004162 (5 / 2) (fun t ↦ (t : ℝ)) mu (_root_.GD.N0232.N0720.N1264.d020244 p) /
      _root_.GD.N0232.N0720.N1292.d004162 (5 / 2) (fun _ ↦ 1) mu (_root_.GD.N0232.N0720.N1264.d020244 p) := by
  dsimp [_root_.GD.N0232.N0720.N1270.d020230, _root_.GD.N0232.N0720.N1368.d020209, _root_.GD.N0232.N0720.N1290.d004140, _root_.GD.N0232.N0720.N1290.d004139,
    _root_.GD.N0232.N0720.N1292.d004162, _root_.GD.N0232.N0720.N1292.d004161, _root_.GD.N0232.N0720.N1292.d004153, _root_.GD.N0232.N0720.N1264.d020244, _root_.GD.N0232.N0720.N1368.d020208]
  simp only [one_mul]


theorem d020251 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1270.d020230 mu) _root_.GD.N0232.N0720.N1292.d004155 := by
  have hD := (_root_.GD.N0232.N0720.N1292.d004173 (5 / 2) continuous_const mu
    (phi := fun _ ↦ 1)).comp _root_.GD.N0232.N0720.N1264.d020245.contDiffOn (fun _ hp ↦ _root_.GD.N0232.N0720.N1264.d020246 hp)
  have hT := (_root_.GD.N0232.N0720.N1292.d004173 (5 / 2) continuous_subtype_val mu).comp
    _root_.GD.N0232.N0720.N1264.d020245.contDiffOn (fun _ hp ↦ _root_.GD.N0232.N0720.N1264.d020246 hp)
  have hratio := hT.div hD (fun p hp ↦ ne_of_gt (_root_.GD.N0232.N0720.N1264.d020248 (5 / 2) mu (_root_.GD.N0232.N0720.N1264.d020246 hp)))
  apply (contDiffOn_const.sub hratio).congr
  intro p hp
  exact _root_.GD.N0232.N0720.N1264.d020250 mu p

theorem d020252 {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) : _root_.GD.N0232.N0720.N1351.d002814 x ∈ _root_.GD.N0232.N0720.N1292.d004155 := by
  apply _root_.GD.N0232.N0720.N1292.d004160
  · exact hx.1
  · exact hx.2
  · exact div_nonneg (sq_nonneg _) (by norm_num)

def d020253 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] : _root_.GD.N0232.N0720.N1270.d020235 mu where
  domain := _root_.GD.N0232.N0720.N1292.d004155
  isOpen_domain := _root_.GD.N0232.N0720.N1292.d004157
  smooth := _root_.GD.N0232.N0720.N1264.d020251 mu
  mapsTo := fun _ hx ↦ _root_.GD.N0232.N0720.N1264.d020252 hx


def d020254 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1351.d002812 :=
  ![x 3, x 2, _root_.GD.N0232.N0720.N1352.d002742 x ^ 2 / 2]

def d020255 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] _root_.GD.N0232.N0720.N1351.d002812 :=
  ContinuousLinearMap.pi ![_root_.GD.N0232.N0720.N1352.d002741 3, _root_.GD.N0232.N0720.N1352.d002741 2, _root_.GD.N0232.N0720.N1352.d002742 x • _root_.GD.N0232.N0720.N1352.d002743]

theorem d020256 (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1264.d020254 x = _root_.GD.N0232.N0720.N1264.d020244 (_root_.GD.N0232.N0720.N1351.d002814 x) := rfl

theorem d020257 {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) : _root_.GD.N0232.N0720.N1264.d020254 x ∈ _root_.GD.N0232.N0720.N1292.d004155 := by
  rw [_root_.GD.N0232.N0720.N1264.d020256]
  exact _root_.GD.N0232.N0720.N1264.d020246 (_root_.GD.N0232.N0720.N1264.d020252 hx)

theorem d020258 : ContDiff ℝ ∞ _root_.GD.N0232.N0720.N1264.d020254 := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [_root_.GD.N0232.N0720.N1264.d020254, _root_.GD.N0232.N0720.N1352.d002742] <;> fun_prop

theorem d020259 (x : _root_.GD.N0232.N0720.N1352.d002739) :
    HasFDerivAt _root_.GD.N0232.N0720.N1264.d020254 (_root_.GD.N0232.N0720.N1264.d020255 x) x := by
  unfold _root_.GD.N0232.N0720.N1264.d020255
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1264.d020254, _root_.GD.N0232.N0720.N1352.d002741] using hasFDerivAt_apply (3 : Fin 4) x
  · simpa [_root_.GD.N0232.N0720.N1264.d020254, _root_.GD.N0232.N0720.N1352.d002741] using hasFDerivAt_apply (2 : Fin 4) x
  · simpa [_root_.GD.N0232.N0720.N1264.d020254] using _root_.GD.N0232.N0720.N1351.d002816 x

def d020260 (q : ℝ) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  _root_.GD.N0232.N0720.N1292.d004162 q phi mu (_root_.GD.N0232.N0720.N1264.d020254 x)

def d020261 (q : ℝ) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ :=
  (-q * _root_.GD.N0232.N0720.N1264.d020260 (q + 1) (fun t ↦ phi t * (t : ℝ)) mu x) • _root_.GD.N0232.N0720.N1352.d002741 2 +
  (-q * _root_.GD.N0232.N0720.N1264.d020260 (q + 1) (fun t ↦ phi t * (1 - (t : ℝ))) mu x) • _root_.GD.N0232.N0720.N1352.d002741 3 +
  (-q * _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1264.d020260 (q + 1) (fun t ↦ phi t * ((t : ℝ) * (1 - (t : ℝ)))) mu x) • _root_.GD.N0232.N0720.N1352.d002743

theorem d020262 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1264.d020260 q phi mu) (_root_.GD.N0232.N0720.N1264.d020261 q phi mu x) x := by
  apply ((_root_.GD.N0232.N0720.N1292.d004172 q hphi mu (_root_.GD.N0232.N0720.N1264.d020257 hx)).comp x
    (_root_.GD.N0232.N0720.N1264.d020259 x)).congr_fderiv
  ext v
  simp only [_root_.GD.N0232.N0720.N1264.d020261, _root_.GD.N0232.N0720.N1264.d020260, _root_.GD.N0232.N0720.N1292.d004167, _root_.GD.N0232.N0720.N1264.d020255, _root_.GD.N0232.N0720.N1292.d004152,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply, _root_.GD.N0232.N0720.N1352.d002744, _root_.GD.N0232.N0720.N1352.d002745,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, smul_eq_mul]
  ring

theorem d020263 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1264.d020260 q phi mu) _root_.GD.N0232.N0720.N1270.d020224 :=
  (_root_.GD.N0232.N0720.N1292.d004173 q hphi mu).comp _root_.GD.N0232.N0720.N1264.d020258.contDiffOn
    (fun _ hx ↦ _root_.GD.N0232.N0720.N1264.d020257 hx)

theorem d020264 (q : ℝ) {phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ} (hphi : Continuous phi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 q phi mu) x = _root_.GD.N0232.N0720.N1264.d020261 q phi mu x :=
  (_root_.GD.N0232.N0720.N1264.d020262 q hphi mu hx).fderiv

theorem d020265 (q : ℝ) (phi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x v : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0720.N1264.d020261 q phi mu x v =
      -q * _root_.GD.N0232.N0720.N1264.d020260 (q + 1) (fun t ↦ phi t * (t : ℝ)) mu x * v 2 +
      -q * _root_.GD.N0232.N0720.N1264.d020260 (q + 1) (fun t ↦ phi t * (1 - (t : ℝ))) mu x * v 3 +
      -q * _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1264.d020260 (q + 1) (fun t ↦ phi t * ((t : ℝ) * (1 - (t : ℝ)))) mu x *
        (v 1 - v 0) := by
  simp only [_root_.GD.N0232.N0720.N1264.d020261, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    _root_.GD.N0232.N0720.N1352.d002744, _root_.GD.N0232.N0720.N1352.d002745, _root_.GD.N0232.N0720.N1352.d002742, smul_eq_mul]

theorem d020266 (q : ℝ) {phi psi : _root_.GD.N0232.N0720.N1290.d004131 → ℝ}
    (hphi : Continuous phi) (hpsi : Continuous psi)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu] {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    _root_.GD.N0232.N0720.N1264.d020260 q (fun t ↦ phi t - psi t) mu x = _root_.GD.N0232.N0720.N1264.d020260 q phi mu x - _root_.GD.N0232.N0720.N1264.d020260 q psi mu x :=
  _root_.GD.N0232.N0720.N1264.d020249 q hphi hpsi mu (_root_.GD.N0232.N0720.N1264.d020257 hx)

def d020267 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0720.N1352.d002739 → ℝ := _root_.GD.N0232.N0720.N1264.d020260 (5 / 2) (fun _ ↦ 1) mu

def d020268 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0720.N1352.d002739 → ℝ :=
  _root_.GD.N0232.N0720.N1264.d020260 (5 / 2) (fun t ↦ 1 - (t : ℝ)) mu

def d020269 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  x 0 * _root_.GD.N0232.N0720.N1264.d020267 mu x + _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1264.d020268 mu x

theorem d020270 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) : 0 < _root_.GD.N0232.N0720.N1264.d020267 mu x :=
  _root_.GD.N0232.N0720.N1264.d020248 (5 / 2) mu (_root_.GD.N0232.N0720.N1264.d020257 hx)

theorem d020271 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    _root_.GD.N0232.N0720.N1264.d020269 mu x = _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1270.d020230 mu ∘ _root_.GD.N0232.N0720.N1351.d002814) x * _root_.GD.N0232.N0720.N1264.d020267 mu x := by
  have hD := ne_of_gt (_root_.GD.N0232.N0720.N1264.d020270 mu hx)
  have hC := _root_.GD.N0232.N0720.N1264.d020266 (5 / 2) continuous_const continuous_subtype_val mu hx
    (phi := fun _ ↦ 1)
  unfold _root_.GD.N0232.N0720.N1264.d020269 _root_.GD.N0232.N0720.N1264.d020268
  rw [hC]
  simp only [_root_.GD.N0232.N0720.N1352.d002804, Function.comp_apply, _root_.GD.N0232.N0720.N1264.d020250,
    ← _root_.GD.N0232.N0720.N1264.d020256]
  change x 0 * _root_.GD.N0232.N0720.N1264.d020267 mu x + _root_.GD.N0232.N0720.N1352.d002742 x *
      (_root_.GD.N0232.N0720.N1264.d020267 mu x - _root_.GD.N0232.N0720.N1264.d020260 (5 / 2) (fun t ↦ (t : ℝ)) mu x) =
    (x 0 + _root_.GD.N0232.N0720.N1352.d002742 x * (1 - _root_.GD.N0232.N0720.N1264.d020260 (5 / 2) (fun t ↦ (t : ℝ)) mu x / _root_.GD.N0232.N0720.N1264.d020267 mu x)) * _root_.GD.N0232.N0720.N1264.d020267 mu x
  field_simp [hD] <;> ring

def d020272 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ :=
  _root_.GD.N0232.N0720.N1264.d020267 mu x • _root_.GD.N0232.N0720.N1352.d002741 0 + x 0 • _root_.GD.N0232.N0720.N1264.d020261 (5 / 2) (fun _ ↦ 1) mu x +
    _root_.GD.N0232.N0720.N1264.d020268 mu x • _root_.GD.N0232.N0720.N1352.d002743 +
      _root_.GD.N0232.N0720.N1352.d002742 x • _root_.GD.N0232.N0720.N1264.d020261 (5 / 2) (fun t ↦ 1 - (t : ℝ)) mu x

theorem d020273 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1264.d020269 mu) (_root_.GD.N0232.N0720.N1264.d020272 mu x) x := by
  have hM := _root_.GD.N0232.N0720.N1264.d020262 (5 / 2) continuous_const mu hx (phi := fun _ ↦ 1)
  have hC := _root_.GD.N0232.N0720.N1264.d020262 (5 / 2) (by fun_prop) mu hx
    (phi := fun t ↦ 1 - (t : ℝ))
  apply (((hasFDerivAt_apply (0 : Fin 4) x).fun_mul hM).fun_add
    ((_root_.GD.N0232.N0720.N1352.d002746 x).fun_mul hC)).congr_fderiv
  ext v
  simp only [_root_.GD.N0232.N0720.N1264.d020272, _root_.GD.N0232.N0720.N1264.d020267, _root_.GD.N0232.N0720.N1264.d020268, _root_.GD.N0232.N0720.N1352.d002741,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

private theorem d020274 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)
    [IsFiniteMeasure mu] {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    _root_.GD.N0232.N0720.N1264.d020260 q (fun t ↦ (1 - (t : ℝ)) * (1 - (t : ℝ))) mu x =
      _root_.GD.N0232.N0720.N1264.d020260 q (fun t ↦ 1 - (t : ℝ)) mu x -
        _root_.GD.N0232.N0720.N1264.d020260 q (fun t ↦ (t : ℝ) * (1 - (t : ℝ))) mu x := by
  rw [← _root_.GD.N0232.N0720.N1264.d020266 q (by fun_prop) (by fun_prop) mu hx]
  congr 1
  funext t
  ring


theorem d020275 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020269 mu) x (_root_.GD.N0232.N0720.N1352.d002740 2) =
        x 0 * fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020267 mu) x (_root_.GD.N0232.N0720.N1352.d002740 2) - fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020267 mu) x (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
      fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020269 mu) x (_root_.GD.N0232.N0720.N1352.d002740 3) =
        x 1 * fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020267 mu) x (_root_.GD.N0232.N0720.N1352.d002740 3) - fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020267 mu) x (_root_.GD.N0232.N0720.N1352.d002740 1) := by
  have hM := _root_.GD.N0232.N0720.N1264.d020264 (5 / 2) continuous_const mu hx (phi := fun _ ↦ 1)
  have hN := (_root_.GD.N0232.N0720.N1264.d020273 mu hx).fderiv
  have hcomm : (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (1 - (t : ℝ)) * (t : ℝ)) =
      (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ) * (1 - (t : ℝ))) := by funext t; ring
  rw [hN]
  change _ = x 0 * fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 (5 / 2) (fun _ ↦ 1) mu) x (_root_.GD.N0232.N0720.N1352.d002740 2) -
      fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 (5 / 2) (fun _ ↦ 1) mu) x (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
    _ = x 1 * fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 (5 / 2) (fun _ ↦ 1) mu) x (_root_.GD.N0232.N0720.N1352.d002740 3) -
      fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 (5 / 2) (fun _ ↦ 1) mu) x (_root_.GD.N0232.N0720.N1352.d002740 1)
  rw [hM]
  simp only [_root_.GD.N0232.N0720.N1264.d020272, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    _root_.GD.N0232.N0720.N1352.d002744, _root_.GD.N0232.N0720.N1352.d002745, _root_.GD.N0232.N0720.N1264.d020265,
    smul_eq_mul, one_mul, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, hcomm]
  rw [_root_.GD.N0232.N0720.N1264.d020274 (5 / 2 + 1) mu hx]
  simp only [_root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0720.N1352.d002742, Pi.single_apply]
  norm_num [Fin.ext_iff]
  constructor <;> ring

theorem d020276 (x : _root_.GD.N0232.N0720.N1352.d002739) (a : ℝ) (t : _root_.GD.N0232.N0720.N1290.d004131) :
    _root_.GD.N0232.N0720.N1292.d004153 (_root_.GD.N0232.N0720.N1264.d020254 (_root_.GD.N0232.N0720.N1352.d002795 x a)) t = a ^ 2 * _root_.GD.N0232.N0720.N1292.d004153 (_root_.GD.N0232.N0720.N1264.d020254 x) t := by
  simp [_root_.GD.N0232.N0720.N1292.d004153, _root_.GD.N0232.N0720.N1264.d020254, _root_.GD.N0232.N0720.N1352.d002795, _root_.GD.N0232.N0720.N1352.d002793, _root_.GD.N0232.N0720.N1352.d002794,
    _root_.GD.N0232.N0720.N1352.d002742, _root_.GD.N0232.N0720.N1352.d002740, smul_eq_mul]
  ring


theorem d020277 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224)
    {a : ℝ} (ha : 0 < a) : a ^ 5 * _root_.GD.N0232.N0720.N1264.d020267 mu (_root_.GD.N0232.N0720.N1352.d002795 x a) = _root_.GD.N0232.N0720.N1264.d020267 mu x := by
  have hpow : (a ^ 2) ^ (-(5 / 2 : ℝ)) = (a ^ 5)⁻¹ := by
    convert! _root_.GD.N0232.N0720.N1358.d004012
      (a ^ 2) (sq_nonneg a) 5 using 1 <;>
      norm_num [Real.sqrt_sq ha.le]
  have hkernel : ∀ t : _root_.GD.N0232.N0720.N1290.d004131,
      _root_.GD.N0232.N0720.N1292.d004161 (5 / 2) (fun _ ↦ 1) (_root_.GD.N0232.N0720.N1264.d020254 (_root_.GD.N0232.N0720.N1352.d002795 x a)) t =
        (a ^ 5)⁻¹ * _root_.GD.N0232.N0720.N1292.d004161 (5 / 2) (fun _ ↦ 1) (_root_.GD.N0232.N0720.N1264.d020254 x) t := by
    intro t
    simp only [_root_.GD.N0232.N0720.N1292.d004161, one_mul, _root_.GD.N0232.N0720.N1264.d020276]
    rw [Real.mul_rpow (sq_nonneg a) (_root_.GD.N0232.N0720.N1292.d004159 (_root_.GD.N0232.N0720.N1264.d020257 hx) t).le, hpow]
  unfold _root_.GD.N0232.N0720.N1264.d020267 _root_.GD.N0232.N0720.N1264.d020260 _root_.GD.N0232.N0720.N1292.d004162
  simp_rw [hkernel]
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 5 (ne_of_gt ha)), one_mul]

def d020278 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    _root_.GD.N0232.N0720.N1270.d020238 5 (_root_.GD.N0232.N0720.N1270.d020230 mu) where
  M := _root_.GD.N0232.N0720.N1264.d020267 mu
  N := _root_.GD.N0232.N0720.N1264.d020269 mu
  smooth_M := _root_.GD.N0232.N0720.N1264.d020263 (5 / 2) continuous_const mu
  positive_M := fun _ hx ↦ _root_.GD.N0232.N0720.N1264.d020270 mu hx
  numerator := fun _ hx ↦ _root_.GD.N0232.N0720.N1264.d020271 mu hx
  pde := fun _ hx ↦ _root_.GD.N0232.N0720.N1264.d020275 mu hx
  homogeneous := fun _ hx _ ha ↦ _root_.GD.N0232.N0720.N1264.d020277 mu hx ha


theorem d020279 : _root_.GD.N0232.N0720.N1270.d020239 := by
  intro mu
  exact ⟨⟨_root_.GD.N0232.N0720.N1264.d020253 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)⟩, ⟨_root_.GD.N0232.N0720.N1264.d020278 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)⟩⟩

end
end GD.N0232.N0720.N1264

#print axioms _root_.GD.N0232.N0720.N1264.d020275
#print axioms _root_.GD.N0232.N0720.N1264.d020279
