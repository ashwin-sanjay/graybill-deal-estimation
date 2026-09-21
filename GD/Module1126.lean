import GD.Module1125


























open Filter MeasureTheory Topology
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1030

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0691
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1037
open _root_.GD.N0232.N0720.N1031
open _root_.GD.N0232.N0720.N1039
open _root_.GD.N0232.N0720.N1108
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1113
open _root_.GD.N0232.N0720.N1148
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false




def d018092 (a b A M c : ℝ) : ℝ :=
  (2 * a * b * M + b ^ 2 * (A - 1)) / _root_.GD.N0232.N0720.N1039.d016521 A c

theorem d018093 {A c : ℝ} (hA : 1 ≤ A) (hc : 0 < c) :
    1 ≤ _root_.GD.N0232.N0720.N1039.d016521 A c := by
  unfold _root_.GD.N0232.N0720.N1039.d016521
  nlinarith

theorem d018094 {A c : ℝ} (hA : 1 ≤ A) (hc : 0 < c) :
    0 ≤ c * (A - 1) / _root_.GD.N0232.N0720.N1039.d016521 A c :=
  div_nonneg (mul_nonneg hc.le (by linarith)) (_root_.GD.N0232.N0720.N1039.d016524 hA hc).le

theorem d018095 {A c : ℝ} (hA : 1 ≤ A) (hc : 0 < c) :
    c * (A - 1) / _root_.GD.N0232.N0720.N1039.d016521 A c ≤ 1 := by
  rw [div_le_one (_root_.GD.N0232.N0720.N1039.d016524 hA hc)]
  unfold _root_.GD.N0232.N0720.N1039.d016521
  linarith



theorem d018096 (a b A M c : ℝ) (ht : _root_.GD.N0232.N0720.N1039.d016521 A c ≠ 0) :
    _root_.GD.N0232.N0720.N1031.d017133 a b A M c =
      _root_.GD.N0232.N0720.N1031.d017133 a 0 A M c +
        c * (A - 1) * (2 * a * b * M + b ^ 2 * (A - 1)) / _root_.GD.N0232.N0720.N1039.d016521 A c := by
  unfold _root_.GD.N0232.N0720.N1031.d017133
  field_simp
  ring


theorem d018097 (a b A M c : ℝ) (ht : _root_.GD.N0232.N0720.N1039.d016521 A c ≠ 0) :
    (2 * a * b * M + b ^ 2 * (A - 1)) -
        c * (A - 1) * (2 * a * b * M + b ^ 2 * (A - 1)) / _root_.GD.N0232.N0720.N1039.d016521 A c =
      _root_.GD.N0232.N0720.N1030.d018092 a b A M c := by
  unfold _root_.GD.N0232.N0720.N1030.d018092
  rw [sub_eq_iff_eq_add, ← add_div, eq_div_iff ht]
  unfold _root_.GD.N0232.N0720.N1039.d016521
  ring

theorem d018098 (a b A M c : ℝ) (hA : 1 ≤ A) (hc : 0 < c) :
    |_root_.GD.N0232.N0720.N1030.d018092 a b A M c| ≤ |2 * a * b| * |M| + b ^ 2 * (A - 1) := by
  unfold _root_.GD.N0232.N0720.N1030.d018092
  rw [abs_div, abs_of_pos (_root_.GD.N0232.N0720.N1039.d016524 hA hc)]
  have h1 : 1 ≤ _root_.GD.N0232.N0720.N1039.d016521 A c := _root_.GD.N0232.N0720.N1030.d018093 hA hc
  have hb : 0 ≤ b ^ 2 * (A - 1) := mul_nonneg (sq_nonneg b) (by linarith)
  calc |2 * a * b * M + b ^ 2 * (A - 1)| / _root_.GD.N0232.N0720.N1039.d016521 A c
      ≤ |2 * a * b * M + b ^ 2 * (A - 1)| / 1 :=
        div_le_div_of_nonneg_left (abs_nonneg _) one_pos h1
    _ = |2 * a * b * M + b ^ 2 * (A - 1)| := div_one _
    _ ≤ |2 * a * b * M| + |b ^ 2 * (A - 1)| := by
        have := norm_add_le (2 * a * b * M) (b ^ 2 * (A - 1))
        simpa only [Real.norm_eq_abs] using this
    _ = |2 * a * b| * |M| + b ^ 2 * (A - 1) := by
        rw [abs_mul, abs_of_nonneg hb]

theorem d018099 (a b A M c : ℝ) (hA : 1 ≤ A) (hc : 0 < c) :
    |c * (A - 1) * (2 * a * b * M + b ^ 2 * (A - 1)) / _root_.GD.N0232.N0720.N1039.d016521 A c| ≤
      |2 * a * b * M + b ^ 2 * (A - 1)| := by
  have hr0 := _root_.GD.N0232.N0720.N1030.d018094 hA hc
  have hr1 := _root_.GD.N0232.N0720.N1030.d018095 hA hc
  have heq : c * (A - 1) * (2 * a * b * M + b ^ 2 * (A - 1)) / _root_.GD.N0232.N0720.N1039.d016521 A c =
      (2 * a * b * M + b ^ 2 * (A - 1)) * (c * (A - 1) / _root_.GD.N0232.N0720.N1039.d016521 A c) := by
    ring
  rw [heq, abs_mul, abs_of_nonneg hr0]
  calc |2 * a * b * M + b ^ 2 * (A - 1)| * (c * (A - 1) / _root_.GD.N0232.N0720.N1039.d016521 A c)
      ≤ |2 * a * b * M + b ^ 2 * (A - 1)| * 1 :=
        mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)
    _ = _ := mul_one _





theorem d018100 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega ^ 2 ≤
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) *
        _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
          omega := by
  let a : ι → ℝ := fun i ↦ weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega
  have ha : ∀ i, 0 ≤ a i := fun i ↦ mul_nonneg (hweight i) (_root_.GD.N0232.N0720.N1126.d016419 packet i omega)
  have hcs : (∑ i, a i * _root_.GD.N0232.N0720.N1126.d016414 packet i) ^ 2 ≤
      (∑ i, a i) * ∑ i, a i * _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) (ι := ι)
      (r := fun i ↦ a i * _root_.GD.N0232.N0720.N1126.d016414 packet i) (f := fun i ↦ a i)
      (g := fun i ↦ a i * _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2)
    · intro i _
      exact ha i
    · intro i _
      exact mul_nonneg (ha i) (sq_nonneg _)
    · intro i _
      show (a i * _root_.GD.N0232.N0720.N1126.d016414 packet i) ^ 2 ≤ a i * (a i * _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2)
      exact le_of_eq (by ring)
  have hmass : _root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1 = ∑ i, a i := by
    unfold _root_.GD.N0232.N0720.N1126.d016415 _root_.GD.N0230.N0617.d000163
    ring
  unfold _root_.GD.N0230.N0617.d000164 _root_.GD.N0230.N0617.d000165
  rw [hmass]
  exact hcs



theorem d018101 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1031.d017133 g.d009239 0 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
        (_root_.GD.N0232.N0720.N1108.d018077 m n g omega) ∧
      _root_.GD.N0232.N0720.N1031.d017133 g.d009239 0 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
        (_root_.GD.N0232.N0720.N1108.d018077 m n g omega) ≤
      g.d009239 ^ 2 *
        _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
          omega := by
  set A := _root_.GD.N0232.N0720.N1126.d016415 packet weight omega with hAdef
  set M := _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega
  set S := _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
    omega with hSdef
  set c := _root_.GD.N0232.N0720.N1108.d018077 m n g omega
  have hA1 : 1 ≤ A := _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
    (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hc : 0 < c := _root_.GD.N0232.N0720.N1108.d018078 g omega
  have hT : 0 < _root_.GD.N0232.N0720.N1039.d016521 A c := _root_.GD.N0232.N0720.N1039.d016524 hA1 hc
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (hweight i) (_root_.GD.N0232.N0720.N1126.d016419 packet i omega)) (sq_nonneg _)
  have hcs : M ^ 2 ≤ (A - 1) * S := _root_.GD.N0232.N0720.N1030.d018100 packet weight hweight omega
  have hratio := _root_.GD.N0232.N0720.N1030.d018095 hA1 hc
  have hval : _root_.GD.N0232.N0720.N1031.d017133 g.d009239 0 A M c =
      g.d009239 ^ 2 * M ^ 2 * (c / _root_.GD.N0232.N0720.N1039.d016521 A c) := by
    unfold _root_.GD.N0232.N0720.N1031.d017133
    field_simp
    ring
  rw [hval]
  constructor
  · positivity
  · have h1 : g.d009239 ^ 2 * M ^ 2 * (c / _root_.GD.N0232.N0720.N1039.d016521 A c) ≤
        g.d009239 ^ 2 * ((A - 1) * S) * (c / _root_.GD.N0232.N0720.N1039.d016521 A c) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg hc.le hT.le)
      exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    have h2 : g.d009239 ^ 2 * ((A - 1) * S) * (c / _root_.GD.N0232.N0720.N1039.d016521 A c) =
        g.d009239 ^ 2 * S * (c * (A - 1) / _root_.GD.N0232.N0720.N1039.d016521 A c) := by
      ring
    have h3 : g.d009239 ^ 2 * S * (c * (A - 1) / _root_.GD.N0232.N0720.N1039.d016521 A c) ≤
        g.d009239 ^ 2 * S * 1 :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg (sq_nonneg _) hS)
    linarith



theorem d018102 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    Integrable (fun omega ↦
      _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0230.N0617.d000164
  apply integrable_finsetSum
  intro i _
  have h := (_root_.GD.N0232.N0720.N1126.d016421 (m := m) (n := n) packet i).const_mul (weight i)
  have h' := h.mul_const (_root_.GD.N0232.N0720.N1126.d016414 packet i)
  exact h'

theorem d018103 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have : (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ _root_.GD.N0232.N0720.N1126.d016415 (m := m) (n := n) packet weight omega - 1) =
      fun omega ↦ ∑ i, weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega := by
    funext omega
    unfold _root_.GD.N0232.N0720.N1126.d016415 _root_.GD.N0230.N0617.d000163
    ring
  rw [this]
  apply integrable_finsetSum
  intro i _
  exact (_root_.GD.N0232.N0720.N1126.d016421 (m := m) (n := n) packet i).const_mul (weight i)

theorem d018104 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    Integrable (_root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0230.N0617.d000182 (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
    (_root_.GD.N0232.N0720.N1126.d016414 packet) (fun i ↦ _root_.GD.N0232.N0720.N1126.d016421 (m := m) (n := n) packet i)


theorem d018105 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Measurable (_root_.GD.N0232.N0720.N1108.d018077 m n g) := by
  unfold _root_.GD.N0232.N0720.N1108.d018077
  have hG : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega) := by
    change Measurable (_root_.GD.N0107.d009024 m n g.shift g.d009239 g.d009239)
    exact _root_.GD.N0107.d009026 m n _ _ _
  exact (_root_.GD.N0232.N0720.N1499.d015002 m n _).comp hG

theorem d018106 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    Measurable (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet)) :=
  _root_.GD.N0230.N0617.d000178 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
    (fun i ↦ _root_.GD.N0232.N0720.N1126.d016420 (m := m) (n := n) packet i)

theorem d018107 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1126.d016415 (m := m) (n := n) packet weight) :=
  _root_.GD.N0230.N0617.d000177 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
    (fun i ↦ _root_.GD.N0232.N0720.N1126.d016420 (m := m) (n := n) packet i)



theorem d018108 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1031.d017133 g.d009239 0
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
      (_root_.GD.N0232.N0720.N1108.d018077 m n g omega)) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hbig := (_root_.GD.N0232.N0720.N1030.d018104 (m := m) (n := n) packet weight).const_mul
    (g.d009239 ^ 2)
  refine hbig.mono' ?_ ?_
  · have hmeasM := _root_.GD.N0232.N0720.N1030.d018106 (m := m) (n := n) packet weight
    have hmeasA := _root_.GD.N0232.N0720.N1030.d018107 (m := m) (n := n) packet weight
    have hmeasc := _root_.GD.N0232.N0720.N1030.d018105 (m := m) (n := n) g
    unfold _root_.GD.N0232.N0720.N1031.d017133 _root_.GD.N0232.N0720.N1039.d016521
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards with omega
    have h := _root_.GD.N0232.N0720.N1030.d018101 g packet weight hweight omega
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2


theorem d018109 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1108.d018079 g packet weight omega) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have htcd := _root_.GD.N0232.N0720.N1030.d018108 (m := m) (n := n) g packet weight
    hweight
  have hcorr := _root_.GD.N0232.N0720.N1031.d017136 (m := m) (n := n) packet weight hweight
  have hdiff := (htcd.sub (hcorr.const_mul (g.d009239 ^ 2))).const_mul (1 / g.d009239 ^ 2)
  refine hdiff.congr ?_
  filter_upwards with omega
  have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
    _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hc : 0 < _root_.GD.N0232.N0720.N1108.d018077 m n g omega := _root_.GD.N0232.N0720.N1108.d018078 g omega
  have hAne : _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≠ 0 := by linarith
  have htne : _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1108.d018077 m n g omega) ≠ 0 := (_root_.GD.N0232.N0720.N1039.d016524 hA1 hc).ne'
  show 1 / g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1031.d017133 g.d009239 0 _ _ _ -
      g.d009239 ^ 2 * _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
        omega) = _root_.GD.N0232.N0720.N1108.d018079 g packet weight omega
  rw [_root_.GD.N0232.N0720.N1031.d017134 hAne htne]
  unfold _root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0230.N0617.d000167
  exact _root_.GD.N0232.N0720.N1031.d017135 hAne htne g.d009240.ne'


def d018110 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1030.d018092 g.d009239 g.shift (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
    (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
    (_root_.GD.N0232.N0720.N1108.d018077 m n g omega)

theorem d018111 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1030.d018110 g packet weight omega) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hM := _root_.GD.N0232.N0720.N1030.d018102 (m := m) (n := n) packet weight
  have hA := _root_.GD.N0232.N0720.N1030.d018103 (m := m) (n := n) packet weight
  have hbig : Integrable (fun omega ↦ |2 * g.d009239 * g.shift| *
      |_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega| +
      g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (hM.abs.const_mul _).add (hA.const_mul _)
  refine hbig.mono' ?_ ?_
  · have hmeasM := _root_.GD.N0232.N0720.N1030.d018106 (m := m) (n := n) packet weight
    have hmeasA := _root_.GD.N0232.N0720.N1030.d018107 (m := m) (n := n) packet weight
    have hmeasc := _root_.GD.N0232.N0720.N1030.d018105 (m := m) (n := n) g
    unfold _root_.GD.N0232.N0720.N1030.d018110 _root_.GD.N0232.N0720.N1030.d018092 _root_.GD.N0232.N0720.N1039.d016521
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards with omega
    have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
      _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
        (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
    have hc : 0 < _root_.GD.N0232.N0720.N1108.d018077 m n g omega := _root_.GD.N0232.N0720.N1108.d018078 g omega
    rw [Real.norm_eq_abs]
    exact _root_.GD.N0232.N0720.N1030.d018098 _ _ _ _ _ hA1 hc

theorem d018112 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1108.d018077 m n g omega *
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) *
      (2 * g.d009239 * g.shift *
          _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
        g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) /
      _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega) (_root_.GD.N0232.N0720.N1108.d018077 m n g omega))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hM := _root_.GD.N0232.N0720.N1030.d018102 (m := m) (n := n) packet weight
  have hA := _root_.GD.N0232.N0720.N1030.d018103 (m := m) (n := n) packet weight
  have hX : Integrable (fun omega ↦ 2 * g.d009239 * g.shift *
      _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
        g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (hM.const_mul _).add (hA.const_mul _)
  refine hX.abs.mono' ?_ ?_
  · have hmeasM := _root_.GD.N0232.N0720.N1030.d018106 (m := m) (n := n) packet weight
    have hmeasA := _root_.GD.N0232.N0720.N1030.d018107 (m := m) (n := n) packet weight
    have hmeasc := _root_.GD.N0232.N0720.N1030.d018105 (m := m) (n := n) g
    unfold _root_.GD.N0232.N0720.N1039.d016521
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards with omega
    have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
      _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
        (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
    have hc : 0 < _root_.GD.N0232.N0720.N1108.d018077 m n g omega := _root_.GD.N0232.N0720.N1108.d018078 g omega
    rw [Real.norm_eq_abs]
    exact _root_.GD.N0232.N0720.N1030.d018099 _ _ _ _ _ hA1 hc



theorem d018113 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    (∫ omega, (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∑ i, weight i := by
  have hfun : (fun omega ↦ _root_.GD.N0232.N0720.N1126.d016415 (m := m) (n := n) packet weight omega - 1) =
      fun omega ↦ ∑ i, weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega := by
    funext omega
    unfold _root_.GD.N0232.N0720.N1126.d016415 _root_.GD.N0230.N0617.d000163
    ring
  rw [hfun, integral_finset_sum _ (fun i _ ↦
    (_root_.GD.N0232.N0720.N1126.d016421 (m := m) (n := n) packet i).const_mul (weight i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul]
  have h1 : (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 :=
    _root_.GD.N0232.N0720.N1484.d015104 m n (packet i)
  rw [h1, mul_one]

theorem d018114 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    (∫ omega, _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∑ i, weight i * _root_.GD.N0232.N0720.N1126.d016414 packet i := by
  have hfun : (fun omega ↦ _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) =
      fun omega ↦ ∑ i, (weight i * _root_.GD.N0232.N0720.N1126.d016414 packet i) * _root_.GD.N0232.N0720.N1126.d016413 packet i omega := by
    funext omega
    unfold _root_.GD.N0230.N0617.d000164
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun, integral_finset_sum _ (fun i _ ↦
    (_root_.GD.N0232.N0720.N1126.d016421 (m := m) (n := n) packet i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul]
  have h1 : (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 :=
    _root_.GD.N0232.N0720.N1484.d015104 m n (packet i)
  rw [h1, mul_one]





theorem d018115 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1126.d016432 s packet weight -
        g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g packet weight +
        ∫ omega, _root_.GD.N0232.N0720.N1030.d018110 g packet weight omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [_root_.GD.N0232.N0720.N1031.d017141 s g packet weight hweight]
  have hA1 : ∀ omega : _root_.GD.N0232.N0720.N1080.d014170 m n, 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
    fun omega ↦ _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hc : ∀ omega : _root_.GD.N0232.N0720.N1080.d014170 m n, 0 < _root_.GD.N0232.N0720.N1108.d018077 m n g omega := fun omega ↦
    _root_.GD.N0232.N0720.N1108.d018078 g omega
  have htne : ∀ omega : _root_.GD.N0232.N0720.N1080.d014170 m n, _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1108.d018077 m n g omega) ≠ 0 := fun omega ↦
    (_root_.GD.N0232.N0720.N1039.d016524 (hA1 omega) (hc omega)).ne'
  have hAne : ∀ omega : _root_.GD.N0232.N0720.N1080.d014170 m n, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≠ 0 :=
    fun omega ↦ by linarith [hA1 omega]

  have htcd0 : Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1031.d017133 g.d009239 0
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1030.d018108 g packet weight hweight
  have hcs : Integrable (fun omega ↦
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) *
        (2 * g.d009239 * g.shift *
            _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
          g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) /
        _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1030.d018112 g packet weight hweight
  have hcorr := _root_.GD.N0232.N0720.N1031.d017136 (m := m) (n := n) packet weight hweight
  have hexc : Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1108.d018079 g packet weight omega) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1030.d018109 g packet weight hweight
  have hM := _root_.GD.N0232.N0720.N1030.d018102 (m := m) (n := n) packet weight
  have hAm := _root_.GD.N0232.N0720.N1030.d018103 (m := m) (n := n) packet weight
  have hX : Integrable (fun omega ↦ 2 * g.d009239 * g.shift *
      _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
        g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (hM.const_mul _).add (hAm.const_mul _)

  have hsplit : (∫ omega, _root_.GD.N0232.N0720.N1031.d017133 g.d009239 g.shift
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      (∫ omega, _root_.GD.N0232.N0720.N1031.d017133 g.d009239 0
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
      ∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) *
        (2 * g.d009239 * g.shift *
            _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
          g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) /
        _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [← integral_add htcd0 hcs]
    apply integral_congr_ae
    filter_upwards with omega
    exact _root_.GD.N0232.N0720.N1030.d018096 _ _ _ _ _ (htne omega)

  have hdil : (∫ omega, _root_.GD.N0232.N0720.N1031.d017133 g.d009239 0
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      g.d009239 ^ 2 * (∫ omega, _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g packet weight := by
    rw [_root_.GD.N0232.N0720.N1108.d018080, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_const_mul, ← integral_add (hcorr.const_mul _) (hexc.const_mul _)]
    apply integral_congr_ae
    filter_upwards with omega
    have htne' := htne omega
    unfold _root_.GD.N0232.N0720.N1108.d018077 at htne'
    rw [_root_.GD.N0232.N0720.N1031.d017134 (hAne omega) htne']
    unfold _root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0230.N0617.d000167 _root_.GD.N0232.N0720.N1126.d016415
    ring

  have hsum : (∑ i, weight i * (2 * g.d009239 * g.shift * _root_.GD.N0232.N0720.N1126.d016414 packet i + g.shift ^ 2)) =
      ∫ omega, (2 * g.d009239 * g.shift *
          _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
        g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [integral_add (hM.const_mul _) (hAm.const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, _root_.GD.N0232.N0720.N1030.d018114, _root_.GD.N0232.N0720.N1030.d018113,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

  have hshift : (∫ omega, (2 * g.d009239 * g.shift *
          _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
        g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) ∂_root_.GD.N0232.N0720.N1080.d014172 m n) -
      (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) *
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1) *
        (2 * g.d009239 * g.shift *
            _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega +
          g.shift ^ 2 * (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega - 1)) /
        _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∫ omega, _root_.GD.N0232.N0720.N1030.d018110 g packet weight omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [← integral_sub hX hcs]
    apply integral_congr_ae
    filter_upwards with omega
    exact _root_.GD.N0232.N0720.N1030.d018097 _ _ _ _ _ (htne omega)
  have hR : _root_.GD.N0232.N0720.N1126.d016432 s packet weight =
      (∑ i, weight i * (_root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet i)) -
        ∫ omega, _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := rfl
  rw [hR]
  linear_combination (-1 : ℝ) * hsplit + (-1 : ℝ) * hdil + hsum + hshift



theorem d018116 (μs A : ℕ → ℝ) (a b c μ : ℝ) (hc : 0 < c)
    (hA1 : ∀ j, 1 ≤ A j) (hA : Tendsto A atTop atTop) (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1030.d018092 a b (A j) (μs j * A j) c) atTop
      (𝓝 ((2 * a * b * μ + b ^ 2) / c)) := by
  have hinv : Tendsto (fun j ↦ (A j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hA
  have hnum : Tendsto (fun j ↦ 2 * a * b * μs j + b ^ 2 * (1 - (A j)⁻¹)) atTop
      (𝓝 (2 * a * b * μ + b ^ 2 * (1 - 0))) :=
    (hμ.const_mul (2 * a * b)).add ((tendsto_const_nhds.sub hinv).const_mul (b ^ 2))
  have hden : Tendsto (fun j ↦ (A j)⁻¹ + c * (1 - (A j)⁻¹)) atTop (𝓝 (0 + c * (1 - 0))) :=
    hinv.add ((tendsto_const_nhds.sub hinv).const_mul c)
  have hden' : Tendsto (fun j ↦ (A j)⁻¹ + c * (1 - (A j)⁻¹)) atTop (𝓝 c) := by
    simpa using hden
  have hlim := hnum.div hden' hc.ne'
  have hfun : ∀ j, _root_.GD.N0232.N0720.N1030.d018092 a b (A j) (μs j * A j) c =
      (2 * a * b * μs j + b ^ 2 * (1 - (A j)⁻¹)) / ((A j)⁻¹ + c * (1 - (A j)⁻¹)) := by
    intro j
    have hA0 : A j ≠ 0 := by linarith [hA1 j]
    have hT : _root_.GD.N0232.N0720.N1039.d016521 (A j) c ≠ 0 := (_root_.GD.N0232.N0720.N1039.d016524 (hA1 j) hc).ne'
    unfold _root_.GD.N0232.N0720.N1030.d018092
    unfold _root_.GD.N0232.N0720.N1039.d016521 at hT ⊢
    field_simp
  simp_rw [hfun]
  have hval : (2 * a * b * μ + b ^ 2) / c = (2 * a * b * μ + b ^ 2 * (1 - 0)) / c := by simp
  rw [hval]
  exact hlim


def d018117 (g : _root_.GD.N0232.N0719.N0946.d009229) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  (2 * g.d009239 * g.shift * P omega + g.shift ^ 2) / _root_.GD.N0232.N0720.N1108.d018077 m n g omega

theorem d018118 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hesc : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
      atTop atTop)
    (hcompl : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
      atTop (𝓝 (P omega))) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega) atTop
      (𝓝 (_root_.GD.N0232.N0720.N1030.d018117 g P omega)) := by
  have hc : 0 < _root_.GD.N0232.N0720.N1108.d018077 m n g omega := _root_.GD.N0232.N0720.N1108.d018078 g omega
  have hA1 : ∀ j, 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega :=
    fun j ↦ _root_.GD.N0230.N0617.d000168 _ _ (candidate j).weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 _) omega
  have h := _root_.GD.N0232.N0720.N1030.d018116
    (fun j ↦ _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
    (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
    g.d009239 g.shift (_root_.GD.N0232.N0720.N1108.d018077 m n g omega) (P omega) hc hA1 hesc hcompl
  refine h.congr ?_
  intro j
  unfold _root_.GD.N0232.N0720.N1030.d018110
  rw [_root_.GD.N0232.N0720.N1108.d018081 _ _ (candidate j).weight_nonneg]

theorem d018119 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (P omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega| ≤ G omega) :
    Tendsto (fun j ↦ ∫ omega, _root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) atTop
      (𝓝 (∫ omega, _root_.GD.N0232.N0720.N1030.d018117 g P omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n)) := by
  have hmeas : ∀ j, AEStronglyMeasurable
      (fun omega ↦ _root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun j ↦ (_root_.GD.N0232.N0720.N1030.d018111 (m := m) (n := n) g (candidate j).packet
      (candidate j).weight (candidate j).weight_nonneg).aestronglyMeasurable
  have hbound : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      ‖_root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega‖ ≤ G omega := by
    intro j
    filter_upwards [hdom j] with omega h
    simpa [Real.norm_eq_abs] using h
  have hlim : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1030.d018117 g P omega)) := by
    filter_upwards [hesc, hcompl] with omega h1 h2
    exact _root_.GD.N0232.N0720.N1030.d018118 g candidate P omega h1 h2
  exact tendsto_integral_of_dominated_convergence G hmeas hG hbound hlim


theorem d018120 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (P omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G omega) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1031.d017143 m n g (candidate j).packet (candidate j).weight) atTop
      (𝓝 (∫ omega, _root_.GD.N0232.N0720.N1108.d018082 g P omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n)) := by
  have hmeas : ∀ j, AEStronglyMeasurable
      (fun omega ↦ _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun j ↦ (_root_.GD.N0232.N0720.N1030.d018109 (m := m) (n := n) g (candidate j).packet
      (candidate j).weight (candidate j).weight_nonneg).aestronglyMeasurable
  have hbound : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      ‖_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega‖ ≤ G omega := by
    intro j
    filter_upwards [hdom j] with omega h
    simpa [Real.norm_eq_abs] using h
  have hlim : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1108.d018082 g P omega)) := by
    filter_upwards [hesc, hcompl] with omega h1 h2
    exact _root_.GD.N0232.N0720.N1108.d018083 g candidate P omega h1 h2
  exact tendsto_integral_of_dominated_convergence G hmeas hG hbound hlim



theorem d018121 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    g.d009239 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location = -g.shift := by
  have hloc : (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location =
      -(Real.exp (-g.logScale) * g.shift) := by
    simp [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0232.N0719.N0946.d009229.d009237]
  have hexp : Real.exp g.logScale * Real.exp (-g.logScale) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hloc]
  unfold _root_.GD.N0232.N0719.N0946.d009229.d009239
  linear_combination (-g.shift) * hexp

theorem d018122 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P ≠ ⊤) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (P omega) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have h1 := _root_.GD.N0232.N0720.N1078.d016376 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P hfin
  rw [_root_.GD.N0232.N0720.N1499.d015006 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169),
    integrable_withDensity_iff (by fun_prop)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at h1
  have hE : Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
      (P omega - (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    refine h1.congr ?_
    filter_upwards with omega
    rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1499.d015003 m n _ omega)]
    unfold _root_.GD.N0232.N0720.N1037.d016512
    ring
  have hbig : Integrable (fun omega ↦ 2 * (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
      (P omega - (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location) ^ 2) +
      2 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location ^ 2 * _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (hE.const_mul 2).add ((_root_.GD.N0232.N0720.N1037.d016516 g⁻¹).const_mul _)
  refine hbig.mono' ?_ ?_
  · exact (_root_.GD.N0232.N0720.N1037.d016515 g⁻¹).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable P).pow 2)
  · filter_upwards with omega
    have hw : 0 ≤ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega := _root_.GD.N0232.N0720.N1037.d016513 g⁻¹ omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    have hsq : (P omega) ^ 2 ≤ 2 * (P omega - (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location) ^ 2 +
        2 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location ^ 2 := by
      nlinarith [sq_nonneg (P omega - 2 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location)]
    calc _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (P omega) ^ 2
        ≤ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
          (2 * (P omega - (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location) ^ 2 +
            2 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hw
      _ = _ := by ring

theorem d018123 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P ≠ ⊤) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have h2 := _root_.GD.N0232.N0720.N1030.d018122 g P hfin
  have hbig : Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (P omega) ^ 2 +
      _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    h2.add (_root_.GD.N0232.N0720.N1037.d016516 (m := m) (n := n) g⁻¹)
  refine hbig.mono' ?_ ?_
  · exact (_root_.GD.N0232.N0720.N1037.d016515 g⁻¹).aestronglyMeasurable.mul (Lp.aestronglyMeasurable P)
  · filter_upwards with omega
    have hw : 0 ≤ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega := _root_.GD.N0232.N0720.N1037.d016513 g⁻¹ omega
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    have habs : |P omega| ≤ (P omega) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|P omega| - 1 / 2), sq_abs (P omega), abs_nonneg (P omega)]
    calc _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * |P omega|
        ≤ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * ((P omega) ^ 2 + 1) :=
          mul_le_mul_of_nonneg_left habs hw
      _ = _ := by ring


theorem d018124 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P ≠ ⊤) :
    (∫ omega, _root_.GD.N0232.N0720.N1108.d018082 g (fun omega ↦ P omega) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ‖P‖ ^ 2 - ∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (P omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have hnorm : ‖P‖ ^ 2 = ∫ omega, (P omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n :=
    _root_.GD.N0230.N0691.d001213 (_root_.GD.N0232.N0720.N1080.d014172 m n) P
  have hsq : Integrable (fun omega ↦ (P omega) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (Lp.memLp P).integrable_sq
  have hw := _root_.GD.N0232.N0720.N1030.d018122 g P hfin
  rw [hnorm, ← integral_sub hsq hw]
  apply integral_congr_ae
  filter_upwards with omega
  unfold _root_.GD.N0232.N0720.N1108.d018082 _root_.GD.N0232.N0720.N1108.d018077
  have hrec := _root_.GD.N0232.N0720.N1031.d017132 g omega
  have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  field_simp
  linear_combination (P omega ^ 2) * hrec


theorem d018125 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P ≠ ⊤) :
    (∫ omega, _root_.GD.N0232.N0720.N1030.d018117 g (fun omega ↦ P omega) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      2 * g.d009239 * g.shift *
          (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
        g.shift ^ 2 := by
  have h1 := _root_.GD.N0232.N0720.N1030.d018123 g P hfin
  have h0 := _root_.GD.N0232.N0720.N1037.d016516 (m := m) (n := n) g⁻¹
  have hone := _root_.GD.N0232.N0720.N1037.d016517 (m := m) (n := n) g⁻¹
  have hI : (∫ omega, (2 * g.d009239 * g.shift * (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega) +
      g.shift ^ 2 * _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega) ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      2 * g.d009239 * g.shift *
          (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
        g.shift ^ 2 * (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    rw [integral_add (h1.const_mul _) (h0.const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hone, mul_one] at hI
  rw [← hI]
  apply integral_congr_ae
  filter_upwards with omega
  unfold _root_.GD.N0232.N0720.N1030.d018117 _root_.GD.N0232.N0720.N1108.d018077 _root_.GD.N0232.N0720.N1037.d016512
  have hrec := _root_.GD.N0232.N0720.N1031.d017132 g omega
  unfold _root_.GD.N0232.N0720.N1037.d016512 at hrec
  have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  have hL : _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) omega =
      1 / _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) := by
    rw [eq_div_iff hc.ne']
    exact hrec
  rw [hL]
  ring



theorem d018126 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P ≠ ⊤) :
    g.d009239 ^ 2 * ‖P‖ ^ 2 -
        g.d009239 ^ 2 *
          (∫ omega, _root_.GD.N0232.N0720.N1108.d018082 g (fun omega ↦ P omega) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
        (∫ omega, _root_.GD.N0232.N0720.N1030.d018117 g (fun omega ↦ P omega) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P).toReal := by
  rw [_root_.GD.N0232.N0720.N1030.d018124 g P hfin, _root_.GD.N0232.N0720.N1030.d018125 g P hfin,
    _root_.GD.N0232.N0720.N1126.d016430 _ P hfin]
  have hloc : g.d009239 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location = -g.shift :=
    _root_.GD.N0232.N0720.N1030.d018121 g
  have h2 := _root_.GD.N0232.N0720.N1030.d018122 g P hfin
  have h1 := _root_.GD.N0232.N0720.N1030.d018123 g P hfin
  have h0 := _root_.GD.N0232.N0720.N1037.d016516 (m := m) (n := n) g⁻¹
  have hone := _root_.GD.N0232.N0720.N1037.d016517 (m := m) (n := n) g⁻¹
  have hrisk : (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) omega *
      (P omega - (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
        (P omega - (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := rfl
  have hpoint : (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
      (P omega - (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∫ omega, (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (P omega) ^ 2 -
        2 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location *
          (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega) +
        (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location ^ 2 * _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega)
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_congr_ae
    filter_upwards with omega
    ring
  have hexpand : (∫ omega, (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (P omega) ^ 2 -
        2 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location *
          (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega) +
        (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location ^ 2 * _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega)
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (P omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) -
        2 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location *
          (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
        (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location ^ 2 *
          (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    have hsub : Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * (P omega) ^ 2 -
        2 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location *
          (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
      h2.sub (h1.const_mul _)
    have hc2 : Integrable (fun omega ↦ (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location ^ 2 *
        _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
      h0.const_mul _
    rw [integral_add hsub hc2, integral_sub h2 (h1.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hrisk, hpoint, hexpand, hone]
  linear_combination
    (2 * g.d009239 * (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * P omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
      g.shift - g.d009239 * (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location) * hloc







theorem d018127 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G₁ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₁ : Integrable G₁ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₁ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G₁ omega)
    (G₂ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₂ : Integrable G₂ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₂ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega| ≤ G₂ omega) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight) atTop
      (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + _root_.GD.N0232.N0720.N1159.d014647 m n s g)) := by
  have hPmem : _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _ hPmem
  have hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ≠ ⊤ := hP _
  have hE := _root_.GD.N0232.N0720.N1030.d018120 g candidate
    (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014633 m n s.value omega) hesc hcompl G₁ hG₁ hdom₁
  have hS := _root_.GD.N0232.N0720.N1030.d018119 g candidate
    (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014633 m n s.value omega) hesc hcompl G₂ hG₂ hdom₂
  have hform : ∀ j, _root_.GD.N0232.N0720.N1126.d016432 s
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight -
        g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g (candidate j).packet (candidate j).weight +
        ∫ omega, _root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n :=
    fun j ↦ _root_.GD.N0232.N0720.N1030.d018115 s g (candidate j).packet
      (candidate j).weight (candidate j).weight_nonneg
  simp only [hform]
  have hlim := ((hR.const_mul (g.d009239 ^ 2)).sub (hE.const_mul (g.d009239 ^ 2))).add hS
  have hval : ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + _root_.GD.N0232.N0720.N1159.d014647 m n s g =
      g.d009239 ^ 2 * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        g.d009239 ^ 2 * (∫ omega, _root_.GD.N0232.N0720.N1108.d018082 g
          (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014633 m n s.value omega) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
        (∫ omega, _root_.GD.N0232.N0720.N1030.d018117 g
          (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014633 m n s.value omega) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    rw [_root_.GD.N0232.N0720.N1030.d018126 g _ hfin, _root_.GD.N0232.N0720.N1148.d018037 s g,
      ENNReal.toReal_ofReal]
    · have ha : g.d009239 ^ 2 ≠ 0 := (pow_pos g.d009240 2).ne'
      have hcancel : g.d009239 ^ 2 *
          ((_root_.GD.N0232.N0720.N1159.d014647 m n s g + ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) /
            g.d009239 ^ 2) =
          _root_.GD.N0232.N0720.N1159.d014647 m n s g + ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
        field_simp
      rw [hcancel]
      ring
    · have hD := _root_.GD.N0232.N0720.N1159.d014650 m n s g
      have ha : (0 : ℝ) < g.d009239 ^ 2 := pow_pos g.d009240 2
      positivity
  rw [hval]
  exact hlim


theorem d018128 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G₁ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₁ : Integrable G₁ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₁ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G₁ omega)
    (G₂ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₂ : Integrable G₂ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₂ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1030.d018110 g (candidate j).packet (candidate j).weight omega| ≤ G₂ omega) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  have hlim := _root_.GD.N0232.N0720.N1030.d018127 s g candidate hR hesc hcompl
    G₁ hG₁ hdom₁ G₂ hG₂ hdom₂
  have hle : ∀ j, _root_.GD.N0232.N0720.N1126.d016432 s
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
    intro j
    let image : _root_.GD.N0232.N0720.N1130.d017074 :=
      { width := (candidate j).width
        packet := fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)
        weight := (candidate j).weight
        weight_nonneg := (candidate j).weight_nonneg }
    exact _root_.GD.N0232.N0720.N1113.d017125 m n s image
  have hbound := le_of_tendsto' hlim hle
  have hnn := _root_.GD.N0232.N0720.N1159.d014650 m n s g
  linarith




theorem d018129 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G₁ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₁ : Integrable G₁ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₁ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0232.N0720.N1482.d015130 (candidate j).packet (candidate j).weight omega| ≤ G₁ omega)
    (G₂ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₂ : Integrable G₂ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₂ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1030.d018110 _root_.GD.N0232.N0720.N1482.d015130 (candidate j).packet (candidate j).weight omega| ≤ G₂ omega)
    (G₃ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₃ : Integrable G₃ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₃ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0232.N0720.N1482.d015131 (candidate j).packet (candidate j).weight omega| ≤
        G₃ omega)
    (G₄ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG₄ : Integrable G₄ (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom₄ : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1030.d018110 _root_.GD.N0232.N0720.N1482.d015131 (candidate j).packet (candidate j).weight omega| ≤
        G₄ omega) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 ∧
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0 :=
  ⟨_root_.GD.N0232.N0720.N1030.d018128 s _root_.GD.N0232.N0720.N1482.d015130 candidate hR hesc hcompl
      G₁ hG₁ hdom₁ G₂ hG₂ hdom₂,
    _root_.GD.N0232.N0720.N1030.d018128 s _root_.GD.N0232.N0720.N1482.d015131 candidate hR hesc
      hcompl G₃ hG₃ hdom₃ G₄ hG₄ hdom₄⟩

end

end N1030
end N0720
end N0232
end GD
