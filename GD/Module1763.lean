import GD.Module1762
import GD.Module1319












set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set

namespace GD.N0106.N0428.N0765.N1516
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1585 _root_.GD.N0106.N0428.N0765.N1627 _root_.GD.N0106.N0428.N0765.N1529
  _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1550 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1512


def d029218 (eta : ℝ) (z w : ℂ) : ℂ :=
  (((1 + eta) / 11 : ℝ) : ℂ) *
    (_root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z * _root_.GD.N0106.N0428.N0765.N1585.d005529 5 5 w *
      ((_root_.GD.N0106.N0428.N0765.N1585.d005540 eta w - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)) ^ 2 -
        (_root_.GD.N0106.N0428.N0765.N1512.d029181 eta z w - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)) ^ 2))

def d029219 (eta α β : ℝ) (q : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1516.d029218 eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)

def d029220 (eta : ℝ) (q : ℝ × ℝ) : ℝ :=
  (1 + eta) / 11 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 q * _root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q))


def d029221 (eta α β : ℝ) : ℝ :=
  (1 + eta) / 11 *
    (((Real.cos (β / 2))⁻¹ + _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2 +
      (_root_.GD.N0106.N0428.N0765.N1512.d029183 α β + _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) ^ 2)

def d029222 (eta α β : ℝ) (q : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1512.d029157 α q.1 * (_root_.GD.N0106.N0428.N0765.N1516.d029221 eta α β * _root_.GD.N0106.N0428.N0765.N1512.d029158 β q.2)

def d029223 (eta α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1516.d029221 eta α β *
    (Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * Real.cos (β / 2) ^ (-(10 : ℝ)))

theorem d029224 {G H : ℂ} {g K o : ℝ}
    (hG : ‖G‖ ≤ g) (hH : ‖H‖ ≤ K) (ho : 0 ≤ o) :
    ‖(G - (o : ℂ)) ^ 2 - (H - (o : ℂ)) ^ 2‖ ≤ (g + o) ^ 2 + (K + o) ^ 2 := by
  have h1 : ‖G - (o : ℂ)‖ ≤ g + o := by
    calc ‖G - (o : ℂ)‖ ≤ ‖G‖ + ‖(o : ℂ)‖ := norm_sub_le _ _
      _ ≤ g + o := by rw [Complex.norm_of_nonneg ho]; exact _root_.add_le_add hG le_rfl
  have h2 : ‖H - (o : ℂ)‖ ≤ K + o := by
    calc ‖H - (o : ℂ)‖ ≤ ‖H‖ + ‖(o : ℂ)‖ := norm_sub_le _ _
      _ ≤ K + o := by rw [Complex.norm_of_nonneg ho]; exact _root_.add_le_add hH le_rfl
  calc
    ‖(G - (o : ℂ)) ^ 2 - (H - (o : ℂ)) ^ 2‖ ≤
        ‖(G - (o : ℂ)) ^ 2‖ + ‖(H - (o : ℂ)) ^ 2‖ := norm_sub_le _ _
    _ = ‖G - (o : ℂ)‖ ^ 2 + ‖H - (o : ℂ)‖ ^ 2 := by rw [norm_pow, norm_pow]
    _ ≤ (g + o) ^ 2 + (K + o) ^ 2 :=
      _root_.add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2)
        (pow_le_pow_left₀ (norm_nonneg _) h2 2)

theorem d029225 {eta : ℝ} (heta : 0 < eta) {w : ℂ}
    (hw : |w.im| < Real.pi / 2) : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1585.d005540 eta) w := by
  exact Complex.differentiableAt_exp.div
    (Complex.differentiableAt_exp.add_const _) (_root_.GD.N0106.N0428.N0765.N1512.d029188 heta hw)

theorem d029226 {eta : ℝ} (heta : 0 < eta) {z w : ℂ}
    (hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1516.d029218 eta q w) z := by
  have hphase := (_root_.GD.N0106.N0428.N0765.N1537.d021535 hs).1
  have hopen : IsOpen {q : ℂ | |q.im| < Real.pi / 2} :=
    isOpen_Iio.preimage (continuous_abs.comp Complex.continuous_im)
  have hd := ((_root_.GD.N0106.N0428.N0765.N1585.d005539 (a := (3 : ℝ) / 2) (b := 10)
    (by norm_num) (by norm_num)) z hphase).differentiableAt (hopen.mem_nhds hphase)
  have hH := _root_.GD.N0106.N0428.N0765.N1512.d029186 heta hs
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029218
  exact ((hd.mul_const _).mul
    ((differentiableAt_const _).sub ((hH.sub_const _).pow 2))).const_mul _

theorem d029227 {eta : ℝ} (heta : 0 < eta) {z w : ℂ}
    (hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1516.d029218 eta z q) w := by
  have hphase := (_root_.GD.N0106.N0428.N0765.N1537.d021535 hs).2
  have hopen : IsOpen {q : ℂ | |q.im| < Real.pi / 2} :=
    isOpen_Iio.preimage (continuous_abs.comp Complex.continuous_im)
  have hd := ((_root_.GD.N0106.N0428.N0765.N1585.d005539 (a := (5 : ℝ)) (b := 5)
    (by norm_num) (by norm_num)) w hphase).differentiableAt (hopen.mem_nhds hphase)
  have hH := _root_.GD.N0106.N0428.N0765.N1512.d029187 heta hs
  have hG := _root_.GD.N0106.N0428.N0765.N1516.d029225 heta hphase
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029218
  exact ((hd.const_mul _).mul
    (((hG.sub_const _).pow 2).sub ((hH.sub_const _).pow 2))).const_mul _

theorem d029228 (eta α β : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β) := by
  have hz : Measurable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) := by unfold _root_.GD.N0106.N0428.N0765.N1550.d005473; fun_prop
  have hw : Measurable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) := by unfold _root_.GD.N0106.N0428.N0765.N1550.d005473; fun_prop
  have hA := (_root_.GD.N0106.N0428.N0765.N1537.d021548 ((3 : ℝ) / 2) 10).comp hz
  have hB := (_root_.GD.N0106.N0428.N0765.N1537.d021548 5 5).comp hw
  have hH := _root_.GD.N0106.N0428.N0765.N1512.d029195 eta α β
  have hG : Measurable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1585.d005540 eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)) := by unfold _root_.GD.N0106.N0428.N0765.N1585.d005540; fun_prop
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029219 _root_.GD.N0106.N0428.N0765.N1516.d029218
  fun_prop

theorem d029229 (eta α β : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1516.d029222 eta α β) :=
  _root_.GD.N0106.N0428.N0765.N1512.d029170 α β _

theorem d029230 (eta α β : ℝ) :
    (∫ q, _root_.GD.N0106.N0428.N0765.N1516.d029222 eta α β q) = _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β := by
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029222 _root_.GD.N0106.N0428.N0765.N1516.d029223
  rw [_root_.GD.N0106.N0428.N0765.N1512.d029171]
  ring

theorem d029231 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β q‖ ≤ _root_.GD.N0106.N0428.N0765.N1516.d029222 eta α β q := by
  obtain ⟨hα, hβ⟩ := _root_.GD.N0106.N0428.N0765.N1537.d021535 hs
  have hp : _root_.GD.N0106.N0428.N0765.N1677.d028882 (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1550.d005477] using hs
  have hH := _root_.GD.N0106.N0428.N0765.N1512.d029184 heta hp
  have hG := _root_.GD.N0106.N0428.N0765.N1585.d005543 heta (z := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hβ)
  have hg := _root_.GD.N0106.N0428.N0765.N1516.d029224 hG hH (_root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta).1
  have hA := _root_.GD.N0106.N0428.N0765.N1585.d005537 (z := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hα)
  have hB := _root_.GD.N0106.N0428.N0765.N1585.d005538 (z := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hβ)
  have hA0 := _root_.GD.N0106.N0428.N0765.N1512.d029151 (z := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hα)
  have hB0 := _root_.GD.N0106.N0428.N0765.N1512.d029152 (z := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hβ)
  have hd := mul_le_mul hA hB (norm_nonneg _) hA0
  have hb := mul_le_mul hd hg (norm_nonneg _) (mul_nonneg hA0 hB0)
  simp only [_root_.GD.N0106.N0428.N0765.N1550.d005476, _root_.GD.N0106.N0428.N0765.N1550.d005477] at hb
  have hN : 0 ≤ (1 + eta) / 11 := by positivity
  simp only [_root_.GD.N0106.N0428.N0765.N1516.d029219, _root_.GD.N0106.N0428.N0765.N1516.d029218, norm_mul, Complex.norm_of_nonneg hN]
  calc _ ≤ (1 + eta) / 11 * _ := mul_le_mul_of_nonneg_left hb hN
    _ = _ := by unfold _root_.GD.N0106.N0428.N0765.N1516.d029222 _root_.GD.N0106.N0428.N0765.N1512.d029157 _root_.GD.N0106.N0428.N0765.N1512.d029158 _root_.GD.N0106.N0428.N0765.N1516.d029221; ring

theorem d029232 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : Integrable (_root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β) :=
  Integrable.mono' (_root_.GD.N0106.N0428.N0765.N1516.d029229 eta α β)
    (_root_.GD.N0106.N0428.N0765.N1516.d029228 eta α β).aestronglyMeasurable
    (Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1516.d029231 heta hs))


theorem d029233 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ q, ‖_root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β q‖) ≤ _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β := by
  rw [← _root_.GD.N0106.N0428.N0765.N1516.d029230]
  exact integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1516.d029232 heta hs).norm (_root_.GD.N0106.N0428.N0765.N1516.d029229 eta α β)
    (Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1516.d029231 heta hs))

theorem d029234 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (b : ℝ) :
    Integrable (fun a : ℝ => _root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β (a, b)) := by
  have hm : Measurable (fun a : ℝ => _root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β (a, b)) :=
    (_root_.GD.N0106.N0428.N0765.N1516.d029228 eta α β).comp (measurable_id.prodMk measurable_const)
  exact Integrable.mono' ((_root_.GD.N0106.N0428.N0765.N1512.d029160 α).mul_const
    (_root_.GD.N0106.N0428.N0765.N1516.d029221 eta α β * _root_.GD.N0106.N0428.N0765.N1512.d029158 β b)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => _root_.GD.N0106.N0428.N0765.N1516.d029231 heta hs (a, b))

theorem d029235 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (a : ℝ) :
    Integrable (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β (a, b)) := by
  have hm : Measurable (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β (a, b)) :=
    (_root_.GD.N0106.N0428.N0765.N1516.d029228 eta α β).comp (measurable_const.prodMk measurable_id)
  exact Integrable.mono' (((_root_.GD.N0106.N0428.N0765.N1512.d029161 β).const_mul
    (_root_.GD.N0106.N0428.N0765.N1516.d029221 eta α β)).const_mul (_root_.GD.N0106.N0428.N0765.N1512.d029157 α a)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => _root_.GD.N0106.N0428.N0765.N1516.d029231 heta hs (a, b))

theorem d029236 (eta b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1585.d005540 eta (b : ℂ) = ((Real.exp b / (Real.exp b + eta) : ℝ) : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1585.d005540
  push_cast
  rfl

theorem d029237 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029218 eta (q.1 : ℂ) (q.2 : ℂ) = (_root_.GD.N0106.N0428.N0765.N1516.d029220 eta q : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1516.d029218, _root_.GD.N0106.N0428.N0765.N1512.d029185 heta, _root_.GD.N0106.N0428.N0765.N1516.d029236,
    ← _root_.GD.N0106.N0428.N0765.N1680.d021562 heta q, _root_.GD.N0106.N0428.N0765.N1585.d005530, _root_.GD.N0106.N0428.N0765.N1585.d005530]
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029220 _root_.GD.N0106.N0428.N0765.N1521.d020868 _root_.GD.N0106.N0428.N0765.N1529.d020802
  push_cast
  ring

theorem d029238 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0 q = (_root_.GD.N0106.N0428.N0765.N1516.d029220 eta q : ℂ) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1516.d029219, _root_.GD.N0106.N0428.N0765.N1550.d005478, _root_.GD.N0106.N0428.N0765.N1516.d029237 heta]

theorem d029239 (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (∫ q, _root_.GD.N0106.N0428.N0765.N1516.d029220 eta q) = _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta := by
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029220 _root_.GD.N0106.N0428.N0765.N1627.d021120
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1521.d020875 location eta heta]

theorem d029240 (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (∫ q, _root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0 q) = (_root_.GD.N0106.N0428.N0765.N1627.d021120 location eta : ℂ) := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1516.d029238 heta]
  rw [integral_complex_ofReal, _root_.GD.N0106.N0428.N0765.N1516.d029239 location heta]




theorem d029241 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β q = (((1 + eta) / 11 * (eta⁻¹) ^ 2 : ℝ) : ℂ) *
      _root_.GD.N0106.N0428.N0765.N1537.d021532 eta⁻¹ α β q := by
  have hp : _root_.GD.N0106.N0428.N0765.N1677.d028882 (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1550.d005477] using hs
  have hd := _root_.GD.N0106.N0428.N0765.N1512.d029188 heta (w := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)
    (_root_.GD.N0106.N0428.N0765.N1677.d028892 hp)
  have hd' := _root_.GD.N0106.N0428.N0765.N1677.d028893 (inv_pos.mpr heta).le hp
  have heta' : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
  have hG : _root_.GD.N0106.N0428.N0765.N1585.d005540 eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) = ((eta⁻¹ : ℝ) : ℂ) *
      _root_.GD.N0106.N0428.N0765.N1537.d021530 eta⁻¹ β q.2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1585.d005540 _root_.GD.N0106.N0428.N0765.N1537.d021530
    change Complex.exp (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) / (Complex.exp (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) + (eta : ℂ)) =
      ((eta⁻¹ : ℝ) : ℂ) * (Complex.exp (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) /
        (1 + ((eta⁻¹ : ℝ) : ℂ) * Complex.exp (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)))
    push_cast at hd' ⊢
    rw [← mul_div_assoc, div_eq_div_iff hd hd']
    field_simp [heta'] <;> ring
  have hH : _root_.GD.N0106.N0428.N0765.N1512.d029181 eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) =
      ((eta⁻¹ : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1675.d021510 eta⁻¹ α β q := by
    simp only [_root_.GD.N0106.N0428.N0765.N1512.d029181, _root_.GD.N0106.N0428.N0765.N1677.d028883,
      _root_.GD.N0106.N0428.N0765.N1675.d021510, _root_.GD.N0106.N0428.N0765.N1550.d005476, _root_.GD.N0106.N0428.N0765.N1550.d005477]
  have hO : _root_.GD.N0106.N0428.N0765.N1607.d012678 eta = eta⁻¹ * _root_.GD.N0106.N0428.N0765.N1537.d021531 eta⁻¹ := by
    rw [_root_.GD.N0106.N0428.N0765.N1680.d021564 (inv_pos.mpr heta), inv_inv,
      ← mul_assoc, inv_mul_cancel₀ heta.ne', one_mul]
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029219 _root_.GD.N0106.N0428.N0765.N1516.d029218
  rw [hG, hH, hO]
  unfold _root_.GD.N0106.N0428.N0765.N1537.d021532 _root_.GD.N0106.N0428.N0765.N1537.d021527
  change _ = _ * (_root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) *
    _root_.GD.N0106.N0428.N0765.N1585.d005529 5 5 (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) * _)
  push_cast
  ring

theorem d029242 {g h o : ℝ}
    (hg : g ∈ Icc (0 : ℝ) 1) (hh : h ∈ Icc (0 : ℝ) 1) (ho : o ∈ Icc (0 : ℝ) 1) :
    |(g - o) ^ 2 - (h - o) ^ 2| ≤ 1 := by
  have hg' : |g - o| ≤ 1 := abs_le.mpr ⟨by linarith [hg.1, ho.2], by linarith [hg.2, ho.1]⟩
  have hh' : |h - o| ≤ 1 := abs_le.mpr ⟨by linarith [hh.1, ho.2], by linarith [hh.2, ho.1]⟩
  have hgs : (g - o) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (g - o)) hg' 2
  have hhs : (h - o) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg (h - o)) hh' 2
  exact abs_le.mpr ⟨by linarith [sq_nonneg (g - o)], by linarith [sq_nonneg (h - o)]⟩

theorem d029243 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1529.d020802 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)| ≤ 1 := by
  obtain ⟨hu, hv, hw⟩ := _root_.GD.N0106.N0428.N0765.N1527.d021473 q.1 q.2
  have hh := _root_.GD.N0106.N0428.N0765.N1534.d005345 heta hu hv hw
  have hd : 0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 q 1 + eta * _root_.GD.N0106.N0428.N0765.N1521.d020862 q 2 := by positivity
  have hg : _root_.GD.N0106.N0428.N0765.N1529.d020800 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hv.le hd.le
    · exact (div_le_one hd).mpr (le_add_of_nonneg_right (by positivity))
  exact _root_.GD.N0106.N0428.N0765.N1516.d029242 hg ⟨hh.1.le, hh.2.le⟩ (_root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta)


theorem d029244 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1516.d029220 eta q‖ ≤ (1 + eta) / 11 * _root_.GD.N0106.N0428.N0765.N1521.d020868 q := by
  have hρ : 0 ≤ _root_.GD.N0106.N0428.N0765.N1521.d020868 q := by
    unfold _root_.GD.N0106.N0428.N0765.N1521.d020868
    exact mul_nonneg (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le
      (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le
  have hN : 0 ≤ (1 + eta) / 11 := by positivity
  simp only [_root_.GD.N0106.N0428.N0765.N1516.d029220, Real.norm_eq_abs, abs_mul, abs_of_nonneg hN, abs_of_nonneg hρ]
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1516.d029243 heta q) hρ) hN).trans_eq (by ring)

theorem d029245 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1516.d029219 eta 0 0 q‖ ≤ (1 + eta) / 11 * _root_.GD.N0106.N0428.N0765.N1521.d020868 q := by
  rw [_root_.GD.N0106.N0428.N0765.N1516.d029238 heta, Complex.norm_real]
  exact _root_.GD.N0106.N0428.N0765.N1516.d029244 heta q




def d029246 (eta α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β * (beta ((3 : ℝ) / 2) 10)⁻¹ * (beta (5 : ℝ) 5)⁻¹

theorem d029247 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β := by
  obtain ⟨hα, hβ⟩ := _root_.GD.N0106.N0428.N0765.N1537.d021535 hs
  have hcα := _root_.GD.N0106.N0428.N0765.N1585.d005527 hα
  have hcβ := _root_.GD.N0106.N0428.N0765.N1585.d005527 hβ
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029223 _root_.GD.N0106.N0428.N0765.N1516.d029221
  positivity

theorem d029248 (eta α β : ℝ) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1516.d029222 eta α β q = _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β *
      _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 q.1 * _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 q.2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029222 _root_.GD.N0106.N0428.N0765.N1516.d029223 _root_.GD.N0106.N0428.N0765.N1512.d029157 _root_.GD.N0106.N0428.N0765.N1512.d029158
  ring

theorem d029249 {eta α β : ℝ} (heta : 0 < eta)
    (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β q‖ ≤ _root_.GD.N0106.N0428.N0765.N1516.d029246 eta α β *
      Real.exp (-((3 : ℝ) / 2) * |q.1|) * Real.exp (-5 * |q.2|) := by
  have hC := _root_.GD.N0106.N0428.N0765.N1516.d029247 heta hs
  have hA : _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 q.1 ≤
      (beta ((3 : ℝ) / 2) 10)⁻¹ * Real.exp (-((3 : ℝ) / 2) * |q.1|) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1512.d029208, _root_.GD.N0106.N0428.N0765.N1512.d029209, Bool.false_eq_true, ↓reduceIte] using _root_.GD.N0106.N0428.N0765.N1512.d029211 false q.1
  have hB := _root_.GD.N0106.N0428.N0765.N1512.d029212 q.2
  have hρ : 0 ≤ _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 q.2 := (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le
  have hbA : 0 < beta ((3 : ℝ) / 2) 10 := beta_pos (by norm_num) (by norm_num)
  calc
    ‖_root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β q‖ ≤ _root_.GD.N0106.N0428.N0765.N1516.d029222 eta α β q := _root_.GD.N0106.N0428.N0765.N1516.d029231 heta hs q
    _ = _root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 q.1 * _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 q.2 :=
      _root_.GD.N0106.N0428.N0765.N1516.d029248 eta α β q
    _ ≤ (_root_.GD.N0106.N0428.N0765.N1516.d029223 eta α β *
        ((beta ((3 : ℝ) / 2) 10)⁻¹ * Real.exp (-((3 : ℝ) / 2) * |q.1|))) *
        ((beta (5 : ℝ) 5)⁻¹ * Real.exp (-5 * |q.2|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA hC) hB hρ (mul_nonneg hC (by positivity))
    _ = _ := by unfold _root_.GD.N0106.N0428.N0765.N1516.d029246; ring

def d029250 : Set (ℝ × ℝ) := {p | ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 p.1 p.2 < Real.pi}

theorem d029251 (eta : ℝ) {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1516.d029250) :
    ContinuousAt (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1516.d029246 eta q.1 q.2) p := by
  have hs := _root_.GD.N0106.N0428.N0765.N1537.d021535 hp
  have hA : ContinuousAt (fun q : ℝ × ℝ => Real.cos (q.1 / 2)) p := by fun_prop
  have hB : ContinuousAt (fun q : ℝ × ℝ => Real.cos (q.2 / 2)) p := by fun_prop
  have hS : ContinuousAt (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1538.d021231 q.1 q.2) p := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021231 _root_.GD.N0106.N0428.N0765.N1538.d021192
    fun_prop
  have hDa := hA.rpow_const (p := -((23 : ℝ) / 2)) (Or.inl (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.1).ne')
  have hDb := hB.rpow_const (p := -(10 : ℝ)) (Or.inl (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.2).ne')
  have hg := hB.inv₀ (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.2).ne'
  have hK := hS.inv₀ (_root_.GD.N0106.N0428.N0765.N1538.d021232 hp).ne'
  unfold _root_.GD.N0106.N0428.N0765.N1516.d029246 _root_.GD.N0106.N0428.N0765.N1516.d029223 _root_.GD.N0106.N0428.N0765.N1516.d029221 _root_.GD.N0106.N0428.N0765.N1512.d029183
  exact ((((((hg.add_const _).pow 2).add ((hK.add_const _).pow 2)).const_mul _).mul
    (hDa.mul hDb)).mul_const _).mul_const _

theorem d029252 {eta : ℝ} (heta : 0 < eta) {S : Set (ℝ × ℝ)}
    (hS : IsCompact S) (hsub : S ⊆ _root_.GD.N0106.N0428.N0765.N1516.d029250) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ S, ∀ a b : ℝ,
      ‖_root_.GD.N0106.N0428.N0765.N1516.d029219 eta p.1 p.2 (a, b)‖ ≤
        K * Real.exp (-((3 : ℝ) / 2) * |a|) * Real.exp (-5 * |b|) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1516.d029246 eta p.1 p.2) S :=
    fun p hp => (_root_.GD.N0106.N0428.N0765.N1516.d029251 eta (hsub hp)).continuousWithinAt
  obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp a b
  have hn : |_root_.GD.N0106.N0428.N0765.N1516.d029246 eta p.1 p.2| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK p hp
  have hcoef : _root_.GD.N0106.N0428.N0765.N1516.d029246 eta p.1 p.2 ≤ max K 1 :=
    (le_abs_self _).trans (hn.trans (le_max_left _ _))
  exact (_root_.GD.N0106.N0428.N0765.N1516.d029249 heta (hsub hp) (a, b)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))
      (Real.exp_nonneg _))

theorem d029253 {eta dA dB : ℝ} (heta : 0 < eta)
    (hd : ((21 : ℝ) / 2) * (dA + dB) < Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ α β : ℝ, |α| ≤ dA → |β| ≤ dB → ∀ a b : ℝ,
      ‖_root_.GD.N0106.N0428.N0765.N1516.d029219 eta α β (a, b)‖ ≤
        K * Real.exp (-((3 : ℝ) / 2) * |a|) * Real.exp (-5 * |b|) := by
  have hsub : Icc (-dA) dA ×ˢ Icc (-dB) dB ⊆ _root_.GD.N0106.N0428.N0765.N1516.d029250 := by
    intro p hp
    have ha := abs_le.mpr hp.1
    have hb := abs_le.mpr hp.2
    change ((21 : ℝ) / 2) * (|p.1| + |p.2|) < Real.pi
    nlinarith
  obtain ⟨K, hK, h⟩ := _root_.GD.N0106.N0428.N0765.N1516.d029252 heta (isCompact_Icc.prod isCompact_Icc) hsub
  exact ⟨K, hK, fun α β hα hβ a b => h (α, β) ⟨abs_le.mp hα, abs_le.mp hβ⟩ a b⟩

end
end GD.N0106.N0428.N0765.N1516

#print axioms _root_.GD.N0106.N0428.N0765.N1516.d029226
#print axioms _root_.GD.N0106.N0428.N0765.N1516.d029227
#print axioms _root_.GD.N0106.N0428.N0765.N1516.d029232
#print axioms _root_.GD.N0106.N0428.N0765.N1516.d029233
#print axioms _root_.GD.N0106.N0428.N0765.N1516.d029240
#print axioms _root_.GD.N0106.N0428.N0765.N1516.d029241
#print axioms _root_.GD.N0106.N0428.N0765.N1516.d029244
#print axioms _root_.GD.N0106.N0428.N0765.N1516.d029253
