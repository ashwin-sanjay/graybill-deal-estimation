import GD.Module0349
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor





















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace GD.N0106.N0428.N0765.N1525
noncomputable section

open Set Filter Topology Complex
open scoped Topology
open _root_.GD.N0106.N0428.N0765.N1533


def d005183 (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) + 1)

def d005184 (n : ℕ) (w : ℂ) : ℂ := (_root_.GD.N0106.N0428.N0765.N1525.d005183 n : ℂ) * w

theorem d005185 (n : ℕ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1525.d005183 n := by
  unfold _root_.GD.N0106.N0428.N0765.N1525.d005183
  positivity

theorem d005186 (n : ℕ) : _root_.GD.N0106.N0428.N0765.N1525.d005183 n < 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1525.d005183
  exact (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2 (by linarith)

theorem d005187 {d : ℝ} (hd : 0 < d)
    {w : ℂ} (hw : w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) (n : ℕ) :
    _root_.GD.N0106.N0428.N0765.N1525.d005184 n w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d := by
  change |(_root_.GD.N0106.N0428.N0765.N1525.d005184 n w).im| < d
  have hw' : |w.im| ≤ d := hw
  have hn := _root_.GD.N0106.N0428.N0765.N1525.d005185 n
  have ht := _root_.GD.N0106.N0428.N0765.N1525.d005186 n
  calc
    |(_root_.GD.N0106.N0428.N0765.N1525.d005184 n w).im| = _root_.GD.N0106.N0428.N0765.N1525.d005183 n * |w.im| := by
      simp only [_root_.GD.N0106.N0428.N0765.N1525.d005184, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, abs_mul, abs_of_nonneg hn]
    _ ≤ _root_.GD.N0106.N0428.N0765.N1525.d005183 n * d := mul_le_mul_of_nonneg_left hw' hn
    _ < 1 * d := mul_lt_mul_of_pos_right ht hd
    _ = d := one_mul d

theorem d005188 (w : ℂ) :
    Tendsto (fun n : ℕ => _root_.GD.N0106.N0428.N0765.N1525.d005184 n w) atTop (𝓝 w) := by
  have ht : Tendsto _root_.GD.N0106.N0428.N0765.N1525.d005183 atTop (𝓝 (1 : ℝ)) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have htc : Tendsto (fun n : ℕ => (_root_.GD.N0106.N0428.N0765.N1525.d005183 n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp ht)
  simpa only [_root_.GD.N0106.N0428.N0765.N1525.d005184, one_mul] using htc.mul_const w

theorem d005189 {d : ℝ} (hd : 0 < d)
    {w : ℂ} (hw : w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
    Tendsto (fun n : ℕ => _root_.GD.N0106.N0428.N0765.N1525.d005184 n w) atTop (𝓝[_root_.GD.N0106.N0428.N0765.N1533.d005164 d] w) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (fun n : ℕ => _root_.GD.N0106.N0428.N0765.N1525.d005184 n w) (_root_.GD.N0106.N0428.N0765.N1525.d005188 w)
  exact Filter.Eventually.of_forall fun n =>
    (show |(_root_.GD.N0106.N0428.N0765.N1525.d005184 n w).im| < d from _root_.GD.N0106.N0428.N0765.N1525.d005187 hd hw n).le



theorem d005190 {F : ℂ → ℂ → ℂ}
    {K S : Set ℂ} {w : ℂ} {wseq : ℕ → ℂ}
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (K ×ˢ S))
    (hK : IsCompact K) (hw : w ∈ S)
    (ht : Tendsto wseq atTop (𝓝[S] w)) :
    TendstoUniformlyOn (fun n z => F z (wseq n)) (fun z => F z w) atTop K := by
  have hswap : ContinuousOn (fun p : ℂ × ℂ => F p.2 p.1) (S ×ˢ K) :=
    hc.comp continuous_swap.continuousOn (fun _ hp => ⟨hp.2, hp.1⟩)
  intro u hu


  obtain ⟨v, hv, hbound⟩ := hK.mem_uniformity_of_prod
    (f := fun q z : ℂ => F z q) hswap hw (symm_le_uniformity hu)
  filter_upwards [ht.eventually hv] with n hn
  intro z hz
  exact hbound (wseq n) hn z hz




theorem d005191 {F : ℂ → ℂ → ℂ} {d : ℝ}
    (hd : 0 < d)
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2)
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    {w : ℂ} (hw : w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
    DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) := by
  have hloc : TendstoLocallyUniformlyOn
      (fun n z => F z (_root_.GD.N0106.N0428.N0765.N1525.d005184 n w)) (fun z => F z w) atTop (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact (_root_.GD.N0106.N0428.N0765.N1533.d005167 d)).2
    intro K hKs hK
    apply _root_.GD.N0106.N0428.N0765.N1525.d005190 (K := K) (S := _root_.GD.N0106.N0428.N0765.N1533.d005164 d)
    · apply hc.mono
      intro p hp
      exact ⟨(show |p.1.im| < d from hKs hp.1).le, hp.2⟩
    · exact hK
    · exact hw
    · exact _root_.GD.N0106.N0428.N0765.N1525.d005189 hd hw
  exact hloc.differentiableOn
    (Filter.Eventually.of_forall fun n => hf _ (_root_.GD.N0106.N0428.N0765.N1525.d005187 hd hw n))
    (_root_.GD.N0106.N0428.N0765.N1533.d005167 d)


theorem d005192 {F : ℂ → ℂ → ℂ} {d : ℝ}
    (hd : 0 < d)
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2)
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
    DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) := by
  have hswap : ContinuousOn (fun p : ℂ × ℂ => F p.2 p.1)
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :=
    hc.comp continuous_swap.continuousOn (fun _ hp => ⟨hp.2, hp.1⟩)
  exact _root_.GD.N0106.N0428.N0765.N1525.d005191 (F := fun w z => F z w) hd hswap hf hz




theorem d005193 {F : ℂ → ℂ → ℂ} {d : ℝ}
    (hd : 0 < d)
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2)
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d)) :
    (∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ContinuousOn (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) ∧
    (∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d)) ∧
    (∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ContinuousOn (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) ∧
    (∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    exact hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hz => ⟨hz, hw⟩)
  · intro w hw
    exact _root_.GD.N0106.N0428.N0765.N1525.d005191 hd hc hfA hw
  · intro z hz
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hz, hw⟩)
  · intro z hz
    exact _root_.GD.N0106.N0428.N0765.N1525.d005192 hd hc hfB hz

end
end GD.N0106.N0428.N0765.N1525
