import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving















open Filter MeasureTheory

namespace GD
namespace N0230
namespace N0593

variable {Alpha Beta E F : Type*}
  [MeasurableSpace Alpha] [MeasurableSpace Beta]







theorem d000108
    [PseudoEMetricSpace E]
    {mu nu : Measure Alpha} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {f : ℕ → Alpha → E} {g : Alpha → E}
    (hnumu : nu ≪ mu)
    (hf : ∀ n, AEStronglyMeasurable (f n) mu)
    (hfg : TendstoInMeasure mu f atTop g) :
    TendstoInMeasure nu f atTop g := by
  rw [exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hf n).mono_ac hnumu)]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ :=
    (exists_seq_tendstoInMeasure_atTop_iff hf).1 hfg ns hns
  exact ⟨ns', hns', hnumu.ae_le hae⟩



theorem d000109
    [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {mu : Measure Alpha} [IsFiniteMeasure mu]
    {f : ℕ → Alpha → E} {g : Alpha → E} {psi : E → F}
    (hf : ∀ n, AEStronglyMeasurable (f n) mu)
    (hpsi : Continuous psi)
    (hfg : TendstoInMeasure mu f atTop g) :
    TendstoInMeasure mu (fun n ↦ psi ∘ f n) atTop (psi ∘ g) := by
  change TendstoInMeasure mu (fun n x ↦ psi (f n x)) atTop
    (fun x ↦ psi (g x))
  rw [exists_seq_tendstoInMeasure_atTop_iff
    (fun n ↦ hpsi.comp_aestronglyMeasurable (hf n))]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ :=
    (exists_seq_tendstoInMeasure_atTop_iff hf).1 hfg ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with x hx
  simpa only [Function.comp_def] using hpsi.continuousAt.tendsto.comp hx



theorem d000110
    [PseudoEMetricSpace E]
    {mu : Measure Alpha} {nu : Measure Beta}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {phi : Alpha → Beta} {f : ℕ → Beta → E} {g : Beta → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) nu)
    (hphi : Measure.QuasiMeasurePreserving phi mu nu)
    (hfg : TendstoInMeasure nu f atTop g) :
    TendstoInMeasure mu (fun n ↦ f n ∘ phi) atTop (g ∘ phi) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (hf n).comp_quasiMeasurePreserving hphi)]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ :=
    (exists_seq_tendstoInMeasure_atTop_iff hf).1 hfg ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hphi.ae hae] with x hx
  simpa only [Function.comp_apply] using hx



theorem d000111
    [PseudoEMetricSpace E]
    {mu : Measure Alpha} [IsFiniteMeasure mu]
    {phi : Alpha → Beta} {f : ℕ → Beta → E} {g : Beta → E}
    (hphi : Measurable phi)
    (hf : ∀ n, AEStronglyMeasurable (f n) (mu.map phi))
    (hfg : TendstoInMeasure (mu.map phi) f atTop g) :
    TendstoInMeasure mu (fun n ↦ f n ∘ phi) atTop (g ∘ phi) := by
  exact _root_.GD.N0230.N0593.d000110
    hf (hphi.quasiMeasurePreserving mu) hfg

end N0593
end N0230
end GD

#print axioms _root_.GD.N0230.N0593.d000108
#print axioms _root_.GD.N0230.N0593.d000109
#print axioms _root_.GD.N0230.N0593.d000110
#print axioms _root_.GD.N0230.N0593.d000111
