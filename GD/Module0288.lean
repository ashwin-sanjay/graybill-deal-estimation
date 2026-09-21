import Mathlib.Probability.CDF
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
























open Filter Set Topology
open MeasureTheory

namespace GD
namespace N0235
namespace N0744

noncomputable section




def d004257 (F : ℝ → ℝ) (p : ℝ) : Set ℝ :=
  {x | p ≤ F x}


def d004258 (F : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf (_root_.GD.N0235.N0744.d004257 F p)





def d004259 (F : ℝ → ℝ) (p : ℝ) : Prop :=
  (_root_.GD.N0235.N0744.d004257 F p).Nonempty ∧ BddBelow (_root_.GD.N0235.N0744.d004257 F p)


def d004260 (c : ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ F (x - c)


theorem d004261
    {F : ℝ → ℝ} {p x : ℝ} :
    x ∈ _root_.GD.N0235.N0744.d004257 F p ↔ p ≤ F x :=
  Iff.rfl


theorem d004262
    {F : ℝ → ℝ} {p x : ℝ} (hx : p ≤ F x) :
    (_root_.GD.N0235.N0744.d004257 F p).Nonempty :=
  ⟨x, hx⟩




theorem d004263
    {F : ℝ → ℝ} {p a : ℝ}
    (hbelow : ∀ x ≤ a, F x < p) :
    BddBelow (_root_.GD.N0235.N0744.d004257 F p) := by
  refine ⟨a, ?_⟩
  intro x hx
  by_contra hax
  have hxa : x ≤ a := le_of_not_ge hax
  exact (not_lt_of_ge hx) (hbelow x hxa)


theorem d004264
    {F : ℝ → ℝ} {p lower upper : ℝ}
    (hupper : p ≤ F upper)
    (hlower : ∀ x ≤ lower, F x < p) :
    _root_.GD.N0235.N0744.d004259 F p :=
  ⟨_root_.GD.N0235.N0744.d004262 hupper,
    _root_.GD.N0235.N0744.d004263 hlower⟩





theorem d004265
    (c : ℝ) (F : ℝ → ℝ) (p : ℝ) :
    _root_.GD.N0235.N0744.d004257 (_root_.GD.N0235.N0744.d004260 c F) p =
      (fun x : ℝ ↦ x + c) '' _root_.GD.N0235.N0744.d004257 F p := by
  ext x
  constructor
  · intro hx
    refine ⟨x - c, ?_, by ring⟩
    exact hx
  · rintro ⟨y, hy, rfl⟩
    simpa [_root_.GD.N0235.N0744.d004257, _root_.GD.N0235.N0744.d004260] using hy


theorem d004266
    {F : ℝ → ℝ} {p : ℝ}
    (hfinite : _root_.GD.N0235.N0744.d004259 F p)
    (c : ℝ) :
    _root_.GD.N0235.N0744.d004259 (_root_.GD.N0235.N0744.d004260 c F) p := by
  rw [_root_.GD.N0235.N0744.d004259, _root_.GD.N0235.N0744.d004265]
  constructor
  · exact hfinite.1.image _
  · rcases hfinite.2 with ⟨a, ha⟩
    refine ⟨a + c, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    simpa [add_comm] using add_le_add_right (ha hx) c




theorem d004267
    {F : ℝ → ℝ} {p : ℝ}
    (hfinite : _root_.GD.N0235.N0744.d004259 F p)
    (c : ℝ) :
    _root_.GD.N0235.N0744.d004258 (_root_.GD.N0235.N0744.d004260 c F) p =
      _root_.GD.N0235.N0744.d004258 F p + c := by
  rw [_root_.GD.N0235.N0744.d004258, _root_.GD.N0235.N0744.d004265]
  exact
    ((OrderIso.addRight c).map_csInf'
      hfinite.1 hfinite.2).symm




def d004268 (μ : Measure ℝ) (p : ℝ) : ℝ :=
  _root_.GD.N0235.N0744.d004258 (ProbabilityTheory.cdf μ) p


def d004269 (μ : Measure ℝ) : ℝ :=
  _root_.GD.N0235.N0744.d004268 μ (1 / 2)





theorem d004270
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c x : ℝ) :
    ProbabilityTheory.cdf
        (μ.map (fun y : ℝ ↦ y + c)) x =
      ProbabilityTheory.cdf μ (x - c) := by
  let shift : ℝ → ℝ := fun y ↦ y + c
  have hshift : Measurable shift := by
    fun_prop
  haveI :
      IsProbabilityMeasure (μ.map shift) :=
    Measure.isProbabilityMeasure_map hshift.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real,
    map_measureReal_apply hshift measurableSet_Iic,
    ProbabilityTheory.cdf_eq_real]
  congr 1
  ext y
  simp only [shift, mem_preimage, mem_Iic]
  constructor <;> intro h <;> linarith


theorem d004271
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) :
    ProbabilityTheory.cdf
        (μ.map (fun y : ℝ ↦ y + c)) =
      _root_.GD.N0235.N0744.d004260 c (ProbabilityTheory.cdf μ) := by
  funext x
  exact _root_.GD.N0235.N0744.d004270 μ c x






theorem d004272
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0235.N0744.d004259 (ProbabilityTheory.cdf μ) p := by
  constructor
  · have hevent :
        ∀ᶠ x : ℝ in atTop,
          p < ProbabilityTheory.cdf μ x :=
      (tendsto_order.1
        (ProbabilityTheory.tendsto_cdf_atTop μ)).1 p hp1
    obtain ⟨x, hx⟩ := hevent.exists
    exact ⟨x, hx.le⟩
  · have hevent :
        ∀ᶠ x : ℝ in atBot,
          ProbabilityTheory.cdf μ x < p :=
      (tendsto_order.1
        (ProbabilityTheory.tendsto_cdf_atBot μ)).2 p hp0
    rcases (eventually_atBot.1 hevent) with ⟨a, ha⟩
    exact
      _root_.GD.N0235.N0744.d004263
        (fun x hx ↦ ha x hx)





theorem d004273
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (c : ℝ) :
    _root_.GD.N0235.N0744.d004268
        (μ.map (fun x : ℝ ↦ x + c)) p =
      _root_.GD.N0235.N0744.d004268 μ p + c := by
  let shift : ℝ → ℝ := fun x ↦ x + c
  have hshift : Measurable shift := by
    fun_prop
  haveI :
      IsProbabilityMeasure (μ.map shift) :=
    Measure.isProbabilityMeasure_map hshift.aemeasurable
  unfold _root_.GD.N0235.N0744.d004268
  rw [_root_.GD.N0235.N0744.d004271]
  exact
    _root_.GD.N0235.N0744.d004267
      (_root_.GD.N0235.N0744.d004272 μ hp0 hp1) c





theorem d004274
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) :
    _root_.GD.N0235.N0744.d004269
        (μ.map (fun x : ℝ ↦ x + c)) =
      _root_.GD.N0235.N0744.d004269 μ + c := by
  unfold _root_.GD.N0235.N0744.d004269
  exact
    _root_.GD.N0235.N0744.d004273 μ
      (by norm_num) (by norm_num) c





theorem d004275
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) :
    _root_.GD.N0235.N0744.d004269
        (μ.map (fun x : ℝ ↦ x + c)) - c =
      _root_.GD.N0235.N0744.d004269 μ := by
  rw [_root_.GD.N0235.N0744.d004274]
  ring

end

end N0744
end N0235
end GD
