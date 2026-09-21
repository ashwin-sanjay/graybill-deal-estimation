import GD.Module0634
import GD.Module0912



























open MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1214

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)





@[simp]
theorem d014259
    (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    g • omega =
      _root_.GD.N0107.d009024
        m n g.shift g.d009239 g.d009239 omega := by
  rfl



local instance d014260 :
    MeasurableSMul₂ _root_.GD.N0232.N0719.N0946.d009229 (_root_.GD.N0232.N0720.N1080.d014170 m n) where
  measurable_smul := by
    change Measurable
      (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦
        _root_.GD.N0107.d009024
          m n z.1.shift z.1.d009239 z.1.d009239 z.2)
    unfold _root_.GD.N0107.d009024
      _root_.GD.N0107.d009018
    have hleft : Measurable
        (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦
          fun i ↦ z.1.shift + z.1.d009239 * z.2.1 i) := by
      apply measurable_pi_lambda
      intro i
      exact
        (_root_.GD.N0232.N0719.N0946.d009229.d009246.comp measurable_fst).add
          ((_root_.GD.N0232.N0719.N0946.d009229.d009248.comp measurable_fst).mul
            ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
    have hright : Measurable
        (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0720.N1080.d014170 m n ↦
          fun j ↦ z.1.shift + z.1.d009239 * z.2.2 j) := by
      apply measurable_pi_lambda
      intro j
      exact
        (_root_.GD.N0232.N0719.N0946.d009229.d009246.comp measurable_fst).add
          ((_root_.GD.N0232.N0719.N0946.d009229.d009248.comp measurable_fst).mul
            ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))
    exact hleft.prodMk hright



def d014261
    (g : _root_.GD.N0232.N0719.N0946.d009229) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦ g • d (g⁻¹ • omega)

theorem d014262
    (g : _root_.GD.N0232.N0719.N0946.d009229) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : Measurable d) :
    Measurable (_root_.GD.N0232.N0720.N1214.d014261 m n g d) := by
  unfold _root_.GD.N0232.N0720.N1214.d014261
  fun_prop

@[simp]
theorem d014263 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0232.N0720.N1214.d014261 m n 1 d = d := by
  funext omega
  simp [_root_.GD.N0232.N0720.N1214.d014261]

theorem d014264
    (g h : _root_.GD.N0232.N0719.N0946.d009229) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014261 m n h d) =
      _root_.GD.N0232.N0720.N1214.d014261 m n (g * h) d := by
  funext omega
  simp [_root_.GD.N0232.N0720.N1214.d014261, mul_smul]





def d014265
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  AEStronglyMeasurable.mk
    (fun omega ↦ p omega) (Lp.aestronglyMeasurable p)

theorem d014266
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    Measurable (_root_.GD.N0232.N0720.N1214.d014265 m n p) :=
  AEStronglyMeasurable.measurable_mk (Lp.aestronglyMeasurable p)

theorem d014267
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1214.d014265 m n p =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] fun omega ↦ p omega :=
  (Lp.aestronglyMeasurable p).ae_eq_mk.symm

theorem d014268
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  exact MemLp.ae_eq
    (_root_.GD.N0232.N0720.N1214.d014267 m n p).symm (Lp.memLp p)

theorem d014269
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014268 m n p) = p := by
  calc
    MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1214.d014268 m n p) =
        MemLp.toLp (fun omega ↦ p omega) (Lp.memLp p) :=
      MemLp.toLp_congr
        (_root_.GD.N0232.N0720.N1214.d014268 m n p) (Lp.memLp p)
        (_root_.GD.N0232.N0720.N1214.d014267 m n p)
    _ = p := Lp.toLp_coeFn p (Lp.memLp p)









theorem d014270
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hmem : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) 2
        (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) (hmem g) = p) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega ↦ _root_.GD.N0232.N0720.N1214.d014265 m n p (g • omega)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ g • _root_.GD.N0232.N0720.N1214.d014265 m n p omega := by
  have hrawFixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
    intro g
    apply (MemLp.toLp_eq_toLp_iff
      (hmem g) (_root_.GD.N0232.N0720.N1214.d014268 m n p)).mp
    rw [hfixed g, _root_.GD.N0232.N0720.N1214.d014269]
  intro g
  filter_upwards [hrawFixed g⁻¹] with omega homega
  unfold _root_.GD.N0232.N0720.N1214.d014261 at homega
  simp only [inv_inv] at homega
  change
    g⁻¹ • _root_.GD.N0232.N0720.N1214.d014265 m n p (g • omega) =
      _root_.GD.N0232.N0720.N1214.d014265 m n p omega at homega
  change
    -(Real.exp (-g.logScale) * g.shift) +
        Real.exp (-g.logScale) * _root_.GD.N0232.N0720.N1214.d014265 m n p (g • omega) =
      _root_.GD.N0232.N0720.N1214.d014265 m n p omega at homega
  change
    _root_.GD.N0232.N0720.N1214.d014265 m n p (g • omega) =
      g.shift + Real.exp g.logScale * _root_.GD.N0232.N0720.N1214.d014265 m n p omega
  rw [Real.exp_neg] at homega
  field_simp [Real.exp_ne_zero] at homega
  linarith








theorem d014271
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hmem : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) 2
        (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) (hmem g) = p) :
    ∃ repaired : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        repaired =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1214.d014265 m n p) ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have hfallbackMeasurable : Measurable (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) := by
    simpa [_root_.GD.N0232.N0720.N1080.d014176] using
      (_root_.GD.N0232.N0720.d014162 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn))
  have hfallbackEquivariant :
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y)
        (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) := by
    intro g omega
    simpa [_root_.GD.N0232.N0720.N1080.d014176, _root_.GD.N0232.N0720.N1214.d014259] using
      (_root_.GD.N0232.N0720.d014164
        (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn) g.shift g.d009241 omega)
  have hcov := _root_.GD.N0232.N0720.N1214.d014270
    m n p hmem hfixed
  obtain ⟨repaired, hrepairedMeasurable, hrepairedReference,
      hrepairedEquivariant⟩ :=
    _root_.GD.N0230.N0605.d000343
      (G := _root_.GD.N0232.N0719.N0946.d009229) (X := _root_.GD.N0232.N0720.N1080.d014170 m n)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) _root_.GD.N0232.N0719.N0946.d009229.d009254
      (_root_.GD.N0232.N0720.N1214.d014265 m n p) (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn)
      (_root_.GD.N0232.N0720.N1214.d014266 m n p)
      hfallbackMeasurable hfallbackEquivariant hcov
      _root_.GD.N0232.N0719.N0946.d009229.d009257
  refine ⟨repaired, hrepairedMeasurable, ?_, hrepairedEquivariant⟩
  intro theta
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
    hrepairedReference

end

end N1214
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1214.d014270
#print axioms _root_.GD.N0232.N0720.N1214.d014271
