import GD.Module1222
import GD.Module1216

set_option autoImplicit false
set_option warningAsError true










open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0719.N0997

open _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329
  (d019654 d019656 d019658)
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0107

noncomputable section



theorem d019803 {A : Type*} [Fintype A]
    {B : A → Type*} [∀ a, Fintype (B a)]
    (mu : (a : A) → B a → Measure ℝ) [∀ a b, SigmaFinite (mu a b)] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (a : A) (_ : B a) => ℝ)).symm
      (Measure.pi fun a => Measure.pi (mu a))
      (Measure.pi fun z : Sigma B => mu z.1 z.2) where
  measurable := (MeasurableEquiv.piCurry (fun (a : A) (_ : B a) => ℝ)).symm.measurable
  map_eq := by
    refine (Measure.pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have heq : (MeasurableEquiv.piCurry (fun (a : A) (_ : B a) => ℝ)).symm ⁻¹'
        Set.univ.pi s = Set.univ.pi (fun a => Set.univ.pi (fun b => s ⟨a, b⟩)) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      exact Sigma.forall
    rw [heq, Measure.pi_pi]
    simp only [Measure.pi_pi, Fintype.prod_sigma]

variable {k d : ℕ} (sizes : Fin k → ℕ)

abbrev d019804 := _root_.GD.N0232.N0719.d009173 k sizes

def d019805 (hdim : (∑ i, sizes i) = d + 1) :
    (Sigma fun i => Fin (sizes i)) ≃ Fin (d + 1) :=
  (Fintype.equivFin _).trans (finCongr (by simpa using hdim))

def d019806 (hdim : (∑ i, sizes i) = d + 1) (j : Fin (d + 1)) : Fin k :=
  ((_root_.GD.N0232.N0719.N0997.d019805 sizes hdim).symm j).1

def d019807 (hdim : (∑ i, sizes i) = d + 1) :
    _root_.GD.N0232.N0719.N0997.d019804 sizes ≃ᵐ _root_.GD.N0232.N0720.N1341.d004414 d :=
  ((MeasurableEquiv.piCurry (fun (i : Fin k) (_ : Fin (sizes i)) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (d + 1) => ℝ)
      (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim))).trans
    (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ))

@[simp] theorem d019808 (hdim : (∑ i, sizes i) = d + 1)
    (x : _root_.GD.N0232.N0720.N1341.d004414 d)
    (i : Fin k) (j : Fin (sizes i)) :
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x i j = x (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩) := rfl

theorem d019809 (hdim : (∑ i, sizes i) = d + 1) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim) volume volume := by
  have h := (PiLp.volume_preserving_toLp (Fin (d + 1))).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (d + 1) => ℝ)
      (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim)).comp
      (_root_.GD.N0232.N0719.N0997.d019803 (fun (i : Fin k) (_ : Fin (sizes i)) => volume)))
  simpa only [_root_.GD.N0232.N0719.N0997.d019807, MeasurableEquiv.coe_trans, Function.comp_assoc] using! h

theorem d019810 (hdim : (∑ i, sizes i) = d + 1)
    (c : ℝ) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm (c • x) = c • (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x := by
  funext i j
  rfl

def d019811 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (i : Fin k) : ℝ := Real.sqrt (q.2 i : ℝ)

theorem d019812 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (i : Fin k) : 0 < _root_.GD.N0232.N0719.N0997.d019811 q i :=
  Real.sqrt_pos.mpr (q.2 i).2.1

theorem d019813 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0719.N0997.d019811 q i) = _root_.GD.N0232.N0720.N1329.d019654 (q.2 i) := by
  apply Subtype.ext
  exact Real.sq_sqrt (q.2 i).2.1.le


theorem d019814 (hdim : (∑ i, sizes i) = d + 1)
    (q : _root_.GD.N0232.N0719.N0988.d019777 k) :
    (_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)).map (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim) =
      volume.withDensity (fun x => ENNReal.ofReal
        (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x)) := by
  let p := _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q
  let mu : Fin (d + 1) → Measure ℝ :=
    fun j => gaussianReal p.1 (_root_.GD.N0232.N0720.N1329.d019654 (p.2 j))
  have hsplit := _root_.GD.N0232.N0719.N0997.d019803
    (fun (i : Fin k) (j : Fin (sizes i)) => mu (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩))
  have hreindex := measurePreserving_piCongrLeft mu (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim)
  have htoLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ))
      (Measure.pi mu) (_root_.GD.N0232.N0720.N1329.d019656 p) := ⟨(MeasurableEquiv.toLp _ _).measurable, rfl⟩
  have h := (htoLp.comp (hreindex.comp hsplit)).map_eq
  have hraw : _root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q) =
      Measure.pi (fun i => Measure.pi (fun j : Fin (sizes i) =>
        mu (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩))) := by
    unfold _root_.GD.N0232.N0719.d009176
    congr 1
    funext i
    rw [_root_.GD.N0232.N0719.N0932.d009211, _root_.GD.N0232.N0719.N0997.d019813]
    congr 1
    funext j
    simp [mu, p, _root_.GD.N0232.N0719.N0988.d019779, _root_.GD.N0232.N0719.N0997.d019806]
  rw [hraw]
  calc
    _ = _root_.GD.N0232.N0720.N1329.d019656 p := by
      simpa only [_root_.GD.N0232.N0719.N0997.d019807, MeasurableEquiv.coe_trans, Function.comp_assoc] using! h
    _ = _ := _root_.GD.N0232.N0720.N1329.d019658 p


theorem d019815 (hdim : (∑ i, sizes i) = d + 1)
    (q : _root_.GD.N0232.N0719.N0988.d019777 k)
    (f : _root_.GD.N0232.N0720.N1341.d004414 d → ℝ)
    (hf : Measurable f) :
    (∫⁻ omega, ENNReal.ofReal ((f (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega) - q.1) ^ 2)
      ∂_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)) =
      ∫⁻ x, ENNReal.ofReal ((f x - q.1) ^ 2)
        ∂volume.withDensity (fun x => ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x)) := by
  rw [← _root_.GD.N0232.N0719.N0997.d019814 sizes hdim q]
  exact (lintegral_map ((hf.sub measurable_const).pow_const 2 |>.ennreal_ofReal)
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).measurable).symm

end
end GD.N0232.N0719.N0997

#print axioms _root_.GD.N0232.N0719.N0997.d019814
#print axioms _root_.GD.N0232.N0719.N0997.d019815
