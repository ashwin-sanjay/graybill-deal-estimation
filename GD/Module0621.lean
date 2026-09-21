import GD.Module0620













open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0232.N0720

noncomputable section

private theorem d009053
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) :
    ∀ n : ℕ,
      Measure.pi (fun _ : Fin n => μ) ≪
        Measure.pi (fun _ : Fin n => ν) := by
  intro n
  induction n with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
      let i : Fin (n + 1) := 0
      let e :=
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => α) i
      have hprod :
          μ.prod (Measure.pi (fun _ : Fin n => μ)) ≪
            ν.prod (Measure.pi (fun _ : Fin n => ν)) :=
        hμν.prod ih
      have hmap := hprod.map e.symm.measurable
      rw [
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => μ) i).symm.map_eq,
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ν) i).symm.map_eq
      ] at hmap
      exact hmap



theorem d009054
    (n : ℕ) :
    _root_.GD.N0137.d008895 n ≪
      (volume : Measure (_root_.GD.N0137.d008894 n)) := by
  unfold _root_.GD.N0137.d008895
    _root_.GD.N0140.d006650
  rw [volume_pi]
  exact _root_.GD.N0232.N0720.d009053
    (gaussianReal 0 1) volume
    (gaussianReal_absolutelyContinuous 0 one_ne_zero) n



theorem d009055
    (n : ℕ) :
    (volume : Measure (_root_.GD.N0137.d008894 n)) ≪
      _root_.GD.N0137.d008895 n := by
  unfold _root_.GD.N0137.d008895
    _root_.GD.N0140.d006650
  rw [volume_pi]
  exact _root_.GD.N0232.N0720.d009053
    volume (gaussianReal 0 1)
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero) n

private theorem d009056
    (μ σ : ℝ) :
    (gaussianReal 0 1).map (fun x : ℝ => μ + σ * x) =
      gaussianReal μ (.mk (σ ^ 2) (sq_nonneg σ)) := by
  calc
    (gaussianReal 0 1).map (fun x : ℝ => μ + σ * x) =
        ((gaussianReal 0 1).map (fun x : ℝ => σ * x)).map
          (fun x : ℝ => μ + x) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            congr 1
    _ = (gaussianReal 0 (.mk (σ ^ 2) (sq_nonneg σ))).map
          (fun x : ℝ => μ + x) := by
            rw [gaussianReal_map_const_mul]
            simp
    _ = gaussianReal μ (.mk (σ ^ 2) (sq_nonneg σ)) := by
          rw [gaussianReal_map_const_add]
          simp

private theorem d009057
    (μ σ : ℝ) (hσ : σ ≠ 0) :
    (gaussianReal 0 1).map (fun x : ℝ => μ + σ * x) ≪ volume := by
  rw [_root_.GD.N0232.N0720.d009056]
  exact gaussianReal_absolutelyContinuous μ (by
    have hsq : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ
    have hpos :
        (0 : ℝ≥0) < ⟨σ ^ 2, sq_nonneg σ⟩ := hsq
    exact hpos.ne')

private theorem d009058
    (μ σ : ℝ) (hσ : σ ≠ 0) :
    volume ≪ (gaussianReal 0 1).map (fun x : ℝ => μ + σ * x) := by
  rw [_root_.GD.N0232.N0720.d009056]
  exact gaussianReal_absolutelyContinuous' μ (by
    have hsq : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ
    have hpos :
        (0 : ℝ≥0) < ⟨σ ^ 2, sq_nonneg σ⟩ := hsq
    exact hpos.ne')



theorem d009059
    (n : ℕ) (μ σ : ℝ) (hσ : σ ≠ 0) :
    (_root_.GD.N0137.d008895 n).map
        (_root_.GD.N0107.d009018 n μ σ) ≪
      _root_.GD.N0137.d008895 n := by
  unfold _root_.GD.N0137.d008895
    _root_.GD.N0140.d006650
    _root_.GD.N0107.d009018
  rw [Measure.pi_map_pi (fun _ => (by fun_prop :
    AEMeasurable (fun x : ℝ => μ + σ * x) (gaussianReal 0 1)))]
  exact _root_.GD.N0232.N0720.d009053
    ((gaussianReal 0 1).map (fun x : ℝ => μ + σ * x))
    (gaussianReal 0 1)
    ((_root_.GD.N0232.N0720.d009057 μ σ hσ).trans
      (gaussianReal_absolutelyContinuous' 0 one_ne_zero)) n



theorem d009060
    (n : ℕ) (μ σ : ℝ) (hσ : σ ≠ 0) :
    _root_.GD.N0137.d008895 n ≪
      (_root_.GD.N0137.d008895 n).map
        (_root_.GD.N0107.d009018 n μ σ) := by
  unfold _root_.GD.N0137.d008895
    _root_.GD.N0140.d006650
    _root_.GD.N0107.d009018
  rw [Measure.pi_map_pi (fun _ => (by fun_prop :
    AEMeasurable (fun x : ℝ => μ + σ * x) (gaussianReal 0 1)))]
  exact _root_.GD.N0232.N0720.d009053
    (gaussianReal 0 1)
    ((gaussianReal 0 1).map (fun x : ℝ => μ + σ * x))
    ((gaussianReal_absolutelyContinuous 0 one_ne_zero).trans
      (_root_.GD.N0232.N0720.d009058 μ σ hσ)) n



theorem d009061
    (m n : ℕ) (μ σ τ : ℝ) :
    _root_.GD.N0107.d009030 m n μ σ τ =
      ((_root_.GD.N0137.d008895 m).map
        (_root_.GD.N0107.d009018 m μ σ)).prod
      ((_root_.GD.N0137.d008895 n).map
        (_root_.GD.N0107.d009018 n μ τ)) := by
  unfold _root_.GD.N0107.d009030
    _root_.GD.N0107.d009024
    _root_.GD.N0137.d008914
  symm
  exact Measure.map_prod_map
    (_root_.GD.N0137.d008895 m)
    (_root_.GD.N0137.d008895 n)
    (_root_.GD.N0107.d009020 m μ σ)
    (_root_.GD.N0107.d009020 n μ τ)



theorem d009062
    (m n : ℕ)
    (μ σ τ μ' σ' τ' : ℝ)
    (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (hσ' : σ' ≠ 0) (hτ' : τ' ≠ 0) :
    _root_.GD.N0107.d009030 m n μ σ τ ≪
      _root_.GD.N0107.d009030 m n μ' σ' τ' := by
  rw [
    _root_.GD.N0232.N0720.d009061,
    _root_.GD.N0232.N0720.d009061
  ]
  exact
    ((_root_.GD.N0232.N0720.d009059
        m μ σ hσ).trans
      (_root_.GD.N0232.N0720.d009060
        m μ' σ' hσ')).prod
    ((_root_.GD.N0232.N0720.d009059
        n μ τ hτ).trans
      (_root_.GD.N0232.N0720.d009060
        n μ' τ' hτ'))





theorem d009063
    (m n : ℕ) (μ σ τ : ℝ)
    (hσ : 0 < σ) (hτ : 0 < τ) :
    (_root_.GD.N0107.d009030 m n μ σ τ ≪
        _root_.GD.N0107.d009030 m n 0 1 1)
      ∧
    (_root_.GD.N0107.d009030 m n 0 1 1 ≪
        _root_.GD.N0107.d009030 m n μ σ τ) := by
  constructor
  · exact _root_.GD.N0232.N0720.d009062
      m n μ σ τ 0 1 1 hσ.ne' hτ.ne' one_ne_zero one_ne_zero
  · exact _root_.GD.N0232.N0720.d009062
      m n 0 1 1 μ σ τ one_ne_zero one_ne_zero hσ.ne' hτ.ne'



theorem d009064
    (m n : ℕ) (μ σ τ : ℝ)
    (hσ : 0 < σ) (hτ : 0 < τ)
    {f g :
      (_root_.GD.N0137.d008894 m ×
        _root_.GD.N0137.d008894 n) → ℝ} :
    f =ᵐ[_root_.GD.N0107.d009030 m n μ σ τ] g ↔
      f =ᵐ[_root_.GD.N0107.d009030 m n 0 1 1] g := by
  let h :=
    _root_.GD.N0232.N0720.d009063
      m n μ σ τ hσ hτ
  exact ⟨fun hfg => h.2.ae_eq hfg, fun hfg => h.1.ae_eq hfg⟩

end

end GD.N0232.N0720
