import GD.Module1857
import GD.Module1858
import GD.Module1874

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology
namespace GD.N0127
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0099 _root_.GD.N0036
open _root_.GD.N0026
open _root_.GD.N0232.N0720.N1220
variable {k : ℕ}

def d030683 (sizes : Fin (k + 2) → ℕ)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (C : ℝ) (θ : _root_.GD.N0099.d022908) : ℝ :=
  C * _root_.GD.N0026.d030459 (sizes i) (sizes (i.succAbove j)) θ

def d030684 (sizes : Fin (k + 2) → ℕ)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (C : ℝ)
    (H : ℝ) (hH : 0 < H) (θ : _root_.GD.N0099.d022908) : ℝ :=
  C * _root_.GD.N0026.d030460 sizes i j θ H hH

theorem d030685
    (sizes : Fin (k + 2) → ℕ) (_hk : 0 < k) (_hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * (_root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ
        (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes)).toReal))
    (F : Finset _root_.GD.N0099.d022908) (w : _root_.GD.N0099.d022908 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (B : ℝ) (hB : 0 < B)
    (hloc : ∀ θ, θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F →
      |θ.location| ≤ B) (ε : ℝ) (hε : 0 < ε) :
    _root_.GD.N0232.N0720.N1220.d017301 (sizes i) (sizes (i.succAbove j)) F w ≤
      _root_.GD.N0026.d030468 sizes i j ε *
        (_root_.GD.N0127.d030684 sizes i j C (_root_.GD.N0026.d030466 B ε)
          (_root_.GD.N0026.d030467 hB hε)
          _root_.GD.N0232.N0720.N1080.d014169 +
        ∑ θ ∈ F, w θ * _root_.GD.N0127.d030684 sizes i j C (_root_.GD.N0026.d030466 B ε)
          (_root_.GD.N0026.d030467 hB hε) θ) := by
  classical
  let m := sizes i
  let n := sizes (i.succAbove j)
  let cost := _root_.GD.N0026.d030468 sizes i j ε
  have hc : 0 < cost := Finset.prod_pos fun _ _ => pow_pos (_root_.GD.N0036.d022653 ε hε) _
  let L := B / ε
  have hL : 0 < L := div_pos hB hε
  let H := _root_.GD.N0026.d030466 B ε
  have hH : 0 < H := _root_.GD.N0026.d030467 hB hε
  have htwice : 2 * H = (1 + ε) * L := by dsimp [H, L, _root_.GD.N0026.d030466]; ring
  let ν := _root_.GD.N0232.N0719.d009176 k (_root_.GD.N0099.d022902 sizes i j) 0 (fun _ => L)
  let η : _root_.GD.N0099.d022908 → Measure (_root_.GD.N0232.N0719.N0859.d010811 k (_root_.GD.N0099.d022902 sizes i j)) :=
    fun θ => _root_.GD.N0232.N0719.d009176 k (_root_.GD.N0099.d022902 sizes i j) θ.location (fun _ => 2 * H)
  let D := fun z => _root_.GD.N0099.d022746 B (d ((_root_.GD.N0099.d022903 sizes i j).symm z))
  have hD : Measurable D := (_root_.GD.N0099.d022749 B).comp
    (hd.comp (_root_.GD.N0099.d022903 sizes i j).symm.measurable)
  have hDb : ∀ z, |D z| ≤ B := fun z => _root_.GD.N0099.d022747 B hB.le _
  have hdom (θ : _root_.GD.N0099.d022908)
      (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
      ν ≤ ENNReal.ofReal cost • η θ := by
    have hh := _root_.GD.N0036.d022658 k (_root_.GD.N0099.d022902 sizes i j) ε L θ.location hε hL
      (show |θ.location| ≤ ε * L by
        simpa only [L, mul_div_cancel₀ _ hε.ne'] using hloc θ hθ)
    simpa only [ν, η, cost, _root_.GD.N0026.d030468, htwice] using hh
  have hupper (θ : _root_.GD.N0099.d022908)
      (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
      (∫ z, (D z - θ.location) ^ 2 ∂
        (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ)) ≤
      _root_.GD.N0127.d030684 sizes i j C H hH θ := by
    let θ' := _root_.GD.N0099.d022905 i j θ H hH
    let f := fun ω => _root_.GD.N0099.d022746 B (d ω)
    have hf : Measurable f := (_root_.GD.N0099.d022749 B).comp hd
    letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') := by
      unfold _root_.GD.N0232.N0719.N0859.d010812
      infer_instance
    have hmem := _root_.GD.N0099.d022750 (_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ')
      f hf B (fun ω => _root_.GD.N0099.d022747 B hB.le (d ω)) θ.location
    have hraw : _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ' f =
        ENNReal.ofReal (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') :=
      (ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
    have hclip : _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ' f ≤
        _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ' d := by
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (_root_.GD.N0099.d022748 B θ.location (d ω) hB.le (hloc θ hθ))
    have hrealGD : (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') ≤
        C * _root_.GD.N0026.d030460 sizes i j θ H hH := by
      apply (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hC ENNReal.toReal_nonneg)).mp
      rw [← hraw]
      exact hclip.trans (hbase θ')
    have heq := (_root_.GD.N0099.d022906 sizes i j θ H hH).integral_comp'
      (fun z => (D z - θ.location) ^ 2)
    have heq' : (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') =
        ∫ z, (D z - θ.location) ^ 2 ∂
          (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ) := by
      simpa only [D, f, MeasurableEquiv.symm_apply_apply] using heq
    rw [← heq']
    exact hrealGD
  exact _root_.GD.N0099.d022754 m n F w hw ν η D hD B hDb cost hc.le
    (_root_.GD.N0127.d030684 sizes i j C H hH) hdom hupper

theorem d030686
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (hlimit : _root_.GD.N0026.d030461 sizes i j)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * (_root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ
        (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes)).toReal)) :
    ∃ g : _root_.GD.N0232.N0720.N1080.d014170
        (sizes i) (sizes (i.succAbove j)) → ℝ, Measurable g ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197
        (sizes i) (sizes (i.succAbove j)) θ g ≤
        ENNReal.ofReal (C * _root_.GD.N0026.d030459 (sizes i) (sizes (i.succAbove j)) θ) := by
  classical
  let m := sizes i
  let n := sizes (i.succAbove j)
  have hbudget : ∀ θ, 0 ≤ _root_.GD.N0127.d030683 sizes i j C θ := fun θ =>
    mul_nonneg hC ENNReal.toReal_nonneg
  have htest : ∀ (F : Finset _root_.GD.N0099.d022908) (w : _root_.GD.N0099.d022908 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤
        _root_.GD.N0127.d030683 sizes i j C
          _root_.GD.N0232.N0720.N1080.d014169 +
        ∑ θ ∈ F, w θ * _root_.GD.N0127.d030683 sizes i j C θ := by
    intro F w hw
    let B := 1 + ∑ θ ∈ F, |θ.location|
    have hB : 0 < B := by dsimp [B]; positivity
    have hloc (θ : _root_.GD.N0099.d022908)
        (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
        |θ.location| ≤ B := by
      rcases hθ with rfl | hθ
      · change |(0 : ℝ)| ≤ B
        simpa using hB.le
      · have hh := Finset.single_le_sum (fun θ _ => abs_nonneg θ.location) hθ
        dsimp [B]
        linarith
    let ε : ℕ → ℝ := fun r => 1 / ((r : ℝ) + 1)
    have hε : ∀ r, 0 < ε r := fun r => by dsimp [ε]; positivity
    let H : ℕ → ℝ := fun r => _root_.GD.N0026.d030466 B (ε r)
    have hH : ∀ r, 0 < H r := fun r => _root_.GD.N0026.d030467 hB (hε r)
    have hHtop : Tendsto H atTop atTop := by
      have hnat : Tendsto (fun r : ℕ => (r : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
      have hmul := Filter.Tendsto.const_mul_atTop
        (show 0 < B / 2 by positivity) hnat
      convert hmul using 1
      funext r
      dsimp [H, ε, _root_.GD.N0026.d030466]
      have hr : (r : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hr]
      ring
    have hcost : Tendsto (fun r => _root_.GD.N0026.d030468 sizes i j (ε r)) atTop (𝓝 1) := by
      have hc : Continuous (_root_.GD.N0026.d030468 sizes i j) :=
        continuous_finsetProd _ (fun _ _ => _root_.GD.N0036.d022659.pow _)
      simpa only [Function.comp_def, _root_.GD.N0026.d030468, _root_.GD.N0036.d022660,
        one_pow, Finset.prod_const_one] using
        (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have hbud (θ : _root_.GD.N0099.d022908) :
        Tendsto (fun r => _root_.GD.N0127.d030684 sizes i j C (H r) (hH r) θ) atTop
          (𝓝 (_root_.GD.N0127.d030683 sizes i j C θ)) :=
      tendsto_const_nhds.mul (hlimit θ H hH hHtop)
    have hsum := (hbud _root_.GD.N0232.N0720.N1080.d014169).add
      (tendsto_finsetSum F (fun θ _ => (tendsto_const_nhds (x := w θ)).mul (hbud θ)))
    have hfinal := hcost.mul hsum
    apply ge_of_tendsto' (by simpa only [one_mul] using hfinal)
    intro r
    exact _root_.GD.N0127.d030685 sizes hk hn i j d hd C hC hbase
      F w hw B hB hloc (ε r) (hε r)
  obtain ⟨p, hp⟩ := (_root_.GD.N0232.N0720.N1220.d017305 m n (hn i) (hn (i.succAbove j))
    (_root_.GD.N0127.d030683 sizes i j C) hbudget).mpr htest
  refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n p,
    _root_.GD.N0232.N0720.N1214.d014266 m n p, ?_⟩
  intro θ
  rw [_root_.GD.N0232.N0720.N1215.d014286]
  exact hp θ



theorem d030687
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (hdeleted : ∀ l, l ≠ i → l ≠ i.succAbove j → 4 ≤ sizes l)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * (_root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ
        (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes)).toReal)) :
    ∃ g : _root_.GD.N0232.N0720.N1080.d014170
        (sizes i) (sizes (i.succAbove j)) → ℝ, Measurable g ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197
        (sizes i) (sizes (i.succAbove j)) θ g ≤
        ENNReal.ofReal (C * _root_.GD.N0026.d030459 (sizes i) (sizes (i.succAbove j)) θ) :=
  _root_.GD.N0127.d030686 sizes hk hn i j
    (_root_.GD.N0050.d030476
      sizes hn i j hdeleted) d hd C hC hbase

end
end GD.N0127
#print axioms _root_.GD.N0127.d030685
#print axioms _root_.GD.N0127.d030686
#print axioms _root_.GD.N0127.d030687
