import GD.Module1442
import GD.Module1856
import GD.Module1369

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace GD.N0026
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0099 _root_.GD.N0036
open _root_.GD.N0232.N0720.N1220

variable {k : ℕ}

def d030459 (m n : ℕ) (θ : _root_.GD.N0099.d022908) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014197 m n θ
    (_root_.GD.N0232.N0720.N1080.d014175 m n)).toReal

def d030460 (sizes : Fin (k + 2) → ℕ)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (θ : _root_.GD.N0099.d022908)
    (H : ℝ) (hH : 0 < H) : ℝ :=
  (_root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes
    (_root_.GD.N0099.d022905 i j θ H hH) (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes)).toReal




def d030461 (sizes : Fin (k + 2) → ℕ)
    (i : Fin (k + 2)) (j : Fin (k + 1)) : Prop :=
  ∀ (θ : _root_.GD.N0099.d022908) (H : ℕ → ℝ) (hH : ∀ r, 0 < H r),
    Tendsto H atTop atTop →
    Tendsto (fun r => _root_.GD.N0026.d030460 sizes i j θ (H r) (hH r)) atTop
      (𝓝 (_root_.GD.N0026.d030459 (sizes i) (sizes (i.succAbove j)) θ))

theorem d030462 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (θ : _root_.GD.N0099.d022908) :
    ENNReal.ofReal (_root_.GD.N0026.d030459 m n θ) =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ
        (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  apply ENNReal.ofReal_toReal
  rw [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn,
    _root_.GD.N0232.N0720.N1080.d014184 m n hm hn]
  exact ENNReal.ofReal_ne_top

theorem d030463 (sizes : Fin (k + 2) → ℕ)
    (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (θ : _root_.GD.N0099.d022908)
    (H : ℝ) (hH : 0 < H) :
    ENNReal.ofReal (_root_.GD.N0026.d030460 sizes i j θ H hH) =
      _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes
        (_root_.GD.N0099.d022905 i j θ H hH) (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes) := by
  apply ENNReal.ofReal_toReal
  rw [_root_.GD.N0232.N0719.N0972.d012341 (k + 2) sizes (by omega) hn]
  exact ENNReal.ofReal_ne_top

def d030464 (sizes : Fin (k + 2) → ℕ)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (C : ℝ) (θ : _root_.GD.N0099.d022908) : ℝ :=
  min (C * _root_.GD.N0232.N0720.N1257.d015508
      (sizes i) (sizes (i.succAbove j)) θ)
    (_root_.GD.N0026.d030459 (sizes i) (sizes (i.succAbove j)) θ)

def d030465 (sizes : Fin (k + 2) → ℕ)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (C : ℝ)
    (H : ℝ) (hH : 0 < H) (θ : _root_.GD.N0099.d022908) : ℝ :=
  min (C * _root_.GD.N0232.N0720.N1257.d015508
      (sizes i) (sizes (i.succAbove j)) θ)
    (_root_.GD.N0026.d030460 sizes i j θ H hH)

def d030466 (B ε : ℝ) : ℝ := (1 + ε) * (B / ε) / 2

theorem d030467 {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) :
    0 < _root_.GD.N0026.d030466 B ε := by unfold _root_.GD.N0026.d030466; positivity

def d030468 (sizes : Fin (k + 2) → ℕ)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (ε : ℝ) : ℝ :=
  ∏ l, _root_.GD.N0036.d022652 ε ^ _root_.GD.N0099.d022902 sizes i j l



theorem d030469
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ
        (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes))
    (F : Finset _root_.GD.N0099.d022908) (w : _root_.GD.N0099.d022908 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (B : ℝ) (hB : 0 < B)
    (hloc : ∀ θ, θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F →
      |θ.location| ≤ B) (ε : ℝ) (hε : 0 < ε) :
    _root_.GD.N0232.N0720.N1220.d017301 (sizes i) (sizes (i.succAbove j)) F w ≤
      _root_.GD.N0026.d030468 sizes i j ε *
        (_root_.GD.N0026.d030465 sizes i j C (_root_.GD.N0026.d030466 B ε)
          (_root_.GD.N0026.d030467 hB hε)
          _root_.GD.N0232.N0720.N1080.d014169 +
        ∑ θ ∈ F, w θ * _root_.GD.N0026.d030465 sizes i j C (_root_.GD.N0026.d030466 B ε)
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
      _root_.GD.N0026.d030465 sizes i j C H hH θ := by
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
    have hreal : (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') ≤
        C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ' := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC
        (_root_.GD.N0232.N0719.N0963.d012143 (k + 2) sizes (by omega)
          (fun l => by have := hn l; omega) θ').le)).mp
      rw [← hraw]
      exact hclip.trans (hcap θ')
    have hrealGD : (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') ≤
        _root_.GD.N0026.d030460 sizes i j θ H hH := by
      apply (ENNReal.ofReal_le_ofReal_iff
        (show 0 ≤ _root_.GD.N0026.d030460 sizes i j θ H hH from ENNReal.toReal_nonneg)).mp
      rw [← hraw, _root_.GD.N0026.d030463 sizes hk hn i j θ H hH]
      exact hclip.trans (hbase θ')
    have heq := (_root_.GD.N0099.d022906 sizes i j θ H hH).integral_comp'
      (fun z => (D z - θ.location) ^ 2)
    have heq' : (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') =
        ∫ z, (D z - θ.location) ^ 2 ∂
          (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ) := by
      simpa only [D, f, MeasurableEquiv.symm_apply_apply] using heq
    rw [← heq']
    exact le_min (hreal.trans (mul_le_mul_of_nonneg_left
      (_root_.GD.N0099.d022907 sizes hn i j θ H hH) hC)) hrealGD
  exact _root_.GD.N0099.d022754 m n F w hw ν η D hD B hDb cost hc.le
    (_root_.GD.N0026.d030465 sizes i j C H hH) hdom hupper



theorem d030470
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (hlimit : _root_.GD.N0026.d030461 sizes i j)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ
        (_root_.GD.N0232.N0719.N0859.d010815 (k + 2) sizes)) :
    ∃ g : _root_.GD.N0232.N0720.N1080.d014170
        (sizes i) (sizes (i.succAbove j)) → ℝ, Measurable g ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197
        (sizes i) (sizes (i.succAbove j)) θ g ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508
          (sizes i) (sizes (i.succAbove j)) θ)) ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197
        (sizes i) (sizes (i.succAbove j)) θ g ≤
        _root_.GD.N0232.N0720.N1080.d014197
          (sizes i) (sizes (i.succAbove j)) θ
          (_root_.GD.N0232.N0720.N1080.d014175
            (sizes i) (sizes (i.succAbove j))) := by
  classical
  let m := sizes i
  let n := sizes (i.succAbove j)
  have hbudget : ∀ θ, 0 ≤ _root_.GD.N0026.d030464 sizes i j C θ := fun θ =>
    le_min (mul_nonneg hC
      (_root_.GD.N0232.N0720.N1257.d015509 m n θ))
      ENNReal.toReal_nonneg
  have htest : ∀ (F : Finset _root_.GD.N0099.d022908) (w : _root_.GD.N0099.d022908 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤
        _root_.GD.N0026.d030464 sizes i j C
          _root_.GD.N0232.N0720.N1080.d014169 +
        ∑ θ ∈ F, w θ * _root_.GD.N0026.d030464 sizes i j C θ := by
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
        Tendsto (fun r => _root_.GD.N0026.d030465 sizes i j C (H r) (hH r) θ) atTop
          (𝓝 (_root_.GD.N0026.d030464 sizes i j C θ)) :=
      tendsto_const_nhds.min (hlimit θ H hH hHtop)
    have hsum := (hbud _root_.GD.N0232.N0720.N1080.d014169).add
      (tendsto_finsetSum F (fun θ _ => (tendsto_const_nhds (x := w θ)).mul (hbud θ)))
    have hfinal := hcost.mul hsum
    apply ge_of_tendsto' (by simpa only [one_mul] using hfinal)
    intro r
    exact _root_.GD.N0026.d030469 sizes hk hn i j d hd C hC hcap hbase
      F w hw B hB hloc (ε r) (hε r)
  obtain ⟨p, hp⟩ := (_root_.GD.N0232.N0720.N1220.d017305 m n (hn i) (hn (i.succAbove j))
    (_root_.GD.N0026.d030464 sizes i j C) hbudget).mpr htest
  refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n p,
    _root_.GD.N0232.N0720.N1214.d014266 m n p, ?_, ?_⟩
  · intro θ
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact (hp θ).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  · intro θ
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact ((hp θ).trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))).trans_eq
      (_root_.GD.N0026.d030462 m n (hn i) (hn (i.succAbove j)) θ)



theorem d030471
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (hlimit : _root_.GD.N0026.d030461 sizes i j)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ)
    (hd : d ∈ _root_.GD.N0213.N0502.d022050 (k + 2) sizes) :
    _root_.GD.N0022.N0255.d030394
      (sizes i) (sizes (i.succAbove j)) ≤
      _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d := by
  by_cases htop : _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d = ⊤
  · rw [htop]
    exact le_top
  let C := (_root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hvalue : ENNReal.ofReal C =
      _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d :=
    ENNReal.ofReal_toReal htop
  have hcap (θ : _root_.GD.N0232.N0719.N0859.d010809 (k + 2)) :
      _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ) := by
    apply (_root_.GD.N0232.N0719.N0962.d012192 (k + 2) sizes
      (by omega) (fun l => by have := hn l; omega) C hC θ d).mp
    rw [hvalue]
    exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 (k + 2) sizes θ d) θ
  obtain ⟨g, hg, hgc, hgb⟩ := _root_.GD.N0026.d030470
    sizes hk hn i j hlimit d hd.1 C hC hcap hd.2
  have hgw : _root_.GD.N0232.N0720.N1256.d015548
      (sizes i) (sizes (i.succAbove j)) g ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro θ
    exact (_root_.GD.N0232.N0720.N1256.d015553
      (sizes i) (sizes (i.succAbove j)) (by have := hn i; omega) C hC θ g).mpr (hgc θ)
  have hmin := _root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0720.N1256.d015547
      (sizes i) (sizes (i.succAbove j)))
    (S := _root_.GD.N0022.N0255.d030393
      (sizes i) (sizes (i.succAbove j))) (show g ∈ _ from ⟨hg, hgb⟩)
  exact hmin.trans (hgw.trans_eq hvalue)

theorem d030472
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (hlimit : _root_.GD.N0026.d030461 sizes i j) :
    _root_.GD.N0022.N0255.d030394
      (sizes i) (sizes (i.succAbove j)) ≤
      _root_.GD.N0213.N0502.d022051 (k + 2) sizes := by
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact _root_.GD.N0026.d030471 sizes hk hn i j hlimit d hd



theorem d030473
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 5)
    (hlimit : _root_.GD.N0026.d030461 sizes i j)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ)
    (hd : d ∈ _root_.GD.N0213.N0502.d022050 (k + 2) sizes) :
    _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d = ⊤ := by
  apply top_unique
  simpa only [hi, hj, _root_.GD.N0048.d030453]
    using _root_.GD.N0026.d030471 sizes hk hn i j hlimit d hd

theorem d030474
    (sizes : Fin (k + 2) → ℕ) (hk : 0 < k) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 5)
    (hlimit : _root_.GD.N0026.d030461 sizes i j) :
    _root_.GD.N0213.N0502.d022051 (k + 2) sizes = ⊤ := by
  apply top_unique
  simpa only [hi, hj, _root_.GD.N0048.d030453]
    using _root_.GD.N0026.d030472 sizes hk hn i j hlimit

end
end GD.N0026

#print axioms _root_.GD.N0026.d030462
#print axioms _root_.GD.N0026.d030463
#print axioms _root_.GD.N0026.d030469
#print axioms _root_.GD.N0026.d030470
#print axioms _root_.GD.N0026.d030471
#print axioms _root_.GD.N0026.d030472
#print axioms _root_.GD.N0026.d030473
#print axioms _root_.GD.N0026.d030474
