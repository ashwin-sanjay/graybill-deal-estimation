import GD.Module0876

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0005.N0252

open _root_.GD.N0228.N0547
open _root_.GD.N0228.N0547.N0778 _root_.GD.N0228.N0547.N0790
open _root_.GD.N0228.N0547.N0787 _root_.GD.N0228.N0547.N0783

noncomputable section

def d030005 (r s : ℕ) (rho : ℝ) : ℝ :=
  rho / r + (1 - rho) / s

def d030006 (r s : ℕ) (rho : ℝ) : ℝ :=
  (rho / r) / _root_.GD.N0005.N0252.d030005 r s rho

def d030007 (r s : ℕ) (rho : ℝ) (q : ℝ × ℝ) : ℝ :=
  rho / r * q.1 + (1 - rho) / s * q.2

def d030008 (r s : ℕ) (rho shift : ℝ) (z : _root_.GD.N0228.N0547.N0783.d013523) : ℝ :=
  (z.1 + shift) / Real.sqrt (_root_.GD.N0005.N0252.d030007 r s rho z.2)

def d030009 (shift : ℝ) (z : _root_.GD.N0228.N0547.N0783.d013523) : _root_.GD.N0228.N0547.N0783.d013523 :=
  (z.1 + shift, z.2)

def d030010 (r s : ℕ) (rho shift : ℝ) : Measure ℝ :=
  (_root_.GD.N0228.N0547.N0790.d012894 r s).map (_root_.GD.N0005.N0252.d030008 r s rho shift)

def d030011 (r s : ℕ) (rho shift : ℝ) : Measure (ℝ × ℝ) :=
  (_root_.GD.N0228.N0547.N0790.d012894 r s).map (_root_.GD.N0228.N0547.N0787.d012939 rho ∘ _root_.GD.N0005.N0252.d030009 shift)

@[fun_prop] theorem d030012 (r s : ℕ) (rho shift : ℝ) :
    Measurable (_root_.GD.N0005.N0252.d030008 r s rho shift) := by
  unfold _root_.GD.N0005.N0252.d030008 _root_.GD.N0005.N0252.d030007
  fun_prop

@[fun_prop] theorem d030013 (shift : ℝ) :
    Measurable (_root_.GD.N0005.N0252.d030009 shift) := by
  unfold _root_.GD.N0005.N0252.d030009
  fun_prop

theorem d030014 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) :
    0 < _root_.GD.N0005.N0252.d030005 r s rho := by
  unfold _root_.GD.N0005.N0252.d030005
  positivity

theorem d030015 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) :
    _root_.GD.N0005.N0252.d030006 r s rho ∈ Ioo (0 : ℝ) 1 := by
  have hc := _root_.GD.N0005.N0252.d030014 hr hs h0 h1
  have hb : 0 < (1 - rho) / (s : ℝ) := by positivity
  constructor
  · exact div_pos (by positivity) hc
  · rw [_root_.GD.N0005.N0252.d030006, div_lt_one hc]
    unfold _root_.GD.N0005.N0252.d030005
    linarith

theorem d030016 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1)
    {q : ℝ × ℝ} (hq1 : 0 < q.1) (hq2 : 0 < q.2) :
    0 < _root_.GD.N0005.N0252.d030007 r s rho q := by
  unfold _root_.GD.N0005.N0252.d030007
  positivity

theorem d030017 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) (z : _root_.GD.N0228.N0547.N0783.d013523) :
    _root_.GD.N0005.N0252.d030007 r s rho z.2 =
      _root_.GD.N0005.N0252.d030005 r s rho * _root_.GD.N0228.N0547.N0787.d012938 (_root_.GD.N0005.N0252.d030006 r s rho) z := by
  let A := rho / (r : ℝ)
  let B := (1 - rho) / (s : ℝ)
  have hc : A + B ≠ 0 := (_root_.GD.N0005.N0252.d030014 hr hs h0 h1).ne'
  change A * z.2.1 + B * z.2.2 =
    (A + B) * (A / (A + B) * z.2.1 + (1 - A / (A + B)) * z.2.2)
  field_simp
  ring

theorem d030018 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) (shift : ℝ)
    {z : _root_.GD.N0228.N0547.N0783.d013523} (hz1 : 0 < z.2.1) (hz2 : 0 < z.2.2) :
    _root_.GD.N0005.N0252.d030008 r s rho shift z ^ 2 =
      (_root_.GD.N0228.N0547.N0787.d012939 (_root_.GD.N0005.N0252.d030006 r s rho) (_root_.GD.N0005.N0252.d030009 shift z)).1 /
        _root_.GD.N0005.N0252.d030005 r s rho := by
  have hD := _root_.GD.N0005.N0252.d030016 hr hs h0 h1 hz1 hz2
  rw [_root_.GD.N0005.N0252.d030008, div_pow, Real.sq_sqrt hD.le,
    _root_.GD.N0005.N0252.d030017 hr hs h0 h1]
  simp only [_root_.GD.N0228.N0547.N0787.d012939, _root_.GD.N0005.N0252.d030009, _root_.GD.N0228.N0547.N0787.d012938]
  rw [div_div, mul_comm (_root_.GD.N0005.N0252.d030005 r s rho)]

theorem d030019 {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ᵐ q ∂(_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s), 0 < q.1 ∧ 0 < q.2 := by
  letI := _root_.GD.N0228.N0547.N0790.d012889 hr
  letI := _root_.GD.N0228.N0547.N0790.d012889 hs
  have ha {d : ℕ} (hd : 0 < d) : ∀ᵐ q ∂_root_.GD.N0228.N0547.N0778.d009365 d, 0 < q := by
    unfold _root_.GD.N0228.N0547.N0778.d009365
    exact _root_.GD.N0232.N0720.N1091.d012773
      (by positivity) (by norm_num)
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_Ioi.prod measurableSet_Ioi)).2
  filter_upwards [ha hr] with q1 hq1
  filter_upwards [ha hs] with q2 hq2
  exact ⟨hq1, hq2⟩

theorem d030020 {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ᵐ z ∂_root_.GD.N0228.N0547.N0790.d012894 r s, 0 < z.2.1 ∧ 0 < z.2.2 := by
  letI := _root_.GD.N0228.N0547.N0790.d012889 hr
  letI := _root_.GD.N0228.N0547.N0790.d012889 hs
  unfold _root_.GD.N0228.N0547.N0790.d012894
  have hm : MeasurableSet {z : _root_.GD.N0228.N0547.N0783.d013523 | 0 < z.2.1 ∧ 0 < z.2.2} :=
    (measurableSet_Ioi.preimage (measurable_fst.comp measurable_snd)).inter
      (measurableSet_Ioi.preimage (measurable_snd.comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hm).2
  filter_upwards with z
  exact _root_.GD.N0005.N0252.d030019 hr hs

theorem d030021 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (rho shift : ℝ) : IsProbabilityMeasure (_root_.GD.N0005.N0252.d030010 r s rho shift) := by
  letI := _root_.GD.N0228.N0547.N0790.d012889 hr
  letI := _root_.GD.N0228.N0547.N0790.d012889 hs
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012894 r s) := by
    unfold _root_.GD.N0228.N0547.N0790.d012894
    infer_instance
  exact Measure.isProbabilityMeasure_map (_root_.GD.N0005.N0252.d030012 r s rho shift).aemeasurable

theorem d030022 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (rho shift : ℝ) : IsProbabilityMeasure (_root_.GD.N0005.N0252.d030011 r s rho shift) := by
  letI := _root_.GD.N0228.N0547.N0790.d012889 hr
  letI := _root_.GD.N0228.N0547.N0790.d012889 hs
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012894 r s) := by
    unfold _root_.GD.N0228.N0547.N0790.d012894
    infer_instance
  exact Measure.isProbabilityMeasure_map
    ((_root_.GD.N0228.N0547.N0787.d012940 rho).comp (_root_.GD.N0005.N0252.d030013 shift)).aemeasurable

theorem d030023 (r s : ℕ) (rho : ℝ) :
    _root_.GD.N0005.N0252.d030011 r s rho 0 = _root_.GD.N0228.N0547.N0787.d012941 r s rho := by
  unfold _root_.GD.N0005.N0252.d030011 _root_.GD.N0228.N0547.N0787.d012941
  congr 1
  funext z
  simp only [Function.comp_apply, _root_.GD.N0005.N0252.d030009, add_zero]

theorem d030024 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) (shift : ℝ) :
    (_root_.GD.N0005.N0252.d030010 r s rho shift).map (fun x => x ^ 2) =
      (_root_.GD.N0005.N0252.d030011 r s (_root_.GD.N0005.N0252.d030006 r s rho) shift).map
        (fun tx => tx.1 / _root_.GD.N0005.N0252.d030005 r s rho) := by
  rw [_root_.GD.N0005.N0252.d030010, _root_.GD.N0005.N0252.d030011,
    Measure.map_map (by fun_prop) (_root_.GD.N0005.N0252.d030012 r s rho shift),
    Measure.map_map (by fun_prop)
      ((_root_.GD.N0228.N0547.N0787.d012940 _).comp (_root_.GD.N0005.N0252.d030013 shift))]
  apply Measure.map_congr
  filter_upwards [_root_.GD.N0005.N0252.d030020 hr hs] with z hz
  exact _root_.GD.N0005.N0252.d030018 hr hs h0 h1 shift hz.1 hz.2

theorem d030025 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) :
    (_root_.GD.N0005.N0252.d030010 r s rho 0).map (fun x => x ^ 2) =
      (_root_.GD.N0228.N0547.N0787.d012941 r s (_root_.GD.N0005.N0252.d030006 r s rho)).map
        (fun tx => tx.1 / _root_.GD.N0005.N0252.d030005 r s rho) := by
  rw [_root_.GD.N0005.N0252.d030024 hr hs h0 h1, _root_.GD.N0005.N0252.d030023]

theorem d030026 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) :
    (_root_.GD.N0005.N0252.d030010 r s rho 0).map (fun x => x ^ 2) =
      (_root_.GD.N0228.N0547.N0783.d013537 r s (_root_.GD.N0005.N0252.d030006 r s rho)).map
        (fun tx => tx.1 / _root_.GD.N0005.N0252.d030005 r s rho) := by
  have ht := _root_.GD.N0005.N0252.d030015 hr hs h0 h1
  rw [_root_.GD.N0005.N0252.d030025 hr hs h0 h1,
    _root_.GD.N0228.N0547.N0783.d013551 hr hs ht.1 ht.2]

theorem d030027 {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {rho : ℝ} (h0 : 0 < rho) (h1 : rho < 1) (shift x : ℝ) :
    _root_.GD.N0005.N0252.d030010 r s rho shift (Iic x) =
      ∫⁻ q, (gaussianReal 0 1)
        (Iic (x * Real.sqrt (_root_.GD.N0005.N0252.d030007 r s rho q) - shift))
        ∂(_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s) := by
  letI := _root_.GD.N0228.N0547.N0790.d012889 hr
  letI := _root_.GD.N0228.N0547.N0790.d012889 hs
  rw [_root_.GD.N0005.N0252.d030010, Measure.map_apply (_root_.GD.N0005.N0252.d030012 r s rho shift) measurableSet_Iic,
    _root_.GD.N0228.N0547.N0790.d012894, Measure.prod_apply_symm
      (measurableSet_Iic.preimage (_root_.GD.N0005.N0252.d030012 r s rho shift))]
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0005.N0252.d030019 hr hs] with q hq
  congr 1
  ext z
  change (z + shift) / Real.sqrt (_root_.GD.N0005.N0252.d030007 r s rho q) ≤ x ↔
    z ≤ x * Real.sqrt (_root_.GD.N0005.N0252.d030007 r s rho q) - shift
  rw [div_le_iff₀ (Real.sqrt_pos.mpr (_root_.GD.N0005.N0252.d030016 hr hs h0 h1 hq.1 hq.2))]
  exact le_sub_iff_add_le.symm

end
end GD.N0005.N0252

#print axioms _root_.GD.N0005.N0252.d030026
#print axioms _root_.GD.N0005.N0252.d030024
#print axioms _root_.GD.N0005.N0252.d030027
#print axioms _root_.GD.N0005.N0252.d030021
