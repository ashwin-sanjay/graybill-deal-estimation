import GD.Module0809
import GD.Module0811

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0213.N0502

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0232.N0719.N0970
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0586
open _root_.GD.N0230.N0602

variable (k : ℕ) (sizes : Fin k → ℕ)

def d022050 : Set (_root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :=
  {f | Measurable f ∧ ∀ θ,
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes)}

def d022051 : ℝ≥0∞ :=
  _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0213.N0502.d022050 k sizes)

theorem d022052 : _root_.GD.N0232.N0719.N0859.d010815 k sizes ∈ _root_.GD.N0213.N0502.d022050 k sizes :=
  ⟨_root_.GD.N0232.N0719.N0900.d009122 k sizes, fun _ => le_rfl⟩

theorem d022053 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ} (hf : f ∈ _root_.GD.N0213.N0502.d022050 k sizes) :
    f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
  refine ⟨hf.1, fun θ => ne_top_of_le_ne_top ?_ (hf.2 θ)⟩
  rw [_root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes, _root_.GD.N0232.N0719.N0859.d010823]
  exact ENNReal.ofReal_ne_top

def d022054 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :=
  _root_.GD.N0232.N0719.N0843.d012222 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) 1

def d022055 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (c : ℝ) :=
  _root_.GD.N0213.N0502.d022054 k sizes hk hsizes ∩ _root_.GD.N0232.N0719.N0963.d012152 k sizes c

theorem d022056 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    Monotone (_root_.GD.N0213.N0502.d022055 k sizes hk hsizes) := by
  intro a b hab x hx
  exact ⟨hx.1, _root_.GD.N0232.N0719.N0969.d012205 k sizes hab hx.2⟩

theorem d022057 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (c : ℝ) (hc : 0 ≤ c) : IsCompact (_root_.GD.N0213.N0502.d022055 k sizes hk hsizes c) := by
  apply (_root_.GD.N0232.N0719.N0843.d012223 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) (by norm_num : (0 : ℝ) ≤ 1)).inter_right
  exact (_root_.GD.N0232.N0719.N0963.d012153 k sizes hc).isClosed

theorem d022058
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (c : ℝ) (hc : 0 ≤ c)
    (hV : _root_.GD.N0213.N0502.d022051 k sizes < ENNReal.ofReal c) :
    (_root_.GD.N0213.N0502.d022055 k sizes hk hsizes c).Nonempty := by
  change (⨅ f ∈ _root_.GD.N0213.N0502.d022050 k sizes,
    _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) f) < ENNReal.ofReal c at hV
  obtain ⟨f, hf⟩ := iInf_lt_iff.mp hV
  obtain ⟨hf, hfc⟩ := iInf_lt_iff.mp hf
  let p := _root_.GD.N0232.N0719.N0970.d012312 k sizes f (_root_.GD.N0213.N0502.d022053 k sizes hk hsizes hf)
  refine ⟨toWeakSpace ℝ _ p, ?_, ?_⟩
  · refine ⟨p, ?_, rfl⟩
    intro θ
    rw [show _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f from _root_.GD.N0232.N0719.N0970.d012313 k sizes f _ θ]
    simpa only [_root_.GD.N0232.N0719.N0972.d012343, one_mul,
      _root_.GD.N0232.N0719.N0972.d012341 k sizes hk hsizes] using hf.2 θ
  · refine ⟨p, ?_, rfl⟩
    intro θ
    rw [show _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f from _root_.GD.N0232.N0719.N0970.d012313 k sizes f _ θ]
    apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
      (fun i => by have := hsizes i; omega) c hc θ f).mp
    exact (le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 k sizes θ f) θ).trans hfc.le

theorem d022059
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hfinite : _root_.GD.N0213.N0502.d022051 k sizes ≠ ⊤) :
    ∃ f ∈ _root_.GD.N0213.N0502.d022050 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0213.N0502.d022051 k sizes := by
  let v := (_root_.GD.N0213.N0502.d022051 k sizes).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0213.N0502.d022051 k sizes :=
    ENNReal.ofReal_toReal hfinite
  obtain ⟨x, hx⟩ := _root_.GD.N0230.N0586.d003514
    (_root_.GD.N0213.N0502.d022055 k sizes hk hsizes)
    (_root_.GD.N0213.N0502.d022056 k sizes hk hsizes) v
    (fun c hc => _root_.GD.N0213.N0502.d022057 k sizes hk hsizes c (hv.trans hc.le))
    (fun c hc => _root_.GD.N0213.N0502.d022058 k sizes hk hsizes c
      (hv.trans hc.le) (by rw [← hV]; exact (ENNReal.ofReal_lt_ofReal_iff (hv.trans_lt hc)).mpr hc))
  let p := (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).symm x
  have hpbase := (_root_.GD.N0232.N0719.N0843.d012225 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hsizes) 1 x).mp
      (hx (v + 1) (by linarith)).1
  have hbase : _root_.GD.N0232.N0719.N0896.d011088 k sizes p ∈ _root_.GD.N0213.N0502.d022050 k sizes := by
    refine ⟨_root_.GD.N0232.N0719.N0896.d011089 k sizes p, fun θ => ?_⟩
    rw [_root_.GD.N0232.N0719.N0896.d011093,
      _root_.GD.N0232.N0719.N0972.d012341 k sizes hk hsizes]
    simpa only [_root_.GD.N0232.N0719.N0972.d012343, one_mul] using hpbase θ
  refine ⟨_root_.GD.N0232.N0719.N0896.d011088 k sizes p, hbase, le_antisymm ?_ ?_⟩
  · rw [← hV]
    apply iSup_le
    intro θ
    apply _root_.GD.N0230.N0586.d003515 hv
    intro c hc
    apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
      (fun i => by have := hsizes i; omega) c (hv.trans hc.le) θ _).mpr
    rw [_root_.GD.N0232.N0719.N0896.d011093]
    exact (_root_.GD.N0232.N0719.N0963.d012155 k sizes c x).mp (hx c hc).2 θ
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hbase

theorem d022060
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ f ∈ _root_.GD.N0213.N0502.d022050 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0213.N0502.d022051 k sizes := by
  by_cases htop : _root_.GD.N0213.N0502.d022051 k sizes = ⊤
  · refine ⟨_root_.GD.N0232.N0719.N0859.d010815 k sizes, _root_.GD.N0213.N0502.d022052 k sizes, le_antisymm ?_ ?_⟩
    · rw [htop]; exact le_top
    · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0213.N0502.d022052 k sizes)
  · exact _root_.GD.N0213.N0502.d022059 k sizes hk hsizes htop

theorem d022061
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      f ∈ _root_.GD.N0213.N0502.d022050 k sizes ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0213.N0502.d022051 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes f := by
  obtain ⟨f, hf, hvalue⟩ := _root_.GD.N0213.N0502.d022060 k sizes hk hsizes
  have hfinite := _root_.GD.N0213.N0502.d022053 k sizes hk hsizes hf
  let e := _root_.GD.N0232.N0719.N0970.d012314 k sizes f hfinite
  have he : e ∈ _root_.GD.N0213.N0502.d022050 k sizes :=
    ⟨(_root_.GD.N0232.N0719.N0970.d012316 k sizes f hfinite).1,
      fun θ => (_root_.GD.N0232.N0719.N0970.d012315 k sizes f hfinite θ).trans (hf.2 θ)⟩
  refine ⟨e, _root_.GD.N0232.N0719.N0970.d012316 k sizes f hfinite, he, le_antisymm ?_ ?_,
    _root_.GD.N0232.N0719.N0970.d012317 k sizes f hfinite⟩
  · exact (_root_.GD.N0232.N0719.N0970.d012319 k sizes f hfinite).trans_eq hvalue
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) he

theorem d022062 :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ _root_.GD.N0213.N0502.d022051 k sizes := by
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hf.1

theorem d022063
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0213.N0502.d022051 k sizes = _root_.GD.N0232.N0719.N0962.d012188 k sizes ↔
      ∃ f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
        f ∈ _root_.GD.N0213.N0502.d022050 k sizes ∧
        _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
        _root_.GD.N0232.N0719.N0970.d012309 k sizes f := by
  constructor
  · intro h
    simpa only [h] using _root_.GD.N0213.N0502.d022061 k sizes hk hsizes
  · rintro ⟨f, _, hf, hvalue, _⟩
    apply le_antisymm
    · exact (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hf).trans_eq hvalue
    · exact _root_.GD.N0213.N0502.d022062 k sizes

end
end GD.N0213.N0502

#print axioms _root_.GD.N0213.N0502.d022060
#print axioms _root_.GD.N0213.N0502.d022061
#print axioms _root_.GD.N0213.N0502.d022063
