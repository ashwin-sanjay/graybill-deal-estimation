import GD.Module1369

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0092
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0968
open _root_.GD.N0213.N0502
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0586

variable (k : ℕ) (sizes : Fin k → ℕ)

def d023963 (f s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (hs : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (t : ℝ) : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0896.d011088 k sizes ((1 - t) • _root_.GD.N0232.N0719.N0970.d012312 k sizes f hf +
    t • _root_.GD.N0232.N0719.N0970.d012312 k sizes s hs)

theorem d023964 (f s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (hs : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0092.d023963 k sizes f s hf hs t) ≤
      ENNReal.ofReal (1 - t) * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f +
      ENNReal.ofReal t * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ s := by
  rw [_root_.GD.N0092.d023963, _root_.GD.N0232.N0719.N0896.d011093]
  have h := _root_.GD.N0230.N0602.d000121 (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ)
    θ.location (_root_.GD.N0232.N0719.N0970.d012312 k sizes f hf) (_root_.GD.N0232.N0719.N0970.d012312 k sizes s hs)
    (sub_nonneg.mpr ht1) ht (by ring : 1 - t + t = 1)
  change _root_.GD.N0232.N0719.N0859.d010821 k sizes θ _ ≤
    ENNReal.ofReal (1 - t) * _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N0970.d012312 k sizes f hf) +
    ENNReal.ofReal t * _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N0970.d012312 k sizes s hs) at h
  simpa only [_root_.GD.N0232.N0719.N0970.d012313] using h

theorem d023965
    (f s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (hs : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hbase : f ∈ _root_.GD.N0213.N0502.d022050 k sizes)
    (hstrict : _root_.GD.N0232.N0719.N0970.d012310 k sizes s)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    _root_.GD.N0232.N0719.N0970.d012310 k sizes (_root_.GD.N0092.d023963 k sizes f s hf hs t) := by
  intro θ
  apply (_root_.GD.N0092.d023964 k sizes f s hf hs t ht.le ht1 θ).trans_lt
  have hsum : ENNReal.ofReal (1 - t) + ENNReal.ofReal t = 1 := by
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht1) ht.le]
    norm_num
  calc
    _ < ENNReal.ofReal (1 - t) * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) +
        ENNReal.ofReal t * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
      apply ENNReal.add_lt_add_of_le_of_lt
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf.2 θ))
        (mul_le_mul_right (hbase.2 θ) _)
      exact ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
        ENNReal.ofReal_ne_top (hstrict θ)
    _ = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
      rw [← add_mul, hsum, one_mul]

theorem d023966 (hk : 0 < k) (hn : ∀ i, 0 < sizes i)
    (f s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (hs : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : _root_.GD.N0232.N0719.N0962.d012187 k sizes f ≤ ENNReal.ofReal A)
    (hsB : _root_.GD.N0232.N0719.N0962.d012187 k sizes s ≤ ENNReal.ofReal B)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0092.d023963 k sizes f s hf hs t) ≤
      ENNReal.ofReal ((1 - t) * A + t * B) := by
  apply iSup_le
  intro θ
  apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes hk hn _ (by positivity) θ _).mpr
  have hfθ := (_root_.GD.N0232.N0719.N0962.d012192 k sizes hk hn A hA θ f).mp
    ((le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 k sizes θ f) θ).trans hfA)
  have hsθ := (_root_.GD.N0232.N0719.N0962.d012192 k sizes hk hn B hB θ s).mp
    ((le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 k sizes θ s) θ).trans hsB)
  have hv := (_root_.GD.N0232.N0719.N0963.d012143 k sizes hk hn θ).le
  calc
    _ ≤ ENNReal.ofReal (1 - t) * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f +
        ENNReal.ofReal t * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ s :=
      _root_.GD.N0092.d023964 k sizes f s hf hs t ht ht1 θ
    _ ≤ ENNReal.ofReal (1 - t) * ENNReal.ofReal (A * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) +
        ENNReal.ofReal t * ENNReal.ofReal (B * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) :=
      add_le_add (mul_le_mul_right hfθ _) (mul_le_mul_right hsθ _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sub_nonneg.mpr ht1), ← ENNReal.ofReal_mul ht,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring




theorem d023967
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hs : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hstrict : _root_.GD.N0232.N0719.N0970.d012310 k sizes s)
    (hfinite : _root_.GD.N0232.N0719.N0962.d012187 k sizes s ≠ ⊤)
    (c : ℝ) (hc : _root_.GD.N0213.N0502.d022051 k sizes < ENNReal.ofReal c) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      _root_.GD.N0232.N0719.N0970.d012310 k sizes e ∧ _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e < ENNReal.ofReal c := by
  have hVfinite : _root_.GD.N0213.N0502.d022051 k sizes ≠ ⊤ := ne_top_of_lt hc
  let v := (_root_.GD.N0213.N0502.d022051 k sizes).toReal
  let B := (_root_.GD.N0232.N0719.N0962.d012187 k sizes s).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0213.N0502.d022051 k sizes :=
    ENNReal.ofReal_toReal hVfinite
  have hSB : _root_.GD.N0232.N0719.N0962.d012187 k sizes s = ENNReal.ofReal B :=
    (ENNReal.ofReal_toReal hfinite).symm
  have hc0 : 0 < c := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hc)
  have hvc : v < c := (ENNReal.ofReal_lt_ofReal_iff hc0).mp (by rwa [hV])
  let t := (c - v) / (B + c + 1)
  have hden : 0 < B + c + 1 := by positivity
  have ht : 0 < t := div_pos (sub_pos.mpr hvc) hden
  have ht1 : t ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith
  have htid : t * (B + c + 1) = c - v := by
    dsimp [t]
    exact div_mul_cancel₀ _ hden.ne'
  have hbound : (1 - t) * v + t * B < c := by
    have hp : 0 < t * (c + 1) := mul_pos ht (by linarith)
    have htv : 0 ≤ t * v := mul_nonneg ht.le hv
    nlinarith
  obtain ⟨f, hf, hfvalue⟩ := _root_.GD.N0213.N0502.d022060 k sizes hk hn
  have hfFin := _root_.GD.N0213.N0502.d022053 k sizes hk hn hf
  let q := _root_.GD.N0092.d023963 k sizes f s hfFin hs t
  have hqs : _root_.GD.N0232.N0719.N0970.d012310 k sizes q :=
    _root_.GD.N0092.d023965 k sizes f s hfFin hs hf hstrict t ht ht1
  have hqbase : q ∈ _root_.GD.N0213.N0502.d022050 k sizes :=
    ⟨_root_.GD.N0232.N0719.N0896.d011089 k sizes _, fun θ => (hqs θ).le⟩
  have hqFin := _root_.GD.N0213.N0502.d022053 k sizes hk hn hqbase
  have hqbound : _root_.GD.N0232.N0719.N0962.d012187 k sizes q < ENNReal.ofReal c := by
    apply (_root_.GD.N0092.d023966 k sizes (by omega) (fun i => by have := hn i; omega)
      f s hfFin hs v B hv hB (by rw [hfvalue, hV]) (by rw [hSB]) t ht.le ht1).trans_lt
    exact (ENNReal.ofReal_lt_ofReal_iff hc0).mpr hbound
  exact ⟨_root_.GD.N0232.N0719.N0970.d012314 k sizes q hqFin,
    _root_.GD.N0232.N0719.N0970.d012316 k sizes q hqFin,
    _root_.GD.N0232.N0719.N0970.d012321 k sizes q hqFin hqs,
    _root_.GD.N0232.N0719.N0970.d012317 k sizes q hqFin,
    (_root_.GD.N0232.N0719.N0970.d012319 k sizes q hqFin).trans_lt hqbound⟩

def d023968 : Set (_root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :=
  {e | e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes e ∧ _root_.GD.N0232.N0719.N0970.d012309 k sizes e}

theorem d023969 :
    _root_.GD.N0092.d023968 k sizes ⊆ _root_.GD.N0213.N0502.d022050 k sizes := by
  intro e he
  exact ⟨he.1.1, fun θ => (he.2.1 θ).le⟩



theorem d023970
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hs : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hstrict : _root_.GD.N0232.N0719.N0970.d012310 k sizes s)
    (hfinite : _root_.GD.N0232.N0719.N0962.d012187 k sizes s ≠ ⊤) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0213.N0502.d022051 k sizes := by
  have hsbase : s ∈ _root_.GD.N0213.N0502.d022050 k sizes :=
    ⟨hs.1, fun θ => (hstrict θ).le⟩
  have hVfinite : _root_.GD.N0213.N0502.d022051 k sizes ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hsbase)
  have hV : ENNReal.ofReal (_root_.GD.N0213.N0502.d022051 k sizes).toReal =
      _root_.GD.N0213.N0502.d022051 k sizes := ENNReal.ofReal_toReal hVfinite
  apply le_antisymm
  · rw [← hV]
    apply _root_.GD.N0230.N0586.d003515 ENNReal.toReal_nonneg
    intro c hc
    have hcap : _root_.GD.N0213.N0502.d022051 k sizes < ENNReal.ofReal c := by
      rw [← hV]
      exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_nonneg.trans_lt hc)).mpr hc
    obtain ⟨e, he, hes, het, hec⟩ := _root_.GD.N0092.d023967
      k sizes hk hn s hs hstrict hfinite c hcap
    exact (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
      (show e ∈ _root_.GD.N0092.d023968 k sizes from ⟨he, hes, het⟩)).trans hec.le
  · apply le_iInf
    intro e
    apply le_iInf
    intro he
    exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
      (_root_.GD.N0092.d023969 k sizes he)

theorem d023971
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hbaseline : _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0859.d010815 k sizes) ≠ ⊤) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0213.N0502.d022051 k sizes := by
  have hs := _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hn
  have hstrict := _root_.GD.N0232.N0719.N0970.d012329 k sizes hk hn
  exact _root_.GD.N0092.d023970 k sizes hk hn
    (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn) ⟨hs.1.1, hs.2⟩ hstrict
    (ne_top_of_le_ne_top hbaseline (_root_.GD.N0232.N0719.N0970.d012318 k sizes fun θ => (hstrict θ).le))

end
end GD.N0092

#print axioms _root_.GD.N0092.d023965
#print axioms _root_.GD.N0092.d023966
#print axioms _root_.GD.N0092.d023967
#print axioms _root_.GD.N0092.d023970
#print axioms _root_.GD.N0092.d023971
