import GD.Module1828
import GD.Module0983
import GD.Module1829

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0046.N0305

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1226
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0718
open _root_.GD.N0046.N0303

variable (m n : ℕ)

abbrev d030201 := _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)

def d030202 (hm : 2 ≤ m) (hn : 2 ≤ n) : Set (_root_.GD.N0046.N0305.d030201 m n) :=
  {p | ∀ θ,
    _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ _root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ) ∧
    _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)}

theorem d030203 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014172 m n ≪ _root_.GD.N0232.N0720.N1080.d014171 m n θ := by
  simpa [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
    (_root_.GD.N0232.N0720.d009063
      m n θ.location θ.scale₁ θ.scale₂ θ.scale₁_pos θ.scale₂_pos).2

theorem d030204
    {hm : 2 ≤ m} {hn : 2 ≤ n}
    {p : _root_.GD.N0046.N0305.d030201 m n} (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014637 m n p := by
  intro θ
  apply ne_top_of_le_ne_top _ (hp θ).2
  rw [_root_.GD.N0232.N0720.N1080.d014184]
  exact ENNReal.ofReal_ne_top

def d030205 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n) : _root_.GD.N0046.N0305.d030201 m n :=
  MemLp.toLp d (_root_.GD.N0232.N0720.N1215.d014285 m n d hd.1
    (hd.2 _root_.GD.N0232.N0720.N1080.d014169))

theorem d030206 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0046.N0305.d030205 m n d hd) = _root_.GD.N0232.N0720.N1080.d014197 m n θ d :=
  (_root_.GD.N0232.N0720.N1080.d014198 m n θ d _).symm

theorem d030207
    {hm : 2 ≤ m} {hn : 2 ≤ n}
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n)
    (hbelow : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) :
    _root_.GD.N0046.N0305.d030205 m n d hd ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
  intro θ
  rw [_root_.GD.N0046.N0305.d030206]
  refine ⟨?_, ?_⟩
  · apply (ENNReal.div_le_iff
      (ne_of_gt (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1257.d015510 m n (by omega) θ)))
      ENNReal.ofReal_ne_top).mp
    change _root_.GD.N0232.N0720.N1256.d015547 m n θ d ≤ _root_.GD.N0232.N0720.N1256.d015549 m n
    rw [← hvalue]
    exact le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 m n θ d) θ
  · simpa only [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn] using hbelow θ

theorem d030208
    {hm : 2 ≤ m} {hn : 2 ≤ n}
    {p : _root_.GD.N0046.N0305.d030201 m n} (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) = _root_.GD.N0232.N0720.N1256.d015549 m n := by
  apply le_antisymm
  · apply iSup_le
    intro θ
    unfold _root_.GD.N0232.N0720.N1256.d015547
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    apply (ENNReal.div_le_iff
      (ne_of_gt (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1257.d015510 m n (by omega) θ)))
      ENNReal.ofReal_ne_top).mpr
    exact (hp θ).1
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n)
      (_root_.GD.N0232.N0720.N1214.d014266 m n p)

theorem d030209
    {hm : 2 ≤ m} {hn : 2 ≤ n} {p q : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
  intro θ
  exact ⟨_root_.GD.N0046.N0303.d030187
      (_root_.GD.N0232.N0720.N1080.d014173 m n θ) θ.location (hp θ).1 (hq θ).1,
    _root_.GD.N0046.N0303.d030187
      (_root_.GD.N0232.N0720.N1080.d014173 m n θ) θ.location (hp θ).2 (hq θ).2⟩

theorem d030210
    {hm : 2 ≤ m} {hn : 2 ≤ n} {p q : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hpq : p ≠ q) :
    _root_.GD.N0232.N0720.N1226.d015576 m n (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0718.d001528 p q)) := by
  refine ⟨_root_.GD.N0232.N0720.N1214.d014266 m n _, ?_,
    _root_.GD.N0046.N0305.d030208 m n (_root_.GD.N0046.N0305.d030209 m n hp hq)⟩
  intro θ
  rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  exact _root_.GD.N0046.N0303.d030188
    (_root_.GD.N0232.N0720.N1080.d014173 m n θ)
    (_root_.GD.N0046.N0305.d030203 m n θ) θ.location
    (by rw [_root_.GD.N0232.N0720.N1080.d014184]; exact ENNReal.ofReal_ne_top)
    (hp θ).2 (hq θ).2 hpq

theorem d030211
    {hm : 2 ≤ m} {hn : 2 ≤ n} {p q : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hpq : p ≠ q) :
    _root_.GD.N0232.N0720.N1226.d015578 m n :=
  _root_.GD.N0232.N0720.N1226.d015583 m n
    (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0230.N0718.d001528 p q))
    (_root_.GD.N0046.N0305.d030210 m n hp hq hpq)

end
end GD.N0046.N0305

#print axioms _root_.GD.N0046.N0305.d030211


set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0046.N0305

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1257
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1226
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0675
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0046.N0304

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030212 : Set (_root_.GD.N0046.N0305.d030201 m n) :=
  {p | p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn ∧
    ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p < _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)}

theorem d030213 : Convex ℝ (_root_.GD.N0046.N0305.d030202 m n hm hn) := by
  simpa only [_root_.GD.N0230.N0602.d000118, _root_.GD.N0046.N0305.d030202, _root_.GD.N0232.N0720.N1080.d014182, le_inf_iff] using
    _root_.GD.N0230.N0602.d000123 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n)
      (fun θ => θ.location)
      (fun θ => min (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))
        (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)))
      (_root_.GD.N0232.N0720.N1080.d014173 m n)

theorem d030214 :
    _root_.GD.N0232.N0720.N1226.d015578 m n ↔
      (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty := by
  rw [_root_.GD.N0232.N0720.N1226.d015584]
  constructor
  · rintro ⟨d, hd⟩
    have hdfin := _root_.GD.N0232.N0720.N1226.d015576.d015579 m n hd
    refine ⟨_root_.GD.N0046.N0305.d030205 m n d hdfin,
      _root_.GD.N0046.N0305.d030207 m n d hdfin hd.2.2 (fun θ => (hd.2.1 θ).le), ?_⟩
    intro θ
    rw [_root_.GD.N0046.N0305.d030206]
    simpa only [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn] using hd.2.1 θ
  · rintro ⟨p, hp, hstrict⟩
    refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n p, _root_.GD.N0232.N0720.N1214.d014266 m n p, ?_,
      _root_.GD.N0046.N0305.d030208 m n hp⟩
    intro θ
    rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
    exact hstrict θ

private theorem d030215 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ≠ ⊤ := by
  rw [_root_.GD.N0232.N0720.N1080.d014184]
  exact ENNReal.ofReal_ne_top

private theorem d030216 :
    _root_.GD.N0046.N0304.d030189 (_root_.GD.N0046.N0305.d030202 m n hm hn)
      (fun θ => _root_.GD.N0230.N0675.d001652 (_root_.GD.N0232.N0720.N1080.d014171 m n θ) θ.location)
      (fun θ => (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).toReal) =
    _root_.GD.N0046.N0305.d030202 m n hm hn := by
  ext p
  constructor
  · exact fun h => h.1
  · intro hp
    exact ⟨hp, fun θ => ENNReal.toReal_mono (_root_.GD.N0046.N0305.d030215 m n hm hn θ) (hp θ).2⟩

private theorem d030217 :
    _root_.GD.N0046.N0304.d030190 (_root_.GD.N0046.N0305.d030202 m n hm hn)
      (fun θ => _root_.GD.N0230.N0675.d001652 (_root_.GD.N0232.N0720.N1080.d014171 m n θ) θ.location)
      (fun θ => (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).toReal) =
    _root_.GD.N0046.N0305.d030212 m n hm hn := by
  ext p
  constructor
  · rintro ⟨hp, hstrict⟩
    refine ⟨hp, ?_⟩
    intro θ
    exact (ENNReal.toReal_lt_toReal
      (_root_.GD.N0046.N0305.d030204 m n hp θ)
      (_root_.GD.N0046.N0305.d030215 m n hm hn θ)).mp (hstrict θ)
  · rintro ⟨hp, hstrict⟩
    refine ⟨hp, ?_⟩
    intro θ
    exact (ENNReal.toReal_lt_toReal
      (_root_.GD.N0046.N0305.d030204 m n hp θ)
      (_root_.GD.N0046.N0305.d030215 m n hm hn θ)).mpr (hstrict θ)

theorem d030218 :
    _root_.GD.N0046.N0305.d030212 m n hm hn = ∅ ↔
      _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ ∨
        ∃ p : _root_.GD.N0046.N0305.d030201 m n, _root_.GD.N0046.N0305.d030202 m n hm hn = {p} ∧
          ∃ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p = _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  have h := _root_.GD.N0046.N0304.d030200
    (_root_.GD.N0232.N0720.N1080.d014171 m n) (fun θ => θ.location) (_root_.GD.N0046.N0305.d030202 m n hm hn)
    (fun θ => (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).toReal)
    (_root_.GD.N0046.N0305.d030213 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014173 m n)
    (_root_.GD.N0046.N0305.d030203 m n)
    (fun _ hp θ => _root_.GD.N0046.N0305.d030204 m n hp θ)
  rw [_root_.GD.N0046.N0305.d030216 m n hm hn,
    _root_.GD.N0046.N0305.d030217 m n hm hn] at h
  rw [h]
  apply or_congr Iff.rfl
  apply exists_congr
  intro p
  constructor
  · rintro ⟨hp, θ, hθ⟩
    refine ⟨hp, θ, ?_⟩
    have hpmem : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by rw [hp]; exact mem_singleton p
    exact (ENNReal.toReal_eq_toReal_iff'
      (_root_.GD.N0046.N0305.d030204 m n hpmem θ)
      (_root_.GD.N0046.N0305.d030215 m n hm hn θ)).mp hθ
  · rintro ⟨hp, θ, hθ⟩
    exact ⟨hp, θ, congrArg ENNReal.toReal hθ⟩

theorem d030219 :
    ¬ _root_.GD.N0232.N0720.N1226.d015578 m n ↔
      _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ ∨
        ∃ p : _root_.GD.N0046.N0305.d030201 m n, _root_.GD.N0046.N0305.d030202 m n hm hn = {p} ∧
          ∃ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p = _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  rw [_root_.GD.N0046.N0305.d030214 m n hm hn,
    Set.not_nonempty_iff_eq_empty]
  exact _root_.GD.N0046.N0305.d030218 m n hm hn

end
end GD.N0046.N0305

#print axioms _root_.GD.N0046.N0305.d030214
#print axioms _root_.GD.N0046.N0305.d030219
