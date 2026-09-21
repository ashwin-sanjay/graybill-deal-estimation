import GD.Module1830
import GD.Module1276

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0096.N0340

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1226 _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1319
open _root_.GD.N0230.N0608
open _root_.GD.N0046.N0305

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030227 {p q : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (hqp : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ q ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ p) :
    q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
  intro θ
  exact ⟨(hqp θ).trans (hp θ).1, (hqp θ).trans (hp θ).2⟩

theorem d030228 (g : _root_.GD.N0232.N0720.N1482.d015118) {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0046.N0305.d030204 m n hp) ∈
      _root_.GD.N0046.N0305.d030202 m n hm hn := by
  intro η
  let θ := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ η
  have hη : _root_.GD.N0232.N0720.N1215.d014272 g θ = η := by simp [θ]
  rw [← hη, _root_.GD.N0232.N0720.N1159.d014643, _root_.GD.N0232.N0720.N1257.d015512,
    _root_.GD.N0232.N0720.N1215.d014293]
  constructor
  · calc
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤
          ENNReal.ofReal (g.d009239 ^ 2) *
            (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ)) :=
        mul_le_mul' le_rfl (hp θ).1
      _ = _root_.GD.N0232.N0720.N1256.d015549 m n *
          ENNReal.ofReal (g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1257.d015508 m n θ) := by
        rw [ENNReal.ofReal_mul (sq_nonneg g.d009239)]
        ac_rfl
  · exact mul_le_mul' le_rfl (hp θ).2

def d030229 : Prop :=
  ∃ (p : _root_.GD.N0046.N0305.d030201 m n) (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn),
    _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p
      (_root_.GD.N0046.N0305.d030204 m n hp) ≠ p ∨
    _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p
      (_root_.GD.N0046.N0305.d030204 m n hp) ≠ p

theorem d030230
    (hstrict : (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty) :
    _root_.GD.N0096.N0340.d030229 m n hm hn := by
  classical
  obtain ⟨s, hs, hsStrict⟩ := hstrict
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s
  have hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn :=
    _root_.GD.N0096.N0340.d030227 m n hm hn hs (_root_.GD.N0232.N0720.N1159.d014634 m n s).1
  have hpStrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
    _root_.GD.N0232.N0720.N1159.d014636 m n s
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hsStrict
  refine ⟨p, hp, ?_⟩
  by_contra hfixed
  push Not at hfixed
  have hall := _root_.GD.N0232.N0720.N1482.d015167 (m := m) (n := n) p
    (_root_.GD.N0046.N0305.d030204 m n hp) hfixed.1 hfixed.2
  have hrep := (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn p
    (_root_.GD.N0046.N0305.d030204 m n hp)).mp hall
  apply _root_.GD.N0232.N0720.N1319.d020618 m n hm hn
  apply (_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn).mpr
  exact ⟨p, hrep, hpStrict, (_root_.GD.N0232.N0720.N1159.d014634 m n s).2.1⟩

theorem d030231
    (h : _root_.GD.N0096.N0340.d030229 m n hm hn) :
    ¬ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  rintro hsub
  obtain ⟨p, hp, hTwo | hThree⟩ := h
  · exact hTwo (hsub (_root_.GD.N0096.N0340.d030228 m n hm hn _root_.GD.N0232.N0720.N1482.d015130 hp) hp)
  · exact hThree
      (hsub (_root_.GD.N0096.N0340.d030228 m n hm hn _root_.GD.N0232.N0720.N1482.d015131 hp) hp)

theorem d030232
    (h : ¬ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton) :
    (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty := by
  classical
  have hex : ∃ p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn,
      ∃ q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, p ≠ q := by
    by_contra hnot
    push Not at hnot
    exact h (fun p hp q hq => hnot p hp q hq)
  obtain ⟨p, hp, q, hq, hpq⟩ := hex
  exact (_root_.GD.N0046.N0305.d030214
    m n hm hn).mp
    (_root_.GD.N0046.N0305.d030211 m n hp hq hpq)

theorem d030233 :
    (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty ↔
      ¬ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton :=
  ⟨fun h => _root_.GD.N0096.N0340.d030231 m n hm hn
      (_root_.GD.N0096.N0340.d030230 m n hm hn h),
    _root_.GD.N0096.N0340.d030232 m n hm hn⟩

theorem d030234 :
    _root_.GD.N0096.N0340.d030229 m n hm hn ↔
      ¬ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton :=
  ⟨_root_.GD.N0096.N0340.d030231 m n hm hn,
    fun h => _root_.GD.N0096.N0340.d030230 m n hm hn
      (_root_.GD.N0096.N0340.d030232 m n hm hn h)⟩

theorem d030235 :
    _root_.GD.N0232.N0720.N1226.d015578 m n ↔
      _root_.GD.N0096.N0340.d030229 m n hm hn := by
  rw [_root_.GD.N0046.N0305.d030214 m n hm hn,
    _root_.GD.N0096.N0340.d030234 m n hm hn]
  exact _root_.GD.N0096.N0340.d030233 m n hm hn

theorem d030236 :
    _root_.GD.N0232.N0720.N1226.d015578 m n ↔
      ¬ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  rw [_root_.GD.N0096.N0340.d030235 m n hm hn,
    _root_.GD.N0096.N0340.d030234 m n hm hn]

theorem d030237 :
    (∀ (p : _root_.GD.N0046.N0305.d030201 m n) (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn),
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p
        (_root_.GD.N0046.N0305.d030204 m n hp) = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p
        (_root_.GD.N0046.N0305.d030204 m n hp) = p) ↔
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  classical
  have h := not_congr (_root_.GD.N0096.N0340.d030234 m n hm hn)
  simpa only [_root_.GD.N0096.N0340.d030229, not_exists, not_or, not_not] using h

theorem d030238 {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (hsub : (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p := by
  intro q hq
  exact hsub (_root_.GD.N0096.N0340.d030227 m n hm hn hp hq) hp

theorem d030239 {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (hsub : (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton) :
    _root_.GD.N0232.N0720.N1159.d014652 m n p := by
  apply (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn p
    (_root_.GD.N0046.N0305.d030204 m n hp)).mp
  intro g
  exact hsub (_root_.GD.N0096.N0340.d030228 m n hm hn g hp) hp

theorem d030240 {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (hsub : (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton) :
    ∃ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p = _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  classical
  by_contra htouch
  have hstrict : (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty := by
    refine ⟨p, hp, ?_⟩
    intro θ
    exact lt_of_le_of_ne (hp θ).2 (fun hθ => htouch ⟨θ, hθ⟩)
  exact (_root_.GD.N0096.N0340.d030233 m n hm hn).mp hstrict hsub

end
end GD.N0096.N0340

#print axioms _root_.GD.N0096.N0340.d030228
#print axioms _root_.GD.N0096.N0340.d030230
#print axioms _root_.GD.N0096.N0340.d030235
#print axioms _root_.GD.N0096.N0340.d030236
#print axioms _root_.GD.N0096.N0340.d030237
#print axioms _root_.GD.N0096.N0340.d030238
#print axioms _root_.GD.N0096.N0340.d030239
#print axioms _root_.GD.N0096.N0340.d030240
