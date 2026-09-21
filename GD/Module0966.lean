import GD.Module0070
import GD.Module0964
import GD.Module0963
import Mathlib.MeasureTheory.Integral.Bochner.Basic






































open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1200

noncomputable section

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0645
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482



variable {Seed : Type*}


def d015234
    (Eligible : Seed → Prop) (defect : Seed → ℝ) : Prop :=
  ∃ s, Eligible s ∧ defect s = 0



def d015235
    (Eligible : Seed → Prop) (defect : Seed → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s, Eligible s ∧ defect s < ε


def d015236
    (Eligible : Seed → Prop) (defect : Seed → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ s, Eligible s → ε ≤ defect s


def d015237
    (Eligible : Seed → Prop) (defect : Seed → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ s, Eligible s ∧ 0 < defect s ∧ defect s < ε




def d015238
    (Eligible : Seed → Prop) (defect : Seed → ℝ) : Prop :=
  (∀ s, Eligible s → 0 < defect s) ∧
    _root_.GD.N0232.N0720.N1200.d015237 Eligible defect


theorem d015239
    {Eligible : Seed → Prop} {defect : Seed → ℝ}
    (hzero : _root_.GD.N0232.N0720.N1200.d015234 Eligible defect) :
    _root_.GD.N0232.N0720.N1200.d015235 Eligible defect := by
  obtain ⟨s, hs, hzero⟩ := hzero
  intro ε hε
  exact ⟨s, hs, by simpa only [hzero] using hε⟩


theorem d015240
    {Eligible : Seed → Prop} {defect : Seed → ℝ} :
    _root_.GD.N0232.N0720.N1200.d015235 Eligible defect ↔
      ¬ _root_.GD.N0232.N0720.N1200.d015236 Eligible defect := by
  constructor
  · intro happrox hfloor
    obtain ⟨ε, hε, hfloor⟩ := hfloor
    obtain ⟨s, hs, hlt⟩ := happrox ε hε
    exact (not_lt_of_ge (hfloor s hs)) hlt
  · intro hfloor ε hε
    have hnotAll : ¬ ∀ s, Eligible s → ε ≤ defect s := by
      intro hall
      exact hfloor ⟨ε, hε, hall⟩
    push Not at hnotAll
    exact hnotAll



theorem d015241
    {Eligible : Seed → Prop} {defect : Seed → ℝ}
    (hnonneg : ∀ s, Eligible s → 0 ≤ defect s) :
    _root_.GD.N0232.N0720.N1200.d015235 Eligible defect ↔
      _root_.GD.N0232.N0720.N1200.d015234 Eligible defect ∨
        _root_.GD.N0232.N0720.N1200.d015238 Eligible defect := by
  constructor
  · intro happrox
    by_cases hzero : _root_.GD.N0232.N0720.N1200.d015234 Eligible defect
    · exact Or.inl hzero
    · right
      constructor
      · intro s hs
        have hne : defect s ≠ 0 := by
          intro heq
          exact hzero ⟨s, hs, heq⟩
        exact lt_of_le_of_ne (hnonneg s hs) (Ne.symm hne)
      · intro ε hε
        obtain ⟨s, hs, hlt⟩ := happrox ε hε
        have hne : defect s ≠ 0 := by
          intro heq
          exact hzero ⟨s, hs, heq⟩
        exact ⟨s, hs,
          lt_of_le_of_ne (hnonneg s hs) (Ne.symm hne), hlt⟩
  · rintro (hzero | hnull)
    · exact _root_.GD.N0232.N0720.N1200.d015239 hzero
    · intro ε hε
      obtain ⟨s, hs, _hpos, hlt⟩ := hnull.2 ε hε
      exact ⟨s, hs, hlt⟩



theorem d015242
    {Eligible : Seed → Prop} {defect : Seed → ℝ}
    (hfloor : _root_.GD.N0232.N0720.N1200.d015236 Eligible defect) :
    ¬ _root_.GD.N0232.N0720.N1200.d015237 Eligible defect := by
  rintro hsmall
  obtain ⟨ε, hε, hfloor⟩ := hfloor
  obtain ⟨s, hs, _hpos, hlt⟩ := hsmall ε hε
  exact (not_lt_of_ge (hfloor s hs)) hlt



theorem d015243
    {Eligible : Seed → Prop} {defect : Seed → ℝ}
    (hfloor : _root_.GD.N0232.N0720.N1200.d015236 Eligible defect) :
    ¬ _root_.GD.N0232.N0720.N1200.d015238 Eligible defect := by
  intro hnull
  exact _root_.GD.N0232.N0720.N1200.d015242 hfloor hnull.2






theorem d015244
    {Eligible : Seed → Prop} {defect : Seed → ℝ}
    (hnonneg : ∀ s, Eligible s → 0 ≤ defect s) :
    ¬ _root_.GD.N0232.N0720.N1200.d015234 Eligible defect ↔
      _root_.GD.N0232.N0720.N1200.d015236 Eligible defect ∨
        _root_.GD.N0232.N0720.N1200.d015238 Eligible defect := by
  constructor
  · intro hzero
    by_cases hfloor : _root_.GD.N0232.N0720.N1200.d015236 Eligible defect
    · exact Or.inl hfloor
    · right
      constructor
      · intro s hs
        have hne : defect s ≠ 0 := by
          intro heq
          exact hzero ⟨s, hs, heq⟩
        exact lt_of_le_of_ne (hnonneg s hs) (Ne.symm hne)
      · intro ε hε
        have hnotAll : ¬ ∀ s, Eligible s → ε ≤ defect s := by
          intro hall
          exact hfloor ⟨ε, hε, hall⟩
        push Not at hnotAll
        obtain ⟨s, hs, hlt⟩ := hnotAll
        have hne : defect s ≠ 0 := by
          intro heq
          exact hzero ⟨s, hs, heq⟩
        have hpos : 0 < defect s :=
          lt_of_le_of_ne (hnonneg s hs) (Ne.symm hne)
        exact ⟨s, hs, hpos, hlt⟩
  · rintro (hfloor | hnull) hzero
    · obtain ⟨ε, hε, hfloor⟩ := hfloor
      obtain ⟨s, hs, hsZero⟩ := hzero
      have := hfloor s hs
      rw [hsZero] at this
      exact (not_lt_of_ge this) hε
    · obtain ⟨s, hs, hzero⟩ := hzero
      exact (ne_of_gt (hnull.1 s hs)) hzero


theorem d015245
    {Eligible : Seed → Prop} {defect : Seed → ℝ}
    (hnonneg : ∀ s, Eligible s → 0 ≤ defect s) :
    _root_.GD.N0232.N0720.N1200.d015234 Eligible defect ∨
      _root_.GD.N0232.N0720.N1200.d015236 Eligible defect ∨
        _root_.GD.N0232.N0720.N1200.d015238 Eligible defect := by
  by_cases hzero : _root_.GD.N0232.N0720.N1200.d015234 Eligible defect
  · exact Or.inl hzero
  · exact Or.inr
      ((_root_.GD.N0232.N0720.N1200.d015244
        hnonneg).1 hzero)



variable {X : Type*} [TopologicalSpace X]



theorem d015246
    {C : Set X} {defect : X → ℝ}
    (hcompact : IsCompact C) (hne : C.Nonempty)
    (hcontinuous : ContinuousOn defect C)
    (hnonneg : ∀ x ∈ C, 0 ≤ defect x)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ x ∈ C, 0 < defect x ∧ defect x < ε) :
    ∃ x ∈ C, defect x = 0 := by
  obtain ⟨x, hx, hmin⟩ := hcompact.exists_isMinOn hne hcontinuous
  refine ⟨x, hx, le_antisymm ?_ (hnonneg x hx)⟩
  by_contra hnot
  have hxpos : 0 < defect x := lt_of_not_ge hnot
  obtain ⟨y, hy, _hypos, hylt⟩ := hsmall (defect x) hxpos
  exact (not_lt_of_ge (hmin hy)) hylt






theorem d015247
    {C : Set X} {defect : X → ℝ}
    (hcompact : IsCompact C) (hne : C.Nonempty)
    (hcontinuous : ContinuousOn defect C)
    (hnonneg : ∀ x ∈ C, 0 ≤ defect x)
    (hnozero : ∀ x ∈ C, defect x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ C, ε ≤ defect x := by
  obtain ⟨x, hx, hmin⟩ := hcompact.exists_isMinOn hne hcontinuous
  have hxpos : 0 < defect x :=
    lt_of_le_of_ne (hnonneg x hx) (Ne.symm (hnozero x hx))
  exact ⟨defect x, hxpos, fun y hy ↦ hmin hy⟩







theorem d015248
    {Eligible : X → Prop} {defect : X → ℝ}
    (hnonneg : ∀ x, Eligible x → 0 ≤ defect x)
    (seq : ℕ → X) (limit : X)
    (_hseqEligible : ∀ j, Eligible (seq j))
    (hlimitEligible : Eligible limit)
    (hseq : Tendsto seq atTop (nhds limit))
    (hdefectZero : Tendsto (fun j ↦ defect (seq j)) atTop (nhds 0))
    (hlsc : LowerSemicontinuousAt defect limit) :
    _root_.GD.N0232.N0720.N1200.d015234 Eligible defect := by
  have hle : defect limit ≤ 0 := by
    by_contra hnot
    have hpos : 0 < defect limit := lt_of_not_ge hnot
    have heventuallyAbove : ∀ᶠ x in nhds limit, defect limit / 2 < defect x :=
      hlsc (defect limit / 2) (by linarith)
    have hseqAbove : ∀ᶠ j in atTop, defect limit / 2 < defect (seq j) :=
      hseq.eventually heventuallyAbove
    have hseqBelow : ∀ᶠ j in atTop, defect (seq j) < defect limit / 2 :=
      (tendsto_order.1 hdefectZero).2 (defect limit / 2) (by linarith)
    obtain ⟨j, hjAbove, hjBelow⟩ := (hseqAbove.and hseqBelow).exists
    exact (not_lt_of_ge hjAbove.le) hjBelow
  exact ⟨limit, hlimitEligible,
    le_antisymm hle (hnonneg limit hlimitEligible)⟩



theorem d015249
    {Eligible : X → Prop} {defect : X → ℝ}
    (hnonneg : ∀ x, Eligible x → 0 ≤ defect x)
    (seq : ℕ → X) (limit : X)
    (hseqEligible : ∀ j, Eligible (seq j))
    (hlimitEligible : Eligible limit)
    (hseq : Tendsto seq atTop (nhds limit))
    (hdefectZero : Tendsto (fun j ↦ defect (seq j)) atTop (nhds 0))
    (hcontinuous : ContinuousAt defect limit) :
    _root_.GD.N0232.N0720.N1200.d015234 Eligible defect :=
  _root_.GD.N0232.N0720.N1200.d015248
    hnonneg seq limit hseqEligible hlimitEligible hseq hdefectZero
      hcontinuous.lowerSemicontinuousAt




def d015250
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  _root_.GD.N0230.N0608.d000675
    (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
    (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)



def d015251
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015236
    (_root_.GD.N0232.N0720.N1200.d015250 m n hm hn)
    (_root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n))



def d015252
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015235
    (_root_.GD.N0232.N0720.N1200.d015250 m n hm hn)
    (_root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n))



def d015253
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015238
    (_root_.GD.N0232.N0720.N1200.d015250 m n hm hn)
    (_root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n))






theorem d015254
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      _root_.GD.N0232.N0720.N1200.d015251 m n hm hn ∨
        _root_.GD.N0232.N0720.N1200.d015253 m n hm hn := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  exact
    _root_.GD.N0232.N0720.N1200.d015244
      (fun s _hs ↦ _root_.GD.N0232.N0720.N1482.d015170
        (m := m) (n := n) s)



theorem d015255
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfloor : _root_.GD.N0232.N0720.N1200.d015251 m n hm hn) :
    ¬ _root_.GD.N0232.N0720.N1200.d015253 m n hm hn :=
  _root_.GD.N0232.N0720.N1200.d015243 hfloor



theorem d015256
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1200.d015252 m n hm hn ↔
      ¬ _root_.GD.N0232.N0720.N1200.d015251 m n hm hn :=
  _root_.GD.N0232.N0720.N1200.d015240



theorem d015257
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1200.d015252 m n hm hn ↔
      _root_.GD.N0232.N0720.N1159.d014661 m n ∨
        _root_.GD.N0232.N0720.N1200.d015253 m n hm hn := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  exact
    _root_.GD.N0232.N0720.N1200.d015241
      (fun s _hs ↦ _root_.GD.N0232.N0720.N1482.d015170
        (m := m) (n := n) s)




def d015258
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (s : _root_.GD.N0232.N0719.N0896.d011106
      k sizes) : Prop :=
  _root_.GD.N0230.N0608.d000675
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
    (_root_.GD.N0232.N0719.N0859.d010819
      k sizes hk hsizes)


def d015259
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015236
    (_root_.GD.N0232.N0720.N1200.d015258 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N1022.d015189
      (k := k) (sizes := sizes))


def d015260
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015235
    (_root_.GD.N0232.N0720.N1200.d015258 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N1022.d015189
      (k := k) (sizes := sizes))



def d015261
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  _root_.GD.N0232.N0720.N1200.d015238
    (_root_.GD.N0232.N0720.N1200.d015258 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N1022.d015189
      (k := k) (sizes := sizes))


theorem d015262
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ¬ _root_.GD.N0232.N0719.N0896.d011132
        k sizes ↔
      _root_.GD.N0232.N0720.N1200.d015259 k sizes hk hsizes ∨
        _root_.GD.N0232.N0720.N1200.d015261 k sizes hk hsizes := by
  rw [_root_.GD.N0232.N0719.N1022.d015193
    k sizes hk hsizes]
  exact
    _root_.GD.N0232.N0720.N1200.d015244
      (fun s _hs ↦
        _root_.GD.N0232.N0719.N1022.d015190
          k sizes s)


theorem d015263
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hfloor : _root_.GD.N0232.N0720.N1200.d015259 k sizes hk hsizes) :
    ¬ _root_.GD.N0232.N0720.N1200.d015261 k sizes hk hsizes :=
  _root_.GD.N0232.N0720.N1200.d015243 hfloor



theorem d015264
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0720.N1200.d015260 k sizes hk hsizes ↔
      ¬ _root_.GD.N0232.N0720.N1200.d015259 k sizes hk hsizes :=
  _root_.GD.N0232.N0720.N1200.d015240


theorem d015265
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0720.N1200.d015260 k sizes hk hsizes ↔
      _root_.GD.N0232.N0719.N0896.d011132
        k sizes ∨
        _root_.GD.N0232.N0720.N1200.d015261 k sizes hk hsizes := by
  rw [_root_.GD.N0232.N0719.N1022.d015193
    k sizes hk hsizes]
  exact
    _root_.GD.N0232.N0720.N1200.d015241
      (fun s _hs ↦
        _root_.GD.N0232.N0719.N1022.d015190
          k sizes s)









def d015266 : Bool → _root_.GD.N0230.N0645.d000855 → ℝ
  | false, x =>
      - (x.1 - 1 / 2) ^ 2 + (x.1 - 1 / 2) ^ 3
  | true, x =>
      - (x.1 - 1 / 2) ^ 2 - (x.1 - 1 / 2) ^ 3


theorem d015267
    (theta : Bool) (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0232.N0720.N1200.d015266 theta (_root_.GD.N0230.N0645.d000856 x) =
      _root_.GD.N0232.N0720.N1200.d015266 (!theta) x := by
  cases theta <;>
    simp only [_root_.GD.N0232.N0720.N1200.d015266, _root_.GD.N0230.N0645.d000856, Bool.not_false,
      Bool.not_true] <;>
    ring


theorem d015268 (theta : Bool) :
    Continuous (_root_.GD.N0232.N0720.N1200.d015266 theta) := by
  cases theta <;>
    unfold _root_.GD.N0232.N0720.N1200.d015266 <;>
    fun_prop


theorem d015269 : Continuous _root_.GD.N0230.N0645.d000856 := by
  apply Continuous.subtype_mk
  exact continuous_const.sub continuous_subtype_val



theorem d015270
    (a b x y : ℝ) (hab : a + b = 1) :
    1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by
  nlinarith




theorem d015271
    (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 _root_.GD.N0230.N0645.d000860 x := by
  intro theta
  have hyLower : -(1 / 2 : ℝ) ≤ x.1 - 1 / 2 := by
    linarith [x.2.1]
  have hyUpper : x.1 - 1 / 2 ≤ (1 / 2 : ℝ) := by
    linarith [x.2.2]
  cases theta
  · have hsquare : 0 ≤ (x.1 - 1 / 2) ^ 2 := sq_nonneg _
    have hlinear : x.1 - 1 / 2 - 1 ≤ 0 := by linarith
    have hmul : (x.1 - 1 / 2) ^ 2 *
        (x.1 - 1 / 2 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsquare hlinear
    calc
      _root_.GD.N0232.N0720.N1200.d015266 false x =
          (x.1 - 1 / 2) ^ 2 * (x.1 - 1 / 2 - 1) := by
        simp only [_root_.GD.N0232.N0720.N1200.d015266]
        ring
      _ ≤ 0 := hmul
      _ = _root_.GD.N0232.N0720.N1200.d015266 false _root_.GD.N0230.N0645.d000860 := by
        norm_num [_root_.GD.N0232.N0720.N1200.d015266, _root_.GD.N0230.N0645.d000860]
  · have hsquare : 0 ≤ (x.1 - 1 / 2) ^ 2 := sq_nonneg _
    have hlinear : 0 ≤ 1 + (x.1 - 1 / 2) := by linarith
    have hmul : -((x.1 - 1 / 2) ^ 2) *
        (1 + (x.1 - 1 / 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsquare) hlinear
    calc
      _root_.GD.N0232.N0720.N1200.d015266 true x =
          -((x.1 - 1 / 2) ^ 2) * (1 + (x.1 - 1 / 2)) := by
        simp only [_root_.GD.N0232.N0720.N1200.d015266]
        ring
      _ ≤ 0 := hmul
      _ = _root_.GD.N0232.N0720.N1200.d015266 true _root_.GD.N0230.N0645.d000860 := by
        norm_num [_root_.GD.N0232.N0720.N1200.d015266, _root_.GD.N0230.N0645.d000860]


theorem d015272 :
    MapsTo _root_.GD.N0230.N0645.d000856
      {x : _root_.GD.N0230.N0645.d000855 |
        _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 _root_.GD.N0230.N0645.d000860 x}
      {x : _root_.GD.N0230.N0645.d000855 |
        _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 _root_.GD.N0230.N0645.d000860 x} := by
  intro x _hx
  exact _root_.GD.N0232.N0720.N1200.d015271 (_root_.GD.N0230.N0645.d000856 x)


theorem d015273 :
    IsCompact (Set.Icc (0 : ℝ) 1) ∧ Convex ℝ (Set.Icc (0 : ℝ) 1) :=
  ⟨isCompact_Icc, convex_Icc 0 1⟩



theorem d015274 :
    _root_.GD.N0230.N0630.d000786 _root_.GD.N0232.N0720.N1200.d015266 _root_.GD.N0230.N0645.d000858 := by
  intro e he
  have hfalse := he false
  let y : ℝ := e.1 - 1 / 2
  let q : ℝ := y ^ 2 - (3 / 2) * y + 3 / 4
  have hqpos : 0 < q := by
    dsimp [q]
    nlinarith [sq_nonneg (y - 3 / 4 : ℝ)]
  have hfactor :
      e.1 * q =
        _root_.GD.N0232.N0720.N1200.d015266 false e -
          _root_.GD.N0232.N0720.N1200.d015266 false _root_.GD.N0230.N0645.d000858 := by
    dsimp [q, y, _root_.GD.N0232.N0720.N1200.d015266, _root_.GD.N0230.N0645.d000858]
    ring
  have hnonneg : 0 ≤ e.1 * q := mul_nonneg e.2.1 hqpos.le
  have hnonpos : e.1 * q ≤ 0 := by
    rw [hfactor]
    exact sub_nonpos.mpr hfalse
  have hzero : e.1 * q = 0 := le_antisymm hnonpos hnonneg
  have hezero : e.1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hqpos.ne'
  exact Subtype.ext hezero


def d015275 (_theta : Bool) : ℝ := 1



def d015276 (s : _root_.GD.N0230.N0645.d000855) : Prop :=
  _root_.GD.N0230.N0645.d000856 s = s ∧
    ∀ theta : Bool,
      _root_.GD.N0232.N0720.N1200.d015266 theta s < _root_.GD.N0232.N0720.N1200.d015275 theta


theorem d015277 (s : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0232.N0720.N1200.d015276 s ↔ s = _root_.GD.N0230.N0645.d000860 := by
  constructor
  · intro hs
    exact (_root_.GD.N0230.N0645.d000870 s).1 hs.1
  · rintro rfl
    refine ⟨_root_.GD.N0230.N0645.d000869, ?_⟩
    intro theta
    cases theta <;>
      norm_num [_root_.GD.N0232.N0720.N1200.d015266, _root_.GD.N0230.N0645.d000860,
        _root_.GD.N0232.N0720.N1200.d015275]



def d015278 (_s : _root_.GD.N0230.N0645.d000855) : _root_.GD.N0230.N0645.d000855 :=
  _root_.GD.N0230.N0645.d000858



theorem d015279
    (s : _root_.GD.N0230.N0645.d000855) (hs : _root_.GD.N0232.N0720.N1200.d015276 s) :
    _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 s (_root_.GD.N0232.N0720.N1200.d015278 s) ∧
      _root_.GD.N0230.N0630.d000786 _root_.GD.N0232.N0720.N1200.d015266
        (_root_.GD.N0232.N0720.N1200.d015278 s) := by
  have hseed : s = _root_.GD.N0230.N0645.d000860 :=
    (_root_.GD.N0232.N0720.N1200.d015277 s).1 hs
  subst s
  exact ⟨_root_.GD.N0232.N0720.N1200.d015271 _root_.GD.N0230.N0645.d000858,
    _root_.GD.N0232.N0720.N1200.d015274⟩



theorem d015280
    (s : _root_.GD.N0230.N0645.d000855) (_hs : _root_.GD.N0232.N0720.N1200.d015276 s) :
    IsMinOn (fun d : _root_.GD.N0230.N0645.d000855 ↦ d.1 ^ 2)
      {d : _root_.GD.N0230.N0645.d000855 | _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 s d}
      (_root_.GD.N0232.N0720.N1200.d015278 s) := by
  intro d _hd
  simpa [_root_.GD.N0232.N0720.N1200.d015278, _root_.GD.N0230.N0645.d000858] using sq_nonneg d.1



theorem d015281
    (s : _root_.GD.N0230.N0645.d000855) (_hs : _root_.GD.N0232.N0720.N1200.d015276 s) :
    ∀ d : _root_.GD.N0230.N0645.d000855,
      _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 s d →
      d.1 ^ 2 ≤ (_root_.GD.N0232.N0720.N1200.d015278 s).1 ^ 2 →
      d = _root_.GD.N0232.N0720.N1200.d015278 s := by
  intro d _hd hmin
  apply Subtype.ext
  have hdnonneg : 0 ≤ d.1 := d.2.1
  have hdsq : d.1 ^ 2 ≤ 0 := by
    simpa [_root_.GD.N0232.N0720.N1200.d015278, _root_.GD.N0230.N0645.d000858] using hmin
  have hd : d.1 = 0 := by nlinarith [sq_nonneg d.1]
  simpa [_root_.GD.N0232.N0720.N1200.d015278, _root_.GD.N0230.N0645.d000858] using hd


def d015282 (s : _root_.GD.N0230.N0645.d000855) : ℝ :=
  (_root_.GD.N0230.N0645.d000856 (_root_.GD.N0232.N0720.N1200.d015278 s)).1 ^ 2 -
    (_root_.GD.N0232.N0720.N1200.d015278 s).1 ^ 2



def d015283 (s : _root_.GD.N0230.N0645.d000855) : ℝ :=
  _root_.GD.N0232.N0720.N1200.d015282 s + _root_.GD.N0232.N0720.N1200.d015282 s


theorem d015284 (s : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0232.N0720.N1200.d015283 s = 2 := by
  norm_num [_root_.GD.N0232.N0720.N1200.d015283, _root_.GD.N0232.N0720.N1200.d015282,
    _root_.GD.N0232.N0720.N1200.d015278, _root_.GD.N0230.N0645.d000858, _root_.GD.N0230.N0645.d000856]


theorem d015285 :
    IsCompact {s : _root_.GD.N0230.N0645.d000855 | _root_.GD.N0232.N0720.N1200.d015276 s} := by
  have heq : {s : _root_.GD.N0230.N0645.d000855 | _root_.GD.N0232.N0720.N1200.d015276 s} =
      ({_root_.GD.N0230.N0645.d000860} : Set _root_.GD.N0230.N0645.d000855) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
      _root_.GD.N0232.N0720.N1200.d015277]
  rw [heq]
  exact isCompact_singleton


theorem d015286 :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ s : _root_.GD.N0230.N0645.d000855,
        _root_.GD.N0232.N0720.N1200.d015276 s →
        ε ≤ _root_.GD.N0232.N0720.N1200.d015283 s := by
  refine ⟨2, by norm_num, ?_⟩
  intro s _hs
  rw [_root_.GD.N0232.N0720.N1200.d015284]



theorem d015287 :
    ¬ ∃ s : _root_.GD.N0230.N0645.d000855,
      _root_.GD.N0232.N0720.N1200.d015276 s ∧
        _root_.GD.N0232.N0720.N1200.d015283 s = 0 := by
  rintro ⟨s, _hs, hzero⟩
  rw [_root_.GD.N0232.N0720.N1200.d015284] at hzero
  norm_num at hzero



theorem d015288 :
    (IsCompact (Set.Icc (0 : ℝ) 1) ∧
      Convex ℝ (Set.Icc (0 : ℝ) 1)) ∧
      Continuous _root_.GD.N0230.N0645.d000856 ∧
      MapsTo _root_.GD.N0230.N0645.d000856
        {x : _root_.GD.N0230.N0645.d000855 |
          _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 _root_.GD.N0230.N0645.d000860 x}
        {x : _root_.GD.N0230.N0645.d000855 |
          _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 _root_.GD.N0230.N0645.d000860 x} ∧
      IsCompact {s : _root_.GD.N0230.N0645.d000855 | _root_.GD.N0232.N0720.N1200.d015276 s} ∧
      _root_.GD.N0232.N0720.N1200.d015276 _root_.GD.N0230.N0645.d000860 ∧
      _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 _root_.GD.N0230.N0645.d000860
        (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860) ∧
      IsMinOn (fun d : _root_.GD.N0230.N0645.d000855 ↦ d.1 ^ 2)
        {d : _root_.GD.N0230.N0645.d000855 |
          _root_.GD.N0230.N0556.d000030 _root_.GD.N0232.N0720.N1200.d015266 _root_.GD.N0230.N0645.d000860 d}
        (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860) ∧
      _root_.GD.N0230.N0630.d000786 _root_.GD.N0232.N0720.N1200.d015266
        (_root_.GD.N0232.N0720.N1200.d015278 _root_.GD.N0230.N0645.d000860) ∧
      _root_.GD.N0232.N0720.N1200.d015283 _root_.GD.N0230.N0645.d000860 = 2 ∧
      (∃ ε : ℝ, 0 < ε ∧
        ∀ s : _root_.GD.N0230.N0645.d000855, _root_.GD.N0232.N0720.N1200.d015276 s →
          ε ≤ _root_.GD.N0232.N0720.N1200.d015283 s) := by
  have hseed : _root_.GD.N0232.N0720.N1200.d015276 _root_.GD.N0230.N0645.d000860 :=
    (_root_.GD.N0232.N0720.N1200.d015277 _root_.GD.N0230.N0645.d000860).2 rfl
  have hspec := _root_.GD.N0232.N0720.N1200.d015279 _root_.GD.N0230.N0645.d000860 hseed
  exact ⟨_root_.GD.N0232.N0720.N1200.d015273,
    _root_.GD.N0232.N0720.N1200.d015269,
    _root_.GD.N0232.N0720.N1200.d015272,
    _root_.GD.N0232.N0720.N1200.d015285, hseed,
    hspec.1,
    _root_.GD.N0232.N0720.N1200.d015280
      _root_.GD.N0230.N0645.d000860 hseed,
    hspec.2,
    _root_.GD.N0232.N0720.N1200.d015284 _root_.GD.N0230.N0645.d000860,
    _root_.GD.N0232.N0720.N1200.d015286⟩




def d015289 (x : NNReal) : ℝ :=
  (x : ℝ) / (1 + (x : ℝ))


def d015290 (x : NNReal) : NNReal := x / 2

theorem d015291 : Continuous _root_.GD.N0232.N0720.N1200.d015289 := by
  unfold _root_.GD.N0232.N0720.N1200.d015289
  exact continuous_subtype_val.div
    (continuous_const.add continuous_subtype_val)
    (fun x ↦ by positivity)

theorem d015292 : Continuous _root_.GD.N0232.N0720.N1200.d015290 := by
  unfold _root_.GD.N0232.N0720.N1200.d015290
  fun_prop

theorem d015293 (x : NNReal) : 0 ≤ _root_.GD.N0232.N0720.N1200.d015289 x := by
  unfold _root_.GD.N0232.N0720.N1200.d015289
  positivity

theorem d015294 (x : NNReal) : _root_.GD.N0232.N0720.N1200.d015289 x ≤ 1 := by
  unfold _root_.GD.N0232.N0720.N1200.d015289
  rw [div_le_one (by positivity)]
  linarith [x.2]



theorem d015295
    (x : NNReal) (hx : x ≠ 0) :
    _root_.GD.N0232.N0720.N1200.d015289 (_root_.GD.N0232.N0720.N1200.d015290 x) < _root_.GD.N0232.N0720.N1200.d015289 x := by
  have hxpos : 0 < (x : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hx)
  unfold _root_.GD.N0232.N0720.N1200.d015289 _root_.GD.N0232.N0720.N1200.d015290
  simp only [NNReal.coe_div, NNReal.coe_ofNat]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

variable (μ : Measure NNReal) [IsProbabilityMeasure μ]

private theorem d015296 : Integrable _root_.GD.N0232.N0720.N1200.d015289 μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact _root_.GD.N0232.N0720.N1200.d015291.aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1200.d015293 x)]
      exact _root_.GD.N0232.N0720.N1200.d015294 x

private theorem d015297 :
    Integrable (fun x ↦ _root_.GD.N0232.N0720.N1200.d015289 (_root_.GD.N0232.N0720.N1200.d015290 x)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact
      (_root_.GD.N0232.N0720.N1200.d015291.comp _root_.GD.N0232.N0720.N1200.d015292).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (_root_.GD.N0232.N0720.N1200.d015293 (_root_.GD.N0232.N0720.N1200.d015290 x))]
      exact _root_.GD.N0232.N0720.N1200.d015294 (_root_.GD.N0232.N0720.N1200.d015290 x)



theorem d015298
    (hinvariant :
      ∫ x, _root_.GD.N0232.N0720.N1200.d015289 (_root_.GD.N0232.N0720.N1200.d015290 x) ∂μ =
        ∫ x, _root_.GD.N0232.N0720.N1200.d015289 x ∂μ) :
    ∀ᵐ x ∂μ, x = 0 := by
  let gap : NNReal → ℝ := fun x ↦
    _root_.GD.N0232.N0720.N1200.d015289 x - _root_.GD.N0232.N0720.N1200.d015289 (_root_.GD.N0232.N0720.N1200.d015290 x)
  have hgapNonneg : ∀ x, 0 ≤ gap x := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp [gap, _root_.GD.N0232.N0720.N1200.d015289, _root_.GD.N0232.N0720.N1200.d015290]
    · exact sub_nonneg.mpr (_root_.GD.N0232.N0720.N1200.d015295 x hx).le
  have hgapInt : Integrable gap μ :=
    (_root_.GD.N0232.N0720.N1200.d015296 μ).sub
      (_root_.GD.N0232.N0720.N1200.d015297 μ)
  have hgapIntegral : ∫ x, gap x ∂μ = 0 := by
    rw [integral_sub (_root_.GD.N0232.N0720.N1200.d015296 μ)
      (_root_.GD.N0232.N0720.N1200.d015297 μ)]
    exact sub_eq_zero.mpr hinvariant.symm
  have hgapZero : gap =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hgapNonneg hgapInt).1 hgapIntegral
  filter_upwards [hgapZero] with x hx
  by_contra hne
  have hpos : 0 < gap x := sub_pos.mpr
    (_root_.GD.N0232.N0720.N1200.d015295 x hne)
  rw [hx] at hpos
  exact (lt_irrefl 0) hpos



theorem d015299
    (hstationary : Measure.map _root_.GD.N0232.N0720.N1200.d015290 μ = μ) :
    ∀ᵐ x ∂μ, x = 0 := by
  apply _root_.GD.N0232.N0720.N1200.d015298 μ
  calc
    ∫ x, _root_.GD.N0232.N0720.N1200.d015289 (_root_.GD.N0232.N0720.N1200.d015290 x) ∂μ =
        ∫ x, _root_.GD.N0232.N0720.N1200.d015289 x ∂Measure.map _root_.GD.N0232.N0720.N1200.d015290 μ := by
      symm
      exact integral_map
        _root_.GD.N0232.N0720.N1200.d015292.aemeasurable
        _root_.GD.N0232.N0720.N1200.d015291.aestronglyMeasurable
    _ = ∫ x, _root_.GD.N0232.N0720.N1200.d015289 x ∂μ := by rw [hstationary]



theorem d015300
    (hpositive : μ (Set.Ioi (0 : NNReal)) = 1) :
    ¬ Measure.map _root_.GD.N0232.N0720.N1200.d015290 μ = μ := by
  intro hstationary
  have hzero : ∀ᵐ x ∂μ, x = 0 :=
    _root_.GD.N0232.N0720.N1200.d015299 μ hstationary
  have hIoiZero : μ (Set.Ioi (0 : NNReal)) = 0 := by
    apply measure_mono_null _ (ae_iff.mp hzero)
    intro x hx
    exact ne_of_gt hx
  rw [hIoiZero] at hpositive
  norm_num at hpositive

end

end N1200
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1200.d015244
#print axioms _root_.GD.N0232.N0720.N1200.d015240
#print axioms _root_.GD.N0232.N0720.N1200.d015248
#print axioms _root_.GD.N0232.N0720.N1200.d015247
#print axioms _root_.GD.N0232.N0720.N1200.d015254
#print axioms _root_.GD.N0232.N0720.N1200.d015257
#print axioms _root_.GD.N0232.N0720.N1200.d015262
#print axioms _root_.GD.N0232.N0720.N1200.d015265
#print axioms _root_.GD.N0232.N0720.N1200.d015288
#print axioms _root_.GD.N0232.N0720.N1200.d015299
#print axioms _root_.GD.N0232.N0720.N1200.d015300
