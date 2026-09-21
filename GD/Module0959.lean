import GD.Module0151
import GD.Module0958































open Filter Set Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1073

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1071
open _root_.GD.N0230.N0569
open _root_.GD.N0230.N0580
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0646
open _root_.GD.N0230.N0670

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)


abbrev d015042 := _root_.GD.N0232.N0720.N1025.d014304 m n hm hn


def d015043
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) : _root_.GD.N0232.N0720.N1025.d014302 m n :=
  (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm
    (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p).1








structure d015044
    (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) where
  thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168
  t : ℝ
  t_pos : 0 < t
  t_lt_one : t < 1
  fraction_tendsto : Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
      (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t)
  pLimit : _root_.GD.N0232.N0720.N1025.d014302 m n
  qLimit : _root_.GD.N0232.N0720.N1025.d014302 m n
  p_weak : _root_.GD.N0230.N0646.d000537
    (fun j ↦ _root_.GD.N0232.N0720.N1073.d015043 m n hm hn (thetaSeq j) p)
    pLimit
  q_weak : _root_.GD.N0230.N0646.d000537
    (fun j ↦ _root_.GD.N0232.N0720.N1073.d015043 m n hm hn (thetaSeq j) q)
    qLimit





structure d015045
    (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    extends _root_.GD.N0232.N0720.N1073.d015044 m n hm hn p q where
  tax_tendsto : Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1067.d014418 m n hm hn (thetaSeq j) p q)
    atTop (nhds 0)



theorem d015045.d015046
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q) :
    packet.pLimit = packet.qLimit := by
  exact _root_.GD.N0232.N0720.N1071.d015040
    m n hm hn packet.thetaSeq packet.t packet.t_pos packet.t_lt_one
    packet.fraction_tendsto p q packet.tax_tendsto
    packet.pLimit packet.qLimit packet.p_weak packet.q_weak





structure d015047
    (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) where
  thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168
  t : ℝ
  t_pos : 0 < t
  t_lt_one : t < 1
  fraction_tendsto : Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
      (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t)
  tax_tendsto : Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1067.d014418 m n hm hn (thetaSeq j) p q)
    atTop (nhds 0)



theorem d015047.d015048
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (data : _root_.GD.N0232.N0720.N1073.d015047 m n hm hn p q) :
    Nonempty (_root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q) := by
  obtain ⟨extraction, hextraction, r, hpweak, hqweak⟩ :=
    _root_.GD.N0232.N0720.N1071.d015041
      m n hm hn data.thetaSeq data.t data.t_pos data.t_lt_one
      data.fraction_tendsto p q data.tax_tendsto
  refine ⟨
    { thetaSeq := fun j ↦ data.thetaSeq (extraction j)
      t := data.t
      t_pos := data.t_pos
      t_lt_one := data.t_lt_one
      fraction_tendsto := data.fraction_tendsto.comp hextraction
      pLimit := r
      qLimit := r
      p_weak := ?_
      q_weak := ?_
      tax_tendsto := data.tax_tendsto.comp hextraction }⟩
  · simpa only [_root_.GD.N0232.N0720.N1073.d015043] using hpweak
  · simpa only [_root_.GD.N0232.N0720.N1073.d015043] using hqweak










def d015049
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n)) : Prop :=
  ∀ (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
    _root_.GD.N0230.N0569.d001684 face p.1 →
    _root_.GD.N0230.N0569.d001684 face q.1 →
    ∀ packet : _root_.GD.N0232.N0720.N1073.d015044 m n hm hn p q,
      packet.pLimit = packet.qLimit → p = q


structure d015050
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n)) where
  p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn
  q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn
  p_survives : _root_.GD.N0230.N0569.d001684 face p.1
  q_survives : _root_.GD.N0230.N0569.d001684 face q.1
  distinct : p ≠ q
  packet : _root_.GD.N0232.N0720.N1073.d015044 m n hm hn p q
  limits_eq : packet.pLimit = packet.qLimit



theorem d015051
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n)) :
    _root_.GD.N0232.N0720.N1073.d015049 m n hm hn face ↔
      ¬ Nonempty
        (_root_.GD.N0232.N0720.N1073.d015050
          m n hm hn face) := by
  constructor
  · intro hproper hcertificate
    obtain ⟨_root_.GD.N0232.N0720.N1080.d014174⟩ := hcertificate
    exact _root_.GD.N0232.N0720.N1080.d014174.distinct
      (hproper _root_.GD.N0232.N0720.N1080.d014174.p _root_.GD.N0232.N0720.N1080.d014174.q
        _root_.GD.N0232.N0720.N1080.d014174.p_survives _root_.GD.N0232.N0720.N1080.d014174.q_survives
        _root_.GD.N0232.N0720.N1080.d014174.packet _root_.GD.N0232.N0720.N1080.d014174.limits_eq)
  · intro hno p q hp hq packet hlimits
    by_contra hpq
    exact hno ⟨
      { p := p
        q := q
        p_survives := hp
        q_survives := hq
        distinct := hpq
        packet := packet
        limits_eq := hlimits }⟩



theorem d015052
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n)) :
    _root_.GD.N0232.N0720.N1073.d015049 m n hm hn face ∨
      Nonempty
        (_root_.GD.N0232.N0720.N1073.d015050
          m n hm hn face) := by
  classical
  by_cases hproper :
      _root_.GD.N0232.N0720.N1073.d015049 m n hm hn face
  · exact Or.inl hproper
  · right
    by_contra hno
    exact hproper
      ((_root_.GD.N0232.N0720.N1073.d015051
        m n hm hn face).2 hno)








theorem d015053
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (hproper : _root_.GD.N0232.N0720.N1073.d015049 m n hm hn face)
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (hp : _root_.GD.N0230.N0569.d001684 face p.1)
    (hq : _root_.GD.N0230.N0569.d001684 face q.1)
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q) :
    p = q := by
  exact hproper p q hp hq (_root_.GD.N0232.N0720.N1073.d015044.mk
    packet.thetaSeq packet.t packet.t_pos packet.t_lt_one
    packet.fraction_tendsto packet.pLimit packet.qLimit packet.p_weak packet.q_weak)
    (packet.d015046 m n hm hn)














def d015054
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) : Prop :=
  ∀ (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
    _root_.GD.N0230.N0569.d001684 face q.1 →
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1 →
    ∀ packet : _root_.GD.N0232.N0720.N1073.d015044 m n hm hn p q,
      packet.pLimit = packet.qLimit → q = p




structure d015055
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) where
  q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn
  q_survives : _root_.GD.N0230.N0569.d001684 face q.1
  dominates : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1
  distinct : q ≠ p
  packet : _root_.GD.N0232.N0720.N1073.d015044 m n hm hn p q
  limits_eq : packet.pLimit = packet.qLimit



theorem d015056
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) :
    _root_.GD.N0232.N0720.N1073.d015054 m n hm hn face p ↔
      ¬ Nonempty
        (_root_.GD.N0232.N0720.N1073.d015055
          m n hm hn face p) := by
  constructor
  · intro hproper hcertificate
    obtain ⟨_root_.GD.N0232.N0720.N1080.d014174⟩ := hcertificate
    exact _root_.GD.N0232.N0720.N1080.d014174.distinct
      (hproper _root_.GD.N0232.N0720.N1080.d014174.q _root_.GD.N0232.N0720.N1080.d014174.q_survives
        _root_.GD.N0232.N0720.N1080.d014174.dominates _root_.GD.N0232.N0720.N1080.d014174.packet _root_.GD.N0232.N0720.N1080.d014174.limits_eq)
  · intro hno q hq hdom packet hlimits
    by_contra hqp
    exact hno ⟨
      { q := q
        q_survives := hq
        dominates := hdom
        distinct := hqp
        packet := packet
        limits_eq := hlimits }⟩


theorem d015057
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) :
    _root_.GD.N0232.N0720.N1073.d015054 m n hm hn face p ∨
      Nonempty
        (_root_.GD.N0232.N0720.N1073.d015055
          m n hm hn face p) := by
  classical
  by_cases hproper :
      _root_.GD.N0232.N0720.N1073.d015054 m n hm hn face p
  · exact Or.inl hproper
  · right
    by_contra hno
    exact hproper
      ((_root_.GD.N0232.N0720.N1073.d015056
        m n hm hn face p).2 hno)




def d015058
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) : Prop :=
  ∀ (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
    _root_.GD.N0230.N0569.d001684 face q.1 →
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1 → q ≠ p →
      Nonempty (_root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q)




def d015059
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) : Prop :=
  ∀ (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
    _root_.GD.N0230.N0569.d001684 face q.1 →
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1 → q ≠ p →
      Nonempty (_root_.GD.N0232.N0720.N1073.d015047 m n hm hn p q)



theorem d015060
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hrouting :
      _root_.GD.N0232.N0720.N1073.d015059
        m n hm hn face p) :
    _root_.GD.N0232.N0720.N1073.d015058
      m n hm hn face p := by
  intro q hq hdom hqp
  obtain ⟨data⟩ := hrouting q hq hdom hqp
  exact data.d015048 m n hm hn



theorem d015061
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (hproper :
      _root_.GD.N0232.N0720.N1073.d015054 m n hm hn face p)
    (hq : _root_.GD.N0230.N0569.d001684 face q.1)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1)
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q) :
    q = p := by
  exact hproper q hq hdom (_root_.GD.N0232.N0720.N1073.d015044.mk
    packet.thetaSeq packet.t packet.t_pos packet.t_lt_one
    packet.fraction_tendsto packet.pLimit packet.qLimit packet.p_weak packet.q_weak)
    (packet.d015046 m n hm hn)












theorem d015062
    (objective : ℕ → _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ)
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (htower : _root_.GD.N0230.N0583.d000745 objective
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) face)
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hp : _root_.GD.N0230.N0569.d001684 face p.1)
    (hmono : _root_.GD.N0230.N0596.d000732
      (_root_.GD.N0232.N0720.N1025.d014305 m n) objective)
    (hrouting :
      _root_.GD.N0232.N0720.N1073.d015058
        m n hm hn face p)
    (hproper :
      _root_.GD.N0232.N0720.N1073.d015054 m n hm hn face p) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) p.1 := by
  have hlex : _root_.GD.N0230.N0596.d000730 objective
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p.1 :=
    _root_.GD.N0230.N0583.d000747
      objective (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) face htower hp
  intro q hdom
  have hqC : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
    _root_.GD.N0232.N0720.N1025.d014314 m n hm hn hlex.1 hdom
  have heq : ∀ i, objective i q = objective i p.1 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
        apply le_antisymm
        · exact hmono i hdom
        · exact hlex.2 i q hqC (fun j hj ↦ ih j hj)
  have hqSurvives : _root_.GD.N0230.N0569.d001684 face q :=
    _root_.GD.N0230.N0580.d001536
      objective (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) face htower hp hqC heq
  let qC : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn := ⟨q, hqC⟩
  by_contra hqp
  have hqCp : qC ≠ p := by
    intro h
    exact hqp (congrArg Subtype.val h)
  obtain ⟨packet⟩ := hrouting qC hqSurvives hdom hqCp
  have hcapEq : qC = p :=
    _root_.GD.N0232.N0720.N1073.d015061
      m n hm hn face hproper hqSurvives hdom packet
  exact hqp (congrArg Subtype.val hcapEq)








theorem d015063
    (objective : ℕ → _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ)
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (htower : _root_.GD.N0230.N0583.d000745 objective
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) face)
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hp : _root_.GD.N0230.N0569.d001684 face p.1)
    (hmono : _root_.GD.N0230.N0596.d000732
      (_root_.GD.N0232.N0720.N1025.d014305 m n) objective)
    (hrouting :
      _root_.GD.N0232.N0720.N1073.d015059
        m n hm hn face p)
    (hproper :
      _root_.GD.N0232.N0720.N1073.d015054 m n hm hn face p) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) p.1 := by
  exact _root_.GD.N0232.N0720.N1073.d015062
    m n hm hn objective face htower p hp hmono
    (_root_.GD.N0232.N0720.N1073.d015060
      m n hm hn face p hrouting)
    hproper



theorem d015064
    (objective : ℕ → _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ)
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (htower : _root_.GD.N0230.N0583.d000745 objective
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) face)
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hp : _root_.GD.N0230.N0569.d001684 face p.1)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hmono : _root_.GD.N0230.N0596.d000732
      (_root_.GD.N0232.N0720.N1025.d014305 m n) objective)
    (hrouting :
      _root_.GD.N0232.N0720.N1073.d015058
        m n hm hn face p)
    (hproper :
      _root_.GD.N0232.N0720.N1073.d015054 m n hm hn face p) :
    (∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p) ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) p.1 := by
  exact ⟨hfixed,
    _root_.GD.N0232.N0720.N1073.d015062
      m n hm hn objective face htower p hp hmono hrouting hproper⟩



def d015065
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (hq : _root_.GD.N0230.N0569.d001684 face q.1)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1)
    (hqp : q ≠ p)
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q) :
    _root_.GD.N0232.N0720.N1073.d015055
      m n hm hn face p where
  q := q
  q_survives := hq
  dominates := hdom
  distinct := hqp
  packet := (_root_.GD.N0232.N0720.N1073.d015044.mk
    packet.thetaSeq packet.t packet.t_pos packet.t_lt_one
    packet.fraction_tendsto packet.pLimit packet.qLimit packet.p_weak packet.q_weak)
  limits_eq := packet.d015046 m n hm hn







theorem d015066
    (objective : ℕ → _root_.GD.N0232.N0720.N1025.d014303 m n → ℝ)
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (htower : _root_.GD.N0230.N0583.d000745 objective
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) face)
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hp : _root_.GD.N0230.N0569.d001684 face p.1)
    (hmono : _root_.GD.N0230.N0596.d000732
      (_root_.GD.N0232.N0720.N1025.d014305 m n) objective)
    (hrouting :
      _root_.GD.N0232.N0720.N1073.d015058
        m n hm hn face p) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) p.1 ∨
      Nonempty
        (_root_.GD.N0232.N0720.N1073.d015055
          m n hm hn face p) := by
  classical
  by_cases hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) p.1
  · exact Or.inl hterminal
  · right
    have hlex : _root_.GD.N0230.N0596.d000730 objective
        (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) p.1 :=
      _root_.GD.N0230.N0583.d000747
        objective (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) face htower hp
    rw [_root_.GD.N0230.N0608.d000674] at hterminal
    push Not at hterminal
    obtain ⟨q, hdom, hqp⟩ := hterminal
    have hqC : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
      _root_.GD.N0232.N0720.N1025.d014314 m n hm hn hlex.1 hdom
    have heq : ∀ i, objective i q = objective i p.1 := by
      intro i
      induction i using Nat.strong_induction_on with
      | h i ih =>
          apply le_antisymm
          · exact hmono i hdom
          · exact hlex.2 i q hqC (fun j hj ↦ ih j hj)
    have hqSurvives : _root_.GD.N0230.N0569.d001684 face q :=
      _root_.GD.N0230.N0580.d001536
        objective (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) face htower hp hqC heq
    let qC : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn := ⟨q, hqC⟩
    have hqCp : qC ≠ p := by
      intro h
      exact hqp (congrArg Subtype.val h)
    obtain ⟨packet⟩ := hrouting qC hqSurvives hdom hqCp
    let certificate :
        _root_.GD.N0232.N0720.N1073.d015055
          m n hm hn face p :=
      _root_.GD.N0232.N0720.N1073.d015065
        (m := m) (n := n) (hm := hm) (hn := hn)
        (face := face) (p := p) (q := qC)
        hqSurvives hdom hqCp packet
    exact ⟨certificate⟩





def d015067
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n)) : Prop :=
  ∀ (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
    _root_.GD.N0230.N0569.d001684 face p.1 →
    _root_.GD.N0230.N0569.d001684 face q.1 → p ≠ q →
      Nonempty (_root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q)



theorem d015068
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (hrouting :
      _root_.GD.N0232.N0720.N1073.d015067
        m n hm hn face)
    (hproper : _root_.GD.N0232.N0720.N1073.d015049 m n hm hn face) :
    ∀ (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
      _root_.GD.N0230.N0569.d001684 face p.1 →
      ∀ (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
        _root_.GD.N0230.N0569.d001684 face q.1 → p = q := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨packet⟩ := hrouting p q hp hq hpq
  exact hpq
    (_root_.GD.N0232.N0720.N1073.d015053
      m n hm hn face hproper hp hq packet)







theorem d015069
    (face : ℕ → Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (hrouting :
      _root_.GD.N0232.N0720.N1073.d015067
        m n hm hn face) :
    (∀ (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
      _root_.GD.N0230.N0569.d001684 face p.1 →
      ∀ (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn),
        _root_.GD.N0230.N0569.d001684 face q.1 → p = q) ∨
      Nonempty
        (_root_.GD.N0232.N0720.N1073.d015050
          m n hm hn face) := by
  rcases _root_.GD.N0232.N0720.N1073.d015052
      m n hm hn face with hproper | hcertificate
  · exact Or.inl
      (_root_.GD.N0232.N0720.N1073.d015068
        m n hm hn face hrouting hproper)
  · exact Or.inr hcertificate

end

end N1073
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1073.d015045.d015046
#print axioms _root_.GD.N0232.N0720.N1073.d015051
#print axioms _root_.GD.N0232.N0720.N1073.d015053
#print axioms _root_.GD.N0232.N0720.N1073.d015062
#print axioms _root_.GD.N0232.N0720.N1073.d015066
#print axioms _root_.GD.N0232.N0720.N1073.d015069
