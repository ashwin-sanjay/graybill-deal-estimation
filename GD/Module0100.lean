import GD.Module0091
import GD.Module0099
import GD.Module0093
























open MeasureTheory Set Topology

namespace GD
namespace N0230
namespace N0659

noncomputable section

open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0691
open _root_.GD.N0230.N0715



variable {I : Type*}
variable {H : I → Type*}
variable [∀ i, NormedAddCommGroup (H i)]
variable [∀ i, InnerProductSpace ℝ (H i)]
variable [∀ i, CompleteSpace (H i)]


def d001275 (C : ∀ i, Set (H i)) :
    Set (∀ i, WeakSpace ℝ (H i)) :=
  Set.pi Set.univ (fun i ↦ toWeakSpace ℝ (H i) '' C i)

theorem d001276
    (C : ∀ i, Set (H i)) (x : ∀ i, WeakSpace ℝ (H i)) :
    x ∈ _root_.GD.N0230.N0659.d001275 C ↔
      ∀ i, x i ∈ toWeakSpace ℝ (H i) '' C i := by
  simp [_root_.GD.N0230.N0659.d001275]



theorem d001277
    (C : ∀ i, Set (H i))
    (hCcompact : ∀ i,
      IsCompact (toWeakSpace ℝ (H i) '' C i)) :
    IsCompact (_root_.GD.N0230.N0659.d001275 C) := by
  exact isCompact_univ_pi hCcompact



theorem d001278
    (C : ∀ i, Set (H i)) (r : I → ℝ)
    (hconv : ∀ i, Convex ℝ (C i))
    (hclosed : ∀ i, IsClosed (C i))
    (hnorm : ∀ i x, x ∈ C i → ‖x‖ ≤ r i) :
    IsCompact (_root_.GD.N0230.N0659.d001275 C) := by
  apply _root_.GD.N0230.N0659.d001277 C
  intro i
  exact _root_.GD.N0230.N0633.d001201
    (r i) (hconv i) (hclosed i) (hnorm i)



theorem d001279
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {anchor x : G} {radius : ℝ}
    (hx : x ∈ Metric.closedBall anchor radius) :
    ‖x‖ ≤ ‖anchor‖ + radius := by
  have htriangle : ‖x‖ ≤ ‖x - anchor‖ + ‖anchor‖ := by
    calc
      ‖x‖ = ‖(x - anchor) + anchor‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - anchor‖ + ‖anchor‖ := norm_add_le _ _
  have hdist : ‖x - anchor‖ ≤ radius := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  linarith



theorem d001280
    (anchor : ∀ i, H i) (radius : I → ℝ) :
    IsCompact (_root_.GD.N0230.N0659.d001275
      (fun i ↦ Metric.closedBall (anchor i) (radius i))) := by
  apply _root_.GD.N0230.N0659.d001278
    (fun i ↦ Metric.closedBall (anchor i) (radius i))
    (fun i ↦ ‖anchor i‖ + radius i)
  · exact fun i ↦ convex_closedBall (anchor i) (radius i)
  · exact fun _ ↦ Metric.isClosed_closedBall
  · intro i x hx
    exact _root_.GD.N0230.N0659.d001279 hx



variable {Omega : Type*} [MeasurableSpace Omega]




def d001281 (mu : I → Measure Omega) :
    Set (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :=
  ⋂ i, ⋂ j,
    (fun x ↦ (x i, x j)) ⁻¹'
      _root_.GD.N0230.N0715.d001272
        (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
        (_root_.GD.N0230.N0691.d001210 (mu i) (mu j))



def d001282 (mu : I → Measure Omega) (i j : I) :
    Set (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :=
  (fun x ↦ (x i, x j)) ⁻¹'
    _root_.GD.N0230.N0715.d001272
      (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
      (_root_.GD.N0230.N0691.d001210 (mu i) (mu j))


theorem d001283
    (mu : I → Measure Omega) (i j : I) :
    IsClosed (_root_.GD.N0230.N0659.d001282 mu i j) := by
  apply (_root_.GD.N0230.N0715.d001274
    (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
    (_root_.GD.N0230.N0691.d001210 (mu i) (mu j))
    (_root_.GD.N0230.N0691.d001216 (mu i) (mu j))).preimage
  exact (continuous_apply i).prodMk (continuous_apply j)

theorem d001284
    (mu : I → Measure Omega)
    (x : ∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :
    x ∈ _root_.GD.N0230.N0659.d001281 mu ↔
      ∀ i j,
        (x i, x j) ∈
          _root_.GD.N0230.N0715.d001272
            (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
            (_root_.GD.N0230.N0691.d001210 (mu i) (mu j)) := by
  simp [_root_.GD.N0230.N0659.d001281]






theorem d001285
    (mu : I → Measure Omega) :
    IsClosed (_root_.GD.N0230.N0659.d001281 mu) := by
  unfold _root_.GD.N0230.N0659.d001281
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply (_root_.GD.N0230.N0715.d001274
    (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
    (_root_.GD.N0230.N0691.d001210 (mu i) (mu j))
    (_root_.GD.N0230.N0691.d001216 (mu i) (mu j))).preimage
  exact (continuous_apply i).prodMk (continuous_apply j)





theorem d001286
    (mu nu : Measure Omega) (hnu : nu ≪ mu)
    {x : Lp ℝ 2 mu} {y : Lp ℝ 2 nu}
    (hxy : _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209 mu nu) (_root_.GD.N0230.N0691.d001210 mu nu) x y) :
    (fun omega ↦ x omega) =ᵐ[nu] fun omega ↦ y omega := by
  obtain ⟨h, hleft, hright⟩ := hxy
  have hleftMu := _root_.GD.N0230.N0691.d001211 mu nu h
  rw [hleft] at hleftMu
  have hleftNu := hnu.ae_le hleftMu
  have hrightNu := _root_.GD.N0230.N0691.d001212 mu nu h
  rw [hright] at hrightNu
  filter_upwards [hleftNu, hrightNu] with omega hL hR
  exact hL.trans hR.symm






theorem d001287
    (mu : I → Measure Omega) (reference : I)
    (hAC : ∀ i, mu i ≪ mu reference)
    (x : ∀ i, Lp ℝ 2 (mu i))
    (hpair : ∀ i j,
      _root_.GD.N0230.N0708.d001177
        (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
        (_root_.GD.N0230.N0691.d001210 (mu i) (mu j)) (x i) (x j)) :
    ∃ f : Omega → ℝ,
      ∃ hf : ∀ i, MemLp f 2 (mu i),
        ∀ i, (hf i).toLp f = x i := by
  let f : Omega → ℝ := fun omega ↦ x reference omega
  have hae : ∀ i, f =ᵐ[mu i] fun omega ↦ x i omega := by
    intro i
    exact _root_.GD.N0230.N0659.d001286
      (mu reference) (mu i) (hAC i) (hpair reference i)
  have hmem : ∀ i, MemLp f 2 (mu i) := by
    intro i
    exact MemLp.ae_eq (hae i).symm (Lp.memLp (x i))
  refine ⟨f, hmem, ?_⟩
  intro i
  apply Lp.ext
  filter_upwards [(hmem i).coeFn_toLp, hae i] with omega hto heq
  exact hto.trans heq





theorem d001288
    (mu : I → Measure Omega) (reference : I)
    (hAC : ∀ i, mu i ≪ mu reference)
    (x : ∀ i, Lp ℝ 2 (mu i))
    (hstar : ∀ i,
      _root_.GD.N0230.N0708.d001177
        (_root_.GD.N0230.N0691.d001209 (mu reference) (mu i))
        (_root_.GD.N0230.N0691.d001210 (mu reference) (mu i))
        (x reference) (x i)) :
    ∃ f : Omega → ℝ,
      ∃ hf : ∀ i, MemLp f 2 (mu i),
        ∀ i, (hf i).toLp f = x i := by
  let f : Omega → ℝ := fun omega ↦ x reference omega
  have hae : ∀ i, f =ᵐ[mu i] fun omega ↦ x i omega := by
    intro i
    exact _root_.GD.N0230.N0659.d001286
      (mu reference) (mu i) (hAC i) (hstar i)
  have hmem : ∀ i, MemLp f 2 (mu i) := by
    intro i
    exact MemLp.ae_eq (hae i).symm (Lp.memLp (x i))
  refine ⟨f, hmem, ?_⟩
  intro i
  apply Lp.ext
  filter_upwards [(hmem i).coeFn_toLp, hae i] with omega hto heq
  exact hto.trans heq





theorem d001289
    (mu : I → Measure Omega) (reference : I)
    (hAC : ∀ i, mu i ≪ mu reference)
    (x : ∀ i, Lp ℝ 2 (mu i)) :
    (∀ i j,
      _root_.GD.N0230.N0708.d001177
        (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
        (_root_.GD.N0230.N0691.d001210 (mu i) (mu j)) (x i) (x j)) ↔
      ∀ i,
        _root_.GD.N0230.N0708.d001177
          (_root_.GD.N0230.N0691.d001209 (mu reference) (mu i))
          (_root_.GD.N0230.N0691.d001210 (mu reference) (mu i))
          (x reference) (x i) := by
  constructor
  · intro hall i
    exact hall reference i
  · intro hstar
    obtain ⟨f, hf, hrealize⟩ :=
      _root_.GD.N0230.N0659.d001288
        mu reference hAC x hstar
    intro i j
    refine ⟨_root_.GD.N0230.N0691.d001218 (mu i) (mu j) f (hf i) (hf j), ?_, ?_⟩
    · rw [_root_.GD.N0230.N0691.d001219, hrealize i]
    · rw [_root_.GD.N0230.N0691.d001220, hrealize j]



def d001290
    (mu : I → Measure Omega) (reference : I) :
    Set (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :=
  ⋂ i, _root_.GD.N0230.N0659.d001282 mu reference i

theorem d001291
    (mu : I → Measure Omega) (reference : I)
    (x : ∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :
    x ∈ _root_.GD.N0230.N0659.d001290 mu reference ↔
      ∀ i,
        (x reference, x i) ∈
          _root_.GD.N0230.N0715.d001272
            (_root_.GD.N0230.N0691.d001209 (mu reference) (mu i))
            (_root_.GD.N0230.N0691.d001210 (mu reference) (mu i)) := by
  simp [_root_.GD.N0230.N0659.d001290, _root_.GD.N0230.N0659.d001282]





theorem d001292
    (mu : I → Measure Omega) (reference : I)
    (hAC : ∀ i, mu i ≪ mu reference) :
    _root_.GD.N0230.N0659.d001290 mu reference =
      _root_.GD.N0230.N0659.d001281 mu := by
  ext x
  constructor
  · intro hx
    let y : ∀ i, Lp ℝ 2 (mu i) :=
      fun i ↦ (toWeakSpace ℝ (Lp ℝ 2 (mu i))).symm (x i)
    have hstar : ∀ i,
        _root_.GD.N0230.N0708.d001177
          (_root_.GD.N0230.N0691.d001209 (mu reference) (mu i))
          (_root_.GD.N0230.N0691.d001210 (mu reference) (mu i))
          (y reference) (y i) := by
      intro i
      have hi := (_root_.GD.N0230.N0659.d001291 mu reference x).1 hx i
      simpa [_root_.GD.N0230.N0715.d001272, y] using hi
    have hall :=
      (_root_.GD.N0230.N0659.d001289 mu reference hAC y).2 hstar
    rw [_root_.GD.N0230.N0659.d001284]
    intro i j
    simpa [_root_.GD.N0230.N0715.d001272, y] using hall i j
  · intro hx
    rw [_root_.GD.N0230.N0659.d001291]
    intro i
    exact (_root_.GD.N0230.N0659.d001284 mu x).1 hx reference i




theorem d001293
    (mu : I → Measure Omega) (reference : I) :
    IsClosed (_root_.GD.N0230.N0659.d001290 mu reference) := by
  unfold _root_.GD.N0230.N0659.d001290
  apply isClosed_iInter
  intro i
  exact _root_.GD.N0230.N0659.d001283 mu reference i


def d001294
    (mu : I → Measure Omega) (reference : I)
    (C : ∀ i, Set (Lp ℝ 2 (mu i))) :
    Set (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :=
  _root_.GD.N0230.N0659.d001275 C ∩ _root_.GD.N0230.N0659.d001290 mu reference



theorem d001295
    (mu : I → Measure Omega) (reference : I)
    (C : ∀ i, Set (Lp ℝ 2 (mu i)))
    (hCcompact : ∀ i,
      IsCompact (toWeakSpace ℝ (Lp ℝ 2 (mu i)) '' C i)) :
    IsCompact (_root_.GD.N0230.N0659.d001294 mu reference C) := by
  exact (_root_.GD.N0230.N0659.d001277 C hCcompact).inter_right
    (_root_.GD.N0230.N0659.d001293 mu reference)





theorem d001296
    (mu : I → Measure Omega) (reference : I)
    (C : ∀ i, Set (Lp ℝ 2 (mu i)))
    (hCcompact : ∀ i,
      IsCompact (toWeakSpace ℝ (Lp ℝ 2 (mu i)) '' C i))
    (hfinite : ∀ u : Finset I,
      (_root_.GD.N0230.N0659.d001275 C ∩
        ⋂ i ∈ u, _root_.GD.N0230.N0659.d001282 mu reference i).Nonempty) :
    (_root_.GD.N0230.N0659.d001294 mu reference C).Nonempty := by
  let t : I → Set (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :=
    fun i ↦ _root_.GD.N0230.N0659.d001282 mu reference i
  have hall : (_root_.GD.N0230.N0659.d001275 C ∩ ⋂ i, t i).Nonempty :=
    (_root_.GD.N0230.N0659.d001277 C hCcompact).inter_iInter_nonempty t
      (fun i ↦ _root_.GD.N0230.N0659.d001283 mu reference i)
      (by simpa [t] using hfinite)
  simpa [_root_.GD.N0230.N0659.d001294, _root_.GD.N0230.N0659.d001290, t]
    using hall




theorem d001297
    (mu : I → Measure Omega) (reference : I)
    (hAC : ∀ i, mu i ≪ mu reference)
    (C : ∀ i, Set (Lp ℝ 2 (mu i)))
    (hCcompact : ∀ i,
      IsCompact (toWeakSpace ℝ (Lp ℝ 2 (mu i)) '' C i))
    (hfinite : ∀ u : Finset I,
      (_root_.GD.N0230.N0659.d001275 C ∩
        ⋂ i ∈ u, _root_.GD.N0230.N0659.d001282 mu reference i).Nonempty) :
    ∃ x : ∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i)),
      x ∈ _root_.GD.N0230.N0659.d001275 C ∧
      ∃ f : Omega → ℝ,
        ∃ hf : ∀ i, MemLp f 2 (mu i),
          ∀ i,
            toWeakSpace ℝ (Lp ℝ 2 (mu i)) ((hf i).toLp f) = x i := by
  obtain ⟨x, hxcap, hxstar⟩ :=
    _root_.GD.N0230.N0659.d001296
      mu reference C hCcompact hfinite
  let y : ∀ i, Lp ℝ 2 (mu i) :=
    fun i ↦ (toWeakSpace ℝ (Lp ℝ 2 (mu i))).symm (x i)
  have hstar : ∀ i,
      _root_.GD.N0230.N0708.d001177
        (_root_.GD.N0230.N0691.d001209 (mu reference) (mu i))
        (_root_.GD.N0230.N0691.d001210 (mu reference) (mu i))
        (y reference) (y i) := by
    intro i
    have hi := (_root_.GD.N0230.N0659.d001291 mu reference x).1 hxstar i
    simpa [_root_.GD.N0230.N0715.d001272, y] using hi
  obtain ⟨f, hf, hrealize⟩ :=
    _root_.GD.N0230.N0659.d001288
      mu reference hAC y hstar
  refine ⟨x, hxcap, f, hf, ?_⟩
  intro i
  rw [hrealize i]
  exact (toWeakSpace ℝ (Lp ℝ 2 (mu i))).apply_symm_apply (x i)






theorem d001298
    (mu : I → Measure Omega) (reference : I)
    (hAC : ∀ i, mu i ≪ mu reference)
    (x : ∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i)))
    (hx : x ∈ _root_.GD.N0230.N0659.d001281 mu) :
    ∃ f : Omega → ℝ,
      ∃ hf : ∀ i, MemLp f 2 (mu i),
        ∀ i, toWeakSpace ℝ (Lp ℝ 2 (mu i)) ((hf i).toLp f) = x i := by
  let y : ∀ i, Lp ℝ 2 (mu i) :=
    fun i ↦ (toWeakSpace ℝ (Lp ℝ 2 (mu i))).symm (x i)
  have hpair : ∀ i j,
      _root_.GD.N0230.N0708.d001177
        (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
        (_root_.GD.N0230.N0691.d001210 (mu i) (mu j)) (y i) (y j) := by
    intro i j
    have hij := (_root_.GD.N0230.N0659.d001284 mu x).1 hx i j
    simpa [_root_.GD.N0230.N0715.d001272, y] using hij
  obtain ⟨f, hf, hrealize⟩ :=
    _root_.GD.N0230.N0659.d001287 mu reference hAC y hpair
  refine ⟨f, hf, ?_⟩
  intro i
  rw [hrealize i]
  exact (toWeakSpace ℝ (Lp ℝ 2 (mu i))).apply_symm_apply (x i)





def d001299
    (mu : I → Measure Omega)
    (C : ∀ i, Set (Lp ℝ 2 (mu i))) :
    Set (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :=
  _root_.GD.N0230.N0659.d001275 C ∩ _root_.GD.N0230.N0659.d001281 mu

theorem d001300
    (mu : I → Measure Omega)
    (C : ∀ i, Set (Lp ℝ 2 (mu i)))
    (x : ∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :
    x ∈ _root_.GD.N0230.N0659.d001299 mu C ↔
      (∀ i, x i ∈ toWeakSpace ℝ (Lp ℝ 2 (mu i)) '' C i) ∧
      (∀ i j,
        (x i, x j) ∈
          _root_.GD.N0230.N0715.d001272
            (_root_.GD.N0230.N0691.d001209 (mu i) (mu j))
            (_root_.GD.N0230.N0691.d001210 (mu i) (mu j))) := by
  simp [_root_.GD.N0230.N0659.d001299, _root_.GD.N0230.N0659.d001276,
    _root_.GD.N0230.N0659.d001284]






theorem d001301
    (mu : I → Measure Omega)
    (C : ∀ i, Set (Lp ℝ 2 (mu i)))
    (hCcompact : ∀ i,
      IsCompact (toWeakSpace ℝ (Lp ℝ 2 (mu i)) '' C i)) :
    IsCompact (_root_.GD.N0230.N0659.d001299 mu C) := by
  exact (_root_.GD.N0230.N0659.d001277 C hCcompact).inter_right
    (_root_.GD.N0230.N0659.d001285 mu)






theorem d001302
    (mu : I → Measure Omega)
    (C : ∀ i, Set (Lp ℝ 2 (mu i)))
    (hCcompact : ∀ i,
      IsCompact (toWeakSpace ℝ (Lp ℝ 2 (mu i)) '' C i))
    (hfinite : ∀ u : Finset (I × I),
      (_root_.GD.N0230.N0659.d001275 C ∩
        ⋂ p ∈ u, _root_.GD.N0230.N0659.d001282 mu p.1 p.2).Nonempty) :
    (_root_.GD.N0230.N0659.d001299 mu C).Nonempty := by
  let t : I × I → Set (∀ i, WeakSpace ℝ (Lp ℝ 2 (mu i))) :=
    fun p ↦ _root_.GD.N0230.N0659.d001282 mu p.1 p.2
  have hall : (_root_.GD.N0230.N0659.d001275 C ∩ ⋂ p, t p).Nonempty :=
    (_root_.GD.N0230.N0659.d001277 C hCcompact).inter_iInter_nonempty t
      (fun p ↦ _root_.GD.N0230.N0659.d001283 mu p.1 p.2)
      (by simpa [t] using hfinite)
  obtain ⟨x, hxcap, hxpair⟩ := hall
  refine ⟨x, hxcap, ?_⟩
  rw [_root_.GD.N0230.N0659.d001284]
  intro i j
  have hij : x ∈ t (i, j) := by
    exact Set.mem_iInter.mp hxpair (i, j)
  exact hij



theorem d001303
    (mu : I → Measure Omega)
    (C : ∀ i, Set (Lp ℝ 2 (mu i))) (r : I → ℝ)
    (hconv : ∀ i, Convex ℝ (C i))
    (hclosed : ∀ i, IsClosed (C i))
    (hnorm : ∀ i x, x ∈ C i → ‖x‖ ≤ r i) :
    IsCompact (_root_.GD.N0230.N0659.d001299 mu C) := by
  apply _root_.GD.N0230.N0659.d001301 mu C
  intro i
  exact _root_.GD.N0230.N0633.d001201
    (r i) (hconv i) (hclosed i) (hnorm i)



theorem d001304
    (mu : I → Measure Omega)
    (anchor : ∀ i, Lp ℝ 2 (mu i)) (radius : I → ℝ) :
    IsCompact (_root_.GD.N0230.N0659.d001299 mu
      (fun i ↦ Metric.closedBall (anchor i) (radius i))) := by
  apply _root_.GD.N0230.N0659.d001301 mu
  intro i
  exact _root_.GD.N0230.N0633.d001201
    (‖anchor i‖ + radius i)
    (convex_closedBall (anchor i) (radius i))
    Metric.isClosed_closedBall
    (fun x hx ↦ _root_.GD.N0230.N0659.d001279 hx)

end

end N0659
end N0230
end GD

#print axioms _root_.GD.N0230.N0659.d001277
#print axioms _root_.GD.N0230.N0659.d001285
#print axioms _root_.GD.N0230.N0659.d001287
#print axioms _root_.GD.N0230.N0659.d001288
#print axioms _root_.GD.N0230.N0659.d001289
#print axioms _root_.GD.N0230.N0659.d001292
#print axioms _root_.GD.N0230.N0659.d001295
#print axioms _root_.GD.N0230.N0659.d001296
#print axioms _root_.GD.N0230.N0659.d001297
#print axioms _root_.GD.N0230.N0659.d001298
#print axioms _root_.GD.N0230.N0659.d001301
#print axioms _root_.GD.N0230.N0659.d001302
#print axioms _root_.GD.N0230.N0659.d001303
#print axioms _root_.GD.N0230.N0659.d001304
