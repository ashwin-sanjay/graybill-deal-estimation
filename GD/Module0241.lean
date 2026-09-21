import GD.Module0232

set_option autoImplicit false
set_option warningAsError true











namespace GD.N0230.N0586

open Set
open scoped ENNReal

noncomputable section



theorem d003514
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (K : ℝ → Set X) (hmono : Monotone K) (v : ℝ)
    (hcompact : ∀ c, v < c → IsCompact (K c))
    (hne : ∀ c, v < c → (K c).Nonempty) :
    ∃ x, ∀ c, v < c → x ∈ K c := by
  classical
  have hbase : v < v + 1 := by linarith
  have hinter :
      (K (v + 1) ∩ ⋂ c : {c : ℝ // v < c}, K c.val).Nonempty := by
    apply (hcompact (v + 1) hbase).inter_iInter_nonempty
      (fun c : {c : ℝ // v < c} ↦ K c.val)
      (fun c ↦ (hcompact c.val c.property).isClosed)
    intro u
    let base : {c : ℝ // v < c} := ⟨v + 1, hbase⟩
    let t := insert base u
    have ht : t.Nonempty := Finset.insert_nonempty base u
    let c := t.min' ht
    obtain ⟨x, hx⟩ := hne c.val c.property
    have hcb : c.val ≤ v + 1 := by
      exact t.min'_le base (Finset.mem_insert_self base u)
    refine ⟨x, hmono hcb hx, ?_⟩
    rw [mem_iInter]
    intro a
    rw [mem_iInter]
    intro ha
    have hca : c.val ≤ a.val := by
      exact t.min'_le a (Finset.mem_insert_of_mem ha)
    exact hmono hca hx
  obtain ⟨x, _, hx⟩ := hinter
  exact ⟨x, fun c hc ↦ mem_iInter.mp hx ⟨c, hc⟩⟩



theorem d003515
    {x : ℝ≥0∞} {v : ℝ} (hv : 0 ≤ v)
    (h : ∀ c : ℝ, v < c → x ≤ ENNReal.ofReal c) :
    x ≤ ENNReal.ofReal v := by
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  have hepsilonR : (0 : ℝ) < epsilon := hepsilon
  have hb := h (v + epsilon) (by linarith)
  simpa only [ENNReal.ofReal_add hv epsilon.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using hb

end

end GD.N0230.N0586

#print axioms _root_.GD.N0230.N0586.d003514
#print axioms _root_.GD.N0230.N0586.d003515
