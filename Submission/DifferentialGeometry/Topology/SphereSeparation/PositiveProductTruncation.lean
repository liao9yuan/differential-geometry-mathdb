import Submission.DifferentialGeometry.Topology.SphereSeparation.PositiveProductFrontier
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set

namespace DifferentialGeometry.Topology.SphereSeparation

variable {X : Type*} [TopologicalSpace X]

theorem isPreconnected_inter_positive_product_tail [PreconnectedSpace X] [Nonempty X]
    {B : Set (X × ℝ)} (hB : IsPreconnected B) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hband : _root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) b ⊆ B) :
    IsPreconnected (B ∩ (_root_.Set.univ ×ˢ _root_.Set.Ioi a)) := by
  let c := (a + b) / 2
  have hac : a < c := by dsimp only [c]; linarith
  have hcb : c < b := by dsimp only [c]; linarith
  let f : X × ℝ → X × ℝ := fun q => (q.1,_root_.Max.max c q.2)
  have hf : Continuous f := continuous_fst.prodMk (continuous_const.max continuous_snd)
  have heq : B ∩ (_root_.Set.univ ×ˢ _root_.Set.Ioi a) = f '' B ∪ (_root_.Set.univ ×ˢ _root_.Set.Ioc a c) := by
    ext q
    constructor
    · rintro ⟨hq,hqa⟩
      by_cases hcq : c ≤ q.2
      · exact Or.inl ⟨q,hq,Prod.ext rfl (max_eq_right hcq)⟩
      · exact Or.inr ⟨mem_univ _,hqa.2,(le_of_not_ge hcq)⟩
    · rintro (⟨z,hz,rfl⟩ | hq)
      · refine ⟨?_,_root_.Set.mem_univ _,lt_of_lt_of_le hac (le_max_left _ _)⟩
        by_cases hcz : c ≤ z.2
        · simpa only [f,max_eq_right hcz,Prod.mk.eta] using hz
        · exact hband ⟨mem_univ _,by change 0 < _root_.Max.max c z.2; rw [max_eq_left (le_of_not_ge hcz)]; exact ha.trans hac,
            by change _root_.Max.max c z.2 < b; rw [max_eq_left (le_of_not_ge hcz)]; exact hcb⟩
      · exact ⟨hband ⟨mem_univ _,ha.trans hq.2.1,hq.2.2.trans_lt hcb⟩,_root_.Set.mem_univ _,hq.2.1⟩
  rw [heq]
  apply IsPreconnected.union' _ (hB.image f hf.continuousOn)
    (isPreconnected_univ.prod isPreconnected_Ioc)
  let x : X := Classical.arbitrary X
  refine ⟨(x,c),?_,_root_.Set.mem_univ _,hac,le_rfl⟩
  exact ⟨(x,c),hband ⟨mem_univ _,ha.trans hac,hcb⟩,Prod.ext rfl (max_self _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isPreconnected_inter_positive_product_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isPreconnected_inter_positive_product_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isPreconnected_inter_positive_product_tail ``Submission.DifferentialGeometry.Topology.SphereSeparation.isPreconnected_inter_positive_product_tail

theorem closure_inter_positive_product_tail
    {B : Set (X × ℝ)} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hband : _root_.Set.univ ×ˢ _root_.Set.Ioo (0 : ℝ) b ⊆ B) :
    closure (B ∩ (_root_.Set.univ ×ˢ _root_.Set.Ioi a)) = closure B ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici a) := by
  apply Subset.antisymm
  · apply closure_minimal
    · exact fun q hq => ⟨subset_closure hq.1,_root_.Set.mem_univ _,(show a < q.2 from hq.2.2).le⟩
    · exact isClosed_closure.inter (isClosed_univ.prod isClosed_Ici)
  · intro q hq
    rcases (show a ≤ q.2 from hq.2.2).eq_or_lt with hqa | hqa
    · have hline : (fun t : ℝ => (q.1,t)) '' _root_.Set.Ioo a b ⊆ B ∩ (_root_.Set.univ ×ˢ _root_.Set.Ioi a) := by
        rintro _ ⟨t,ht,rfl⟩
        exact ⟨hband ⟨mem_univ _,ha.trans ht.1,ht.2⟩,_root_.Set.mem_univ _,ht.1⟩
      have hacl : a ∈ closure (_root_.Set.Ioo a b) := by rw [closure_Ioo hab.ne]; exact ⟨le_rfl,hab.le⟩
      have hmem : (q.1,a) ∈ closure ((fun t : ℝ => (q.1,t)) '' _root_.Set.Ioo a b) :=
        image_closure_subset_closure_image (continuous_const.prodMk continuous_id) ⟨a,hacl,rfl⟩
      have hqeq : (q.1,a) = q := Prod.ext rfl hqa
      exact hqeq ▸ closure_mono hline hmem
    · have h := (isOpen_univ.prod (isOpen_Ioi (a := a))).inter_closure
        ⟨⟨mem_univ q.1,hqa⟩,hq.1⟩
      simpa only [_root_.Set.inter_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.closure_inter_positive_product_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.closure_inter_positive_product_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.closure_inter_positive_product_tail ``Submission.DifferentialGeometry.Topology.SphereSeparation.closure_inter_positive_product_tail

end DifferentialGeometry.Topology.SphereSeparation
