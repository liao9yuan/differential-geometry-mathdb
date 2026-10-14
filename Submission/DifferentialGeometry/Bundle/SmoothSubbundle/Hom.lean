import Submission.DifferentialGeometry.Bundle.SmoothSubbundle.VectorBundle
import Submission.DifferentialGeometry.Bundle.Hom.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Set
open scoped _root_.Manifold _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
variable [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
variable [VectorBundle 𝕜 F V] {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
variable [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
variable [∀ x, TopologicalSpace (W x)] [FiberBundle G W]
variable [VectorBundle 𝕜 G W] [ContMDiffVectorBundle n G W I]

namespace ContMDiffVectorSubbundle

theorem contMDiffWithinAt_hom_section_iff
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (A : ∀ x, W x →L[𝕜] S.fiber x) (U : Set M) (x₀ : M) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, G →L[𝕜] (Fin S.rank → 𝕜))) n
      (fun x => TotalSpace.mk' (G →L[𝕜] (Fin S.rank → 𝕜)) x (A x)) U x₀ ↔
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, G →L[𝕜] F)) n
      (fun x => TotalSpace.mk' (G →L[𝕜] F) x ((S.fiber x).subtypeL.comp (A x))) U x₀ := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  constructor
  · intro hA
    have hinc := ContMDiff.clm_bundle_of_map
      (φ := fun x => (S.fiber x).subtypeL) S.contMDiff_subtypeVal
    exact (hinc x₀).contMDiffWithinAt.clm_bundle_comp hA
  · intro hA
    obtain ⟨O, s, hO, hx₀O, hs⟩ := S.exists_frame x₀
    let e := _root_.FiberBundle.trivializationAt G W x₀
    let q := _root_.FiberBundle.trivializationAt F V x₀
    let f := S.frameTrivialization hs hO
    have hx₀e : x₀ ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt G W x₀
    have hx₀q : x₀ ∈ q.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V x₀
    have hx₀f : x₀ ∈ f.baseSet := hx₀O
    obtain ⟨O', B, hO', hx₀O', hO'O, hB, hBA⟩ :=
      hs.exists_contMDiffOn_coeff_extension hO hx₀O
    let Q := fun x => ((e.continuousLinearMap (RingHom.id 𝕜) q)
      (TotalSpace.mk' (G →L[𝕜] F) x ((S.fiber x).subtypeL.comp (A x)))).2
    have hQ : ContMDiffWithinAt I 𝓘(𝕜, G →L[𝕜] F) n Q U x₀ :=
      ((e.continuousLinearMap (RingHom.id 𝕜) q).contMDiffWithinAt_section U
        ⟨hx₀e, hx₀q⟩).mp hA
    apply ((e.continuousLinearMap (RingHom.id 𝕜) f).contMDiffWithinAt_section U
      ⟨hx₀e, hx₀f⟩).mpr
    have hcomp := ((hB.contMDiffAt (hO'.mem_nhds hx₀O')).contMDiffWithinAt).clm_comp hQ
    have heq (x : M) (hx : x ∈ O') :
        ((e.continuousLinearMap (RingHom.id 𝕜) f)
          (TotalSpace.mk' (G →L[𝕜] (Fin S.rank → 𝕜)) x (A x))).2 = (B x).comp (Q x) := by
      apply ContinuousLinearMap.ext
      intro v
      have h := hBA x hx (A x (e.symmL 𝕜 x v))
      simpa only [Q, Trivialization.continuousLinearMap_apply,
        ContinuousLinearMap.comp_apply,
        Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 q (hO'O hx).2,
        Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 f (hO'O hx).1,
        f, frameTrivialization_apply, Submodule.subtypeL_apply] using h.symm
    apply hcomp.congr_of_eventuallyEq _ (heq x₀ hx₀O')
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hO'.mem_nhds hx₀O')] with x hx
    exact heq x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.contMDiffWithinAt_hom_section_iff then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.contMDiffWithinAt_hom_section_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.contMDiffWithinAt_hom_section_iff ``Submission.ContMDiffVectorSubbundle.contMDiffWithinAt_hom_section_iff

theorem contMDiffAt_hom_section_iff
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (A : ∀ x, W x →L[𝕜] S.fiber x) (x₀ : M) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiffAt I (I.prod 𝓘(𝕜, G →L[𝕜] (Fin S.rank → 𝕜))) n
      (fun x => TotalSpace.mk' (G →L[𝕜] (Fin S.rank → 𝕜)) x (A x)) x₀ ↔
    ContMDiffAt I (I.prod 𝓘(𝕜, G →L[𝕜] F)) n
      (fun x => TotalSpace.mk' (G →L[𝕜] F) x ((S.fiber x).subtypeL.comp (A x))) x₀ := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  simpa only [contMDiffWithinAt_univ] using S.contMDiffWithinAt_hom_section_iff A _root_.Set.univ x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.contMDiffAt_hom_section_iff then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.contMDiffAt_hom_section_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.contMDiffAt_hom_section_iff ``Submission.ContMDiffVectorSubbundle.contMDiffAt_hom_section_iff

theorem contMDiffOn_hom_section_iff
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (A : ∀ x, W x →L[𝕜] S.fiber x) (U : Set M) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiffOn I (I.prod 𝓘(𝕜, G →L[𝕜] (Fin S.rank → 𝕜))) n
      (fun x => TotalSpace.mk' (G →L[𝕜] (Fin S.rank → 𝕜)) x (A x)) U ↔
    ContMDiffOn I (I.prod 𝓘(𝕜, G →L[𝕜] F)) n
      (fun x => TotalSpace.mk' (G →L[𝕜] F) x ((S.fiber x).subtypeL.comp (A x))) U := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  exact forall₂_congr fun x _ => S.contMDiffWithinAt_hom_section_iff A U x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.contMDiffOn_hom_section_iff then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.contMDiffOn_hom_section_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.contMDiffOn_hom_section_iff ``Submission.ContMDiffVectorSubbundle.contMDiffOn_hom_section_iff

theorem contMDiff_hom_section_iff
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n))
    (A : ∀ x, W x →L[𝕜] S.fiber x) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiff I (I.prod 𝓘(𝕜, G →L[𝕜] (Fin S.rank → 𝕜))) n
      (fun x => TotalSpace.mk' (G →L[𝕜] (Fin S.rank → 𝕜)) x (A x)) ↔
    ContMDiff I (I.prod 𝓘(𝕜, G →L[𝕜] F)) n
      (fun x => TotalSpace.mk' (G →L[𝕜] F) x ((S.fiber x).subtypeL.comp (A x))) := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  exact forall_congr' fun x => S.contMDiffAt_hom_section_iff A x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorSubbundle.contMDiff_hom_section_iff then
    throwError "Refusing to shadow existing declaration ContMDiffVectorSubbundle.contMDiff_hom_section_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorSubbundle.contMDiff_hom_section_iff ``Submission.ContMDiffVectorSubbundle.contMDiff_hom_section_iff

end ContMDiffVectorSubbundle
