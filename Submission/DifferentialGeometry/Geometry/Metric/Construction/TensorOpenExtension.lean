import Submission.DifferentialGeometry.Topology.Manifold.CompactSectionExtension
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.OpenRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem exists_tensor0SField_eqOn_openSubtype (s : ℕ)
    (U : TopologicalSpace.Opens M) {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    (A : Tensor0SField (I := I) (M := U) (n := ∞) s) :
    ∃ B : Tensor0SField (I := I) (M := M) (n := ∞) s,
      ∀ x : U, (x : M) ∈ K → ∀ v : Fin s → TangentSpace I x, B (x : M) v = A x v := by
  classical
  let l (x : M) : Tensor0SSpace s I x :=
    if hx : x ∈ U then A ⟨x, hx⟩ else 0
  have hl (x : U) : l (x : M) = A x := by
    exact dif_pos x.property
  let _ := tensor0SBundleTopology (I := I) (M := M) s
  have hlocal : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ (Tensor0SModel s ℝ E))) ∞
      (fun x => (⟨x, l x⟩ : _root_.Bundle.TotalSpace (Tensor0SModel s ℝ E) (Tensor0SSpace s I))) U := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    rw [_root_.Bundle.contMDiffAt_section]
    let xu : U := ⟨x, hx⟩
    have hA := A.contMDiff.contMDiffAt (x := xu)
    rw [_root_.Bundle.contMDiffAt_section] at hA
    apply (contMDiffAt_subtype_iff (U := U) (x := xu)).mp
    apply hA.congr_of_eventuallyEq
    have hnb : {y : U | (y : M) ∈ (chartAt H x).source} ∈ 𝓝 xu :=
      ((chartAt H x).open_source.preimage continuous_subtype_val).mem_nhds
        (mem_chart_source H x)
    filter_upwards [hnb] with y hy
    rw [hl]
    exact (tensor0SModelAt_opens s xu y hy (A y)).symm
  obtain ⟨B, _, hB⟩ :=
    Topology.exists_contMDiffSection_eqOn_of_isCompact_of_local
      (I := I) (Tensor0SSpace s I) hK l (fun x hx =>
        ⟨U, U.isOpen.mem_nhds (hKU hx), l, hlocal, fun _ _ _ => rfl⟩)
  refine ⟨B, fun x hx v => ?_⟩
  rw [hB (x : M) hx, hl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_tensor0SField_eqOn_openSubtype then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_tensor0SField_eqOn_openSubtype"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_tensor0SField_eqOn_openSubtype ``Submission.DifferentialGeometry.exists_tensor0SField_eqOn_openSubtype

end DifferentialGeometry
