import Submission.DifferentialGeometry.Bundle.Homotopy
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SoulDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_soul_homotopic_retraction
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex g S ∧
      relBoundary I S = ∅ ∧ ∃ r : C(M, M),
        _root_.Set.range r = S ∧ ContinuousMap.Homotopic r (ContinuousMap.id M) ∧
        ∀ x ∈ S, r x = x := by
  classical
  obtain ⟨S, hconv, hB, hne, hcompact, _hconnected, _hcodim, _hgeodesic, hbundle⟩ :=
    exists_soul_normal_diffeomorph g hEnorm hsec (Classical.arbitrary M)
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  obtain ⟨_hembedding, e, hezero⟩ := hbundle
  let FN := Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ
  let NB := _root_.Bundle.TotalSpace FN (normalBundleFiber g S)
  let r : C(M, M) :=
    ⟨fun x => (e.symm x).proj.1,
      continuous_subtype_val.comp
        ((FiberBundle.continuous_proj FN (normalBundleFiber g S)).comp e.symm.continuous)⟩
  have hfix (x : M) (hx : x ∈ S) : r x = x := by
    let q : S := ⟨x, hx⟩
    have hpreimage : e.symm x = (⟨q, 0⟩ : NB) := by
      calc
        e.symm x = e.symm (e (⟨q, 0⟩ : NB)) := congrArg e.symm (hezero q).symm
        _ = (⟨q, 0⟩ : NB) := e.symm_apply_apply _
    change (e.symm x).proj.1 = x
    rw [hpreimage]
  have hrange : _root_.Set.range r = S := by
    apply Subset.antisymm
    · rintro x ⟨y, rfl⟩
      exact (e.symm y).proj.2
    · intro x hx
      exact ⟨x, hfix x hx⟩
  let HN := VectorBundle.zeroSectionHomotopy (F := FN) (V := normalBundleFiber g S)
  let HM : ContinuousMap.Homotopy r (ContinuousMap.id M) :=
    { toFun := fun q => e (HN (q.1, e.symm q.2))
      continuous_toFun := e.continuous.comp
        (HN.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
      map_zero_left := by
        intro x
        change e (HN (0, e.symm x)) = (e.symm x).proj.1
        rw [HN.apply_zero]
        exact hezero (e.symm x).proj
      map_one_left := by
        intro x
        change e (HN (1, e.symm x)) = x
        rw [HN.apply_one]
        exact e.apply_symm_apply x }
  exact ⟨S, hne, hcompact, hconv, hB, r, hrange, ⟨HM⟩, hfix⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_soul_homotopic_retraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_soul_homotopic_retraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_soul_homotopic_retraction ``Submission.DifferentialGeometry.Geometry.Topology.exists_soul_homotopic_retraction

end DifferentialGeometry.Geometry.Topology
