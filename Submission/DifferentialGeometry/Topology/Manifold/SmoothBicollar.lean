/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Manifold.AmbientSectionExtension
import Submission.DifferentialGeometry.Topology.Manifold.TransverseFlow
import Submission.DifferentialGeometry.Topology.Manifold.CompactBicollar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Bundle _root_.Function _root_.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.Analysis.ODE

theorem exists_smoothTwoSidedCollar_of_coorientedAtlas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G]
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B] [T2Space B] [CompactSpace B]
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A] [T2Space A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ B] [IsManifold J ∞ A]
    {f : B → A} (C : CoorientedSmoothEmbeddingRealNormalAtlas I J ∞ f)
    (hf : _root_.Function.Injective f) (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1) :
    Nonempty (SmoothTwoSidedCollar I J f) := by
  obtain ⟨S, hsupp, _, htrans⟩ := C.exists_compactlySupported_transverseField hf
  let v : ∀ a : A, TangentSpace J a := S
  have hv : ContMDiff J J.tangent ∞ (fun a ↦ (⟨a, v a⟩ : TangentBundle J A)) := S.contMDiff
  let hc := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let Φ : B × ℝ → A := fun p ↦ curveAt v hc (f p.1) p.2
  have hΦ : ContMDiff (I.prod (modelWithCornersSelf ℝ ℝ)) J ∞ Φ :=
    (contMDiff_globalFlow_joint_of_compactSupport v hv hsupp).comp
      (contMDiff_snd.prodMk (C.toSmoothEmbeddingRealNormalAtlas.contMDiff.comp contMDiff_fst))
  apply exists_smoothTwoSidedCollar_of_localDiffeomorphAt_zero hf Φ hΦ.continuous
    (fun x ↦ curveAt_zero v hc (f x))
  intro x
  exact C.toSmoothEmbeddingRealNormalAtlas.isLocalDiffeomorphAt_flowMap
    hdim v hv hsupp x (htrans x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_coorientedAtlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_coorientedAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_coorientedAtlas ``Submission.DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_coorientedAtlas

theorem exists_smoothTwoSidedCollar_of_smoothSphereEmbedding
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ M]
    (e : SphereTwo → M)
    (he : _root_.Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ e) :
    Nonempty (SmoothTwoSidedCollar
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) e) := by
  obtain ⟨C⟩ := nonempty_coorientedSmoothSphereEmbeddingRealNormalAtlas he
  exact exists_smoothTwoSidedCollar_of_coorientedAtlas C he.isEmbedding.injective (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_smoothSphereEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_smoothSphereEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_smoothSphereEmbedding ``Submission.DifferentialGeometry.Topology.exists_smoothTwoSidedCollar_of_smoothSphereEmbedding

end DifferentialGeometry.Topology
