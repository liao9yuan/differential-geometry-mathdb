import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedFiniteCappingSmooth
import Submission.DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreDomainSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Handle
open _root_.Submission.DifferentialGeometry.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (R : Set (ConnectedComponents (cutCore f)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))

local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
local notation "S" => (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj) ⁻¹' retainedCore f R
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def bufferedRetainedCoreHomeomorph : S ≃ₜ retainedCore f R :=
  (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).subtype (fun _ => Iff.rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreHomeomorph

@[instance_reducible]
def bufferedRetainedCoreChartedSpace : ChartedSpace (EuclideanHalfSpace 3) S := by
  letI : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
    retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  letI := euclideanHalfSpaceProdChartedSpace (retainedCore f R)
  exact chartedSpaceOfHomeomorph (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreChartedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreChartedSpace

include hs in
theorem bufferedRetainedCore_isManifold :
    letI := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
    IsManifold (𝓡∂ 3) ∞ S := by
  let : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
    retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  let : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (retainedCore f R) :=
    retainedCore_isManifold ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R hs
  let := euclideanHalfSpaceProdChartedSpace (retainedCore f R)
  let : IsManifold (𝓡∂ 3) ∞ (retainedCore f R) := euclideanHalfSpaceProd_isManifold (retainedCore f R)
  exact isManifoldOfHomeomorph (𝓡∂ 3) (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_isManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_isManifold

def bufferedRetainedCoreDiffeomorph :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
      retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
    letI := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
    S ≃ₘ⟮𝓡∂ 3, (𝓡 2).prod (𝓡∂ 1)⟯ retainedCore f R := by
  letI : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
    retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (retainedCore f R) :=
    retainedCore_isManifold ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R hs
  letI := euclideanHalfSpaceProdChartedSpace (retainedCore f R)
  letI : IsManifold (𝓡∂ 3) ∞ (retainedCore f R) := euclideanHalfSpaceProd_isManifold (retainedCore f R)
  letI := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
  let D : S ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ retainedCore f R :=
    { toEquiv := (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R) (𝓡∂ 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R) (𝓡∂ 3) ∞ }
  exact D.trans (euclideanHalfSpaceProdDiffeomorph (retainedCore f R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCoreDiffeomorph

include hs in
theorem bufferedRetainedCore_isSmoothEmbedding :
    letI := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (fun x : S => (x.val.val : M)) := by
  let : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
    retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  let : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (retainedCore f R) :=
    retainedCore_isManifold ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R hs
  let := euclideanHalfSpaceProdChartedSpace (retainedCore f R)
  let := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
  let : IsManifold (𝓡∂ 3) ∞ S := bufferedRetainedCore_isManifold hδ hδ1 f hf hdisj R hs
  let : IsManifold (𝓡∂ 3) ∞ (retainedCore f R) := euclideanHalfSpaceProd_isManifold (retainedCore f R)
  let D : S ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ retainedCore f R :=
    { toEquiv := (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R) (𝓡∂ 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R) (𝓡∂ 3) ∞ }
  exact isSmoothEmbedding_diffeomorph_precomp (fun p : retainedCore f R => (p.val.val : M))
    (DifferentialGeometry.Manifold.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd _
      (retainedCore_ambientInclusion_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three
        hδ f hf hdisj R hs)) D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_isSmoothEmbedding

omit [IsManifold ThreeModel ∞ M] in
theorem isCompact_bufferedRetainedCore [CompactSpace M] : IsCompact S := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  exact (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).isCompact_preimage.mpr
    (isCompact_retained_discardedCore hδ f hf hdisj R).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_bufferedRetainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_bufferedRetainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_bufferedRetainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_bufferedRetainedCore

include hs in
theorem bufferedRetainedCore_metric_eq
    (U : TopologicalSpace.Opens M)
    (hRet : _root_.Set.MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    letI : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
    letI : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    letI : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
      retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
    ∀ (g : SmoothRiemannianMetric ThreeModel U)
      (gRet : SmoothRiemannianMetric ThreeModel (finiteCapRetained hL hδ f hf hdisj R)),
      (∀ (p : retainedCore f R) (v w : TangentSpace ((𝓡 2).prod (𝓡∂ 1)) p),
        g.inner (retainedCoreDomainMap f R U hRet p)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (retainedCoreDomainMap f R U hRet) p v)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (retainedCoreDomainMap f R U hRet) p w) =
        gRet.inner (finiteRetainedCoreInclusion hL hδ f hf hdisj R p)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p v)
          (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ThreeModel (finiteRetainedCoreInclusion hL hδ f hf hdisj R) p w)) →
      letI := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
      ∀ (x : S) (v w : TangentSpace (𝓡∂ 3) x),
        g.inner (retainedCoreDomainMap f R U hRet (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R x))
          (mfderiv (𝓡∂ 3) ThreeModel
            (retainedCoreDomainMap f R U hRet ∘ bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R) x v)
          (mfderiv (𝓡∂ 3) ThreeModel
            (retainedCoreDomainMap f R U hRet ∘ bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R) x w) =
        gRet.inner (finiteRetainedCoreInclusion hL hδ f hf hdisj R (bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R x))
          (mfderiv (𝓡∂ 3) ThreeModel
            (finiteRetainedCoreInclusion hL hδ f hf hdisj R ∘ bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R) x v)
          (mfderiv (𝓡∂ 3) ThreeModel
            (finiteRetainedCoreInclusion hL hδ f hf hdisj R ∘ bufferedRetainedCoreHomeomorph hδ hδ1 f hf hdisj R) x w) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected ThreeModel finrank_threeSpace_eq_three
  let : ChartedSpace ThreeSpace Q := finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q := finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  let : ChartedSpace EuclideanHalfSpaceProdModel (retainedCore f R) :=
    retainedCoreChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj R
  intro g gRet hTensor
  let := bufferedRetainedCoreChartedSpace hδ hδ1 f hf hdisj R
  intro x v w
  let D := bufferedRetainedCoreDiffeomorph hδ hδ1 f hf hdisj R hs
  have hD : MDifferentiableAt (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) D x := D.contMDiff.mdifferentiableAt (by simp)
  have hΨ := (retainedCoreDomainMap_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three
    hδ f hf hdisj hs R U hRet).contMDiff.mdifferentiableAt (by simp) (x := D x)
  have hΦ := (finiteRetainedCoreInclusion_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three
    hL hδ f hf hdisj hs R).contMDiff.mdifferentiableAt (by simp) (x := D x)
  change g.inner _ (mfderiv (𝓡∂ 3) ThreeModel (retainedCoreDomainMap f R U hRet ∘ D) x v)
      (mfderiv (𝓡∂ 3) ThreeModel (retainedCoreDomainMap f R U hRet ∘ D) x w) =
    gRet.inner _ (mfderiv (𝓡∂ 3) ThreeModel (finiteRetainedCoreInclusion hL hδ f hf hdisj R ∘ D) x v)
      (mfderiv (𝓡∂ 3) ThreeModel (finiteRetainedCoreInclusion hL hδ f hf hdisj R ∘ D) x w)
  rw [mfderiv_comp x hΨ hD, mfderiv_comp x hΦ hD]
  exact hTensor (D x) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_metric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_metric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_metric_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bufferedRetainedCore_metric_eq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
