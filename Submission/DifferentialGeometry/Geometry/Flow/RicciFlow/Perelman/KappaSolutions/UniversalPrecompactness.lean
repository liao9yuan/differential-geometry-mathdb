import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimThreeDimensionalBounded
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalKappaGap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private theorem threeSpace_finrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeSpace_finrank
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeSpace_finrank target :: scope.openDecls } }

variable (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)


def universalNormalizedFlow {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I3) kappa F) {t : ℝ} (ht : t ≤ 0) (p : F.M) :
    PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval :=
  curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq t (F.S.scalar t p)
    (ancientKappa_scalar_pos F hF ht p) ht p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow


theorem universalNormalizedFlow_isAncientKappaSolution {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I3) kappa F) {t : ℝ} (ht : t ≤ 0) (p : F.M) :
    IsAncientKappaSolution (I := I3) kappa (universalNormalizedFlow F hF ht p) :=
  isAncientKappaSolution_curvatureNormalizedFlow F hF t (F.S.scalar t p)
    (ancientKappa_scalar_pos F hF ht p) ht p rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_isAncientKappaSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_isAncientKappaSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_isAncientKappaSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_isAncientKappaSolution


theorem universalNormalizedFlow_scalarAtBase {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I3) kappa F) {t : ℝ} (ht : t ≤ 0) (p : F.M) :
    PointedFlowScalarAtBase (I := I3) (universalNormalizedFlow F hF ht p) 1 :=
  curvatureNormalizedFlow_scalar_base F hF.carrier_eq hF.regular_eq t (F.S.scalar t p)
    (ancientKappa_scalar_pos F hF ht p) ht p rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_scalarAtBase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_scalarAtBase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_scalarAtBase ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_scalarAtBase


theorem universalNormalizedFlow_not_isShrinkingSphericalSpaceFormFlow {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I3) kappa F)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow (I := I3) F)
    {t : ℝ} (ht : t ≤ 0) (p : F.M) :
    ¬ IsShrinkingSphericalSpaceFormFlow (I := I3) (universalNormalizedFlow F hF ht p) := by
  intro hround
  exact hnotround (round_of_curvatureNormalizedFlow_round F threeSpace_finrank
    hF.connected t (F.S.scalar t p)
    (ancientKappa_scalar_pos F hF ht p) ht p hround)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_not_isShrinkingSphericalSpaceFormFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_not_isShrinkingSphericalSpaceFormFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_not_isShrinkingSphericalSpaceFormFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_not_isShrinkingSphericalSpaceFormFlow


theorem universalNormalizedFlow_isAncientKappaSolution_universal {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I3) kappa F)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow (I := I3) F)
    {t : ℝ} (ht : t ≤ 0) (p : F.M) :
    IsAncientKappaSolution (I := I3) universalKappaConstant
      (universalNormalizedFlow F hF ht p) := by
  rcases ancientKappaThree_universal_kappa_gap (universalNormalizedFlow F hF ht p)
    (universalNormalizedFlow_isAncientKappaSolution F hF ht p) threeSpace_finrank with
    hround | huniversal
  · exact absurd hround
      (universalNormalizedFlow_not_isShrinkingSphericalSpaceFormFlow F hF hnotround ht p)
  · exact huniversal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_isAncientKappaSolution_universal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_isAncientKappaSolution_universal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_isAncientKappaSolution_universal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedFlow_isAncientKappaSolution_universal


def universalNormalizedSeq
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    {kappa : ℕ → ℝ} (hX : ∀ i, IsAncientKappaSolution (I := I3) (kappa i) (X i))
    {t : ℕ → ℝ} (ht : ∀ i, t i ≤ 0) (p : ∀ i, (X i).M) :
    PointedFlowSeq.{u, 0, 0} (I := I3) where
  D := ancientTimeInterval
  term := fun i => universalNormalizedFlow (X i) (hX i) (ht i) (p i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedSeq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalNormalizedSeq


theorem exists_universal_precompactness
    (X : ℕ → PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    {kappa : ℕ → ℝ} (hX : ∀ i, IsAncientKappaSolution (I := I3) (kappa i) (X i))
    (hnotround : ∀ i, ¬ IsShrinkingSphericalSpaceFormFlow (I := I3) (X i))
    {t : ℕ → ℝ} (ht : ∀ i, t i ≤ 0) (p : ∀ i, (X i).M) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I3) (universalNormalizedSeq X hX ht p)
        (L.atTime (I := I3) 0) phi,
        IsAncientKappaSolution (I := I3) universalKappaConstant L ∧
        PointedFlowScalarAtBase (I := I3) L 1 ∧
        KLim (I := I3) universalKappaConstant L ∧
        (∀ s : ℝ, s ≤ 0 →
          ∃ C : MetricConvergenceData (I := I3)
            (Phi.atTime (X := universalNormalizedSeq X hX ht p) (L := L) s),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I3)
              (Phi.atTime (X := universalNormalizedSeq X hX ht p) (L := L) s) k) ∧
        (∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set L.M, IsCompact K →
          ∀ order : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in _root_.Filter.atTop,
            Nonempty (MetricComparisonOn
              (fun s => L.S.base.metric s)
              (fun s => ((universalNormalizedSeq X hX ht p).term (phi i)).S.base.metric s)
              (Phi.map i) K (_root_.Set.Icc a b) order ε)) ∧
        ((∀ i, NoncompactSpace (X i).M) → NoncompactSpace L.M) := by
  have hnorm (i : ℕ) : IsAncientKappaSolution (I := I3) universalKappaConstant
      ((universalNormalizedSeq X hX ht p).term i) :=
    universalNormalizedFlow_isAncientKappaSolution_universal (X i) (hX i)
      (hnotround i) (ht i) (p i)
  have hbase (i : ℕ) : PointedFlowScalarAtBase (I := I3)
      ((universalNormalizedSeq X hX ht p).term i) 1 :=
    universalNormalizedFlow_scalarAtBase (X i) (hX i) (ht i) (p i)
  obtain ⟨L, phi, hphi, Phi, hKL, hbaseL, hconv, hcmp, hanc⟩ :=
    exists_fixed_kappa_compactness (universalNormalizedSeq X hX ht p) rfl
      (fun i => ancientKappaThree_toKLim _ (hnorm i) threeSpace_finrank) hbase
  refine ⟨L, phi, hphi, Phi, hanc, hbaseL, hKL, hconv, hcmp, ?_⟩
  intro hnoncompact
  exact klim_pointedLimit_noncompact Phi (fun i => (hX i).connected) hnoncompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_precompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_precompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_precompactness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_precompactness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
