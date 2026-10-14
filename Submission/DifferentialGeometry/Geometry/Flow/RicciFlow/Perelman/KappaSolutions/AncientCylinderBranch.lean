import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderFixedModels
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureDichotomy
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.AntipodalCylinderOrientation
import Submission.DifferentialGeometry.Topology.Covering.TwoPointDeckHomeomorphs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderNullPlane

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => S × ℝ
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance cylinderBranchSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSphereDimension target :: scope.openDecls } }

universe u uE uH

section General

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance cylinderBranchTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchTopology
local instance cylinderBranchCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchCharted
local instance cylinderBranchSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSmooth
local instance cylinderBranchInhabited : Inhabited F.M := ⟨F.basepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchInhabited then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchInhabited"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchInhabited ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchInhabited
local instance cylinderBranchT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchT2
local instance cylinderBranchLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchLocallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchLocallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchLocallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchLocallyPathConnected
local instance cylinderBranchSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSemilocallySimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSemilocallySimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSemilocallySimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderBranchSemilocallySimplyConnected

structure ShrinkingCylinderCover where
  extinctionTime : ℝ
  extinctionTime_pos : 0 < extinctionTime
  parametrization : Cylinder ≃ₘ⟮CI, I⟯ UniversalCover F.M
  metric : ∀ t : ℝ, t ≤ 0 → ∀ (y : S) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner
        (parametrization (y, s))
        (mfderiv CI I parametrization (y, s) (v, a))
        (mfderiv CI I parametrization (y, s) (w, b)) =
      (2 * (extinctionTime - t)) * (gS).inner y v w + a * b
  surjective : Function.Surjective
    (fun p : Cylinder => UniversalCover.proj (parametrization p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover

namespace ShrinkingCylinderCover

variable {F} (C : ShrinkingCylinderCover F)

def projection : Cylinder → F.M :=
  fun p => UniversalCover.proj (C.parametrization p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection

theorem projection_local : IsLocalDiffeomorph CI I ∞ C.projection :=
  isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I) (M := F.M))
    C.parametrization.isLocalDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_local ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_local

theorem projection_covering : IsCoveringMap C.projection :=
  (UniversalCover.proj_isCoveringMap (X := F.M)).comp_homeomorph
    C.parametrization.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_covering then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_covering"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_covering ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_covering

theorem projection_metric (t : ℝ) (ht : t ≤ 0) (y : S) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a b : ℝ) :
    (F.S.family.metric t).inner (C.projection (y, s))
        (mfderiv CI I C.projection (y, s) (v, a))
        (mfderiv CI I C.projection (y, s) (w, b)) =
      (2 * (C.extinctionTime - t)) * (gS).inner y v w + a * b :=
  (cylinderCover_projection_inner (F.S.family.metric t) C.parametrization
    (y, s) (v, a) (w, b)).trans (C.metric t ht y s v w a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.projection_metric

def TrivialModel : Prop :=
  (∃ d : Cylinder ≃ₘ⟮CI, I⟯ F.M, ∀ p : Cylinder, d p = C.projection p) ∧
    ∀ d : Cylinder ≃ₜ Cylinder,
      C.projection ∘ d = C.projection ↔ d = Homeomorph.refl Cylinder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.TrivialModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.TrivialModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.TrivialModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.TrivialModel

def AntipodalProductModel : Prop :=
  (∃ d : (SphereAntipodalQuotient × ℝ) ≃ₘ⟮CI, I⟯ F.M,
      ∀ p : Cylinder, d (SphereAntipodalQuotient.productProjection p) = C.projection p) ∧
    ∀ d : Cylinder ≃ₜ Cylinder, C.projection ∘ d = C.projection ↔
      d = Homeomorph.refl Cylinder ∨ d = cylinderAntipodalProductDiffeomorph.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.AntipodalProductModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.AntipodalProductModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.AntipodalProductModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.AntipodalProductModel

def DiagonalModel : Prop :=
  (∃ d : CylinderDiagonalQuotient ≃ₘ⟮CI, I⟯ F.M,
      ∀ p : Cylinder, d (CylinderDiagonalQuotient.proj p) = C.projection p) ∧
    ∀ d : Cylinder ≃ₜ Cylinder, C.projection ∘ d = C.projection ↔
      d = Homeomorph.refl Cylinder ∨ d = cylinderDiagonalDiffeomorph.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.DiagonalModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.DiagonalModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.DiagonalModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.DiagonalModel

include C in
theorem not_positive (hdim : Module.finrank ℝ E = 3) :
    ¬ AncientPositiveCurvatureOperator F := by
  obtain ⟨x, a, b, hgram, hnull⟩ := cylinderCover_exists_null_plane
    (F.S.family.metric 0) (2 * (C.extinctionTime - 0))
    (mul_pos (by norm_num) (sub_pos.mpr C.extinctionTime_pos))
    C.parametrization (C.metric 0 le_rfl)
  intro hpos
  exact ancientPositiveCurvatureOperator_not_null_plane F hpos hdim
    0 le_rfl x a b hgram hnull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_positive

end ShrinkingCylinderCover

def AncientCylinderBranch : Prop :=
  ∃ C : ShrinkingCylinderCover F,
    C.TrivialModel ∨ C.AntipodalProductModel ∨ C.DiagonalModel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch

theorem ancientKappa_null_plane_cylinder_branch {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (t : ℝ) (ht : t ≤ 0) (x : F.M) (a b : TangentSpace I x)
    (hgram : 0 < (F.S.family.metric t).inner x a a *
      (F.S.family.metric t).inner x b b - ((F.S.family.metric t).inner x a b) ^ 2)
    (hnull : F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0) :
    AncientCylinderBranch F := by
  obtain ⟨T, hT, Psi, hmetric, _, hcover, hsurj, hcases⟩ :=
    ancientKappa_null_plane_fixed_cylinder_smooth_models F hF hdim
      t ht x a b hgram hnull
  let _ : PreconnectedSpace S := Subtype.preconnectedSpace
    (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp :
        1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
      (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let _ : Nonempty S := ⟨sphereEquator 0⟩
  let C : ShrinkingCylinderCover F := ⟨T, hT, Psi, hmetric, hsurj⟩
  refine ⟨C, ?_⟩
  rcases hcases with ⟨hmodel, hfibres⟩ | ⟨hmodel, hfibres⟩ | ⟨hmodel, hfibres⟩
  · refine Or.inl ⟨hmodel, ?_⟩
    intro d
    constructor
    · intro hd
      apply Homeomorph.ext
      intro p
      exact (hfibres p (d p)).mp (congrFun hd p).symm
    · rintro rfl
      rfl
  · refine Or.inr (Or.inl ⟨hmodel, ?_⟩)
    intro d
    exact covering_deck_iff_self_or_fibre_swap C.projection hcover
      cylinderAntipodalProductDiffeomorph.toHomeomorph hfibres d
  · refine Or.inr (Or.inr ⟨hmodel, ?_⟩)
    intro d
    exact covering_deck_iff_self_or_fibre_swap C.projection hcover
      cylinderDiagonalDiffeomorph.toHomeomorph hfibres d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_branch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_branch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_branch ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_null_plane_cylinder_branch

theorem ancientKappa_three_dimensional_split_branch {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3) :
    Xor (AncientPositiveCurvatureOperator F) (AncientCylinderBranch F) := by
  apply (xor_iff_or_and_not_and _ _).mpr
  constructor
  · rcases ancientKappa_positive_or_null_plane F hF hdim with hpos | hnull
    · exact Or.inl hpos
    · obtain ⟨t, ht, x, a, b, hgram, hzero⟩ := hnull
      exact Or.inr (ancientKappa_null_plane_cylinder_branch F hF hdim
        t ht x a b hgram hzero)
  · rintro ⟨hpos, C, _⟩
    exact C.not_positive hdim hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_three_dimensional_split_branch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_three_dimensional_split_branch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_three_dimensional_split_branch ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_three_dimensional_split_branch

end General

section Oriented

variable (F : PointedFlowData.{u, 0, 0} (I := ThreeModel) ancientTimeInterval)

local instance orientedCylinderTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderTopology
local instance orientedCylinderCharted : ChartedSpace ThreeSpace F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderCharted
local instance orientedCylinderSmooth : IsManifold ThreeModel ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderSmooth

theorem ShrinkingCylinderCover.not_antipodalProductModel
    (C : ShrinkingCylinderCover F) (o : TangentOrientationSection F.M) :
    ¬ C.AntipodalProductModel := by
  intro hmodel
  have hdeck := (hmodel.2 cylinderAntipodalProductDiffeomorph.toHomeomorph).mpr
    (Or.inr rfl)
  exact not_antipodal_product_localDiffeomorph o C.projection C.projection_local
    (fun p => congrFun hdeck p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_antipodalProductModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_antipodalProductModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_antipodalProductModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_antipodalProductModel

theorem ancientKappa_three_dimensional_split_branch_oriented {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (horientable : Nonempty (TangentOrientationSection F.M)) :
    Xor (AncientPositiveCurvatureOperator F)
      (∃ C : ShrinkingCylinderCover F, C.TrivialModel ∨ C.DiagonalModel) := by
  obtain ⟨o⟩ := horientable
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have h := (xor_iff_or_and_not_and _ _).mp
    (ancientKappa_three_dimensional_split_branch F hF hdim)
  apply (xor_iff_or_and_not_and _ _).mpr
  constructor
  · rcases h.1 with hpos | ⟨C, hmodel⟩
    · exact Or.inl hpos
    · right
      refine ⟨C, ?_⟩
      rcases hmodel with htrivial | hantipodal | hdiagonal
      · exact Or.inl htrivial
      · exact (ShrinkingCylinderCover.not_antipodalProductModel F C o hantipodal).elim
      · exact Or.inr hdiagonal
  · rintro ⟨hpos, C, _⟩
    exact C.not_positive hdim hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_three_dimensional_split_branch_oriented then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_three_dimensional_split_branch_oriented"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_three_dimensional_split_branch_oriented ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_three_dimensional_split_branch_oriented

end Oriented

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
