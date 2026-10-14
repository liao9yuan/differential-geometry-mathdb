import Submission.DifferentialGeometry.Geometry.Metric.Cylinder.Line
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.IntrinsicLineNullPlane

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance lineCylinderSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineCylinderSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineCylinderSphereDimension target :: scope.openDecls } }
private local instance lineCylinderSpherePathConnected : PathConnectedSpace SphereTwo := by
  exact isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 (by norm_num))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineCylinderSpherePathConnected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.lineCylinderSpherePathConnected target :: scope.openDecls } }

universe u uE uH

section General
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ShrinkingCylinderCover.not_diagonalModel_of_intrinsic_line
    (C : ShrinkingCylinderCover F) {t : ℝ} (ht : t ≤ 0) (γ : ℝ → F.M)
    (hline : ∀ s u : ℝ, riemannianEDistOf (F.S.family.metric t) (γ s) (γ u) =
      ENNReal.ofReal |s - u|) : ¬ C.DiagonalModel := by
  intro hdiag
  have hdeck := (hdiag.2 cylinderDiagonalDiffeomorph.toHomeomorph).mpr (Or.inr rfl)
  have hscale : 0 < 2 * (C.extinctionTime - t) := by linarith [C.extinctionTime_pos]
  apply not_intrinsic_line_of_compact_cylinder_cover_reflection
    (scaleMetric (2 * (C.extinctionTime - t)) hscale gS) (F.S.family.metric t)
    C.projection C.projection_local C.projection_covering C.surjective ?_
    (fun x : SphereTwo => -x) ?_ γ hline
  · rintro ⟨x, s⟩ v w
    change TangentSpace (𝓡 2) x × ℝ at v w
    rcases v with ⟨v, a⟩
    rcases w with ⟨w, b⟩
    exact C.projection_metric t ht x s v w a b
  · intro p
    exact congrFun hdeck p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_diagonalModel_of_intrinsic_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_diagonalModel_of_intrinsic_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_diagonalModel_of_intrinsic_line ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_diagonalModel_of_intrinsic_line

theorem ancientKappa_cylinder_branch_of_intrinsic_line {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    {t₀ : ℝ} (ht₀ : t₀ ≤ 0) (γ : ℝ → F.M)
    (hline : ∀ s t : ℝ, riemannianEDistOf (F.S.family.metric t₀) (γ s) (γ t) =
      ENNReal.ofReal |s - t|) :
    ∃ C : ShrinkingCylinderCover F, C.TrivialModel ∨ C.AntipodalProductModel := by
  have hsec (x : F.M) : metricRm04At (F.S.family.metric t₀) x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := F.M) := by
    apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff _ x).mpr
    intro v w
    have hh := hF.nonnegativeCurvatureOperator t₀ ht₀ x 1 (fun _ => 1) (fun _ => v) (fun _ => w)
    simpa only [Fin.sum_univ_one, one_mul, SolutionOn.family, SolutionFamily.rm04,
      metricRm04_apply, metricRm04StandardAt_apply, vec4] using hh
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨v, w, hplane, hnull⟩ := exists_null_plane_of_nonnegative_sectional_intrinsic_line
    (F.S.family.metric t₀)
    ⟨MetricComplete.complete (F.atTime t₀) (hF.complete t₀ ht₀)⟩
    (by omega) hsec hline F.basepoint
  obtain ⟨C, htrivial | hantipodal | hdiag⟩ :=
    ancientKappa_null_plane_cylinder_branch F hF hdim t₀ ht₀ F.basepoint v w hplane hnull
  · exact ⟨C, Or.inl htrivial⟩
  · exact ⟨C, Or.inr hantipodal⟩
  · exact (C.not_diagonalModel_of_intrinsic_line F ht₀ γ hline hdiag).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_cylinder_branch_of_intrinsic_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_cylinder_branch_of_intrinsic_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_cylinder_branch_of_intrinsic_line ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_cylinder_branch_of_intrinsic_line

end General

section Three

variable (F : PointedFlowData.{u, 0, 0} (I := ThreeModel) ancientTimeInterval)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancientKappa_cylinder_of_intrinsic_line {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (horientable : Nonempty (TangentOrientationSection F.M))
    {t₀ : ℝ} (ht₀ : t₀ ≤ 0) (γ : ℝ → F.M)
    (hline : ∀ s t : ℝ, riemannianEDistOf (F.S.family.metric t₀) (γ s) (γ t) =
      ENNReal.ofReal |s - t|) :
    ∃ T : ℝ, 0 < T ∧ ∃ d : Cylinder ≃ₘ⟮CI, ThreeModel⟯ F.M,
      ∀ t : ℝ, t ≤ 0 → ∀ (y : SphereTwo) (s : ℝ)
        (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
        (F.S.family.metric t).inner (d (y, s))
          (mfderiv CI ThreeModel d (y, s) (v, a))
          (mfderiv CI ThreeModel d (y, s) (w, b)) =
          (2 * (T - t)) * (gS).inner y v w + a * b := by
  obtain ⟨o⟩ := horientable
  obtain ⟨C, htrivial | hantipodal⟩ :=
    ancientKappa_cylinder_branch_of_intrinsic_line F hF (by simp [ThreeSpace]) ht₀ γ hline
  · obtain ⟨d, hd⟩ := htrivial.1
    refine ⟨C.extinctionTime, C.extinctionTime_pos, d, ?_⟩
    have heq : (d : Cylinder → F.M) = C.projection := funext hd
    rw [heq]
    exact C.projection_metric
  · exact (C.not_antipodalProductModel F o hantipodal).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_cylinder_of_intrinsic_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_cylinder_of_intrinsic_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_cylinder_of_intrinsic_line ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_cylinder_of_intrinsic_line

end Three
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end
