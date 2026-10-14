import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactPositiveCanonical
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalLowerBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactAncientPositive

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_positive_canonicalWitness_of_compact_ancientKappa
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (data : PositiveComponent (_root_.Set.univ : Set F.M)) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ K : CanonicalWitness F.S eps A C x t, K.domain.carrier = _root_.Set.univ ∧
        ∃ whole positive lower, K.alternative = CanonicalAlternative.positive whole positive lower := by
  let _ : ConnectedSpace F.M := hF.connected
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hpos := ancientKappa_curvatureOperatorPositive_of_compact F hF hdim
  have hsec : HasPositiveSectionalCurvature (F.S.base.metric t) :=
    fun y v w hvw => ((curvatureOperatorPositiveAt_iff_sectional
      (F.S.base.metric t) y hdim).mp (hpos t ht y)) v w (by
        simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
          Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
            (F.S.base.metric t) y v w hvw)
  obtain ⟨c, hc, hclower⟩ := exists_pos_secLower_of_compact_positive_sectional (F.S.base.metric t) hsec
  exact exists_positive_canonicalWitness_of_compact ht
    (fun y => ancientKappa_scalar_pos F hF ht y) data hc hclower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_positive_canonicalWitness_of_compact_ancientKappa then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_positive_canonicalWitness_of_compact_ancientKappa"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_positive_canonicalWitness_of_compact_ancientKappa ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_positive_canonicalWitness_of_compact_ancientKappa

theorem exists_bufferedCanonical_of_compact_ancientKappa_of_positiveComponent
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (data : PositiveComponent (_root_.Set.univ : Set F.M)) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ alpha : ℝ, 0 < alpha → ∀ H : ℝ,
      Nonempty (BufferedCanonical F.S alpha C H x t) := by
  let _ : ConnectedSpace F.M := hF.connected
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hpos := ancientKappa_curvatureOperatorPositive_of_compact F hF hdim
  have hsec : HasPositiveSectionalCurvature (F.S.base.metric t) :=
    fun y v w hvw => ((curvatureOperatorPositiveAt_iff_sectional
      (F.S.base.metric t) y hdim).mp (hpos t ht y)) v w (by
        simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
          Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
            (F.S.base.metric t) y v w hvw)
  obtain ⟨c, hc, hclower⟩ := exists_pos_secLower_of_compact_positive_sectional (F.S.base.metric t) hsec
  exact exists_bufferedCanonical_of_compact_positive ht
    (fun y => ancientKappa_scalar_pos F hF ht y) data hc hclower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_ancientKappa_of_positiveComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_ancientKappa_of_positiveComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_ancientKappa_of_positiveComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_ancientKappa_of_positiveComponent

theorem exists_bufferedCanonical_of_compact_ancientKappa_of_projectivePresentation
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (pr : ProjectivePresentation F.M) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ alpha : ℝ, 0 < alpha → ∀ H : ℝ,
      Nonempty (BufferedCanonical F.S alpha C H x t) :=
  exists_bufferedCanonical_of_compact_ancientKappa_of_positiveComponent F hF
    (positiveComponentOfDiffeomorphProjective F.M pr (Diffeomorph.refl I3 F.M ∞)) ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_ancientKappa_of_projectivePresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_ancientKappa_of_projectivePresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_ancientKappa_of_projectivePresentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_ancientKappa_of_projectivePresentation

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
