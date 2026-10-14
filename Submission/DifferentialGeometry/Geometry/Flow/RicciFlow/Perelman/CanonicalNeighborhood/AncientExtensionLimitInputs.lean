import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem secLower_of_pointedFlowNonnegativeCurvatureOperator {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} I3 D) (t : ℝ)
    (h : PointedFlowNonnegativeCurvatureOperator (I := I3) F t) :
    SecLower (F.S.base.metric t) 0 Set.univ := by
  intro x _ V W
  have hquad := h x 1 (fun _ => (1 : ℝ)) (fun _ => V) (fun _ => W)
  have hvec : (fun i : Fin 4 => ![V, W, W, V] i) = vec4 (I := I3) V W W V := by
    funext i
    fin_cases i <;> rfl
  have hgoal : metricRm04At (I := I3) (F.S.base.metric t) x
        (fun i : Fin 4 => ![V, W, W, V] i) =
      metricRm04At (I := I3) (F.S.base.metric t) x (vec4 (I := I3) V W W V) := by
    rw [hvec]
  rw [hgoal]
  simpa only [Fin.sum_univ_one, SolutionFamily.rm04, metricRm04_apply, one_mul,
    _root_.MulZeroClass.zero_mul] using hquad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_of_pointedFlowNonnegativeCurvatureOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_of_pointedFlowNonnegativeCurvatureOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_of_pointedFlowNonnegativeCurvatureOperator ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_of_pointedFlowNonnegativeCurvatureOperator

theorem metricComplete_slice_of_ancientKappaSolution {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hsol : IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval))
    (hanc : IsAncientKappaSolution (I := I3) kappa
      (flowOfMetric ancientTimeInterval L.space g hsol)) :
    ∀ t ∈ ancientTimeInterval.carrier,
      MetricComplete ({ L.space with metric := g t } :
        PointedRiemannianManifold.{u, 0, 0} I3) := by
  intro t ht
  have hc := hanc.complete t ht
  rwa [show (flowOfMetric ancientTimeInterval L.space g hsol).atTime t =
      ({ L.space with metric := g t } : PointedRiemannianManifold.{u, 0, 0} I3)
      from rfl] at hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComplete_slice_of_ancientKappaSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComplete_slice_of_ancientKappaSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComplete_slice_of_ancientKappaSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.metricComplete_slice_of_ancientKappaSolution

theorem secLower_slice_of_ancientKappaSolution {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hsol : IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval))
    (hanc : IsAncientKappaSolution (I := I3) kappa
      (flowOfMetric ancientTimeInterval L.space g hsol)) :
    ∀ t ∈ ancientTimeInterval.carrier, SecLower (g t) 0 Set.univ :=
  fun t ht => secLower_of_pointedFlowNonnegativeCurvatureOperator _ t
    (hanc.nonnegativeCurvatureOperator t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_slice_of_ancientKappaSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_slice_of_ancientKappaSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_slice_of_ancientKappaSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.secLower_slice_of_ancientKappaSolution

theorem rmNormSq_le_of_ancientKappaSolution {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hsol : IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval))
    (hanc : IsAncientKappaSolution (I := I3) kappa
      (flowOfMetric ancientTimeInterval L.space g hsol)) :
    ∃ C : ℝ, ∀ t ∈ ancientTimeInterval.carrier, ∀ x : L.space.M,
      FlowMetricBall.rmNormSq ({ base := { metric := g } } :
        SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval) t x ≤ C := by
  obtain ⟨C, _hscalar, hrm⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded
      (I := I3) (flowOfMetric ancientTimeInterval L.space g hsol) (by simp [ThreeSpace]) hanc
  exact ⟨(Real.sqrt 3 * C) ^ 2, fun t ht x => hrm t ht x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.rmNormSq_le_of_ancientKappaSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.rmNormSq_le_of_ancientKappaSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.rmNormSq_le_of_ancientKappaSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.rmNormSq_le_of_ancientKappaSolution

theorem eventually_metricComparisonOn_of_halfLineExtension {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M} (hg : IsHalfLineExtension B g) :
    ∃ diagonal : ℕ → ℕ, StrictMono diagonal ∧
      ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b →
        Set.Icc a b ⊆ ancientTimeInterval.carrier → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps →
          ∀ᶠ i in Filter.atTop,
            Nonempty (MetricComparisonOn (fun s => g s)
              (fun s => (X.term (L.subseq (B.subseq (diagonal i)))).S.base.metric s)
              (L.maps.partialDiffeomorph (B.subseq (diagonal i)))
              K (Set.Icc a b) order eps) := by
  obtain ⟨_hg0, _hagree, diagonal, hdiag, hconv⟩ := hg
  exact ⟨diagonal, hdiag, fun K hK a b hab hsub order eps heps => by
    filter_upwards [hconv K hK a b hab hsub order eps heps] with i hi
    simpa only [subsequenceMaps, Function.comp_apply] using hi.2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricComparisonOn_of_halfLineExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricComparisonOn_of_halfLineExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricComparisonOn_of_halfLineExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricComparisonOn_of_halfLineExtension

def HalfLineAncientLimitFrontier {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) : Prop :=
  ∃ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsHalfLineExtension B g ∧
    ∃ hsol : IsSolutionOn ({ base := { metric := g } } :
        SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval),
      IsAncientKappaSolution (I := I3) kappa (flowOfMetric ancientTimeInterval L.space g hsol)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HalfLineAncientLimitFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HalfLineAncientLimitFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HalfLineAncientLimitFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HalfLineAncientLimitFrontier

theorem halfLineExtensionExists_of_halfLineAncientLimitFrontier {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J}
    (h : HalfLineAncientLimitFrontier B) : HalfLineExtensionExists B := by
  obtain ⟨g, hg, _⟩ := h
  exact ⟨g, hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineExtensionExists_of_halfLineAncientLimitFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineExtensionExists_of_halfLineAncientLimitFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineExtensionExists_of_halfLineAncientLimitFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineExtensionExists_of_halfLineAncientLimitFrontier

theorem halfLineAncientLimitFrontier_of_exists_ancient {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J}
    (h : HalfLineExtensionExists B) (hancient : HalfLineExtensionAncient B) :
    HalfLineAncientLimitFrontier B := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg, hancient g hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientLimitFrontier_of_exists_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientLimitFrontier_of_exists_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientLimitFrontier_of_exists_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientLimitFrontier_of_exists_ancient

theorem halfLineAncientLimitFrontier_of_halfLineAnalyticInputs {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J} (h : HalfLineAnalyticInputs B) :
    HalfLineAncientLimitFrontier B := by
  obtain ⟨⟨g, hg⟩, _hgeom, _hrm, hancient⟩ := h
  exact ⟨g, hg, hancient g hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientLimitFrontier_of_halfLineAnalyticInputs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientLimitFrontier_of_halfLineAnalyticInputs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientLimitFrontier_of_halfLineAnalyticInputs ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientLimitFrontier_of_halfLineAnalyticInputs

theorem ancientExtension_nonempty_of_halfLineAncientLimitFrontier {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (h : HalfLineAncientLimitFrontier B) : Nonempty (AncientExtension B) := by
  obtain ⟨g, hlim, hsol, hanc⟩ := h
  obtain ⟨hg0, hagree, diagonal, hdiag, hconv⟩ := hlim
  have hnormalized : PointedFlowScalarAtBase
      (flowOfMetric ancientTimeInterval L.space g hsol) 1 :=
    pointedFlowScalarAtBase_flowOfMetric hg0 hsol
  have hcomplete := metricComplete_slice_of_ancientKappaSolution hsol hanc
  have hsec := secLower_slice_of_ancientKappaSolution hsol hanc
  obtain ⟨C, hC⟩ := rmNormSq_le_of_ancientKappaSolution hsol hanc
  refine ⟨{ extension :=
              { solution := ({ base := { metric := g } } :
                  SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval)
                isSolution := hsol
                terminal := hg0
                subseq := B.subseq ∘ diagonal
                strictMono := B.strictMono.comp hdiag
                convergence := hconv
                complete := hcomplete
                nonnegative := hsec
                compact_time_bound := fun a b hab hsub =>
                  ⟨C, fun t ht x => hC t (hsub ht) x⟩ }
            agrees := hagree
            diagonal := diagonal
            strictMono := hdiag
            maps_agree := rfl
            ancient := hanc
            normalized := hnormalized
            global_rm := ⟨C, fun t ht x => hC t ht x⟩ }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancientExtension_nonempty_of_halfLineAncientLimitFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancientExtension_nonempty_of_halfLineAncientLimitFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancientExtension_nonempty_of_halfLineAncientLimitFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancientExtension_nonempty_of_halfLineAncientLimitFrontier

def HalfLineAncientExtensionFrontier (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
      (delta : ℝ) (hd : 0 < delta)
      (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
      HalfLineAncientLimitFrontier B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HalfLineAncientExtensionFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HalfLineAncientExtensionFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HalfLineAncientExtensionFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.HalfLineAncientExtensionFrontier

theorem halfLineAncientExtensionFrontier_of_halfLineAnalyticInputFrontier {kappa sigma : ℝ}
    {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
        HalfLineAnalyticInputs B) :
    HalfLineAncientExtensionFrontier.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hpos, hmain⟩ := h
  exact ⟨epsStar, hpos, fun eps heps hle X L delta hd B =>
    halfLineAncientLimitFrontier_of_halfLineAnalyticInputs (hmain eps heps hle X L delta hd B)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientExtensionFrontier_of_halfLineAnalyticInputFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientExtensionFrontier_of_halfLineAnalyticInputFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientExtensionFrontier_of_halfLineAnalyticInputFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.halfLineAncientExtensionFrontier_of_halfLineAnalyticInputFrontier

theorem ancient_extension_of_halfLineAncientLimitFrontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : HalfLineAncientExtensionFrontier.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
          Nonempty (AncientExtension B) := by
  obtain ⟨epsStar, hpos, hmain⟩ := h
  refine ⟨epsStar, hpos, fun eps heps hle X L delta hd B => ?_⟩
  exact ancientExtension_nonempty_of_halfLineAncientLimitFrontier B
    (hmain eps heps hle X L delta hd B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_extension_of_halfLineAncientLimitFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_extension_of_halfLineAncientLimitFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_extension_of_halfLineAncientLimitFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_extension_of_halfLineAncientLimitFrontier

theorem exists_slab_not_subset_closedInterval {delta : ℝ} (hd : 0 < delta) :
    ∃ a b : ℝ, a ≤ b ∧ Set.Icc a b ⊆ ancientTimeInterval.carrier ∧
      ¬ (Set.Icc a b ⊆ (RealTimeInterval.closed (-delta) 0 (by linarith)).carrier) := by
  refine ⟨-delta - 1, 0, by linarith, ?_, ?_⟩
  · intro s hs
    rw [ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr hs.2
  · intro hsub
    have hmem : -(delta + 1) ∈ Set.Icc (-delta) (0 : ℝ) :=
      hsub ⟨by linarith, by linarith⟩
    linarith [hmem.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_slab_not_subset_closedInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_slab_not_subset_closedInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_slab_not_subset_closedInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_slab_not_subset_closedInterval

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
