import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingNegativeTime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianProduct
import Submission.DifferentialGeometry.Geometry.Curvature.PositiveSectional
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance nullPlaneSplittingTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingTopology
local instance nullPlaneSplittingCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingCharted
local instance nullPlaneSplittingSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSmooth
local instance nullPlaneSplittingC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingC1
local instance nullPlaneSplittingT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingT2
local instance nullPlaneSplittingSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSigma
local instance nullPlaneSplittingInhabited : Inhabited F.M := ⟨F.basepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingInhabited then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingInhabited"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingInhabited ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingInhabited

local instance nullPlaneSplittingLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingLocallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingLocallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingLocallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingLocallyPathConnected

local instance nullPlaneSplittingSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSemilocallySimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSemilocallySimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSemilocallySimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nullPlaneSplittingSemilocallySimplyConnected

theorem exists_null_plane_of_universal_cover_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (t : ℝ)
    (hproduct : ∀ (y : G.M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c) :
    ∃ x : F.M, ∃ a b : TangentSpace I x,
      0 < (F.S.family.metric t).inner x a a * (F.S.family.metric t).inner x b b -
          ((F.S.family.metric t).inner x a b) ^ 2 ∧
        F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0 := by
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  let y : G.M := G.basepoint
  have hfin : 0 < Module.finrank ℝ (TangentSpace (𝓡 2) y) := by
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) y) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := rfl
    rw [hdim]
    simp
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hfin
  let p : G.M × ℝ := (y, 0)
  let x : F.M := UniversalCover.proj (Phi p)
  let a : TangentSpace I x := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi p (v, (0 : ℝ))
  let b : TangentSpace I x :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi p ((0 : TangentSpace (𝓡 2) y), (1 : ℝ))
  have hAA : (F.S.family.metric t).inner x a a = (G.S.family.metric t).inner y v v := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.family.metric t)
      (Phi p) a a).trans ?_
    have hh := hproduct y 0 v v 0 0
    simpa only [a, p, _root_.MulZeroClass.mul_zero, add_zero] using hh
  have hBB : (F.S.family.metric t).inner x b b = 1 := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.family.metric t)
      (Phi p) b b).trans ?_
    have hh := hproduct y 0 0 0 1 1
    simpa only [b, p, map_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul, one_mul, add_zero, zero_add] using hh
  have hAB : (F.S.family.metric t).inner x a b = 0 := by
    refine (UniversalCover.liftedMetric_inner_eq (I := I) (F.S.family.metric t)
      (Phi p) a b).trans ?_
    have hh := hproduct y 0 v 0 0 1
    simpa only [a, b, p, map_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul, add_zero] using hh
  refine ⟨x, a, b, ?_, ?_⟩
  · rw [hAA, hBB, hAB, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
    exact (G.S.family.metric t).pos y v hv
  · let gP : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) (G.M × ℝ) :=
      Diffeomorph.pullbackMetricCross
        (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi
    have hgP : ∀ (y' : G.M) (s' : ℝ) (v' w' : TangentSpace (𝓡 2) y') (a' c' : ℝ),
        gP.inner (y', s') (v', a') (w', c') =
          (G.S.family.metric t).inner y' v' w' + a' * c' := by
      intro y' s' v' w' a' c'
      exact (Diffeomorph.pullbackMetricCross_inner
        (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi
        (y', s') (v', a') (w', c')).trans (hproduct y' s' v' w' a' c')
    have hprodRm := metricRm04At_product_real_of_inner_eq (G.S.family.metric t) gP hgP y 0
      (vec4 (I := 𝓡 2) (M := G.M) (x := y) v 0 0 v) (![0, 1, 1, 0] : Fin 4 → ℝ)
    have hslots : (fun i : Fin 4 =>
        ((vec4 (I := 𝓡 2) (M := G.M) (x := y) v 0 0 v) i,
          (![0, 1, 1, 0] : Fin 4 → ℝ) i)) =
        vec4 (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (M := G.M × ℝ) (x := p)
          (v, 0) (0, 1) (0, 1) (v, 0) := by
      funext i
      fin_cases i <;> rfl
    have hzero : metricRm04StandardAt (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) gP p
        (v, 0) (0, 1) (0, 1) (v, 0) = 0 :=
      (congrArg (metricRm04At gP p) hslots.symm).trans
        (hprodRm.trans
          ((metricRm04At (G.S.family.metric t) y).map_coord_zero (1 : Fin 4) (by rfl)))
    have hpull := metricRm04Standard_pullbackCross
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi p
      (v, 0) (0, 1) (0, 1) (v, 0)
    have hlift := UniversalCover.metricRm_lifted (I := I) (F.S.family.metric t) (Phi p) a b b a
    simpa only [metricRm04StandardAt_apply, SolutionOn.family, SolutionFamily.rm04,
      metricRm04_apply] using hlift.symm.trans (hpull.symm.trans hzero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_null_plane_of_universal_cover_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_null_plane_of_universal_cover_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_null_plane_of_universal_cover_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_null_plane_of_universal_cover_product

theorem not_hasPositiveSectionalCurvature_of_universal_cover_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (t : ℝ)
    (hproduct : ∀ (y : G.M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c) :
    ¬ DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
      (F.S.family.metric t) := by
  intro hpos
  obtain ⟨x, a, b, hgram, hnull⟩ :=
    exists_null_plane_of_universal_cover_product F G Phi t hproduct
  have hpair : LinearIndependent ℝ ![a, b] :=
    Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      (I := I) (M := F.M) (F.S.family.metric t) x a b
      (by simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram)
  exact (ne_of_gt (hpos x a b hpair)) hnull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_hasPositiveSectionalCurvature_of_universal_cover_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_hasPositiveSectionalCurvature_of_universal_cover_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_hasPositiveSectionalCurvature_of_universal_cover_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_hasPositiveSectionalCurvature_of_universal_cover_product

theorem exists_null_plane_of_negativeTimeUniversalCoverSplitting
    (hsplit : NegativeTimeUniversalCoverSplitting (I := I) F)
    (t : ℝ) (ht : t < 0) :
    ∃ x : F.M, ∃ a b : TangentSpace I x,
      0 < (F.S.family.metric t).inner x a a * (F.S.family.metric t).inner x b b -
          ((F.S.family.metric t).inner x a b) ^ 2 ∧
        F.S.base.rm04 t x (vec4 (I := I) a b b a) = 0 := by
  obtain ⟨G, hconnG, hsimplyG, hcompleteG, hscalarG, hscalar0, Phi, hprod⟩ := hsplit
  exact exists_null_plane_of_universal_cover_product F G Phi t (hprod t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_null_plane_of_negativeTimeUniversalCoverSplitting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_null_plane_of_negativeTimeUniversalCoverSplitting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_null_plane_of_negativeTimeUniversalCoverSplitting ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_null_plane_of_negativeTimeUniversalCoverSplitting

theorem negativeTimeUniversalCoverSplitting_of_ancient_fixed_universal_cover_product
    (h : ∃ G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G.M := G.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
      let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
      let _ : IsManifold (𝓡 2) 1 G.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
      let _ : T2Space G.M := G.t2
      let _ : SigmaCompactSpace G.M := G.sigmaCompact
      ConnectedSpace G.M ∧ SimplyConnectedSpace G.M ∧
        (∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G.atTime t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ y : G.M, 0 < G.S.scalar t y) ∧
        ∃ Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
          ∀ (t : ℝ), t ≤ 0 → ∀ (y : G.M) (s : ℝ)
            (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
            (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
              (G.S.family.metric t).inner y v w + a * c) :
    NegativeTimeUniversalCoverSplitting (I := I) F := by
  obtain ⟨G, hconnG, hsimplyG, hcompleteG, hscalarG, Phi, hprod⟩ := h
  exact ⟨G, hconnG, hsimplyG, fun t ht => hcompleteG t ht.le, fun t ht => hscalarG t ht.le,
    fun y => hscalarG 0 le_rfl y, Phi, fun t ht => hprod t ht.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.negativeTimeUniversalCoverSplitting_of_ancient_fixed_universal_cover_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.negativeTimeUniversalCoverSplitting_of_ancient_fixed_universal_cover_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.negativeTimeUniversalCoverSplitting_of_ancient_fixed_universal_cover_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.negativeTimeUniversalCoverSplitting_of_ancient_fixed_universal_cover_product

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
