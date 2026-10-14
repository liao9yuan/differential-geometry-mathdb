import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CurvatureRankModels
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.RankOneModelCover
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCurvatureRank
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverGaussian
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverRoundThreeSphere
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCylinderClassification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.euclideanThreeFinrankFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.euclideanThreeFinrankFact target :: scope.openDecls } }

private instance euclideanFourFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.euclideanFourFinrankFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.euclideanFourFinrankFact target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_solitonModelCovering_trichotomy
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) :
    (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover) ∨
    (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover) ∨
    (∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover) := by
  let x : M := Classical.choice (inferInstance : Nonempty M)
  rcases gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy g f
    (show (0 : ℝ) ≤ 1 by norm_num) h.1 h.2.1 hdim x with hzero | hone | hthree
  · exact Or.inl (exists_gaussian_solitonModelCovering_of_rank_zero h hdim hzero)
  · exact Or.inr (Or.inr (exists_roundThreeCylinder_solitonModelCovering_of_rank_one h hdim hone))
  · exact Or.inr (Or.inl (exists_roundThreeSphere_solitonModelCovering_of_rank_three h hdim hthree))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelCovering_trichotomy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelCovering_trichotomy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelCovering_trichotomy ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelCovering_trichotomy

theorem normalizedGradientRicciSoliton_solitonModelCovering_classification
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) :
    let gaussian := ∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover
    let sphere := ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  intro gaussian sphere cylinder
  have hgs : ¬ (gaussian ∧ sphere) := by
    rintro ⟨⟨_, hg⟩, ⟨_, hs⟩⟩
    exact not_solitonModelCovering_gaussian_and_roundThreeSphere hg hs
  have hgc : ¬ (gaussian ∧ cylinder) := by
    rintro ⟨⟨_, hg⟩, ⟨_, hc⟩⟩
    exact not_solitonModelCovering_gaussian_and_roundThreeCylinder hg hc
  have hsc : ¬ (sphere ∧ cylinder) := by
    rintro ⟨⟨_, hs⟩, ⟨_, hc⟩⟩
    exact not_solitonModelCovering_roundThreeSphere_and_roundThreeCylinder hs hc
  rcases normalizedGradientRicciSoliton_solitonModelCovering_trichotomy h hdim with hg | hs | hc
  · exact Or.inl ⟨hg, fun hs => hgs ⟨hg, hs⟩, fun hc => hgc ⟨hg, hc⟩⟩
  · exact Or.inr (Or.inl ⟨hs, fun hg => hgs ⟨hg, hs⟩, fun hc => hsc ⟨hs, hc⟩⟩)
  · exact Or.inr (Or.inr ⟨hc, fun hg => hgc ⟨hg, hc⟩, fun hs => hsc ⟨hs, hc⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelCovering_classification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelCovering_classification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelCovering_classification ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_solitonModelCovering_classification

theorem normalizedGradientRicciSoliton_isometry_classification
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) :
    let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = g ∧
      f = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross g e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, f x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∧
        Diffeomorph.pullbackMetricCross g e =
          (scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := Real)) ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross g
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, f (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  intro gaussian sphere cylinder
  have hgaussian : (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover) ↔ gaussian :=
    exists_solitonModelCovering_gaussian_iff
  have hsphere : (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover) ↔
      sphere := exists_solitonModelCovering_roundThreeSphere_iff h
  have hcylinder : (∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover) ↔
      cylinder := by
    constructor
    · rintro ⟨cover, hcover⟩
      exact ⟨cover, hcover, solitonModelCovering_roundThreeCylinder_target_isometry_trichotomy hcover⟩
    · rintro ⟨cover, hcover, _⟩
      exact ⟨cover, hcover⟩
  rcases normalizedGradientRicciSoliton_solitonModelCovering_classification h hdim with
    ⟨hg, hs, hc⟩ | ⟨hs, hg, hc⟩ | ⟨hc, hg, hs⟩
  · exact Or.inl ⟨hgaussian.mp hg, fun hh => hs (hsphere.mpr hh), fun hh => hc (hcylinder.mpr hh)⟩
  · exact Or.inr (Or.inl
      ⟨hsphere.mp hs, fun hh => hg (hgaussian.mpr hh), fun hh => hc (hcylinder.mpr hh)⟩)
  · exact Or.inr (Or.inr
      ⟨hcylinder.mp hc, fun hh => hg (hgaussian.mpr hh), fun hh => hs (hsphere.mpr hh)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_isometry_classification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_isometry_classification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_isometry_classification ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_isometry_classification

theorem gradientRicciSoliton_isometry_classification
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {sigma : ℝ}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hdim : Module.finrank ℝ E = 3) :
    ∃! C : ℝ,
      (∀ x : M, metricScalarAt (I := I) g x +
        Operator.normGradSqFun (I := I) g f x - sigma * f x = C) ∧
      let gnorm := scaleMetric (I := I) sigma hsigma g
      let fnorm := f + ContMDiffMap.const (I := I)
        (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)
      normalizedGradientRicciSoliton (I := I) gnorm fnorm ∧
    let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = gnorm ∧
      fnorm = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross gnorm e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, fnorm x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential gnorm fnorm cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross gnorm e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, fnorm (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∧
        Diffeomorph.pullbackMetricCross gnorm e =
          (scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := Real)) ∧
        ∀ x, fnorm (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross gnorm
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, fnorm (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  obtain ⟨C, ⟨hC, hnormalized⟩, hunique⟩ :=
    gradientRicciSoliton_existsUnique_normalized hcomplete hsol hsigma
  refine ⟨C, ⟨hC, hnormalized, ?_⟩, ?_⟩
  · exact normalizedGradientRicciSoliton_isometry_classification hnormalized hdim
  · intro D hD
    exact hunique D ⟨hD.1, hD.2.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_isometry_classification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_isometry_classification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_isometry_classification ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_isometry_classification

theorem normalizedGradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3)
    (hΩ : ∃ Ω : DifferentialForm I M 3, ∀ x, Ω x ≠ 0) :
    let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = g ∧
      f = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross g e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, f x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross g
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, f (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  intro gaussian sphere cylinder
  have hgaussian : (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover) ↔ gaussian :=
    exists_solitonModelCovering_gaussian_iff
  have hsphere : (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover) ↔
      sphere := exists_solitonModelCovering_roundThreeSphere_iff h
  have hcylinder : (∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover) ↔
      cylinder := by
    constructor
    · rintro ⟨cover, hcover⟩
      exact ⟨cover, hcover, solitonModelCovering_roundThreeCylinder_target_isometry_dichotomy_of_exists_nonvanishing_top_form
        hcover hΩ⟩
    · rintro ⟨cover, hcover, _⟩
      exact ⟨cover, hcover⟩
  rcases normalizedGradientRicciSoliton_solitonModelCovering_classification h hdim with
    ⟨hg, hs, hc⟩ | ⟨hs, hg, hc⟩ | ⟨hc, hg, hs⟩
  · exact Or.inl ⟨hgaussian.mp hg, fun hh => hs (hsphere.mpr hh), fun hh => hc (hcylinder.mpr hh)⟩
  · exact Or.inr (Or.inl
      ⟨hsphere.mp hs, fun hh => hg (hgaussian.mpr hh), fun hh => hc (hcylinder.mpr hh)⟩)
  · exact Or.inr (Or.inr
      ⟨hcylinder.mp hc, fun hh => hg (hgaussian.mpr hh), fun hh => hs (hsphere.mpr hh)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form ``Submission.DifferentialGeometry.Geometry.normalizedGradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form

theorem gradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {sigma : ℝ}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hdim : Module.finrank ℝ E = 3)
    (hΩ : ∃ Ω : DifferentialForm I M 3, ∀ x, Ω x ≠ 0) :
    ∃! C : ℝ,
      (∀ x : M, metricScalarAt (I := I) g x +
        Operator.normGradSqFun (I := I) g f x - sigma * f x = C) ∧
      let gnorm := scaleMetric (I := I) sigma hsigma g
      let fnorm := f + ContMDiffMap.const (I := I)
        (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)
      normalizedGradientRicciSoliton (I := I) gnorm fnorm ∧
    let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = gnorm ∧
      fnorm = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross gnorm e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, fnorm x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential gnorm fnorm cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross gnorm e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, fnorm (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross gnorm
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, fnorm (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  obtain ⟨C, ⟨hC, hnormalized⟩, hunique⟩ :=
    gradientRicciSoliton_existsUnique_normalized hcomplete hsol hsigma
  refine ⟨C, ⟨hC, hnormalized, ?_⟩, ?_⟩
  · exact normalizedGradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form hnormalized hdim hΩ
  · intro D hD
    exact hunique D ⟨hD.1, hD.2.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_isometry_classification_of_exists_nonvanishing_top_form

end DifferentialGeometry.Geometry
