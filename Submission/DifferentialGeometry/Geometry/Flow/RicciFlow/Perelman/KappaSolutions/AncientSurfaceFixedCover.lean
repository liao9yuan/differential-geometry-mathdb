import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceRoundFlow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRoundCover
import Mathlib.Analysis.Normed.Module.Connected

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
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance ancientFixedCoverSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSphereDimension target :: scope.openDecls } }

theorem roundSurfaceCover_deck_eq_self_or_antipodal
    {M : Type*} [TopologicalSpace M] (pi : SphereTwo → M)
    (hcover : IsCoveringMap pi)
    (hfibres : Function.Injective pi ∨
      ∀ x y : SphereTwo, pi x = pi y ↔ y = x ∨ y = -x)
    (d : SphereTwo ≃ₜ SphereTwo) (hd : pi ∘ d = pi) :
    d = Homeomorph.refl SphereTwo ∨ ∀ x : SphereTwo, d x = -x := by
  classical
  rcases hfibres with hinjective | hantipodal
  · left
    apply Homeomorph.ext
    intro x
    exact hinjective (congrFun hd x)
  · have hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
      norm_num [finrank_euclideanSpace_fin]
    let _ : PreconnectedSpace SphereTwo := Subtype.preconnectedSpace
      (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank hdim)
        (0 : EuclideanSpace ℝ (Fin 3)) 1)
    let p : SphereTwo := Classical.choice
      (NormedSpace.sphere_nonempty_rclike ℝ
        (E := EuclideanSpace ℝ (Fin 3)) (r := (1 : ℝ)) zero_le_one)
    rcases (hantipodal p (d p)).mp (congrFun hd p).symm with hp | hp
    · left
      have heq : (d : SphereTwo → SphereTwo) = id :=
        hcover.eq_of_comp_eq d.continuous continuous_id
          (by simpa only [Function.comp_id] using hd) p hp
      apply Homeomorph.ext
      exact congrFun heq
    · right
      have hneg : pi ∘ (fun x : SphereTwo => -x) = pi := by
        funext x
        exact ((hantipodal x (-x)).mpr (Or.inr rfl)).symm
      have hnegContinuous : Continuous (fun x : SphereTwo => -x) :=
        (contMDiff_neg_sphere (n := 2) (m := ∞)).continuous
      have heq := hcover.eq_of_comp_eq d.continuous hnegContinuous
        (hd.trans hneg.symm) p hp
      exact congrFun heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSurfaceCover_deck_eq_self_or_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSurfaceCover_deck_eq_self_or_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSurfaceCover_deck_eq_self_or_antipodal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundSurfaceCover_deck_eq_self_or_antipodal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientFixedCoverTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverTopology
local instance ancientFixedCoverCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverCharted
local instance ancientFixedCoverSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSmooth
local instance ancientFixedCoverC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverC1
local instance ancientFixedCoverT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverT2
local instance ancientFixedCoverSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientFixedCoverSigma

theorem ancientKappaSurface_fixed_round_cover
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (hdim : Module.finrank ℝ E = 2) :
    let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
    let T := surfaceArea (F.S.family.metric 0) /
      totalScalarCurvature (F.S.family.metric 0)
    0 < T ∧ ∃ pi : SphereTwo → F.M,
      IsLocalDiffeomorph (𝓡 2) I ∞ pi ∧ IsCoveringMap pi ∧ Function.Surjective pi ∧
      (∀ (t : ℝ), t ≤ 0 → ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
        (F.S.family.metric t).inner (pi x)
            (mfderiv (𝓡 2) I pi x v) (mfderiv (𝓡 2) I pi x w) =
          (2 * (T - t)) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w) ∧
      ((∃ e : SphereTwo ≃ₘ⟮𝓡 2, I⟯ F.M, ∀ x : SphereTwo, e x = pi x) ∨
        ∀ x y : SphereTwo, pi x = pi y ↔ y = x ∨ y = -x) ∧
      (∀ d : SphereTwo ≃ₜ SphereTwo, pi ∘ d = pi →
        d = Homeomorph.refl SphereTwo ∨ ∀ x : SphereTwo, d x = -x) := by
  let _ : CompactSpace F.M := ancientKappaSurface_compact F hF hdim
  let _ : ConnectedSpace F.M := hF.connected
  let T := surfaceArea (F.S.family.metric 0) /
    totalScalarCurvature (F.S.family.metric 0)
  obtain ⟨hT, _, _, hscalar, hscale⟩ := ancientKappaSurface_roundScaling F hF hdim
  have hTpos : 0 < T := hT
  have hscalar0 : ∀ x : F.M,
      metricScalarAt (I := I) (F.S.family.metric 0) x = 1 / T := by
    intro x
    change F.S.scalar 0 x = 1 / T
    simpa only [sub_zero] using hscalar 0 le_rfl x
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.family.metric 0) :=
    RiemannianMetricComplete.of_compact (F.S.family.metric 0)
  obtain ⟨pi, hlocal, hcover, hsurj, hmetric, hfibres⟩ :=
    complete_surface_constant_scalar_round_cover (F.S.family.metric 0) hdim
      (1 / T) (one_div_pos.mpr hTpos) hcomplete hscalar0
  refine ⟨hTpos, pi, hlocal, hcover, hsurj, ?_, ?_,
    fun d hd => roundSurfaceCover_deck_eq_self_or_antipodal pi hcover hfibres d hd⟩
  · intro t ht x v w
    rw [hscale t ht, scaleMetric_inner, hmetric]
    have hfactor : (2 : ℝ) / (1 / T) = 2 * T := by
      simp only [one_div, div_inv_eq_mul]
    rw [hfactor]
    change ((T - t) / T) * (2 * T * _) = (2 * (T - t)) * _
    have hcoefficient : ((T - t) / T) * (2 * T) = 2 * (T - t) := by
      calc
        ((T - t) / T) * (2 * T) = 2 * (((T - t) / T) * T) := by ring
        _ = 2 * (T - t) := by rw [div_mul_cancel₀ _ hTpos.ne']
    rw [← mul_assoc, hcoefficient]
  · rcases hfibres with hinjective | hantipodal
    · exact Or.inl ⟨hlocal.diffeomorphOfBijective ⟨hinjective, hsurj⟩, fun _ => rfl⟩
    · exact Or.inr hantipodal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_fixed_round_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_fixed_round_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_fixed_round_cover ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_fixed_round_cover

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
