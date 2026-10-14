import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.Cover
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.PositiveCover
import Submission.DifferentialGeometry.Topology.Covering.DeckGroup
import Submission.DifferentialGeometry.Topology.Covering.SemilocallySimplyConnected
import Submission.DifferentialGeometry.Topology.StandardModel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry
namespace Geometry

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private instance roundSphereFinFact (n : ℕ) :
    Fact (Module.finrank ℝ
      (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.roundSphereFinFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.roundSphereFinFact target :: scope.openDecls } }

theorem exists_round_sphere_quotient_cover_of_constant_positive_sectional_curvature
    {n : ℕ} (hn : 1 < n)
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = n)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∃ cover : _root_.Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → M,
      IsLocalDiffeomorph (𝓡 n) I ∞ cover ∧
        IsQuotientCoveringMap cover (coveringDeckGroup cover) ∧
        ∀ (x : _root_.Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          (v w : TangentSpace (𝓡 n) x),
          (scaleMetric c hc g).inner (cover x)
              (mfderiv (𝓡 n) I cover x v)
              (mfderiv (𝓡 n) I cover x w) =
            (roundMetric
              (E := EuclideanSpace ℝ (Fin (n + 1)))
              (n := n)).inner x v w := by
  classical
  let : CompactSpace M := hcompact
  let : ConnectedSpace M := hconn
  let : I.Boundaryless := hbdry
  let : NeZero (Module.finrank ℝ E) :=
    ⟨by rw [hdim]; omega⟩
  let : NeZero n := ⟨by omega⟩
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) := by
    exact ContinuousLinearEquiv.ofFinrankEq (by
      rw [hdim, finrank_euclideanSpace_fin])
  let S := Topology.standardModelCopy (I := I) (M := M) e
  let : CompactSpace S.Q := S.equiv.toHomeomorph.compactSpace
  let : ConnectedSpace S.Q :=
    S.equiv.surjective.connectedSpace S.equiv.continuous
  let : Inhabited S.Q := Classical.inhabited_of_nonempty inferInstance
  let : LocallyPathConnectedSpace S.Q :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin n)) S.Q
  let : Riemannian.Topology.SemilocallySimplyConnectedSpace S.Q :=
    Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := 𝓡 n) (M := S.Q)
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  let gQ : SmoothRiemannianMetric (𝓡 n) S.Q :=
    Diffeomorph.pullbackMetricCross (I := 𝓡 n) (J := I) g S.equiv.symm
  have hsecQ :
      ∀ x : S.Q, ∀ X Y : TangentSpace (𝓡 n) x,
        metricRm04StandardAt (I := 𝓡 n) (M := S.Q) gQ x X Y Y X =
          c * (gQ.inner x X X * gQ.inner x Y Y -
            gQ.inner x X Y * gQ.inner x X Y) := by
    intro x X Y
    rw [metricRm04Standard_pullbackCross g S.equiv.symm x X Y Y X,
      hsec,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X X,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x Y Y,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X Y]
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let p : _root_.Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereBasisPt i0
  let q : _root_.Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereBasisPt i1
  have hi : i0 ≠ i1 := by
    intro hi
    have := congrArg Fin.val hi
    simp [i0, i1] at this
  have hpq : p ≠ q := by
    simpa only [p, q] using sphereBasisPt_ne hi
  have hqneg : q ≠ -p := by
    simpa only [p, q] using sphereBasisPt_ne_neg hi
  obtain ⟨d, hd⟩ := sphereCover_one
    (A := EuclideanSpace ℝ (Fin (n + 1))) (n := n) (Q := S.Q)
    hn gQ c hc hsecQ p q hpq hqneg
  let proj : _root_.Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → S.Q :=
    Riemannian.Topology.UniversalCover.proj ∘ d
  let cover : _root_.Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → M :=
    S.equiv.symm ∘ proj
  have hprojSurj : Function.Surjective
      (Riemannian.Topology.UniversalCover.proj :
        Riemannian.Topology.UniversalCover S.Q → S.Q) := by
    let : PathConnectedSpace S.Q :=
      PathConnectedSpace.of_locallyPathConnectedSpace
    intro x
    let gamma : Path (_root_.Inhabited.default : S.Q) x :=
      PathConnectedSpace.somePath _root_.Inhabited.default x
    exact ⟨⟨x, Path.Homotopic.Quotient.mk gamma⟩, rfl⟩
  have hprojCont : ContMDiff (𝓡 n) (𝓡 n) ∞ proj :=
    (Riemannian.Topology.UniversalCover.proj_contMDiff
      (I := 𝓡 n) (M := S.Q)).comp d.contMDiff
  have hprojLocal : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ proj :=
    isLocalDiffeomorph_comp
      (Riemannian.Topology.UniversalCover.proj_localDiffeo
        (I := 𝓡 n) (M := S.Q)) d.isLocalDiffeomorph
  have hcoverLocal : IsLocalDiffeomorph (𝓡 n) I ∞ cover :=
    isLocalDiffeomorph_comp S.equiv.symm.isLocalDiffeomorph hprojLocal
  have hcoverSurj : Function.Surjective cover :=
    S.equiv.symm.surjective.comp (hprojSurj.comp d.surjective)
  have hcovering : IsCoveringMap cover :=
    hcoverLocal.isLocalHomeomorph.covering_compact
  have hrank : 1 < Module.rank ℝ
      (EuclideanSpace ℝ (Fin (n + 1))) :=
    Module.one_lt_rank_of_one_lt_finrank (by
      rw [finrank_euclideanSpace_fin]
      omega)
  let : PreconnectedSpace
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere hrank 0 1)
  have htrans : ∀ {x y}, cover x = cover y →
      ∃ gamma : coveringDeckGroup cover, gamma • y = x := by
    intro x y hxy
    have hproj : proj x = proj y := by
      apply S.equiv.symm.injective
      exact hxy
    obtain ⟨a, ha⟩ :=
      (Riemannian.Topology.UniversalCover.proj_eq_iff_smul (d y) (d x)).mp
        hproj.symm
    let phi : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
        ≃ₘ⟮𝓡 n, 𝓡 n⟯ _root_.Metric.sphere
          (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
      (d.trans (Riemannian.Topology.UniversalCover.deckDiffeo
        (I := 𝓡 n) a)).trans d.symm
    have hphiCover (z : _root_.Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
        cover (phi z) = cover z := by
      change S.equiv.symm (Riemannian.Topology.UniversalCover.proj (d (phi z))) =
        S.equiv.symm (Riemannian.Topology.UniversalCover.proj (d z))
      simp only [phi, Diffeomorph.coe_trans, Function.comp_apply,
        Diffeomorph.apply_symm_apply]
      exact congrArg S.equiv.symm
        (Riemannian.Topology.UniversalCover.proj_deckAct a (d z))
    let gamma : coveringDeckGroup cover :=
      ⟨phi.toEquiv, phi.contMDiff.continuous,
        phi.symm.contMDiff.continuous, hphiCover⟩
    refine ⟨gamma, ?_⟩
    change phi y = x
    apply d.injective
    change d (d.symm (a • d y)) = d x
    rw [d.apply_symm_apply]
    exact ha
  refine ⟨cover, hcoverLocal,
    isQuotientCoveringMap_coveringDeckGroup_of_fiber_transitive
      hcovering hcoverSurj htrans, ?_⟩
  intro x v w
  have hprojDeriv (u : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 n) proj x u =
        mfderiv (𝓡 n) (𝓡 n) d x u := by
    rw [show proj = Riemannian.Topology.UniversalCover.proj ∘ d from rfl,
      mfderiv_comp_apply x
        ((Riemannian.Topology.UniversalCover.proj_contMDiff
          (I := 𝓡 n) (M := S.Q)).mdifferentiableAt (by simp))
        (d.contMDiff.mdifferentiableAt (by simp)),
      (Riemannian.Topology.UniversalCover.hasMFDerivAt_proj
        (I := 𝓡 n) (M := S.Q) (d x)).mfderiv]
    rfl
  have hcoverDeriv (u : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) I cover x u =
        mfderiv (𝓡 n) I S.equiv.symm (proj x)
          (mfderiv (𝓡 n) (𝓡 n) proj x u) := by
    rw [show cover = S.equiv.symm ∘ proj from rfl,
      mfderiv_comp_apply x
        (S.equiv.symm.contMDiff.mdifferentiableAt (by simp))
        (hprojCont.mdifferentiableAt (by simp))]
  rw [scaleMetric_inner, hcoverDeriv v, hcoverDeriv w]
  change c * g.inner (S.equiv.symm (proj x))
      (mfderiv (𝓡 n) I S.equiv.symm (proj x)
        (mfderiv (𝓡 n) (𝓡 n) proj x v))
      (mfderiv (𝓡 n) I S.equiv.symm (proj x)
        (mfderiv (𝓡 n) (𝓡 n) proj x w)) = _
  rw [← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm (proj x)]
  rw [hprojDeriv v, hprojDeriv w]
  change (Riemannian.Topology.UniversalCover.liftedMetric
      (I := 𝓡 n) (scaleMetric c hc gQ)).inner (d x)
        (mfderiv (𝓡 n) (𝓡 n) d x v)
        (mfderiv (𝓡 n) (𝓡 n) d x w) = _
  exact hd x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_round_sphere_quotient_cover_of_constant_positive_sectional_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_round_sphere_quotient_cover_of_constant_positive_sectional_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_round_sphere_quotient_cover_of_constant_positive_sectional_curvature ``Submission.DifferentialGeometry.Geometry.exists_round_sphere_quotient_cover_of_constant_positive_sectional_curvature

theorem exists_round_sphere_cover_of_constant_positive_sectional_curvature
    {n : ℕ} (hn : 1 < n)
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = n)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∃ cover : _root_.Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → M,
      IsLocalDiffeomorph (𝓡 n) I ∞ cover ∧
        Function.Surjective cover ∧
        IsCoveringMap cover ∧
        ∀ (x : _root_.Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          (v w : TangentSpace (𝓡 n) x),
          (scaleMetric c hc g).inner (cover x)
              (mfderiv (𝓡 n) I cover x v)
              (mfderiv (𝓡 n) I cover x w) =
            (roundMetric
              (E := EuclideanSpace ℝ (Fin (n + 1)))
              (n := n)).inner x v w := by
  obtain ⟨cover, hlocal, hquotient, hmetric⟩ :=
    exists_round_sphere_quotient_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) hn hcompact hconn hbdry hdim g c hc hsec
  exact ⟨cover, hlocal, hquotient.surjective,
    hquotient.isCoveringMap, hmetric⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_round_sphere_cover_of_constant_positive_sectional_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_round_sphere_cover_of_constant_positive_sectional_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_round_sphere_cover_of_constant_positive_sectional_curvature ``Submission.DifferentialGeometry.Geometry.exists_round_sphere_cover_of_constant_positive_sectional_curvature

theorem exists_round_two_sphere_quotient_cover_of_constant_positive_sectional_curvature
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∃ cover : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M,
      IsLocalDiffeomorph (𝓡 2) I ∞ cover ∧
        IsQuotientCoveringMap cover (coveringDeckGroup cover) ∧
        ∀ (x : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (v w : TangentSpace (𝓡 2) x),
          (scaleMetric c hc g).inner (cover x)
              (mfderiv (𝓡 2) I cover x v)
              (mfderiv (𝓡 2) I cover x w) =
            (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w := by
  simpa only [Nat.reduceAdd] using
    exists_round_sphere_quotient_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) (n := 2) (by omega)
      hcompact hconn hbdry hdim g c hc hsec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_round_two_sphere_quotient_cover_of_constant_positive_sectional_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_round_two_sphere_quotient_cover_of_constant_positive_sectional_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_round_two_sphere_quotient_cover_of_constant_positive_sectional_curvature ``Submission.DifferentialGeometry.Geometry.exists_round_two_sphere_quotient_cover_of_constant_positive_sectional_curvature

theorem exists_round_two_sphere_cover_of_constant_positive_sectional_curvature
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∃ cover : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M,
      IsLocalDiffeomorph (𝓡 2) I ∞ cover ∧
        Function.Surjective cover ∧
        IsCoveringMap cover ∧
        ∀ (x : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (v w : TangentSpace (𝓡 2) x),
          (scaleMetric c hc g).inner (cover x)
              (mfderiv (𝓡 2) I cover x v)
              (mfderiv (𝓡 2) I cover x w) =
            (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w := by
  simpa only [Nat.reduceAdd] using
    exists_round_sphere_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) (n := 2) (by omega)
      hcompact hconn hbdry hdim g c hc hsec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_round_two_sphere_cover_of_constant_positive_sectional_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_round_two_sphere_cover_of_constant_positive_sectional_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_round_two_sphere_cover_of_constant_positive_sectional_curvature ``Submission.DifferentialGeometry.Geometry.exists_round_two_sphere_cover_of_constant_positive_sectional_curvature

noncomputable def roundSphereQuotientOfConstantPositiveSectionalCurvature
    {n : ℕ} [NeZero n] (hn : 1 < n)
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = n)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
          (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    Σ data : RoundSphereQuotient.{0, u}
        (EuclideanSpace ℝ (Fin (n + 1))) n,
      M ≃ₘ⟮I, 𝓡 n⟯ data.Q := by
  classical
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconn
  letI : I.Boundaryless := hbdry
  letI : NeZero (Module.finrank ℝ E) :=
    ⟨by rw [hdim]; omega⟩
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) := by
    exact ContinuousLinearEquiv.ofFinrankEq (by
      rw [hdim, finrank_euclideanSpace_fin])
  let S := Topology.standardModelCopy (I := I) (M := M) e
  letI : CompactSpace S.Q := S.equiv.toHomeomorph.compactSpace
  letI : ConnectedSpace S.Q :=
    S.equiv.surjective.connectedSpace S.equiv.continuous
  letI : Inhabited S.Q :=
    Classical.inhabited_of_nonempty inferInstance
  letI : LocallyPathConnectedSpace S.Q :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin n)) S.Q
  letI : Riemannian.Topology.SemilocallySimplyConnectedSpace S.Q :=
    Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := 𝓡 n) (M := S.Q)
  letI : NeZero
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  let gQ : SmoothRiemannianMetric (𝓡 n) S.Q :=
    Diffeomorph.pullbackMetricCross
      (I := 𝓡 n) (J := I) g S.equiv.symm
  have hsecQ :
      ∀ x : S.Q, ∀ X Y : TangentSpace (𝓡 n) x,
        DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
            (I := 𝓡 n) (M := S.Q) gQ x X Y Y X =
          c * (gQ.inner x X X * gQ.inner x Y Y -
            gQ.inner x X Y * gQ.inner x X Y) := by
    intro x X Y
    rw [DifferentialGeometry.Geometry.Curvature.metricRm04Standard_pullbackCross
          g S.equiv.symm x X Y Y X,
      hsec,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X X,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x Y Y,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X Y]
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let p : _root_.Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereBasisPt i0
  let q : _root_.Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereBasisPt i1
  have hi : i0 ≠ i1 := by
    intro hi
    have := congrArg Fin.val hi
    simp [i0, i1] at this
  have hpq : p ≠ q := by
    simpa only [p, q] using sphereBasisPt_ne hi
  have hqneg : q ≠ -p := by
    simpa only [p, q] using sphereBasisPt_ne_neg hi
  have hcover := sphereCover_one
    (A := EuclideanSpace ℝ (Fin (n + 1))) (n := n) (Q := S.Q)
    hn gQ c hc hsecQ p q hpq hqneg
  let d := Classical.choose hcover
  have hd := Classical.choose_spec hcover
  let g₁ : SmoothRiemannianMetric (𝓡 n) S.Q :=
    DifferentialGeometry.scaleMetric (I := 𝓡 n) c hc gQ
  let data : RoundSphereQuotient.{0, u}
      (EuclideanSpace ℝ (Fin (n + 1))) n :=
    roundQuotientUC g₁ d (by simpa only [g₁] using hd)
  refine ⟨data, ?_⟩
  change M ≃ₘ⟮I, 𝓡 n⟯ S.Q
  exact S.equiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundSphereQuotientOfConstantPositiveSectionalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundSphereQuotientOfConstantPositiveSectionalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundSphereQuotientOfConstantPositiveSectionalCurvature ``Submission.DifferentialGeometry.Geometry.roundSphereQuotientOfConstantPositiveSectionalCurvature

noncomputable def roundThreeSphereQuotientOfConstantPositiveSectionalCurvature
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt
          (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    Σ data : RoundSphereQuotient.{0, u}
        (EuclideanSpace ℝ (Fin 4)) 3,
      M ≃ₘ⟮I, 𝓡 3⟯ data.Q := by
  simpa only [Nat.reduceAdd] using
    roundSphereQuotientOfConstantPositiveSectionalCurvature
      (I := I) (M := M) (n := 3) (by omega)
      hcompact hconn hbdry hdim g c hc hsec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.roundThreeSphereQuotientOfConstantPositiveSectionalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.roundThreeSphereQuotientOfConstantPositiveSectionalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.roundThreeSphereQuotientOfConstantPositiveSectionalCurvature ``Submission.DifferentialGeometry.Geometry.roundThreeSphereQuotientOfConstantPositiveSectionalCurvature

noncomputable def constPosQuotient
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    Σ data : RoundSphereQuotient.{0, u}
        (EuclideanSpace ℝ (Fin 4)) 3,
      M ≃ₘ⟮I, 𝓡 3⟯ data.Q := by
  exact roundThreeSphereQuotientOfConstantPositiveSectionalCurvature
    (I := I) (M := M) hcompact hconn hbdry hdim g c hc hsec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.constPosQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.constPosQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.constPosQuotient ``Submission.DifferentialGeometry.Geometry.constPosQuotient

end Geometry
end DifferentialGeometry
