import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.Source.CompactPoints

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]

namespace NetLimitData

omit [FiniteDimensional ℝ E] in
theorem hat_source_points_of_composition
    [FiniteDimensional Real E]
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ∀ gamma : Fin (pb.A r), IsCompact (sourceK gamma))
    (hSsub :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ∀ gamma : Fin (pb.A r),
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ∩
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) ⊆ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      ∀ gamma : Fin (pb.A r), sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvergenceOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvergenceOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : _root_.Bundle.RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  let : ConnectedSpace (X.obj (L.φ n)).M := hconn
  let : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  let : T3Space (X.obj (L.φ n)).M := inferInstance
  let : _root_.Bundle.RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  exact
    NetLimitData.hat_chart_points_converge_on_source_compact (I := I) (X := X) hd P L pb r n center sourceK
      (fun gamma a b v => A gamma b (B gamma a v)) hconn hKsrc hSsub hsrcK
      (fun gamma δ hδ =>
        let ψ := NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)
        have hcont : ContinuousOn (fun x : (X.obj (L.φ n)).M => ψ x)
            (sourceK gamma) := by
          exact ψ.contMDiffOn_toFun.continuousOn.mono (hsrcK gamma)
        have hKimg : IsCompact (ψ '' sourceK gamma) :=
          (hKsrc gamma).image_of_continuousOn hcont
        mapCInf_comp_pair_dist_tail
          (E := E) (F := E) (U := U gamma) (V := V gamma)
          (K := ψ '' sourceK gamma) (hVopen gamma) (B gamma) (Binf gamma)
          (A gamma) (Ainf gamma) (hB gamma) (hA gamma) (hBcont gamma)
          (hAcont gamma) (hid gamma) hKimg (hKU gamma) (hKV gamma) δ hδ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hat_source_points_of_composition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hat_source_points_of_composition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hat_source_points_of_composition ``Submission.DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hat_source_points_of_composition

omit [FiniteDimensional ℝ E] in
theorem hatSupportPointsOfComp
    [FiniteDimensional Real E]
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (n : Nat)
    {s : Set (X.obj (L.φ n)).M} {ι : Type*}
    (mu : (X.obj (L.φ n)).M -> ι -> Real)
    (center : ι -> (X.obj (L.φ n)).M)
    (sourceK : ι -> Set (X.obj (L.φ n)).M)
    (U V : ι -> Set E)
    (B : ι -> Nat -> E -> E)
    (Binf : ι -> E -> E)
    (A : ι -> Nat -> E -> E)
    (Ainf : ι -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hKsrc :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : ι, IsCompact (sourceK gamma))
    (hSupport :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      forall gamma : ι, forall x : (X.obj (L.φ n)).M,
        x ∈ s ->
        mu x gamma ≠ 0 -> x ∈ sourceK gamma)
    (hsrcK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι, sourceK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hVopen : forall gamma : ι, IsOpen (V gamma))
    (hB : forall gamma : ι,
      MapCInfConvergenceOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : ι,
      MapCInfConvergenceOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : ι, ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : ι, ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : ι, forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι,
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma ⊆ U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : ι, forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) '' sourceK gamma -> Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : _root_.Bundle.RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : ι, forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ s ->
          mu x gamma ≠ 0 ->
            dist x ((NormalCoordinates.normalChartAt (I := I)
              (X.obj (L.φ n)).metric (center gamma)).symm
                (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                  (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  let : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  let : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  let : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  let : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  let : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  let : ConnectedSpace (X.obj (L.φ n)).M := hconn
  let : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  let : T3Space (X.obj (L.φ n)).M := inferInstance
  let : _root_.Bundle.RiemannianBundle
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
    ⟨(X.obj (L.φ n)).metric.inner,
      (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  intro gamma eps heps
  let S : Set (X.obj (L.φ n)).M :=
    {x | x ∈ s ∧ mu x gamma ≠ 0}
  have hSsub : S ⊆ sourceK gamma := by
    intro x hx
    exact hSupport gamma x hx.1 hx.2
  let psi := NormalCoordinates.normalChartAt (I := I)
    (X.obj (L.φ n)).metric (center gamma)
  have hcont : ContinuousOn (fun x : (X.obj (L.φ n)).M => psi x)
      (sourceK gamma) :=
    psi.contMDiffOn_toFun.continuousOn.mono (hsrcK gamma)
  have hKimg : IsCompact (psi '' sourceK gamma) :=
    (hKsrc gamma).image_of_continuousOn hcont
  have hclose : forall delta : Real, delta > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N -> forall v : E,
        v ∈ psi '' sourceK gamma -> _root_.Dist.dist (A gamma b (B gamma a v)) v < delta := by
    intro delta hdelta
    exact mapCInf_comp_pair_dist_tail
      (E := E) (F := E) (U := U gamma) (V := V gamma)
      (K := psi '' sourceK gamma) (hVopen gamma) (B gamma) (Binf gamma)
      (A gamma) (Ainf gamma) (hB gamma) (hA gamma) (hBcont gamma)
      (hAcont gamma) (hid gamma) hKimg (hKU gamma) (hKV gamma) delta hdelta
  obtain ⟨N, hN⟩ :=
    chart_points_converge_on_source_compact (I := I) (g := (X.obj (L.φ n)).metric)
      (p := center gamma) (S := S) (Ksrc := sourceK gamma)
      (hKsrc gamma) hSsub (hsrcK gamma)
      (fun a b v => A gamma b (B gamma a v)) (by simpa [psi] using hclose)
      eps heps
  refine ⟨N, fun a ha b hb x hx hmu => ?_⟩
  exact hN a ha b hb x ⟨hx, hmu⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatSupportPointsOfComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatSupportPointsOfComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatSupportPointsOfComp ``Submission.DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatSupportPointsOfComp

omit [Module.Finite ℝ E] in
theorem hat_source_cage_composition_points
    [FiniteDimensional Real E]
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = _root_.Option.some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        4 * L.lamInf (gamma : Nat) <
          metricCoerciveExpRadius (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvergenceOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvergenceOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : _root_.Bundle.RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  let sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M :=
    fun gamma =>
      NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma
  exact
    NetLimitData.hat_source_points_of_composition (I := I) (X := X) hd P L pb r n center sourceK
      U V B Binf A Ainf hconn
      (NetLimitData.hatCageCompact (I := I) (X := X) hd P L pb r n)
      (NetLimitData.hatCageSub (I := I) (X := X) hd P L pb r n)
      (fun gamma =>
        NetLimitData.hat_source_cage_subset_normalChartAt_source_of_radius (I := I) (X := X) hd P L pb r n center gamma
          (hcenter gamma) (hR gamma))
      hVopen hB hA hBcont hAcont hid hKU hKV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hat_source_cage_composition_points then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hat_source_cage_composition_points"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hat_source_cage_composition_points ``Submission.DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hat_source_cage_composition_points

omit [Module.Finite ℝ E] in
theorem hatPointsCasesComp
    [FiniteDimensional Real E]
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall c : (X.obj (L.φ n)).M,
        seqCenter hd D P (L.φ n) (gamma : Nat) = _root_.Option.some c ->
          c = center gamma ∧
            4 * L.lamInf (gamma : Nat) <
              metricCoerciveExpRadius (I := I) (X.obj (L.φ n)).metric c)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvergenceOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvergenceOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
          U gamma)
    (hKV :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : _root_.Bundle.RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  let sourceK : Fin (pb.A r) -> Set (X.obj (L.φ n)).M := fun gamma =>
    NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma
  exact
    NetLimitData.hat_source_points_of_composition (I := I) (X := X) hd P L pb r n center sourceK
      U V B Binf A Ainf hconn
      (NetLimitData.hatCageCompact (I := I) (X := X) hd P L pb r n)
      (NetLimitData.hatCageSub (I := I) (X := X) hd P L pb r n)
      (NetLimitData.hat_source_cage_subset_normalChartAt_source (I := I) (X := X) hd P L pb r n center hR)
      hVopen hB hA hBcont hAcont hid hKU hKV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatPointsCasesComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatPointsCasesComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatPointsCasesComp ``Submission.DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatPointsCasesComp

omit [FiniteDimensional ℝ E] in
theorem hatChartPointsOfComp
    [FiniteDimensional Real E]
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.CheegerGromovCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (coordK : Fin (pb.A r) -> Set E)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hK :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      forall gamma : Fin (pb.A r), IsCompact (coordK gamma))
    (hKtarget :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), coordK gamma ⊆
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).target)
    (hsource :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        x ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)).source)
    (hcoord :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
        x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M) ->
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric
          (center gamma)) x ∈ coordK gamma)
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r),
      MapCInfConvergenceOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r),
      MapCInfConvergenceOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU : forall gamma : Fin (pb.A r), coordK gamma ⊆ U gamma)
    (hKV : forall gamma : Fin (pb.A r), forall v : E,
      v ∈ coordK gamma -> Binf gamma v ∈ V gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : _root_.Bundle.RiemannianBundle
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner,
        (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M :=
      HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    forall gamma : Fin (pb.A r), forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            x ∈ (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
              (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
              Set (X.obj (L.φ n)).M) ->
              dist x ((NormalCoordinates.normalChartAt (I := I)
                (X.obj (L.φ n)).metric (center gamma)).symm
                  (A gamma b (B gamma a ((NormalCoordinates.normalChartAt (I := I)
                    (X.obj (L.φ n)).metric (center gamma)) x)))) < eps := by
  exact
    NetLimitData.hatChartPoints (I := I) (X := X) hd P L pb r n center coordK
      (fun gamma a b v => A gamma b (B gamma a v)) hconn hK hKtarget hsource
      hcoord
      (fun gamma δ hδ =>
        mapCInf_comp_pair_dist_tail
          (E := E) (F := E) (U := U gamma) (V := V gamma)
          (K := coordK gamma) (hVopen gamma) (B gamma) (Binf gamma) (A gamma)
          (Ainf gamma) (hB gamma) (hA gamma) (hBcont gamma) (hAcont gamma)
          (hid gamma) (hK gamma) (hKU gamma) (hKV gamma) δ hδ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatChartPointsOfComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatChartPointsOfComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatChartPointsOfComp ``Submission.DifferentialGeometry.CheegerGromovCompactness.NetLimitData.hatChartPointsOfComp

end NetLimitData

end CheegerGromovCompactness
end DifferentialGeometry
