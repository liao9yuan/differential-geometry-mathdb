import Submission.DifferentialGeometry.Geometry.Geodesic.Maximal.Interval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space (TangentBundle I M)]

theorem maximalGeodesic_eqOn
    (g : SmoothRiemannianMetric I M)
    {p : M} {v : TangentSpace I p}
    {γ : ℝ → M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (h0J : (0 : ℝ) ∈ J)
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) :
    Set.EqOn (maximalGeodesic (I := I) g p v) γ J := by
  classical
  intro t ht
  have ht_mem : t ∈ maximalGeodesicInterval (I := I) g p v :=
    ⟨γ, J, hJ_open, hJ_conn, h0J, ht, hγ⟩
  rw [maximalGeodesic_of_mem (I := I) ht_mem]
  obtain ⟨J', hJ'_open, hJ'_conn, h0J', htJ', hγ'⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v ht_mem
  obtain ⟨f, hproj, hf0, hf_on⟩ := hγ
  obtain ⟨f', hproj', hf0', hf'_on⟩ := hγ'
  set K : Set ℝ := J ∩ J' with hK_def
  have hK_open : IsOpen K := hJ_open.inter hJ'_open
  have hK_conn : IsPreconnected K := by
    exact (hJ_conn.ordConnected.inter hJ'_conn.ordConnected).isPreconnected
  have h0K : (0 : ℝ) ∈ K := ⟨h0J, h0J'⟩
  have htK : t ∈ K := ⟨ht, htJ'⟩
  have heq := integralCurve_eqOn (I := I) g hK_open hK_conn h0K
    (hf_on.mono Set.inter_subset_left)
    (hf'_on.mono Set.inter_subset_right)
    (by rw [hf0, hf0'])
  calc
    maximalGeodesicChosenCurve (I := I) g p v ht_mem t = (f' t).proj := (hproj' t).symm
    _ = (f t).proj := congrArg (fun q => q.proj) (heq htK).symm
    _ = γ t := hproj t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_eqOn ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_eqOn

end DifferentialGeometry.Geometry.Riemannian.Geodesic
