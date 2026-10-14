import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Subbundle
import Submission.DifferentialGeometry.Geometry.Connection.ExteriorDerivative
import Submission.DifferentialGeometry.Tensor.Exterior.Poincare

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Connection

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

theorem exists_local_gradient_potential_of_parallel_section
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {U : Set M} (hUopen : IsOpen U)
    {x : M} (hxU : x ∈ U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hparallel : ∀ y ∈ U, ∀ v : TangentSpace I y,
      (LeviCivita (I := I) g) s y v = 0) :
    ∃ (V : Set M) (f : M → ℝ),
      And (IsOpen V) (And (x ∈ V) (And (V ⊆ U)
        (And (f x = 0) (And (ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V)
          (∀ y ∈ V, ∀ v : TangentSpace I y,
            mvfderiv (I := I) f y v = g.inner y (s y) v))))) := by
  let theta := metricFlat g fun y => s y
  have htheta : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun z : M => TangentSpace I z →L[ℝ] ℝ) y (theta y)) := by
    exact ContMDiff.clm_bundle_apply (b := id) g.contMDiff s.contMDiff
  let alpha : DifferentialGeometry.DifferentialForm I M 1 :=
    DifferentialGeometry.DifferentialForm.ofCotangent theta htheta
  have halpha : ∀ y ∈ U, DifferentialGeometry.DifferentialForm.exteriorDerivative alpha y = 0 := by
    intro y hy
    apply ContinuousAlternatingMap.ext
    intro q
    have hq : q = ![q 0, q 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hq]
    rw [DifferentialGeometry.DifferentialForm.exteriorDerivative_ofCotangent_apply
      (LeviCivita (I := I) g) theta htheta y (q 0) (q 1)]
    rw [cotangentCov_metricDuality g
      (s.contMDiff.mdifferentiableAt (by simp)) (q 0) (q 1)]
    rw [cotangentCov_metricDuality g
      (s.contMDiff.mdifferentiableAt (by simp)) (q 1) (q 0)]
    rw [hparallel y hy (q 0), hparallel y hy (q 1)]
    rw [LeviCivita_torsion_eq_zero (I := I) g]
    simp [theta]
  obtain ⟨V, f, hVopen, hxV, hVU, hfx, hf, hdf⟩ :=
    DifferentialGeometry.DifferentialForm.exists_local_potential_of_exteriorDerivative_eq_zero_on
      alpha U hUopen halpha hxU
  refine ⟨V, f, hVopen, hxV, hVU, hfx, hf, ?_⟩
  intro y hy v
  rw [hdf y hy v]
  rw [DifferentialGeometry.DifferentialForm.ofCotangent_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.exists_local_gradient_potential_of_parallel_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.exists_local_gradient_potential_of_parallel_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.exists_local_gradient_potential_of_parallel_section ``Submission.DifferentialGeometry.Geometry.Connection.exists_local_gradient_potential_of_parallel_section

theorem ContMDiffVectorSubbundle.exists_local_unit_gradient_section_of_rank_eq_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsCovariantlyInvariantSubmoduleFamily (LeviCivita (I := I) g) S.fiber)
    (x : M) :
    ∃ (U : Set M) (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ),
      And (IsOpen U) (And (x ∈ U)
        (And (∀ y ∈ U, s y ∈ S.fiber y)
          (And (∀ y ∈ U, g.inner y (s y) (s y) = 1)
            (And (∀ y ∈ U, ∀ v : TangentSpace I y,
              (LeviCivita (I := I) g) s y v = 0)
              (And (f x = 0) (And (ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
                (∀ y ∈ U, ∀ v : TangentSpace I y,
                  mvfderiv (I := I) f y v = g.inner y (s y) v))))))) := by
  obtain ⟨V, s, hVopen, hxV, hs_mem, hs_unit, hs_parallel⟩ :=
    ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one_of_covariantly_invariant
      g S hSrank hS x
  obtain ⟨U, f, hUopen, hxU, hUsub, hfx, hf, hdf⟩ :=
    exists_local_gradient_potential_of_parallel_section g hVopen hxV s hs_parallel
  refine ⟨U, s, f, hUopen, hxU, ?_, ?_, ?_, hfx, hf, ?_⟩
  · intro y hy
    exact hs_mem y (hUsub hy)
  · intro y hy
    exact hs_unit y (hUsub hy)
  · intro y hy v
    exact hs_parallel y (hUsub hy) v
  · intro y hy v
    exact hdf y hy v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.exists_local_unit_gradient_section_of_rank_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.exists_local_unit_gradient_section_of_rank_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.exists_local_unit_gradient_section_of_rank_eq_one ``Submission.DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.exists_local_unit_gradient_section_of_rank_eq_one

end DifferentialGeometry.Geometry.Connection
