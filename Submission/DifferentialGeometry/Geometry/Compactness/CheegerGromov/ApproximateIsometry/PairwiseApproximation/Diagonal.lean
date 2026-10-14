import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Diagonal
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Monotonicity
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private def hasPointedMetricApproximation
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (r ε : ℝ) (p k l : ℕ) : Prop :=
  ∃ Ψ : PartialDiffeomorph I I (X.obj k).M (X.obj l).M ∞,
    Ψ (X.obj k).basepoint = (X.obj l).basepoint ∧
    Nonempty (PartialDiffeomorphMetricApproximation
      (riemannianClosedBallOf (X.obj k).metric (X.obj k).basepoint r)
      ε p Ψ (X.obj k).metric (X.obj l).metric)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.hasPointedMetricApproximation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.hasPointedMetricApproximation target :: scope.openDecls } }

private def pairwiseApproximationAtRadius
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (r : ℝ) (phi : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
    ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
      hasPointedMetricApproximation X r ε p (phi k) (phi l)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pairwiseApproximationAtRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pairwiseApproximationAtRadius target :: scope.openDecls } }

private theorem pairwiseApproximationAtRadius_subseq
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (r : ℝ) (phi psi : ℕ → ℕ)
    (hpsi : StrictMono psi) (h : pairwiseApproximationAtRadius X r phi) :
    pairwiseApproximationAtRadius X r (phi ∘ psi) := by
  intro ε hε hε1 p
  obtain ⟨N, hN⟩ := h ε hε hε1 p
  refine ⟨N, fun k l hk hl => ?_⟩
  exact hN (psi k) (psi l) (hk.trans hpsi.le_apply) (hl.trans hpsi.le_apply)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pairwiseApproximationAtRadius_subseq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pairwiseApproximationAtRadius_subseq target :: scope.openDecls } }

private theorem pairwiseApproximationAtRadius_of_tail
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (r : ℝ) (phi : ℕ → ℕ) (m : ℕ)
    (h : pairwiseApproximationAtRadius X r (fun k => phi (k + m))) :
    pairwiseApproximationAtRadius X r phi := by
  intro ε hε hε1 p
  obtain ⟨N, hN⟩ := h ε hε hε1 p
  refine ⟨N + m, fun k l hk hl => ?_⟩
  have hmK : m ≤ k := by omega
  have hmL : m ≤ l := by omega
  have h := hN (k - m) (l - m) (by omega) (by omega)
  change hasPointedMetricApproximation X r ε p (phi (k - m + m)) (phi (l - m + m)) at h
  simpa only [Nat.sub_add_cancel hmK, Nat.sub_add_cancel hmL] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.pairwiseApproximationAtRadius_of_tail
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.pairwiseApproximationAtRadius_of_tail target :: scope.openDecls } }

theorem exists_subsequence_pairwise_partialDiffeomorph_metric_approximation_on_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (radii : ℕ → ℝ)
    (hstep : ∀ (q : ℕ) (phi : ℕ → ℕ), StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
          ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
            ∃ Ψ : PartialDiffeomorph I I (X.obj (phi (psi k))).M (X.obj (phi (psi l))).M ∞,
              Ψ (X.obj (phi (psi k))).basepoint = (X.obj (phi (psi l))).basepoint ∧
              Nonempty (PartialDiffeomorphMetricApproximation
                (riemannianClosedBallOf (X.obj (phi (psi k))).metric
                  (X.obj (phi (psi k))).basepoint (radii q))
                ε p Ψ (X.obj (phi (psi k))).metric (X.obj (phi (psi l))).metric)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ q : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
        ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
          ∃ Ψ : PartialDiffeomorph I I (X.obj (phi k)).M (X.obj (phi l)).M ∞,
            Ψ (X.obj (phi k)).basepoint = (X.obj (phi l)).basepoint ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              (riemannianClosedBallOf (X.obj (phi k)).metric (X.obj (phi k)).basepoint (radii q))
              ε p Ψ (X.obj (phi k)).metric (X.obj (phi l)).metric) := by
  exact exists_diag_subseq
    (fun q phi => pairwiseApproximationAtRadius X (radii q) phi)
    hstep
    (fun q phi psi hpsi h => pairwiseApproximationAtRadius_subseq X (radii q) phi psi hpsi h)
    (fun q phi m h => pairwiseApproximationAtRadius_of_tail X (radii q) phi m h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_subsequence_pairwise_partialDiffeomorph_metric_approximation_on_radii then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_subsequence_pairwise_partialDiffeomorph_metric_approximation_on_radii"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_subsequence_pairwise_partialDiffeomorph_metric_approximation_on_radii ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_subsequence_pairwise_partialDiffeomorph_metric_approximation_on_radii

theorem exists_subsequence_pairwise_partialDiffeomorph_metric_approximation
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hstep : ∀ (q : ℕ) (phi : ℕ → ℕ), StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
          ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
            ∃ Ψ : PartialDiffeomorph I I (X.obj (phi (psi k))).M (X.obj (phi (psi l))).M ∞,
              Ψ (X.obj (phi (psi k))).basepoint = (X.obj (phi (psi l))).basepoint ∧
              Nonempty (PartialDiffeomorphMetricApproximation
                (riemannianClosedBallOf (X.obj (phi (psi k))).metric
                  (X.obj (phi (psi k))).basepoint ((q : ℝ) + 1))
                ε p Ψ (X.obj (phi (psi k))).metric (X.obj (phi (psi l))).metric)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ r : ℝ, 0 < r → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
        ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
          ∃ Ψ : PartialDiffeomorph I I (X.obj (phi k)).M (X.obj (phi l)).M ∞,
            Ψ (X.obj (phi k)).basepoint = (X.obj (phi l)).basepoint ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              (riemannianClosedBallOf (X.obj (phi k)).metric (X.obj (phi k)).basepoint r)
              ε p Ψ (X.obj (phi k)).metric (X.obj (phi l)).metric) := by
  obtain ⟨phi, hphi, hP⟩ :=
    exists_subsequence_pairwise_partialDiffeomorph_metric_approximation_on_radii
      X (fun q => (q : ℝ) + 1) hstep
  refine ⟨phi, hphi, fun r _ ε hε hε1 p => ?_⟩
  obtain ⟨q, hq⟩ := exists_nat_gt r
  obtain ⟨N, hN⟩ := hP q ε hε hε1 p
  refine ⟨N, fun k l hk hl => ?_⟩
  obtain ⟨Ψ, hbase, ⟨happrox⟩⟩ := hN k l hk hl
  exact ⟨Ψ, hbase, ⟨happrox.mono
    (riemannianClosedBallOf_mono _ _ (by linarith : r ≤ (q : ℝ) + 1)) le_rfl hε1⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_subsequence_pairwise_partialDiffeomorph_metric_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_subsequence_pairwise_partialDiffeomorph_metric_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_subsequence_pairwise_partialDiffeomorph_metric_approximation ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_subsequence_pairwise_partialDiffeomorph_metric_approximation

end DifferentialGeometry.CheegerGromovCompactness
