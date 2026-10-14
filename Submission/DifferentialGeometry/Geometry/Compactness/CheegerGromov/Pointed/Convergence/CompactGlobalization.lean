import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Globalization
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Mathlib.Topology.Connected.Clopen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : Nat → Nat}

theorem compactLimit_eventually_source_eq_univ
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (hcompact :
      let : TopologicalSpace L.M := L.topology
      CompactSpace L.M) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → Φ.source k = Set.univ := by
  let : TopologicalSpace L.M := L.topology
  let : CompactSpace L.M := hcompact
  obtain ⟨k0, hk0⟩ := Φ.source_subset (K := Set.univ) isCompact_univ
  refine ⟨k0, ?_⟩
  intro k hk
  exact Set.eq_univ_of_univ_subset (hk0 k hk)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_source_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_source_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_source_eq_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_source_eq_univ

theorem compactLimit_eventually_globalizes
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (hcompact :
      let : TopologicalSpace L.M := L.topology
      CompactSpace L.M)
    (hconnected : ∀ k : Nat,
      let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
      ConnectedSpace (X.obj (subseq k)).M) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
      let : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
      Φ.source k = Set.univ ∧ Φ.target k = Set.univ ∧
        ∃ e : Diffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞),
          (∀ x, e x = Φ.map k x) ∧
          (∀ y, e.symm y = (Φ.partialDiffeomorph k).symm y) ∧
          e L.basepoint = (X.obj (subseq k)).basepoint ∧
          CompactSpace (X.obj (subseq k)).M := by
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_source_eq_univ Φ hcompact
  refine ⟨k0, ?_⟩
  intro k hk
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let : CompactSpace L.M := hcompact
  let : ConnectedSpace (X.obj (subseq k)).M := hconnected k
  have hsource : (Φ.partialDiffeomorph k).source = Set.univ := hk0 k hk
  have hsourceCompact : IsCompact (Φ.partialDiffeomorph k).source := by
    rw [hsource]
    exact isCompact_univ
  have htarget : (Φ.partialDiffeomorph k).target = Set.univ :=
    partialDiffeomorph_target_eq_univ_of_compact_source (Φ.partialDiffeomorph k)
      hsourceCompact ⟨L.basepoint, Φ.base_mem k⟩
  let e := globalDiffeomorphOfUniv (Φ.partialDiffeomorph k) hsource htarget
  refine ⟨hsource, htarget, e, ?_, ?_, ?_, e.toHomeomorph.compactSpace⟩
  · intro x
    rfl
  · intro y
    rfl
  · exact Φ.basepoint_map k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_globalizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_globalizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_globalizes ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_eventually_globalizes

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
