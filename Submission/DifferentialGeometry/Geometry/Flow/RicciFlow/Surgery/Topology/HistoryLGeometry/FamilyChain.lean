import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.IndexChain
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianUnconditional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

variable {H : ObservedHistory.{u}}

structure LFamilyChain (H : ObservedHistory.{u}) {first last fst : Fin (H.eventCount + 1)}
    (hle : first ≤ last) (hfst : first ≤ fst) (T w v : ℝ) (p : (H.stage last).Carrier)
    (Z₀ : H.historyLExpDomain hle T w p) extends
    H.LWindowChain T v (fun j : H.StageInterval fst last =>
      H.historyLCurve hle T w p Z₀ ⟨j.val, hfst.trans j.property.1, j.property.2⟩) where
  V : ℕ → Set ThreeSpace
  K : ℕ → Set ℝ
  β : (k : ℕ) → ThreeSpace × ℝ → (W k).X
  isOpen_V : ∀ k, IsOpen (V k)
  mem_V : ∀ k, Z₀.1 ∈ V k
  V_sub : ∀ k, ∀ Z ∈ V k, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T w p
  isOpen_K : ∀ k, IsOpen (K k)
  piece_K : ∀ k < n, _root_.Set.Icc (c k) (c (k + 1)) ⊆ K k
  K_W : ∀ k, K k ∩ _root_.Set.Ioi 0 ⊆ _root_.Set.Ioo (W k).a (W k).b
  smooth : ∀ k, ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ (β k) (V k ×ˢ K k)
  family : ∀ k, ∀ Z ∈ V k, IsLRegularizedGeodesicOn (W k).S T (fun r => β k (Z, r)) (K k)
  curve : ∀ k, ∀ s ∈ K k, β k (Z₀.1, s) = γ k s
  rep : ∀ k, ∀ Z (hZ : Z ∈ V k) (j : H.StageInterval (lo k) (hi k)),
    ∀ r ∈ K k ∩ _root_.Set.Ioo (H.regularizedStageStart T (W k).a j.val)
      (H.regularizedStageEnd T (W k).b j.val),
      H.historyLCurve hle T w p ⟨Z, V_sub k Z hZ⟩
        ⟨j.val, hfst.trans ((first_le k).trans j.property.1), j.property.2.trans (le_last k)⟩ r =
        (W k).f j (β k (Z, r))
  base : ∃ (x : (W 0).X) (L : ThreeSpace →L[ℝ] ThreeSpace), Function.Injective L ∧
    ∀ Z ∈ V 0, ∀ s ∈ K 0, s ∈ lRegularizedDomain (W 0).S T x (L Z) ∧
      β 0 (Z, s) = lRegularizedCurve (W 0).S T x (L Z) s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.LFamilyChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.LFamilyChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.LFamilyChain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.LFamilyChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
