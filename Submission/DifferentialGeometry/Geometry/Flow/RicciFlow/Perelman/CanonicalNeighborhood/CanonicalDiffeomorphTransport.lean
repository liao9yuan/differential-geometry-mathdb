import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiffeomorphComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckLimitTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem StrongNeck.eventually_transport_of_diffeomorph_tendsto
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps alpha : ℝ} {x : M} (nk : StrongNeck S eps x 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha)
    (Y : P → M ≃ₘ⟮I3, I3⟯ M)
    (hY : ContMDiff (𝓘(ℝ, P).prod I3) I3 ∞ (fun p : P × M => Y p.1 p.2))
    {p₀ : P} (hY₀ : Y p₀ = _root_.Diffeomorph.refl I3 M ∞)
    (τ : ℕ → P) (hτ : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 p₀)) :
    ∀ᶠ n in _root_.Filter.atTop, ∃ nk' : StrongNeck S (2 * alpha) (Y (τ n) x) 0,
      nk'.map = partialDiffeomorphTransMixed nk.map (Y (τ n)).toPartialDiffeomorph := by
  let B : Set Cylinder := _root_.Set.univ ×ˢ _root_.Set.Icc (-alpha⁻¹) alpha⁻¹
  have hB : IsCompact B := isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc
  have hrad : alpha⁻¹ < eps⁻¹ :=
    inv_strictAnti₀ nk.eps_pos (heps.trans_le (neckModelTolerance_le alpha))
  have hBsource : B ⊆ nk.map.source := by
    intro y hy
    exact nk.domain ⟨hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  let K := nk.map '' B
  have hK : IsCompact K := hB.image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono hBsource)
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  let _ : RegularSpace M := inferInstance
  obtain ⟨U, hUopen, hKU, _hUuniv, hUcompact⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (_root_.Set.subset_univ K)
  let U' : TopologicalSpace.Opens M := ⟨U, hUopen⟩
  let nk0 := nk.mono heps.le
    ((neckModelTolerance_le alpha).trans_lt (by linarith : alpha < 1 / 11))
  have houter : ∀ y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-alpha⁻¹) alpha⁻¹, nk0.map y ∈ K := by
    intro y hy
    exact ⟨y, ⟨hy.1, hy.2.1.le, hy.2.2.le⟩, rfl⟩
  apply nk0.eventually_transport_of_comparisons hS ha hsmall U' hUcompact hK hKU houter
    (fun _ => S) (fun _ => hS) (fun n => (Y (τ n)).toPartialDiffeomorph)
  · exact Eventually.of_forall (fun _ => _root_.Set.subset_univ _)
  · intro A _hA
    exact Eventually.of_forall (fun _ => ⟨fun _ ht => ht.2, fun _ ht => ht.2⟩)
  · intro A hA order delta hdelta
    let D := RealTimeInterval.closed (-A - 1) 0 (by linarith)
    have hwin : IsSolutionOn (S.timeRestrict D) :=
      isSolutionOn_timeRestrict hS (fun _ ht => ht.2) (fun _ ht => ht.2)
    have hc := eventually_metricComparisonOn_of_diffeomorph_tendsto
      (S.timeRestrict D) hwin (a := -A - 1) (c := -A) (b := 0)
      (by linarith) (by linarith) rfl (Subset.rfl) Y hY hY₀ τ hτ
      (uniqueDiffOn_Icc (by linarith : -A < 0)) (Subset.rfl) hUcompact order hdelta
    filter_upwards [hc] with n hn
    obtain ⟨C⟩ := hn
    exact ⟨C.mono subset_closure le_rfl le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.eventually_transport_of_diffeomorph_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.eventually_transport_of_diffeomorph_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.eventually_transport_of_diffeomorph_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.eventually_transport_of_diffeomorph_tendsto

theorem LocalCap.eventually_transport_of_diffeomorph_tendsto
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps alpha : ℝ} {x : M} {U : Set M} (cap : LocalCap S eps x 0 U)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha)
    (Y : P → M ≃ₘ⟮I3, I3⟯ M)
    (hY : ContMDiff (𝓘(ℝ, P).prod I3) I3 ∞ (fun p : P × M => Y p.1 p.2))
    {p₀ : P} (hY₀ : Y p₀ = _root_.Diffeomorph.refl I3 M ∞)
    (τ : ℕ → P) (hτ : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 p₀)) :
    ∀ᶠ n in _root_.Filter.atTop, ∃ cap' : LocalCap S (2 * alpha) (Y (τ n) x) 0 (Y (τ n) '' U),
      cap'.tube = Y (τ n) '' cap.tube ∧
      cap'.core.carrier = Y (τ n) '' cap.core.carrier ∧
      cap'.tube_map = cap.tube_map.trans (Y (τ n)).toPartialDiffeomorph := by
  classical
  have hnecks : ∀ j : Fin cap.chain.count, ∀ᶠ n in _root_.Filter.atTop,
      ∃ nk : StrongNeck S (2 * alpha) (Y (τ n) (cap.chain.centers j)) 0,
        nk.map = partialDiffeomorphTransMixed (cap.chain.necks j).map
          (Y (τ n)).toPartialDiffeomorph := by
    intro j
    exact StrongNeck.eventually_transport_of_diffeomorph_tendsto hS
      (cap.chain.necks j) ha hsmall heps Y hY hY₀ τ hτ
  have htol : eps ≤ 2 * alpha :=
    heps.le.trans ((neckModelTolerance_le alpha).trans (by linarith))
  filter_upwards [eventually_all.mpr hnecks] with n hn
  choose necks hmap using hn
  exact ⟨LocalCap.mapOfNeckFamily (cap.mono_eps htol hsmall)
    (Y (τ n)).toPartialDiffeomorph (_root_.Set.subset_univ U) necks (fun j => hmap j), rfl, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.eventually_transport_of_diffeomorph_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.eventually_transport_of_diffeomorph_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.eventually_transport_of_diffeomorph_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.eventually_transport_of_diffeomorph_tendsto

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
