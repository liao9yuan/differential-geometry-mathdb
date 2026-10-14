import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Jacobian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialFamily

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter _root_.Matrix _root_.Submission.Matrix
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

universe u
variable {H : ObservedHistory.{u}}

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier} {Z₀ : H.historyLExpDomain hle T v p}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_window_historyLJacobianDensity_eq_lJacobianDensity (hv : 0 < v)
    (hZ₀ : Z₀.1 ∈ H.historyLExpOpenDomain hle T v p) {s₀ : ℝ} (hs₀ : s₀ ∈ _root_.Set.Ioo 0 v) :
    ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : first ≤ lo) (hhi : hi ≤ last)
      (W : H.LWindow lo hi T) (K : Set ℝ) (β : ThreeSpace × ℝ → W.X),
      IsOpen K ∧ s₀ ∈ K ∧ K ⊆ _root_.Set.Ioo W.a W.b ∧
      IsLRegularizedGeodesicOn W.S T (fun r => β (Z₀.1, r)) K ∧
      (∀ (j : H.StageInterval lo hi) {D' : RealTimeInterval}
        (S' : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D') {K' : Set ℝ},
        IsOpen K' →
        K' ⊆ K ∩ _root_.Set.Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        (∀ s ∈ K', S'.base.metric (T - s ^ 2) = H.stageMetric j.val (T - s ^ 2)) →
        ∀ i : Fin (Module.finrank ℝ ThreeSpace),
        IsLRegularizedJacobi S' T (fun r => H.historyLCurveMap hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r Z₀.1)
          (fun r => H.historyLJacobiField hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ i r) K') ∧
      (∀ (j : H.StageInterval lo hi) {τ : ℝ}, Real.sqrt τ ∈
        K ∩ _root_.Set.Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        H.historyLGram hle T v p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩
            (Real.sqrt τ) =
          lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace i)) τ) ∧
      (∀ (j : H.StageInterval lo hi) {τ : ℝ}, Real.sqrt τ ∈
        K ∩ _root_.Set.Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        H.historyLJacobianDensity hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ (Real.sqrt τ) =
          lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace i)) τ) ∧
      (∀ (j : H.StageInterval lo hi) {τ : ℝ}, Real.sqrt τ ∈
        K ∩ _root_.Set.Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        0 < (lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
          (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
            (chartModelBasis ThreeSpace i)) τ).det →
        HasDerivAt (fun τ' => H.historyLJacobianDensity hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ (Real.sqrt τ'))
          ((1 / 2) * _root_.Matrix.trace ((lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
              (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
                (chartModelBasis ThreeSpace i)) τ)⁻¹ *
            lGramDeriv W.S T (fun q => β (Z₀.1, Real.sqrt q))
              (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
                (chartModelBasis ThreeSpace i)) τ) *
            lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
              (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
                (chartModelBasis ThreeSpace i)) τ) τ) ∧
      ∀ (j : H.StageInterval lo hi) {s₁ : ℝ}, s₁ ∈ K → ∀ {l : Filter ℝ}, l ≤ 𝓝 s₁ →
        (∀ᶠ r in l,
          r ∈ _root_.Set.Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) →
        _root_.Filter.Tendsto (H.historyLJacobianDensity hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩) l
          (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace i)) (s₁ ^ 2))) := by
  obtain ⟨V, hV, hZ₀V, -, hVdom, lo, hi, hlo, hhi, W, K, hK, hs₀K, hKW, β, hβ, hgeo, hrep⟩ :=
    exists_contMDiffOn_window_family_historyLCurve hv hZ₀ hs₀
  exact ⟨lo, hi, hlo, hhi, W, K, β, hK, hs₀K, hKW, hgeo _ hZ₀V,
    fun j _ S' _ hK' hK'sub hS' i => isLRegularizedJacobi_historyLJacobiField (hlo := hlo)
      (hhi := hhi) (Z₀ := Z₀) hV hZ₀V hVdom hK hβ hgeo hrep j S' hK' hK'sub hS' i,
    fun j _ hτ => historyLGram_eq_lGram (hlo := hlo) (hhi := hhi) (Z₀ := Z₀) hV hZ₀V hVdom hK
      hKW hβ hrep j hτ,
    fun j _ hτ => historyLJacobianDensity_eq_lJacobianDensity (hlo := hlo) (hhi := hhi)
      (Z₀ := Z₀) hV hZ₀V hVdom hK hKW hβ hrep j hτ,
    fun j _ hτ hpos => hasDerivAt_historyLJacobianDensity (hlo := hlo) (hhi := hhi) (Z₀ := Z₀)
      hV hZ₀V hVdom hK hKW hβ hgeo hrep j hτ hpos,
    fun j _ hs₁ _ hl hpiece => tendsto_historyLJacobianDensity (hlo := hlo) (hhi := hhi)
      (Z₀ := Z₀) hV hZ₀V hVdom hK hKW hβ hgeo hrep j hs₁ hl hpiece⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_window_historyLJacobianDensity_eq_lJacobianDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_window_historyLJacobianDensity_eq_lJacobianDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_window_historyLJacobianDensity_eq_lJacobianDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_window_historyLJacobianDensity_eq_lJacobianDensity

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_seam_window_tendsto_historyLJacobianDensity (hv : 0 < v)
    (hZ₀ : Z₀.1 ∈ H.historyLExpOpenDomain hle T v p) (i : Fin H.eventCount)
    (hlo : first ≤ i.castSucc) (hhi : i.succ ≤ last)
    (hw : Real.sqrt (T - H.time i.succ) ∈ _root_.Set.Ioo 0 v) :
    ∃ (W : H.LWindow i.castSucc i.succ T) (K : Set ℝ) (β : ThreeSpace × ℝ → W.X),
      IsOpen K ∧ Real.sqrt (T - H.time i.succ) ∈ K ∧ K ⊆ _root_.Set.Ioo W.a W.b ∧
      IsLRegularizedGeodesicOn W.S T (fun r => β (Z₀.1, r)) K ∧
      (∀ (j : H.StageInterval i.castSucc i.succ) {τ : ℝ}, Real.sqrt τ ∈
        K ∩ _root_.Set.Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        H.historyLJacobianDensity hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ (Real.sqrt τ) =
          lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun k q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace k)) τ) ∧
      _root_.Filter.Tendsto (H.historyLJacobianDensity hle T v p Z₀
          ⟨i.succ, hlo.trans i.castSucc_lt_succ.le, hhi⟩)
          (𝓝[<] Real.sqrt (T - H.time i.succ))
          (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun k q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace k)) (Real.sqrt (T - H.time i.succ) ^ 2))) ∧
      _root_.Filter.Tendsto (H.historyLJacobianDensity hle T v p Z₀
          ⟨i.castSucc, hlo, i.castSucc_lt_succ.le.trans hhi⟩)
          (𝓝[>] Real.sqrt (T - H.time i.succ))
          (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun k q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace k)) (Real.sqrt (T - H.time i.succ) ^ 2))) := by
  obtain ⟨V, hV, hZ₀V, -, hVdom, W, K, hK, hwK, hKW, β, hβ, hgeo, hrep⟩ :=
    exists_contMDiffOn_seam_window_family_historyLCurve hv hZ₀ i hlo hhi hw
  exact ⟨W, K, β, hK, hwK, hKW, hgeo _ hZ₀V,
    fun j _ hτ => historyLJacobianDensity_eq_lJacobianDensity (hlo := hlo) (hhi := hhi)
      (Z₀ := Z₀) hV hZ₀V hVdom hK hKW hβ hrep j hτ,
    tendsto_historyLJacobianDensity_seam (hlo := hlo) (hhi := hhi) (Z₀ := Z₀) hV hZ₀V hVdom hK
      hKW hβ hgeo hrep hwK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_seam_window_tendsto_historyLJacobianDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_seam_window_tendsto_historyLJacobianDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_seam_window_tendsto_historyLJacobianDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_seam_window_tendsto_historyLJacobianDensity

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
