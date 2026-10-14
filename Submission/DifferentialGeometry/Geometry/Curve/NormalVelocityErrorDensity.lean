import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Submission.DifferentialGeometry.Geometry.Metric.Family.OpenSubtypeCoefficients
import Submission.DifferentialGeometry.Topology.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.Topology _root_.Submission.Topology
namespace DifferentialGeometry.Geometry.Curve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalVelocityErrorDensity
    (q : (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E) : ℝ :=
  let G := q.1
  let X := q.2.1
  let A := q.2.2.1
  let V := q.2.2.2
  let σ := G X X
  let H := σ⁻¹ • A - (σ⁻¹ ^ 2 * G A X) • X
  let W := V - H
  let N := W - (σ⁻¹ * G W X) • X
  Real.sqrt (G N N) * Real.sqrt (G X X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity ``Submission.DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity

theorem normalVelocityErrorDensity_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E →L[ℝ] E →L[ℝ] ℝ) (G' : F →L[ℝ] F →L[ℝ] ℝ) (L : E →ₗ[ℝ] F)
    (hG : ∀ X Y, G' (L X) (L Y) = G X Y) (X A V : E) :
    normalVelocityErrorDensity (G', L X, L A, L V) =
      normalVelocityErrorDensity (G, X, A, V) := by
  simp only [normalVelocityErrorDensity, hG, ← L.map_smul, ← L.map_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_comp ``Submission.DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_comp


theorem normalVelocityErrorDensity_continuousAt
    (q : (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E)
    (hσ : q.1 q.2.1 q.2.1 ≠ 0) :
    ContinuousAt normalVelocityErrorDensity q := by
  unfold normalVelocityErrorDensity
  dsimp only
  have hG : ContinuousAt (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E => p.1) q :=
    continuousAt_fst
  have hX : ContinuousAt (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E => p.2.1) q :=
    continuousAt_fst.comp continuousAt_snd
  have hA : ContinuousAt (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E => p.2.2.1) q :=
    continuousAt_fst.comp (continuousAt_snd.comp continuousAt_snd)
  have hV : ContinuousAt (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E => p.2.2.2) q :=
    continuousAt_snd.comp (continuousAt_snd.comp continuousAt_snd)
  have hσ' : ContinuousAt
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E => p.1 p.2.1 p.2.1) q :=
    (hG.clm_apply hX).clm_apply hX
  have hi : ContinuousAt
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E => (p.1 p.2.1 p.2.1)⁻¹) q :=
    hσ'.inv₀ hσ
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_continuousAt ``Submission.DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_continuousAt

theorem normalVelocityErrorDensity_continuousOn :
    ContinuousOn (normalVelocityErrorDensity (E := E))
      {q | q.1 q.2.1 q.2.1 ≠ 0} :=
  fun q hq => (normalVelocityErrorDensity_continuousAt q hq).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_continuousOn ``Submission.DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_continuousOn

theorem normalVelocityErrorDensity_tendstoUniformlyOn
    {α ι : Type*} {l : Filter ι} {s : Set α}
    {F : ι → α → (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E}
    {f : α → (E →L[ℝ] E →L[ℝ] ℝ) × E × E × E}
    {K : Set ((E →L[ℝ] E →L[ℝ] ℝ) × E × E × E)}
    (hK : IsCompact K) (hσ : ∀ q ∈ K, q.1 q.2.1 q.2.1 ≠ 0)
    (hF : ∀ᶠ i in l, _root_.Set.MapsTo (F i) s K) (hf : _root_.Set.MapsTo f s K)
    (hconv : TendstoUniformlyOn F f l s) :
    TendstoUniformlyOn (fun i x => normalVelocityErrorDensity (F i x))
      (fun x => normalVelocityErrorDensity (f x)) l s := by
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hF hf
    (hK.uniformContinuousOn_of_continuous
      (normalVelocityErrorDensity_continuousOn.mono hσ)) hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_tendstoUniformlyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_tendstoUniformlyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_tendstoUniformlyOn ``Submission.DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_tendstoUniformlyOn

end DifferentialGeometry.Geometry.Curve

end

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Geometry.Curve

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {U : TopologicalSpace.Opens F}

def covariantCurveJet (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U)
    (q : ℝ × U × F × F × F) : (F →L[ℝ] F →L[ℝ] ℝ) × F × F × F :=
  ((G q.1).inner q.2.1, q.2.2.1,
    q.2.2.2.1 + chartChristoffelContraction (G q.1) q.2.1 q.2.2.1 q.2.2.1 (q.2.1 : F),
    q.2.2.2.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.covariantCurveJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.covariantCurveJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.covariantCurveJet ``Submission.DifferentialGeometry.Geometry.Curve.covariantCurveJet

theorem covariantCurveJet_continuousAt
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U}
    (hG : MetricFamilySmoothOn D G) {q : ℝ × U × F × F × F}
    (hq : q.1 ∈ D.regular) : ContinuousAt (covariantCurveJet G) q := by
  have hz : ContinuousAt (fun p : ℝ × U × F × F × F => (p.1, p.2.1)) q :=
    continuousAt_fst.prodMk (continuousAt_fst.comp continuousAt_snd)
  have hX : ContinuousAt (fun p : ℝ × U × F × F × F => p.2.2.1) q :=
    continuousAt_fst.comp (continuousAt_snd.comp continuousAt_snd)
  have hxx : ContinuousAt (fun p : ℝ × U × F × F × F => p.2.2.2.1) q :=
    continuousAt_fst.comp (continuousAt_snd.comp (continuousAt_snd.comp continuousAt_snd))
  have hV : ContinuousAt (fun p : ℝ × U × F × F × F => p.2.2.2.2) q :=
    continuousAt_snd.comp (continuousAt_snd.comp (continuousAt_snd.comp continuousAt_snd))
  have hmetric : ContinuousAt (show (ℝ × U × F × F × F) → F →L[ℝ] F →L[ℝ] ℝ from
      fun p => (G p.1).inner p.2.1) q :=
    ContinuousAt.comp (f := fun p : ℝ × U × F × F × F => (p.1, p.2.1))
      (x := q) (hG.inner_opens_continuousAt (q := (q.1, q.2.1)) hq) hz
  have hΓ : ContinuousAt (fun p : ℝ × U × F × F × F =>
      chartChristoffelContraction (G p.1) p.2.1 p.2.2.1 p.2.2.1 (p.2.1 : F)) q :=
    ContinuousAt.comp (f := fun p : ℝ × U × F × F × F => (p.1, p.2.1, p.2.2.1))
      (x := q) (hG.chartChristoffelContraction_opens_continuousAt
        (q := (q.1, q.2.1, q.2.2.1)) hq)
      (continuousAt_fst.prodMk ((continuousAt_fst.comp continuousAt_snd).prodMk hX))
  exact hmetric.prodMk (hX.prodMk ((hxx.add hΓ).prodMk hV))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.covariantCurveJet_continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.covariantCurveJet_continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.covariantCurveJet_continuousAt ``Submission.DifferentialGeometry.Geometry.Curve.covariantCurveJet_continuousAt

theorem normalVelocityErrorDensity_covariantCurveJet_continuousAt
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U}
    (hG : MetricFamilySmoothOn D G) {q : ℝ × U × F × F × F}
    (hq : q.1 ∈ D.regular) (hX : q.2.2.1 ≠ 0) :
    ContinuousAt (fun p => normalVelocityErrorDensity (covariantCurveJet G p)) q := by
  exact (normalVelocityErrorDensity_continuousAt (covariantCurveJet G q)
    (ne_of_gt ((G q.1).pos q.2.1 q.2.2.1 hX))).comp
      (covariantCurveJet_continuousAt hG hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_covariantCurveJet_continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_covariantCurveJet_continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_covariantCurveJet_continuousAt ``Submission.DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_covariantCurveJet_continuousAt

theorem normalVelocityErrorDensity_covariantCurveJet_tendstoUniformlyOn
    {α ι : Type*} [TopologicalSpace α] {l : Filter ι} {K : Set α}
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, F) U}
    {J : ι → α → ℝ × U × F × F × F} {j : α → ℝ × U × F × F × F}
    (hG : MetricFamilySmoothOn D G) (hK : IsCompact K)
    (hj : ContinuousOn j K) (hreg : ∀ x ∈ K, (j x).1 ∈ D.regular)
    (hX : ∀ x ∈ K, (j x).2.2.1 ≠ 0) (hconv : TendstoUniformlyOn J j l K) :
    TendstoUniformlyOn (fun i x => normalVelocityErrorDensity (covariantCurveJet G (J i x)))
      (fun x => normalVelocityErrorDensity (covariantCurveJet G (j x))) l K := by
  let _ : LocallyCompactSpace F := inferInstance
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let V : Set (ℝ × U × F × F × F) := {q | q.1 ∈ D.regular ∧ q.2.2.1 ≠ 0}
  have hV : IsOpen V :=
    (D.regular_isOpen.preimage continuous_fst).inter
      (isOpen_ne_fun (continuous_fst.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hjV : _root_.Set.MapsTo j K V := fun x hx => ⟨hreg x hx, hX x hx⟩
  obtain ⟨L, hL, hLV, hjL, hJL⟩ :=
    hconv.exists_isCompact_eventually_mapsTo_of_isCompact hK hj hV hjV
  have hΦ : ContinuousOn (fun q => normalVelocityErrorDensity (covariantCurveJet G q)) L :=
    fun q hq => (normalVelocityErrorDensity_covariantCurveJet_continuousAt hG
      (hLV hq).1 (hLV hq).2).continuousWithinAt
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hJL
    (fun x hx => interior_subset (hjL hx))
    (hL.uniformContinuousOn_of_continuous hΦ) hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_covariantCurveJet_tendstoUniformlyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_covariantCurveJet_tendstoUniformlyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_covariantCurveJet_tendstoUniformlyOn ``Submission.DifferentialGeometry.Geometry.Curve.normalVelocityErrorDensity_covariantCurveJet_tendstoUniformlyOn

end DifferentialGeometry.Geometry.Curve

end
