import Submission.DifferentialGeometry.Topology.SphereSeparation.CylinderCapTransport
import Submission.DifferentialGeometry.Topology.Morse.ReplacementTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold _root_.Filter
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

theorem criticalPoints_cylinderCap_displacement
    {e f : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hf : Continuous f) (Φ : EuclideanThree ≃ₘ[ℝ] EuclideanThree)
    (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree) {a δ c ε : ℝ}
    (hheight : ∀ p, Ψ p 2 = c + p.2)
    {D : Set SphereTwo} (hD : IsClosed D) (χ : Schoenflies.Plane → SphereTwo)
    (hχD : χ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 = D)
    (hcap : ∀ x ∈ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hfix : _root_.Set.EqOn f e Dᶜ) (himage : Φ '' _root_.Set.range e = _root_.Set.range e)
    {U : Set (Schoenflies.Plane × ℝ)} (hU : IsOpen U)
    (hcapU : EuclideanGeometry.cylinderCap a '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 ⊆ U)
    (hmove : ∀ p ∈ U, Φ (Ψ p) = Ψ (p.1, p.2 + δ))
    {J : Set EuclideanThree} (hJ : IsClosed J)
    (hJheight : ∀ z ∈ J, z 2 ∈ _root_.Set.Icc (c - ε) (c + ε))
    (hsupport : _root_.Set.EqOn Φ id Jᶜ)
    (hregular : ∀ x, e x 2 ∈ _root_.Set.Icc (c - ε) (c + ε) →
      ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) :
    criticalPoints (𝓡 2) (fun y => Φ (f y) 2) =
      criticalPoints (𝓡 2) (fun y => f y 2) ∧
    (∀ x, IsCriticalPointAt (𝓡 2) (fun y => f y 2) x →
      chartHessianAt (fun y => Φ (f ((extChartAt (𝓡 2) x).symm y)) 2)
        (extChartAt (𝓡 2) x x) =
      chartHessianAt (fun y => f ((extChartAt (𝓡 2) x).symm y) 2)
        (extChartAt (𝓡 2) x x)) ∧
    (∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → x ∉ D → Φ (f x) = f x) ∧
    Φ (f (χ 0)) 2 = c - a + δ := by
  have hzero : (0 : Schoenflies.Plane) ∈ _root_.Metric.closedBall 0 1 := _root_.Metric.mem_closedBall_self zero_le_one
  have hΦnear (x : SphereTwo) (hx : IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) :
      (Φ ∘ e) =ᶠ[𝓝 x] e := by
    have hxJ : e x ∉ J := fun hh => hregular x (hJheight _ hh) hx
    filter_upwards [he.contMDiff.continuous.continuousAt.preimage_mem_nhds
      (hJ.isOpen_compl.mem_nhds hxJ)] with y hy
    exact hsupport hy
  have hshift (x : SphereTwo) (hx : x ∈ D) :
      (fun y => Φ (f y) 2) =ᶠ[𝓝 x] (fun y => f y 2 + δ) := by
    obtain ⟨v, hv, hvx⟩ := hχD.symm.subset hx
    have hxU : Ψ.symm (f x) ∈ U := by
      rw [← hvx, hcap v hv, Ψ.symm_apply_apply]
      exact hcapU ⟨v, hv, rfl⟩
    filter_upwards [(Ψ.symm.contMDiff.continuous.comp hf).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hxU)] with y hy
    have hh := hmove (Ψ.symm (f y)) hy
    rw [Ψ.apply_symm_apply] at hh
    rw [hh, hheight]
    have hh' := hheight (Ψ.symm (f y))
    rw [Ψ.apply_symm_apply] at hh'
    linarith
  have hshift' (x : SphereTwo) (hx : x ∈ D) : ∃ a' : ℝ,
      ((fun z : EuclideanThree => z 2) ∘ Φ ∘ f) =ᶠ[𝓝 x]
        (fun y => f y 2 + a') := ⟨δ, hshift x hx⟩
  refine ⟨criticalPoints_comp_diffeomorph_replacement_eq
    (h := fun z : EuclideanThree => z 2) he Φ hD hfix himage
    (fun x hx => (hΦnear x hx).self_of_nhds) hshift', ?_, ?_, ?_⟩
  · intro x hx
    exact chartHessianAt_comp_diffeomorph_replacement_eq Φ hD hfix hΦnear hshift' hx
  · intro x hx hxD
    rw [hfix hxD]
    exact (hΦnear x hx).self_of_nhds
  · rw [hcap 0 hzero, hmove _ (hcapU ⟨0, hzero, rfl⟩), hheight,
      EuclideanGeometry.cylinderCap_zero]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.criticalPoints_cylinderCap_displacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.criticalPoints_cylinderCap_displacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.criticalPoints_cylinderCap_displacement ``Submission.DifferentialGeometry.Topology.SphereSeparation.criticalPoints_cylinderCap_displacement

end DifferentialGeometry.Topology.SphereSeparation
