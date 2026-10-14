import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.Set _root_.Bundle _root_.Module
open scoped _root_.Manifold _root_.Topology

universe u v w

namespace DifferentialGeometry.Topology

open _root_.Classical in
theorem integralLocalHomology_generator_of_orientation_coordinates
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [T1Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (p x : M) (hx : x ∈ (chartAt E p).source)
    (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (c : integralLocalHomology (Module.finrank ℝ E) (0 : E))
    (hc : Function.Bijective (fun z : ℤ => z • c))
    (a : integralLocalHomology (Module.finrank ℝ E) x)
    (ha : ((integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (chartAt E p x)))
        (show _root_.Set.MapsTo (Homeomorph.subRight (chartAt E p x))
          ({chartAt E p x}ᶜ : Set E) ({0}ᶜ : Set E) from fun _ hz => sub_ne_zero.mpr hz)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
          (chartAt E p) x hx).hom.hom) a =
        if (Orientation.map _
          ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv
          o) = ω then c else -c) :
    Function.Bijective (fun z : ℤ => z • a) := by
  classical
  let J := integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
      (chartAt E p) x hx ≪≫
    integralRelativeHomologyHomeomorphIso (Module.finrank ℝ E)
      (Homeomorph.subRight (chartAt E p x)) ({chartAt E p x}ᶜ : Set E) {0}ᶜ
      (fun _ hz => sub_ne_zero.mpr hz)
      (fun z hz heq => by
        apply hz
        change z + chartAt E p x = chartAt E p x at heq
        exact add_right_cancel (heq.trans (zero_add _).symm))
  let d := if (Orientation.map _
    ((_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv o) = ω
    then c else -c
  have hgen : Function.Bijective (fun z : ℤ => z • d) := by
    dsimp only [d]
    split_ifs
    · exact hc
    · refine ⟨?_, ?_⟩
      · intro z w h
        apply neg_injective
        apply hc.1
        simpa only [neg_zsmul, zsmul_neg] using h
      · intro b
        obtain ⟨z, hz⟩ := hc.2 b
        exact ⟨-z, by simpa only [neg_zsmul, zsmul_neg, neg_neg] using hz⟩
  have hJ : J.toLinearEquiv a = d := ha
  have hcomp : J.toLinearEquiv ∘ (fun z : ℤ => z • a) = fun z : ℤ => z • d := by
    funext z
    rw [Function.comp_apply, map_zsmul, hJ]
  rw [← hcomp] at hgen
  exact (J.toLinearEquiv.bijective.of_comp_iff' _).mp hgen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLocalHomology_generator_of_orientation_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLocalHomology_generator_of_orientation_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLocalHomology_generator_of_orientation_coordinates ``Submission.DifferentialGeometry.Topology.integralLocalHomology_generator_of_orientation_coordinates

end DifferentialGeometry.Topology

end
