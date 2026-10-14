-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.PositivePartPrelude

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 02: Sobolev Infrastructure

Public facade for the Sobolev weak-derivative, witness, and approximation
layers.
-/
