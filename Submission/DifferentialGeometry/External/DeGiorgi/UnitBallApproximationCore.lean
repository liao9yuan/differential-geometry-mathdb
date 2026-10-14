-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Profiles
import Submission.DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Rescaling
import Submission.DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Dilation
import Submission.DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Approximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 02: Unit-Ball Approximation

Public facade for the unit-ball approximation infrastructure.
-/
