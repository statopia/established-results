import Lean
import Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur
import Lean

namespace PaperProofTasks.ResidualE2ESupport20261106

/-!
The source module deliberately keeps its ensemble bookkeeping private. These
term elaborators resolve the exact, uniquely identified declarations inspected in
`Probe.log`; the kernel still checks the original proof terms. No declaration is
axiomatized and no private index is guessed. Source: MarchenkoPastur.lean lines
12230-12347 and 11956-12053.
-/
open Lean Elab Term Meta in
private def exactMPPrivate (suffix : String) : TermElabM Expr := do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "_private.Statlib.RandomMatrix.SampleCovariance.MarchenkoPastur." &&
       n.toString.endsWith ("." ++ suffix) then some n else none
  match names with
  | [n] => mkConstWithFreshMVarLevels n
  | _ => throwError "Expected one audited MarchenkoPastur private declaration ending {suffix}, got {names.length}"

elab "mpPartialTraceVariance" : term => exactMPPrivate "MarchenkoPasturInternal.partialTraceVariance"
elab "mpPartialTraceMeasurable" : term => exactMPPrivate "MarchenkoPasturInternal.partialResolventTrace_measurable"
elab "mpPartialTraceBound" : term => exactMPPrivate "MarchenkoPasturInternal.partialResolventTrace_bound"
elab "mpPartialTrace" : term => exactMPPrivate "MarchenkoPasturInternal.partialResolventTrace"
elab "mpPartialCovariance" : term => exactMPPrivate "MarchenkoPasturInternal.partialCovariance"
elab "mpIndependentRows" : term => exactMPPrivate "sampleCovariance_support_71"

#check mpPartialTraceVariance
#check mpPartialTraceMeasurable
#check mpPartialTraceBound
#check mpIndependentRows

