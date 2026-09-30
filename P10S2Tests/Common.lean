import P10S2

/-!
# P10S2Tests.Common — shared runners for the concrete vector modules

This library is OUTSIDE `VerifierManifestS2aV0` (prereg §6a partition rule): it instantiates the
generic checker on concrete vector bytes. The checker library never imports it.
-/

namespace P10S2Tests
open P10S2

/-- `coverageCheck` at the fixture, typed so that `DecidableEq` of the outcome is found. -/
def cov (inst : InstanceCommitment) (pB : Bytes) (T : Transcript fx.Item) :
    CoverageOutcome P10.S1.Evidence := coverageCheck fx inst pB T

/-- Decode the frozen `InstanceCommitment` fixture. -/
def decodeInst (instB : Bytes) : Option InstanceCommitment :=
  cInstanceCommitment.decodeAll instB

/-- Run `coverageCheck` on the committed vector bytes. `none` = undecodable fixture input. -/
def run (pB instB tB : Bytes) : Option (CoverageOutcome P10.S1.Evidence) :=
  (decodeInst instB).bind fun inst =>
    (decodeTranscript fxItemC tB).map fun T =>
      (coverageCheck fx inst pB T : CoverageOutcome P10.S1.Evidence)

/-- Same, when S2b could not produce a transcript at all (TB5). -/
def runMissing (pB instB : Bytes) : Option (CoverageOutcome P10.S1.Evidence) :=
  (decodeInst instB).map fun inst =>
    (coverageCheckM fx inst pB none : CoverageOutcome P10.S1.Evidence)

/-- The checker-owned end-to-end statement on the committed bytes. -/
def runE2E (tDigest tB pB iB instB : Bytes) :
    Option (P10.S1.Evidence × P10.S1.Claim) :=
  (decodeInst instB).bind fun inst => e2eCheck tDigest tB pB iB inst

/-- `runE2E` on an instance fixture that decodes to `inst` (generic; no computation). -/
theorem runE2E_of_inst {tDigest tB pB iB instB : Bytes} {inst : InstanceCommitment}
    (h : decodeInst instB = some inst) :
    runE2E tDigest tB pB iB instB = e2eCheck tDigest tB pB iB inst := by
  unfold runE2E
  rw [h]
  rfl

end P10S2Tests
