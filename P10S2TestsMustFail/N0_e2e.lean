import P10S2Tests.Common

/-!
# MUST-FAIL: S2-N0 strategic omission, end to end

The scenario of vector N0 (closure [A1] omits the determining admission A2) with S1 instance bytes for evidence `obs false none`.
This file asserts `s2_end_to_end` for evidence `obs false none`. It MUST NOT compile: the
coverage hypothesis `hCov` is false, because `coverageCheck` REJECTs this transcript.
Every other hypothesis is discharged honestly (same pattern as vector P2), so the only
failure is the coverage link. `scripts/s2a.py mustfail` requires a non-zero exit and the
`decide` failure message.
-/

open P10S2 P10S2Tests

def pB : Bytes := filebytes% "vectors/N0/pB.json"
def instB : Bytes := filebytes% "vectors/N0/inst.bin"
def tB : Bytes := filebytes% "vectors/N0/tB.bin"
def iB : Bytes := filebytes% "vectors/N0/iB.json"

def inst : InstanceCommitment := (decodeInst instB).get (by decide +kernel)
def T : Transcript fx.Item := (decodeTranscript fxItemC tB).get (by decide +kernel)
def prof : ProfileArtifact := (decodeProfileArtifact pB).get (by decide +kernel)
def si : P10.Wire.Instance := (P10.Wire.decode iB).get (by decide +kernel)

example (V : LogView fx.Item) (hf : TranscriptFaithful T V) :=
  s2_end_to_end (tB := tB) (pB := pB) (iB := iB) (inst := inst) (T := T) (V := V)
    (prof := prof) (si := si) (c := P10.S1.Claim.secondBit)
    (e := P10.S1.Evidence.obs false none)
    (hT := (Option.some_get _).symm) (hPB := (Option.some_get _).symm) (hFaithful := hf)
    (hCov := (by decide +kernel :
      cov inst pB T = .accept (.obs false none)))
    (hS1 := P10.bound_of_check (by decide +kernel) (by decide +kernel))
    (hDec := (Option.some_get _).symm) (hEv := rfl)
    (hC := ⟨rfl, by decide +kernel⟩)
