import P10S2Tests.Common

/-!
# MUST-FAIL: S2 end-to-end without the faithfulness hypothesis hFaithful

Vector P2 (a valid composition) with the hypothesis `hFaithful` removed from `s2_end_to_end`.
The coverage conjunct `CoverageSpecV` cannot be obtained from S1's hypotheses alone, so this
file MUST NOT compile. (It guards against a composition theorem that ignores `hFaithful`.)
-/

open P10S2 P10S2Tests

def pB : Bytes := filebytes% "vectors/P2/pB.json"
def instB : Bytes := filebytes% "vectors/P2/inst.bin"
def tB : Bytes := filebytes% "vectors/P2/tB.bin"
def iB : Bytes := filebytes% "vectors/P2/iB.json"

def inst : InstanceCommitment := (decodeInst instB).get (by decide +kernel)
def T : Transcript fx.Item := (decodeTranscript fxItemC tB).get (by decide +kernel)
def prof : ProfileArtifact := (decodeProfileArtifact pB).get (by decide +kernel)
def si : P10.Wire.Instance := (P10.Wire.decode iB).get (by decide +kernel)

theorem dropped (V : LogView fx.Item) :
    CoverageSpecV fx inst pB V (P10.S1.Evidence.obs false none) :=
  s2_end_to_end (tB := tB) (pB := pB) (iB := iB) (inst := inst) (T := T) (V := V)
    (prof := prof) (si := si) (c := P10.S1.Claim.secondBit)
    (e := P10.S1.Evidence.obs false none)
    (hT := (Option.some_get _).symm) (hPB := (Option.some_get _).symm) (hCov := (by decide +kernel :
      cov inst pB T = .accept (.obs false none)))
    (hS1 := P10.bound_of_check (by decide +kernel) (by decide +kernel))
    (hDec := (Option.some_get _).symm) (hEv := rfl)
    (hC := ⟨rfl, by decide +kernel⟩) |>.1
