import P10S2.Codec
import P10.Bytes

/-!
# P10S2.TranscriptCodec — canonical transcript bytes `tB`

`decodeTranscript` is strict: any byte string that is not the canonical encoding of a
transcript is rejected, including trailing bytes. The general laws are
`decodeTranscript_encode` and `encodeTranscript_decode` (non-malleability of `tB`).
The codec is generic in the item codec; the fixture instantiates it.
-/

namespace P10S2
open Codec

def cDigest : Codec Digest :=
  iso Codec.bytes Digest.bytes Digest.mk (fun _ => rfl) (fun _ => rfl)
def cIss : Codec Iss :=
  iso Codec.bytes Iss.bytes Iss.mk (fun _ => rfl) (fun _ => rfl)
def cSubject : Codec Subject :=
  iso Codec.bytes Subject.bytes Subject.mk (fun _ => rfl) (fun _ => rfl)

def kindToNat : Kind → Nat
  | .profileCommit => 0 | .instanceCommit => 1 | .admission => 2
  | .closure => 3 | .adjudication => 4

def kindOfNat : Nat → Option Kind
  | 0 => some .profileCommit | 1 => some .instanceCommit | 2 => some .admission
  | 3 => some .closure | 4 => some .adjudication | _ => none

def cKind : Codec Kind :=
  enum kindToNat kindOfNat (by intro a; cases a <;> rfl)
    (by
      intro n a h
      rcases n with _ | _ | _ | _ | _ | n
      all_goals first
        | (simp [kindOfNat] at h; subst h; rfl)
        | (simp [kindOfNat] at h))

def sigToNat : SigObservation → Nat
  | .verified => 0 | .badSignature => 1 | .keyUnavailable => 2

def sigOfNat : Nat → Option SigObservation
  | 0 => some .verified | 1 => some .badSignature | 2 => some .keyUnavailable | _ => none

def cSig : Codec SigObservation :=
  enum sigToNat sigOfNat (by intro a; cases a <;> rfl)
    (by
      intro n a h
      rcases n with _ | _ | _ | n
      all_goals first
        | (simp [sigOfNat] at h; subst h; rfl)
        | (simp [sigOfNat] at h))

def cInstanceCommitment : Codec InstanceCommitment :=
  iso (prod Codec.bytes (prod cIss (prod cSubject (prod cIss (prod cDigest (prod cDigest
        (prod cDigest (prod cDigest (prod cDigest (prod cDigest (prod cDigest
        (prod cDigest cDigest))))))))))))
    (fun ic => (ic.requestId, ic.issuerId, ic.instanceSubject, ic.instanceOwnerIss,
      ic.logIdentityDigest, ic.leafEncodingProfileDigest, ic.claimDigest, ic.profileDigest,
      ic.evidenceScopeDigest, ic.admissionRuleDigest, ic.coverageRuleDigest,
      ic.authorizedAdmitterSetDigest, ic.subjectDerivationDigest))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl) (fun _ => rfl)

def cClosurePayload : Codec ClosurePayload :=
  iso (prod cSubject (prod Codec.bool (prod (Codec.list Codec.nat) (prod cDigest cDigest))))
    (fun c => (c.instanceSubject, c.terminal, c.orderedAdmissionRefs,
      c.closedEvidenceSetDigest, c.checkpointPreclosureTranscriptDigest))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun _ => rfl) (fun _ => rfl)

abbrev PayloadRep (Item : Type) :=
  Digest ⊕ (InstanceCommitment ⊕ (Item ⊕ (ClosurePayload ⊕ (Nat × Nat × Nat))))

def payloadToRep {Item : Type} : Payload Item → PayloadRep Item
  | .profileCommit d => .inl d
  | .instanceCommit ic => .inr (.inl ic)
  | .admission i => .inr (.inr (.inl i))
  | .closure c => .inr (.inr (.inr (.inl c)))
  | .adjudication a b c => .inr (.inr (.inr (.inr (a, b, c))))

def payloadOfRep {Item : Type} : PayloadRep Item → Payload Item
  | .inl d => .profileCommit d
  | .inr (.inl ic) => .instanceCommit ic
  | .inr (.inr (.inl i)) => .admission i
  | .inr (.inr (.inr (.inl c))) => .closure c
  | .inr (.inr (.inr (.inr (a, b, c)))) => .adjudication a b c

def cPayload {Item : Type} (I : Codec Item) : Codec (Payload Item) :=
  iso (Codec.sum cDigest (Codec.sum cInstanceCommitment (Codec.sum I
        (Codec.sum cClosurePayload (prod Codec.nat (prod Codec.nat Codec.nat))))))
    payloadToRep payloadOfRep
    (by intro a; cases a <;> rfl)
    (by
      intro b
      rcases b with d | ic | i | c | ⟨a, b, c⟩ <;> rfl)

def cRowStatus : Codec RowStatus :=
  iso (Codec.sum cSubject Codec.unit)
    (fun s => match s with | .available x => Sum.inl x | .unavailable => Sum.inr ())
    (fun s => match s with | Sum.inl x => .available x | Sum.inr _ => .unavailable)
    (by intro a; cases a <;> rfl)
    (by intro b; rcases b with x | ⟨⟩ <;> rfl)

def cRow : Codec Row :=
  iso (prod Codec.nat cRowStatus) (fun r => (r.idx, r.status)) (fun t => ⟨t.1, t.2⟩)
    (fun _ => rfl) (fun _ => rfl)

def cDetailed {Item : Type} (I : Codec Item) : Codec (DetailedEntry Item) :=
  iso (prod Codec.nat (prod cIss (prod cKind (prod cSig (Codec.option (cPayload I))))))
    (fun d => (d.idx, d.iss, d.kind, d.sig, d.payload))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun _ => rfl) (fun _ => rfl)

def cCheckpoint : Codec Checkpoint :=
  iso (prod Codec.nat cDigest) (fun c => (c.size, c.rootDigest)) (fun t => ⟨t.1, t.2⟩)
    (fun _ => rfl) (fun _ => rfl)

/-- Domain-separation magic for transcript bytes. -/
def transcriptMagic : Bytes := bytes% "P10S2-Transcript-v0:"

def cTranscript {Item : Type} (I : Codec Item) : Codec (Transcript Item) :=
  pre transcriptMagic <|
  iso (prod cDigest (prod cDigest (prod cCheckpoint (prod (Codec.list cRow)
        (Codec.list (cDetailed I))))))
    (fun t => (t.logIdentityDigest, t.keyResolutionDigest, t.checkpoint, t.rows, t.detailed))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun _ => rfl) (fun _ => rfl)

def encodeTranscript {Item : Type} (I : Codec Item) (t : Transcript Item) : Bytes :=
  (cTranscript I).enc t

def decodeTranscript {Item : Type} (I : Codec Item) (b : Bytes) : Option (Transcript Item) :=
  (cTranscript I).decodeAll b

/-- `decode ∘ encode = id` on every transcript. -/
theorem decode_encode_transcript {Item : Type} (I : Codec Item) (t : Transcript Item) :
    decodeTranscript I (encodeTranscript I t) = some t :=
  Codec.decodeAll_enc _ t

/-- `encode ∘ decode = id` on every byte string that decodes (non-malleability of `tB`). -/
theorem encode_decode_transcript {Item : Type} (I : Codec Item) (b : Bytes) (t : Transcript Item)
    (h : decodeTranscript I b = some t) : encodeTranscript I t = b :=
  Codec.enc_decodeAll _ b t h

end P10S2
