import P10S2.Composition

/-!
# Axiom audit

`scripts/acceptance.py` runs this file and requires, for every `#print axioms` line, that the
declaration depends only on the permitted axioms of `profile/AXIOM_POLICY.md`
(`propext`, `Classical.choice`, `Quot.sound`) — never `sorryAx`, `Lean.ofReduceBool` or a custom
axiom — and that the number of lines equals the number of exported theorems listed there.
-/

#print axioms P10S2.Codec.nat
#print axioms P10S2.Codec.decodeAll_enc
#print axioms P10S2.Codec.enc_decodeAll
#print axioms P10S2.decode_encode_transcript
#print axioms P10S2.encode_decode_transcript
#print axioms P10S2.decode_encode_profile
#print axioms P10S2.encode_decode_profile
#print axioms P10S2.fx_projection
#print axioms P10S2.bundle_perm
#print axioms P10S2.bundle_dedup
#print axioms P10S2.bundle_faithful
#print axioms P10S2.bundle_refines
#print axioms P10S2.bundle_truth_nil
#print axioms P10S2.bundle_truth_second
#print axioms P10S2.bundle_truth_eU
#print axioms P10S2.bundle_truth_eD
#print axioms P10S2.bundle_truth_first_conflict
#print axioms P10S2.bundle_truth_second_conflict
#print axioms P10S2.bundle_truth_second_conflict_nofirst
#print axioms P10S2.coreCheck_sound
#print axioms P10S2.coverage_sound
#print axioms P10S2.coverage_sound_view
#print axioms P10S2.s2_end_to_end
#print axioms P10S2.p10Verdict_halt
#print axioms P10S2.p10Verdict_reject
#print axioms P10S2.p10Verdict_some
#print axioms P10S2.coverage_halt_no_verdict
#print axioms P10S2.unavailable_row_no_verdict
#print axioms P10S2.unavailable_payload_no_verdict
#print axioms P10S2.e2eCheck_sound
