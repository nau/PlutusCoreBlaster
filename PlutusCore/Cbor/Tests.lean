import PlutusCore.Cbor.Basic

namespace PlutusCore.Cbor
open PlutusCore.Cbor.CborInternal

/-- Convert a String of codepoint-as-byte characters to its `ByteArray` representation.
    Test-only helper: matches the historical convention where each Char in 0–255 stands
    for the byte with the same value (the same convention used by the UPLC `ByteString`
    domain wrapper). -/
private def s2ba (s : String) : ByteArray := ⟨(Char.toUInt8 <$> s.data).toArray⟩

-- ==============
-- =  Encoding  =
-- ==============

example : e₈ 7234295460216005990 = "deadbeef".toUTF8 := by rfl

example : splitToChunks .empty = [] := by rfl

example : splitToChunks (s2ba "1234567890123456789012345678901234567890123456789012345678901234") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234" ] := by native_decide

example : splitToChunks (s2ba "12345678901234567890123456789012345678901234567890123456789012345") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "5"
  ] := by native_decide

example : splitToChunks (s2ba "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456") =
  [ s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "1234567890123456789012345678901234567890123456789012345678901234"
  , s2ba "56"
  ] := by native_decide

example : encodeBytestring (s2ba "1234567890123456789012345678901234567890123456789012345678901234") =
  .some (s2ba ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234")) := by native_decide

example : encodeBytestring (s2ba "12345678901234567890123456789012345678901234567890123456789012345") =
  .some (s2ba ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x41"     ++ "5"
         ++ "\xFF")) := by native_decide

example : encodeBytestring (s2ba "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456") =
  .some (s2ba ("\x5F"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234"
         ++ "\x42"     ++ "56"
         ++ "\xFF")) := by native_decide

example : encodeData (.I 12) = .some (s2ba "\x0c")     := by native_decide
example : encodeData (.I 42) = .some (s2ba "\x18\x2a") := by native_decide

example :
    encodeData (
      .Constr 0 [
        .Constr 0 [.I 1284531],
        .I 1739713998000
      ]
    ) = .some (s2ba "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff") := by native_decide

example :
  encodeData (
    .Constr 0 [
      .I 144375414,
      .I 22710,
      .I 4387720097
    ]
  ) = .some (s2ba "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff") := by native_decide

-- Bignum encoding (magnitude ≥ 2^64) goes through `itos`, which must be big-endian (Spec B.6).
example : itos 258 = s2ba "\x01\x02" := by native_decide
-- Positive bignum: CBOR tag 2 (0xc2), then a 9-byte bytestring 01 00…00 for 2^64.
example : encodeData (.I 18446744073709551616) =
  .some (s2ba "\xc2\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00") := by native_decide
-- Negative bignum: CBOR tag 3 (0xc3); the encoded magnitude is -n-1 = 2^64.
example : encodeData (.I (-18446744073709551617)) =
  .some (s2ba "\xc3\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00") := by native_decide

-- ==============
-- =  Decoding  =
-- ==============

example :
    d₈ { input := s2ba "deadbeef", pos := 0 } =
    .some ({ input := s2ba "deadbeef", pos := 8 }, 7234295460216005990) := by native_decide

example :
    d₁ { input := s2ba "deadbeef", pos := 0 } =
    .some ({ input := s2ba "deadbeef", pos := 1 }, 100) := by native_decide

example : decodeBytestring (s2ba ("\x58\x40" ++ "1234567890123456789012345678901234567890123456789012345678901234")) =
  .some (s2ba "", s2ba "1234567890123456789012345678901234567890123456789012345678901234") := by native_decide

example : decodeData (s2ba "\x0C")     = .some (s2ba "", .I 12) := by native_decide
example : decodeData (s2ba "\x18\x2A") = .some (s2ba "", .I 42) := by native_decide

example : decodeData (s2ba "\xd8\x79\x9f\xd8\x79\x9f\x1a\x00\x13\x99\xb3\xff\x1b\x00\x00\x01\x95\x0f\x08\xec\xb0\xff\x34\x32")
    = .some (
        s2ba "42",
        .Constr 0 [
          .Constr 0 [.I 1284531],
          .I 1739713998000
        ]
      ) := by native_decide

example : decodeData (s2ba "\xd8\x79\x9f\x1a\x08\x9a\xfe\x76\x19\x58\xb6\x1b\x00\x00\x00\x01\x05\x87\x4b\xa1\xff\x43\x62\x6f\x72\x44\x61\x74\x61")
  = .some (
      s2ba "CborData",
      .Constr 0 [
        .I 144375414,
        .I 22710,
        .I 4387720097
      ]
  ) := by native_decide

-- Empty collections encode as a DEFINITE empty array (0x80), matching the on-chain
-- serialiseData builtin (aiken/cbor.serialise), not an indefinite 0x9f..0xff.
-- (The List [], Constr 0, and nested cases are byte-anchored in the reference fixtures below.)
example : encodeData (.Constr 1 []) = .some ⟨#[0xd8, 0x7a, 0x80]⟩ := by native_decide
example : encodeData (.Constr 7 []) = .some ⟨#[0xd9, 0x05, 0x00, 0x80]⟩ := by native_decide

-- decodeData round-trips negative bignums (tag 3), not just positive (tag 2).
example : (encodeData (.I (-(2 ^ 512 + 1)))).bind decodeData = .some (.empty, .I (-(2 ^ 512 + 1))) := by native_decide

-- Byte-anchored DECODE vector pinning the tag-1/tag-3 boundary: `-(2^64)` is the largest negative
-- on the major-type-1 side. `-(2^64+1)` (first tag-3 negative bignum) is byte-anchored in the
-- reference fixtures below, and would decode wrong under the old `1 - m` sign bug.
example : decodeData ⟨#[0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]⟩ = .some (.empty, .I (-(2 ^ 64))) := by native_decide
example : (encodeData (.I (2 ^ 512))).bind decodeData = .some (.empty, .I (2 ^ 512)) := by native_decide
example : (encodeData (.Constr 1 [])).bind decodeData = .some (.empty, .Constr 1 []) := by native_decide

-- An empty ByteString is a definite 0-length string (0x40), not zero bytes, and round-trips.
-- (The bare 0x40 and the empty-B-in-map cases are byte-anchored in the reference fixtures below.)
example : (encodeData (.B { data := "" })).bind decodeData = .some (.empty, .B { data := "" }) := by native_decide
example : (encodeData (.List [.B { data := "" }, .I 5])).bind decodeData
  = .some (.empty, .List [.B { data := "" }, .I 5]) := by native_decide

-- Constructor index > 127 uses the tag-102 fallback. The index must be a direct Word64: in-range
-- indices (128, 2^63-1, 2^64-1) are byte-anchored in the reference fixtures below. An index >= 2^64
-- or a negative index is rejected on decode, matching the real ledger decoder (decodeWord64), even
-- though serialiseData will emit it (write-only).
example : (encodeData (.Constr (2 ^ 64) [.I 1])).bind decodeData = .none := by native_decide
example : (encodeData (.Constr (-1) [])).bind decodeData = .none := by native_decide

-- Map round-trips through decodePairList (definite-length map header + key/value pairs).
example : (encodeData (.Map [(.I 1, .B { data := "aa" }), (.List [], .Constr 3 [.I 4])])).bind decodeData
  = .some (.empty, .Map [(.I 1, .B { data := "aa" }), (.List [], .Constr 3 [.I 4])]) := by native_decide

-- Reference fixtures: golden CBOR vectors for the shapes this PR touches (empty containers, empty
-- bytestring, negative bignums, tag-102 indices, nesting). Each pins `encodeData` to fixed bytes
-- and `decodeData` to invert them. The bytes are the canonical CBOR encoding mandated by the
-- reference (`Data.hs` / cborg / RFC 8949), hand-verifiable byte by byte, so the encode direction
-- is a genuine anchor and not a self-referential round-trip.
-- emptyList
example : encodeData (.List []) = .some ⟨#[0x80]⟩ := by native_decide
example : decodeData ⟨#[0x80]⟩ = .some (.empty, .List []) := by native_decide
-- emptyConstr0
example : encodeData (.Constr 0 []) = .some ⟨#[0xd8, 0x79, 0x80]⟩ := by native_decide
example : decodeData ⟨#[0xd8, 0x79, 0x80]⟩ = .some (.empty, .Constr 0 []) := by native_decide
-- emptyConstr5
example : encodeData (.Constr 5 []) = .some ⟨#[0xd8, 0x7e, 0x80]⟩ := by native_decide
example : decodeData ⟨#[0xd8, 0x7e, 0x80]⟩ = .some (.empty, .Constr 5 []) := by native_decide
-- emptyB
example : encodeData (.B { data := "" }) = .some ⟨#[0x40]⟩ := by native_decide
example : decodeData ⟨#[0x40]⟩ = .some (.empty, .B { data := "" }) := by native_decide
-- mapEmptyB
example : encodeData (.Map [(.B { data := "" }, .I 0)]) = .some ⟨#[0xa1, 0x40, 0x00]⟩ := by native_decide
example : decodeData ⟨#[0xa1, 0x40, 0x00]⟩ = .some (.empty, .Map [(.B { data := "" }, .I 0)]) := by native_decide
-- negBignum64
example : encodeData (.I (-(2 ^ 64 + 1))) = .some ⟨#[0xc3, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]⟩ := by native_decide
example : decodeData ⟨#[0xc3, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]⟩ = .some (.empty, .I (-(2 ^ 64 + 1))) := by native_decide
-- negBignum128
example : encodeData (.I (-(2 ^ 128))) = .some ⟨#[0xc3, 0x50, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]⟩ := by native_decide
example : decodeData ⟨#[0xc3, 0x50, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]⟩ = .some (.empty, .I (-(2 ^ 128))) := by native_decide
-- constr128
example : encodeData (.Constr 128 []) = .some ⟨#[0xd8, 0x66, 0x82, 0x18, 0x80, 0x80]⟩ := by native_decide
example : decodeData ⟨#[0xd8, 0x66, 0x82, 0x18, 0x80, 0x80]⟩ = .some (.empty, .Constr 128 []) := by native_decide
-- constrBig (2^63-1)
example : encodeData (.Constr (2 ^ 63 - 1) [.I 1]) = .some ⟨#[0xd8, 0x66, 0x82, 0x1b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x9f, 0x01, 0xff]⟩ := by native_decide
example : decodeData ⟨#[0xd8, 0x66, 0x82, 0x1b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x9f, 0x01, 0xff]⟩ = .some (.empty, .Constr (2 ^ 63 - 1) [.I 1]) := by native_decide
-- constrMax (2^64-1, the largest in-range Word64 index)
example : encodeData (.Constr (2 ^ 64 - 1) [.I 1]) = .some ⟨#[0xd8, 0x66, 0x82, 0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x9f, 0x01, 0xff]⟩ := by native_decide
example : decodeData ⟨#[0xd8, 0x66, 0x82, 0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x9f, 0x01, 0xff]⟩ = .some (.empty, .Constr (2 ^ 64 - 1) [.I 1]) := by native_decide
-- nested
example : encodeData (.Constr 0 [.List [], .I 5]) = .some ⟨#[0xd8, 0x79, 0x9f, 0x80, 0x05, 0xff]⟩ := by native_decide
example : decodeData ⟨#[0xd8, 0x79, 0x9f, 0x80, 0x05, 0xff]⟩ = .some (.empty, .Constr 0 [.List [], .I 5]) := by native_decide
-- mapKV
example : encodeData (.Map [(.I 0, .I 1)]) = .some ⟨#[0xa1, 0x00, 0x01]⟩ := by native_decide
example : decodeData ⟨#[0xa1, 0x00, 0x01]⟩ = .some (.empty, .Map [(.I 0, .I 1)]) := by native_decide
-- listII
example : encodeData (.List [.I 1, .I 2]) = .some ⟨#[0x9f, 0x01, 0x02, 0xff]⟩ := by native_decide
example : decodeData ⟨#[0x9f, 0x01, 0x02, 0xff]⟩ = .some (.empty, .List [.I 1, .I 2]) := by native_decide

-- Bignum decode: reads the big-endian bytestring back to 2^64 (round-trips with encoding above).
example : decodeData (s2ba "\xc2\x49\x01\x00\x00\x00\x00\x00\x00\x00\x00") =
  .some (s2ba "", .I 18446744073709551616) := by native_decide

end PlutusCore.Cbor
