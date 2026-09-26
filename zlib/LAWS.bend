import Base
import ./zlib.bend as Z
import ./zstd.bend as Zs
import ./brotli.bend as Br

def bytes(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{c, t}:
      SCon{Chr{c}, bytes(t)}

# Every byte value once, 0 through 255: all four fixed literal code ranges.
def every(k: Nat, +i: U32) -> String:
  match k:
    case 0n:
      SNil{}
    case 1n+p:
      SCon{Chr{i}, every(p, (i + 1 : U32))}

# RFC 1951 §3.2.4: a stored block is copied as is.
law inflate_stored:
  {Z.inflate(bytes([1, 12, 0, 243, 255, 104, 101, 108, 108, 111, 32, 115, 116, 111, 114, 101, 100])) == Some{"hello stored"} : Maybe<&2, String>}

# RFC 1951 §3.2.6: a fixed-Huffman block.
law inflate_fixed:
  {Z.inflate(bytes([203, 72, 205, 201, 201, 7, 0])) == Some{"hello"} : Maybe<&2, String>}

# RFC 1951 §3.2.7: a dynamic-Huffman block.
law inflate_dynamic:
  {Z.inflate(bytes([5, 193, 177, 13, 0, 64, 12, 2, 177, 85, 178, 90, 138, 147, 160, 249, 34, 176, 191, 222, 70, 161, 231, 17, 135, 27, 112, 226, 29, 24, 222, 2, 162, 212, 183, 31])) == Some{"ehsetri hereitseeissia ee enaeeehetetira"} : Maybe<&2, String>}

# A stream cut short is not a stream.
law inflate_truncated:
  {Z.inflate(bytes([203, 72, 205, 201, 201, 87, 40, 207, 47, 202, 73, 81, 200])) == None{} : Maybe<&2, String>}

# RFC 1951 §3.2.3: block type 3 is reserved.
law inflate_bad_type:
  {Z.inflate(bytes([7])) == None{} : Maybe<&2, String>}

# RFC 1952 §2.3: FNAME is skipped up to its zero byte.
law gunzip_fname:
  {Z.gunzip(bytes([31, 139, 8, 8, 0, 0, 0, 0, 2, 255, 97, 46, 116, 120, 116, 0, 203, 75, 204, 77, 77, 81, 72, 202, 79, 169, 204, 27, 210, 44, 0, 219, 138, 47, 170, 200, 0, 0, 0])) == Some{String.repeat("named body", 20n)} : Maybe<&2, String>}

# RFC 1952 §2.3: FEXTRA, FNAME, FCOMMENT and FHCRC together.
law gunzip_all_flags:
  {Z.gunzip(bytes([31, 139, 8, 30, 0, 0, 0, 0, 0, 255, 6, 0, 65, 66, 2, 0, 104, 105, 110, 46, 116, 120, 116, 0, 99, 111, 109, 109, 101, 110, 116, 0, 241, 55, 75, 203, 73, 76, 47, 86, 200, 207, 6, 0, 76, 161, 200, 174, 8, 0, 0, 0])) == Some{"flags ok"} : Maybe<&2, String>}

# RFC 1952 §2.3.1: a CRC-32 mismatch rejects the member.
law gunzip_bad_crc:
  {Z.gunzip(bytes([31, 139, 8, 0, 0, 0, 0, 0, 2, 255, 203, 72, 205, 201, 201, 87, 72, 175, 202, 44, 80, 40, 207, 47, 202, 73, 1, 0, 106, 125, 232, 183, 16, 0, 0, 0])) == None{} : Maybe<&2, String>}

# A member without its trailer is rejected.
law gunzip_truncated:
  {Z.gunzip(bytes([31, 139, 8, 0, 0, 0, 0, 0, 2, 255, 203, 72, 205, 201, 201, 87, 72, 175, 202, 44, 80, 40, 207, 47, 202, 73, 1, 0, 107, 125, 232])) == None{} : Maybe<&2, String>}

# RFC 1950: a zlib stream.
law unzlib_ok:
  {Z.unzlib(bytes([120, 156, 203, 72, 205, 201, 201, 87, 168, 202, 201, 76, 82, 40, 207, 47, 202, 73, 1, 0, 52, 90, 6, 46])) == Some{"hello zlib world"} : Maybe<&2, String>}

# RFC 1950 §2.2: an Adler-32 mismatch rejects the stream.
law unzlib_bad_adler:
  {Z.unzlib(bytes([120, 156, 203, 72, 205, 201, 201, 87, 168, 202, 201, 76, 82, 40, 207, 47, 202, 73, 1, 0, 52, 90, 6, 47])) == None{} : Maybe<&2, String>}

# CRC-32 of "hello", as zlib computes it.
law crc32_hello:
  {Z.crc32("hello") == 907060870 : U32}

# Adler-32 of "hello", as zlib computes it.
law adler32_hello:
  {Z.adler32("hello") == 103547413 : U32}

# RFC 1951 §3.2.5: length/distance pairs copy from earlier output, overlapping included.
law inflate_matches:
  {Z.inflate(bytes([43, 201, 72, 85, 40, 44, 205, 76, 206, 86, 72, 42, 202, 47, 207, 83, 72, 203, 175, 80, 200, 42, 205, 45, 40, 86, 200, 47, 75, 45, 82, 40, 1, 74, 231, 36, 86, 85, 42, 164, 228, 167, 235, 129, 121, 163, 138, 71, 21, 143, 42, 30, 85, 60, 170, 120, 84, 241, 48, 82, 12, 0])) == Some{String.repeat("the quick brown fox jumps over the lazy dog. ", 40n)} : Maybe<&2, String>}

law deflate_empty:
  {Z.inflate(Z.deflate("")) == Some{""} : Maybe<&2, String>}

law deflate_hello:
  {Z.inflate(Z.deflate("hello")) == Some{"hello"} : Maybe<&2, String>}

law deflate_every_byte:
  {Z.inflate(Z.deflate(every(256n, 0))) == Some{every(256n, 0)} : Maybe<&2, String>}

# A run longer than 258 needs several overlapping matches.
law deflate_run:
  {Z.inflate(Z.deflate(String.repeat("a", 600n))) == Some{String.repeat("a", 600n)} : Maybe<&2, String>}

law deflate_repeats:
  {Z.inflate(Z.deflate(String.repeat("the quick brown fox jumps over the lazy dog. ", 40n))) == Some{String.repeat("the quick brown fox jumps over the lazy dog. ", 40n)} : Maybe<&2, String>}

# These bytes decode with system gzip -d.
law gzip_pinned:
  {Z.gzip("hello hello hello hello, world") == bytes([31, 139, 8, 0, 0, 0, 0, 0, 0, 255, 203, 72, 205, 201, 201, 87, 192, 32, 117, 20, 202, 243, 139, 114, 82, 0, 247, 26, 144, 221, 30, 0, 0, 0]) : String}

law gzip_roundtrip:
  {Z.gunzip(Z.gzip("gzip round trip, gzip round trip")) == Some{"gzip round trip, gzip round trip"} : Maybe<&2, String>}

law zlib_roundtrip:
  {Z.unzlib(Z.zlib("zlib round trip, zlib round trip")) == Some{"zlib round trip, zlib round trip"} : Maybe<&2, String>}

# RFC 8878 §3.1.1.2.2: a Raw_Block is copied as is.
law zstd_raw:
  {Zs.decode(bytes([40, 181, 47, 253, 32, 5, 41, 0, 0, 104, 101, 108, 108, 111])) == Some{"hello"} : Maybe<&2, String>}

# RFC 8878 §3.1.1.2.2: an RLE_Block repeats one byte Block_Size times.
law zstd_rle:
  {Zs.decode(bytes([40, 181, 47, 253, 32, 10, 83, 0, 0, 122])) == Some{"zzzzzzzzzz"} : Maybe<&2, String>}

# An empty frame is empty.
law zstd_empty:
  {Zs.decode(bytes([40, 181, 47, 253, 32, 0, 1, 0, 0])) == Some{""} : Maybe<&2, String>}

# RFC 8878 §3.1.1.3.2: raw literals and sequences with predefined tables.
law zstd_sequences:
  {Zs.decode(bytes([40, 181, 47, 253, 32, 42, 141, 0, 0, 72, 97, 98, 99, 32, 104, 101, 108, 108, 111, 2, 0, 41, 92, 241, 115, 67])) == Some{"abcabcabcabcabcabcabcabc hello hello hello"} : Maybe<&2, String>}

# RFC 8878 §4.2: Huffman literals in one stream, weights compressed with FSE.
law zstd_huffman:
  {Zs.decode(bytes([40, 181, 47, 253, 96, 44, 0, 173, 3, 0, 114, 12, 16, 6, 240, 57, 50, 205, 231, 30, 215, 25, 181, 98, 9, 153, 42, 180, 20, 196, 188, 1, 69, 203, 184, 14, 110, 1, 174, 193, 74, 203, 236, 42, 211, 38, 185, 24, 69, 116, 65, 184, 184, 226, 146, 50, 4, 71, 225, 140, 13, 104, 24, 102, 229, 188, 44, 56, 116, 151, 202, 242, 62, 212, 24, 89, 1, 19, 0, 125, 164, 200, 66, 51, 149, 128, 116, 115, 23, 110, 44, 170, 11, 144, 26, 45, 122, 33, 179, 6, 104, 134, 56, 103, 13, 95, 70, 194, 231, 2, 31, 143, 65, 234, 70, 122, 218, 227, 137, 242, 44, 248, 2, 130, 86, 237, 1])) == Some{"aabadcdcaadaccacbaabaaaeacacadacdeabaacbaceaababdcdabbddcadaccabebacdaadcbdadabcaadaaaeeacdbbcbeacdadeacadbeadcdbcbaeebcaaaeaaebaaaacababaabbaaabdabbcbddaabcbcababdacaaacaaacdceadcadacbcabaaabaabbacbaaeaacadacabaacadacbddabcbaaababcabacebedeaaaaaaaeabbdbbbbabadaeabacacaabacaeaabbbeacbaabaaacaaaacaac"} : Maybe<&2, String>}

# RFC 8878 §3.1.1.3.1.6: Huffman literals in four streams.
law zstd_huffman4:
  {Zs.decode(bytes([40, 181, 47, 253, 96, 44, 0, 29, 3, 0, 198, 210, 23, 7, 240, 25, 3, 82, 202, 207, 36, 21, 0, 21, 0, 20, 0, 66, 180, 18, 195, 164, 70, 2, 42, 66, 188, 68, 198, 41, 53, 115, 199, 200, 164, 142, 162, 56, 1, 10, 7, 70, 204, 99, 239, 193, 22, 129, 162, 131, 230, 84, 57, 4, 80, 110, 215, 65, 13, 8, 74, 72, 205, 152, 154, 55, 18, 24, 199, 32, 53, 186, 40, 207, 83, 136, 65, 176, 132, 57, 159, 99, 228, 0, 188, 137, 51, 113, 21, 1, 64, 192, 253, 167, 97, 137, 65, 60, 0])) == Some{"aabadcdcaadaccacbaabaaaeacacadacdeabaacbaceaababdcdabbddcadaccabebacdaadcbdadabcaadaaaeeacdbbcbeacdadeacadbeadcdbcbaeebcaaaeaaebaaaacababaabbaaabdabbcbddaabcbcababdacaaacaaacdceadcadacbcabaaabaabbacbaaeaacadacabaacadacbddabcbaaababcabacebedeaaaaaaaeabbdbbbbabadaeabacacaabacaeaabbbeacbaabaaacaaaacaac"} : Maybe<&2, String>}

# RFC 8878 §4.1: sequence tables sent as FSE distributions.
law zstd_fse:
  {Zs.decode(bytes([40, 181, 47, 253, 96, 243, 1, 53, 6, 0, 194, 133, 14, 13, 208, 231, 178, 111, 229, 206, 73, 88, 146, 3, 240, 128, 226, 191, 177, 103, 227, 217, 179, 255, 153, 189, 57, 215, 11, 61, 177, 112, 190, 177, 82, 61, 99, 213, 216, 240, 73, 16, 135, 187, 152, 128, 104, 245, 227, 243, 232, 181, 0, 213, 121, 49, 25, 201, 216, 48, 6, 65, 168, 209, 154, 149, 164, 198, 206, 1, 16, 18, 164, 156, 187, 14, 17, 84, 24, 211, 16, 101, 80, 82, 208, 100, 51, 153, 64, 132, 182, 138, 254, 215, 192, 199, 172, 176, 20, 89, 42, 217, 52, 223, 45, 216, 68, 10, 16, 174, 168, 161, 64, 76, 146, 210, 220, 195, 149, 2, 223, 69, 211, 49, 142, 140, 107, 192, 114, 58, 30, 198, 40, 114, 92, 68, 124, 169, 100, 204, 231, 172, 40, 216, 20, 64, 167, 215, 138, 226, 57, 187, 19, 60, 105, 131, 81, 102, 40, 254, 84, 245, 96, 142, 215, 202, 167, 193, 149, 7, 92, 239, 142, 111, 0, 57, 142, 214, 63, 17, 210, 50, 172, 0, 116, 36, 26, 119, 231, 65, 155, 122, 182, 130, 247, 155, 184, 106])) == Some{"dolor do ipsum amet ipsum elit elit elit eiusmod adipiscing sit ipsum elit lorem adipiscing adipiscing do lorem tempor elit amet tempor sit do ipsum consectetur lorem lorem lorem eiusmod sed lorem adipiscing eiusmod sit adipiscing tempor lorem sed sit elit elit sed sit consectetur sit eiusmod sit elit amet lorem adipiscing sed eiusmod ipsum dolor eiusmod tempor amet ipsum tempor consectetur tempor tempor sed adipiscing sed eiusmod sit amet amet do elit sed adipiscing do lorem elit sit tempor adipiscing adipiscing eiusmod dolor consectetur sed tempor eiusmod tempor consectetur ipsum elit eiusmod sed ipsum dolor sed adipiscing consectetur elit tempor lorem elit lorem amet tempor do do do adipiscing eiusmod dolor dolor sed sit lorem sit sed sed sit"} : Maybe<&2, String>}

# RFC 8878 §3.1.1.5: an offset value of 1 reuses the most recent offset.
law zstd_repeat:
  {Zs.decode(bytes([40, 181, 47, 253, 32, 117, 29, 1, 0, 144, 106, 97, 106, 102, 98, 101, 102, 101, 104, 102, 99, 104, 89, 90, 88, 89, 90, 89, 6, 0, 238, 33, 128, 187, 158, 11, 3, 139, 0, 238, 2, 110, 126, 1])) == Some{"jajfbefehfchYjajfbefehfchZjajfbefehfchXjajfbefehfchXjajfbefehfchYjajfbefehfchXjajfbefehfchZjajfbefehfchYjajfbefehfchY"} : Maybe<&2, String>}

# RFC 8878 §3.1.1.5: the other repeat codes reorder the three recent offsets.
law zstd_repeat_codes:
  {Zs.decode(bytes([40, 181, 47, 253, 32, 156, 13, 1, 0, 136, 99, 101, 104, 99, 97, 98, 106, 105, 103, 97, 100, 106, 89, 90, 88, 90, 89, 5, 0, 81, 176, 197, 93, 206, 93, 88, 207, 69, 8, 207, 252, 2])) == Some{"cehcabjigadjYcehcabjigadjYcehcabjigadjYcehcabjigadjZcehcabjigadjYcehcabjigadjXcehcabjigadjXcehcabjigadjZcehcabjigadjXcehcabjigadjYcehcabjigadjYcehcabjigadjX"} : Maybe<&2, String>}

# RFC 8878 §3.1.1: the Content_Checksum is the low 32 bits of XXH64.
law zstd_checksum:
  {Zs.decode(bytes([40, 181, 47, 253, 36, 18, 145, 0, 0, 99, 104, 101, 99, 107, 115, 117, 109, 32, 109, 101, 32, 112, 108, 101, 97, 115, 101, 4, 178, 244, 70])) == Some{"checksum me please"} : Maybe<&2, String>}

# A checksum mismatch rejects the frame.
law zstd_bad_checksum:
  {Zs.decode(bytes([40, 181, 47, 253, 36, 18, 145, 0, 0, 99, 104, 101, 99, 107, 115, 117, 109, 32, 109, 101, 32, 112, 108, 101, 97, 115, 101, 4, 178, 244, 71])) == None{} : Maybe<&2, String>}

# A frame cut short is not a frame.
law zstd_truncated:
  {Zs.decode(bytes([40, 181, 47, 253, 32, 42, 141, 0, 0, 72, 97, 98, 99, 32, 104, 101, 108, 108, 111, 2, 0, 41, 92])) == None{} : Maybe<&2, String>}

# RFC 8878 §3.1.2: frames follow one another; a skippable frame yields nothing.
law zstd_frames:
  {Zs.decode(bytes([40, 181, 47, 253, 32, 12, 97, 0, 0, 102, 105, 114, 115, 116, 32, 102, 114, 97, 109, 101, 32, 83, 42, 77, 24, 3, 0, 0, 0, 120, 121, 122, 40, 181, 47, 253, 32, 12, 97, 0, 0, 115, 101, 99, 111, 110, 100, 32, 102, 114, 97, 109, 101])) == Some{"first frame second frame"} : Maybe<&2, String>}

# A frame that needs a dictionary is rejected.
law zstd_dictionary:
  {Zs.decode(bytes([40, 181, 47, 253, 33, 5, 5, 41, 0, 0, 104, 101, 108, 108, 111])) == None{} : Maybe<&2, String>}

# Bytes that are not a frame are rejected.
law zstd_bad_magic:
  {Zs.decode(bytes([104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100])) == None{} : Maybe<&2, String>}

# RFC 7932 §9.2: ISLAST and ISLASTEMPTY end an empty stream.
law brotli_empty:
  {Br.decode(bytes([59])) == Some{""} : Maybe<&2, String>}

# RFC 7932 §9.2: an uncompressed meta-block holds MLEN raw bytes.
law brotli_uncompressed:
  {Br.decode(bytes([11, 2, 128, 104, 101, 108, 108, 111, 3])) == Some{"hello"} : Maybe<&2, String>}

# Quality 1 output of a short string with repeats.
law brotli_quality1:
  {Br.decode(bytes([139, 20, 0, 0, 128, 170, 170, 170, 234, 255, 116, 229, 243, 149, 69, 128, 1, 248, 64, 0, 12, 27, 112, 14, 187, 132, 97, 160, 56, 27, 140, 57, 110, 80, 190, 207, 58, 212, 192, 212, 192, 212, 192, 6])) == Some{"abcabcabcabcabcabcabcabc hello hello hello"} : Maybe<&2, String>}

# RFC 7932 §8, §3.4: English text refers to static dictionary words, with simple prefix codes.
law brotli_dictionary:
  {Br.decode(bytes([27, 42, 0, 136, 156, 9, 54, 78, 168, 119, 55, 188, 36, 51, 163, 75, 144, 51, 188, 66, 123, 75, 144, 178, 57, 152, 200, 129, 67, 91, 160, 247, 222, 167, 21, 14, 233, 11, 71, 137, 234, 12, 27, 224, 86, 53, 6])) == Some{"the quick brown fox jumps over the lazy dog"} : Maybe<&2, String>}

# RFC 7932 §3.5: complex prefix codes.
law brotli_complex:
  {Br.decode(bytes([27, 170, 2, 0, 68, 183, 121, 189, 222, 111, 228, 136, 129, 102, 52, 133, 127, 215, 22, 114, 191, 49, 126, 63, 250, 21, 67, 21, 44, 134, 123, 127, 163, 11, 198, 42, 104, 219, 18, 130, 232, 19, 69, 158, 187, 185, 212, 62, 251, 12, 246, 193, 167, 73, 91, 137, 174, 119, 193, 45, 234, 35, 235, 174, 123, 138, 180, 0, 18, 196, 74, 68, 137, 247, 65, 175, 135, 140, 181, 121, 241, 64, 176, 223, 67, 174, 224, 40, 203, 229, 24, 85, 255, 89, 206, 71, 109, 222, 67, 223, 213, 180, 87, 145, 8, 233, 107, 236, 199, 58, 72, 165, 156, 141, 128, 188, 138, 195, 7, 135, 52, 204, 110, 64, 245, 249, 252, 108, 204, 74, 211, 24, 29, 178, 9, 77, 163, 11, 65, 220, 141, 190, 47, 126, 23, 254, 8, 209, 110, 157, 47, 64, 252, 67, 229, 169, 209, 243, 237, 152, 78, 47])) == Some{"ipsum amet amet sed lorem lorem sed lorem sit amet sed amet amet amet lorem sit lorem lorem lorem amet sed amet lorem amet lorem sed sed lorem amet lorem sed sed elit dolor eiusmod eiusmod dolor dolor dolor dolor adipiscing eiusmod adipiscing dolor eiusmod eiusmod adipiscing adipiscing amet amet amet elit lorem lorem amet lorem lorem sed amet sit sit lorem sed sed lorem lorem amet sed lorem sed sed amet lorem lorem lorem lorem amet sed tempor lorem sed amet amet sed sed amet lorem lorem amet amet amet amet sed amet tempor elit tempor elit dolor eiusmod eiusmod lorem amet amet sed amet amet sed lorem sed lorem tempor elit dolor dolor adipiscing adipiscing consectetur ipsum do"} : Maybe<&2, String>}

# RFC 7932 §7.3: a context map sent with run lengths and the inverse move-to-front transform.
law brotli_context_map:
  {Br.decode(bytes([27, 74, 2, 0, 140, 212, 94, 53, 121, 208, 236, 192, 13, 151, 170, 33, 114, 244, 19, 205, 233, 104, 90, 111, 152, 85, 191, 184, 141, 193, 28, 114, 208, 54, 190, 77, 252, 167, 155, 36, 45, 192, 0, 248, 222, 111, 78, 176, 177, 45, 220, 64, 37, 86, 192, 225, 1, 135, 146, 234, 92, 2, 15, 112, 120, 204, 173, 174, 117, 24, 227, 43, 63, 244, 164, 168, 90, 35, 252, 115, 127, 247, 3, 139, 159, 147, 89, 31, 22, 29, 61, 62, 14, 84, 98, 27, 172, 198, 130, 29, 187, 18, 70, 55, 236, 153, 230, 87, 142, 125, 113, 242, 188, 176, 193, 204, 107, 28, 183, 125, 252, 181, 240, 192, 76, 9, 15, 84, 70, 134, 118, 196, 19, 45, 95, 84, 7, 203, 35, 246, 121, 188, 22, 130, 33, 7, 196, 208, 196, 124, 6, 75, 219, 46, 237, 57, 36, 199, 27, 248, 185, 230, 45, 151, 215, 84, 232, 178, 191, 194, 15, 166, 60, 106, 82, 85, 162, 46, 176, 175, 247, 143, 225, 251, 3, 230, 122, 181, 110, 205, 167, 140, 106, 37, 244, 174, 26, 207, 211, 103, 236, 37, 28, 242, 112, 173, 235, 95, 134, 230, 56, 119, 101, 20, 11, 108, 180, 103, 187, 234, 244, 27, 76, 168, 118, 169, 225, 4, 84, 203, 17, 49, 225, 194, 34, 88, 164, 231, 234, 161, 131, 130, 221, 21, 117, 32, 231, 74, 194, 124, 105, 191, 134, 157, 69, 37, 1])) == Some{"86348 eiusmod dolor consectetur sed lorem ut 24620 lorem sed elit elit magna sed 4718 et sed amet dolor et dolor 34250 lorem ut labore do ut lorem 79682 labore sed sed dolor dolore lorem 41306 consectetur elit amet magna elit labore 79832 ut tempor elit incididunt dolore dolor 6664 do dolor consectetur ut ut dolore 92002 ut dolor adipiscing consectetur sit ipsum 59056 lorem sit incididunt consectetur ut aliqua 72828 amet labore dolor eiusmod sed dolor 26648 ipsum incididunt ipsum sed labore et 26760 ipsum ipsum sit do consectetur ipsum 98038 sit ut sed dolor sit lorem 36760 dolore"} : Maybe<&2, String>}

# A stream cut short is not a stream.
law brotli_truncated:
  {Br.decode(bytes([27, 41, 0, 0, 164, 65, 194, 196, 198, 228, 34, 193, 108, 147, 68, 226, 189, 13])) == None{} : Maybe<&2, String>}

# Bytes after the last meta-block are rejected.
law brotli_trailing:
  {Br.decode(bytes([27, 41, 0, 0, 164, 65, 194, 196, 198, 228, 34, 193, 108, 147, 68, 226, 189, 13, 179, 39, 0])) == None{} : Maybe<&2, String>}

# RFC 7932 §9.1: the WBITS pattern 0010001 is invalid.
law brotli_bad_wbits:
  {Br.decode(bytes([17, 0])) == None{} : Maybe<&2, String>}
