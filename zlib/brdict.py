#!/usr/bin/env python3
"""Write brdict.bend from the text of RFC 7932: python3 brdict.py brdict.bend"""
import re, sys, urllib.request, zlib

t = urllib.request.urlopen('https://www.rfc-editor.org/rfc/rfc7932.txt').read().decode().split('\n')
a = t.index('Appendix A.  Static Dictionary Data')
b = [i for i, l in enumerate(t) if l.startswith('Appendix B.')][0]
hexs = ''.join(l.strip() for l in t[a:b] if re.fullmatch(r'\s{6}[0-9a-f]{2,64}', l))
d = bytes.fromhex(hexs)
assert len(d) == 122784, len(d)
assert zlib.crc32(d) == 0x5136cb04
ndbits = [0, 0, 0, 0, 10, 10, 11, 11, 10, 10, 10, 10, 10, 9, 9, 8, 7, 7, 8, 7, 7, 6, 6, 5, 5]
# transforms
rows = []
for l in t[b:]:
    m = re.match(r'\s+(\d+)\s+("(?:[^"\\]|\\.)*")\s+(\w+)\s+("(?:[^"\\]|\\.)*")\s*$', l)
    if m:
        rows.append((int(m.group(1)), m.group(2), m.group(3), m.group(4)))
assert [r[0] for r in rows] == list(range(121)), len(rows)
def cstr(s):
    return eval('b' + s)
kinds = {'Identity': 0, 'FermentFirst': 1, 'FermentAll': 2}
for k in range(1, 10):
    kinds[f'OmitFirst{k}'] = 2 + k
    kinds[f'OmitLast{k}'] = 11 + k
blob = b''
trs = []
for i, p, k, s in rows:
    pb, sb = cstr(p), cstr(s)
    trs.append((pb, kinds[k], sb))
    blob += pb + b'\0' + bytes([kinds[k]]) + sb + b'\0'
assert len(blob) == 648 and zlib.crc32(blob) == 0x3d965f81, (len(blob), hex(zlib.crc32(blob)))
def lit(bs):
    out = []
    for x in bs:
        c = chr(x)
        if x == 34:
            out.append('\\"')
        elif x == 92:
            out.append('\\\\')
        elif 32 <= x < 127:
            out.append(c)
        else:
            out.append('\\u{%x}' % x)
    return '"' + ''.join(out) + '"'
off = 0
src = ['# The brotli static dictionary (RFC 7932 Appendix A) and word transforms (Appendix B), written by brdict.py from the RFC text.', 'import Base', '']
src.append('# A transform: prefix, elementary transform (0 Identity, 1 FermentFirst, 2 FermentAll, 3..11 OmitFirst1..9, 12..20 OmitLast1..9), suffix.')
src.append('type Tr is Data:')
src.append('  Tr{pre: String, kind: U32, suf: String}')
src.append('')
blocks = {}
for n in range(4, 25):
    nw = 1 << ndbits[n]
    per = max(1, 1024 // n)
    nb = (nw + per - 1) // per
    blocks[n] = (per, nb)
    for j in range(nb):
        lo = off + j * per * n
        hi = off + min(nw, (j + 1) * per) * n
        src.append(f'def w{n}b{j}() -> String:')
        src.append('  ' + lit(d[lo:hi]))
        src.append('')
    off += n * nw
assert off == len(d)
src.append('def transforms() -> List<&2, Tr>:')
src.append('  [' + ', '.join(f'Tr{{{lit(p)}, {k}, {lit(s)}}}' for p, k, s in trs) + ']')
src.append('')
for n in range(4, 25):
    per, nb = blocks[n]
    src.append(f'# Words of length {n}, {per} to a block: word i of block b.')
    for j in range(nb - 1, -1, -1):
        src.append(f'def w{n}.at{j}(hit: Bool, +b: U32, +i: U32) -> String:')
        src.append('  match hit:')
        src.append('    case True{}:')
        src.append(f'      String.take(String.drop(w{n}b{j}(), U32.to_nat((i * {n} : U32))), {n}n)')
        src.append('    case False{}:')
        src.append('      ""' if j == nb - 1 else f'      w{n}.at{j + 1}(U32.is_eq(b, {j + 1}), b, i)')
        src.append('')
    src.append(f'def w{n}(+i: U32) -> String:')
    src.append(f'  +b = U32.div(i, {per})')
    src.append(f'  w{n}.at0(U32.is_zero(b), b, (i - b * {per} : U32))')
    src.append('')
src.append('# Word i of length l.')
for n in range(24, 3, -1):
    src.append(f'def wl{n}(hit: Bool, +l: U32, +i: U32) -> String:')
    src.append('  match hit:')
    src.append('    case True{}:')
    src.append(f'      w{n}(i)')
    src.append('    case False{}:')
    src.append('      ""' if n == 24 else f'      wl{n + 1}(U32.is_eq(l, {n + 1}), l, i)')
    src.append('')
src.append('def word(+l: U32, +i: U32) -> String:')
src.append('  wl4(U32.is_eq(l, 4), l, i)')

src.append(r"""
def tr.nth(xs: List<&2, Tr>, +i: U32) -> Tr:
  match xs:
    case Nil{}:
      Tr{"", 0, ""}
    case Con{h, t}:
      Bool.pick(Tr, U32.is_zero(i), h, tr.nth(t, (i - 1 : U32)))

def slen(s: String, +n: U32) -> U32:
  match s:
    case SNil{}:
      n
    case SCon{h, t}:
      slen(t, (n + 1 : U32))

# Ferment (RFC 7932 §8): one UTF-8 character, upper-cased the brotli way; answers it and the rest.
def fm.up(+c: U32) -> U32:
  Bool.pick(U32, Bool.and(U32.is_le(97, c), U32.is_le(c, 122)), U32.xor(c, 32), c)

def fm.two(+c: U32, t: String) -> String & String:
  match t:
    case SNil{}:
      (SCon{Chr{c}, SNil{}}, SNil{})
    case SCon{Chr{+d}, u}:
      (SCon{Chr{c}, SCon{Chr{U32.xor(d, 32)}, SNil{}}}, u)

def fm.three2(+c: U32, +d: U32, u: String) -> String & String:
  match u:
    case SNil{}:
      (SCon{Chr{c}, SCon{Chr{d}, SNil{}}}, SNil{})
    case SCon{Chr{+e}, v}:
      (SCon{Chr{c}, SCon{Chr{d}, SCon{Chr{U32.xor(e, 5)}, SNil{}}}}, v)

def fm.three(+c: U32, t: String) -> String & String:
  match t:
    case SNil{}:
      (SCon{Chr{c}, SNil{}}, SNil{})
    case SCon{Chr{+d}, u}:
      fm.three2(c, d, u)

def fm.pick(lo: Bool, mid: Bool, +c: U32, t: String) -> String & String:
  match lo:
    case True{}:
      (SCon{Chr{fm.up(c)}, SNil{}}, t)
    case False{}:
      match mid:
        case True{}:
          fm.two(c, t)
        case False{}:
          fm.three(c, t)

def fm.step(s: String) -> String & String:
  match s:
    case SNil{}:
      (SNil{}, SNil{})
    case SCon{Chr{+c}, t}:
      fm.pick(U32.is_lt(c, 192), U32.is_lt(c, 224), c, t)

def fm.join(acc: String, r: String & String) -> String & String:
  (a, b) = r
  (acc ++ a, b)

def fm.all(k: Nat, st: String & String) -> String & String:
  match k:
    case 0n:
      st
    case 1n+f:
      (acc, rest) = st
      fm.all(f, fm.join(acc, fm.step(rest)))

def fm.cat(r: String & String) -> String:
  (a, b) = r
  a ++ b

def tr.body(+k: U32, +w: String) -> String:
  +n = slen(w, 0)
  +first = fm.cat(fm.step(w))
  +all = fm.cat(fm.all(24n, ("", w)))
  +omitf = String.drop(w, U32.to_nat((k - 2 : U32)))
  +cut = (k - 11 : U32)
  +omitl = String.take(w, U32.to_nat(Bool.pick(U32, U32.is_lt(cut, n), (n - cut : U32), 0)))
  Bool.pick(String, U32.is_zero(k), w, Bool.pick(String, U32.is_eq(k, 1), first, Bool.pick(String, U32.is_eq(k, 2), all, Bool.pick(String, U32.is_le(k, 11), omitf, omitl))))

def tr.apply(t: Tr, +w: String) -> String:
  Tr{pre, +kind, suf} = t
  pre ++ tr.body(kind, w) ++ suf

# Transform tid applied to word w.
def transform(+tid: U32, +w: String) -> String:
  tr.apply(tr.nth(transforms(), tid), w)
""")

open(sys.argv[1], 'w').write('\n'.join(src) + '\n')
