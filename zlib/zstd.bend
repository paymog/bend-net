# Zstandard (RFC 8878) decoding over byte strings.
import Base

# Bytes are one Char per octet (0..255), as everywhere in bend-kit.

def byte(h: Char) -> U32:
  Chr{c} = h
  c

def bits(+n: U32) -> Nat:
  U32.to_nat(n)

def mask(+n: U32) -> U32:
  (U32.shln(1, bits(n)) - 1 : U32)

def umin(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), a, b)

def nth(xs: List<&2, U32>, +i: U32) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      Bool.pick(U32, U32.is_zero(i), h, nth(t, (i - 1 : U32)))

def rep(k: Nat, +v: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      rep(p, v, Con{v, acc})

def slen(s: String, +n: U32) -> U32:
  match s:
    case SNil{}:
      n
    case SCon{h, t}:
      slen(t, (n + 1 : U32))

def src.fill(s: String, +i: U32, a: Array<U32>) -> Array<U32>:
  match s:
    case SNil{}:
      a
    case SCon{h, t}:
      src.fill(t, (i + 1 : U32), Array.set(U32, a, i, byte(h)))

# The smallest depth whose 2^depth slots hold n.
def depth(k: Nat, +d: Nat, +n: U32) -> Nat:
  match k:
    case 0n:
      d
    case 1n+f:
      Bool.pick(Nat, U32.is_le(n, U32.shln(1, d)), d, depth(f, 1n+d, n))

# The index of the highest set bit; 0 for 0 and 1.
def hib.go(k: Nat, +z: Bool, +v: U32, +acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+f:
      match z:
        case True{}:
          acc
        case False{}:
          hib.go(f, U32.is_zero(U32.shr(U32.shr(v))), U32.shr(v), (acc + 1 : U32))

def hib(+v: U32) -> U32:
  hib.go(32n, U32.is_zero(U32.shr(v)), v, 0)

def ar.inc.of(av: Array<U32> & U32, +i: U32) -> Array<U32>:
  (a, +v) = av
  Array.set(U32, a, i, (v + 1 : U32))

def ar.inc(a: Array<U32>, +i: U32) -> Array<U32>:
  ar.inc.of(Array.get(U32, a, i), i)

# Little-endian words: k bytes at i.
def le.add(av: Array<U32> & U32, +acc: U32, +sh: Nat) -> Array<U32> & U32:
  (a, +v) = av
  (a, U32.or(acc, U32.shln(v, sh)))

def le.go(k: Nat, st: Array<U32> & U32, +i: U32, +sh: Nat) -> Array<U32> & U32:
  match k:
    case 0n:
      st
    case 1n+f:
      (a, acc) = st
      le.go(f, le.add(Array.get(U32, a, i), acc, sh), (i + 1 : U32), Nat.add(sh, 8n))

def le(a: Array<U32>, +i: U32, k: Nat) -> Array<U32> & U32:
  le.go(k, (a, 0), i, 0n)

# n bits (at most 24) from bit p, least significant first.
def fb.of(av: Array<U32> & U32, +p: U32, +n: U32) -> Array<U32> & U32:
  (a, +w) = av
  (a, U32.and(U32.shrn(w, bits(U32.and(p, 7))), mask(n)))

def fb(a: Array<U32>, +p: U32, +n: U32) -> Array<U32> & U32:
  fb.of(le(a, U32.shrn(p, 3n), 4n), p, n)

# Backward bit reader (RFC 8878 §4.1): pos bits are left above byte base; reads past the start give zeros and set over.
type Rd is Type:
  Rd{a: Array<U32>, base: U32, pos: U32, over: Bool}

def rd.shl(av: Array<U32> & U32, +k: U32) -> Array<U32> & U32:
  (a, +v) = av
  (a, U32.shln(v, bits(k)))

def rd.peek.go(+ok: Bool, a: Array<U32>, +base: U32, +pos: U32, +n: U32) -> Array<U32> & U32:
  match ok:
    case True{}:
      fb(a, (base * 8 + pos - n : U32), n)
    case False{}:
      rd.shl(fb(a, (base * 8 : U32), pos), (n - pos : U32))

def rd.wrap(av: Array<U32> & U32, +base: U32, +pos: U32, +over: Bool) -> Rd & U32:
  (a, v) = av
  (Rd{a, base, pos, over}, v)

def rd.peek(r: Rd, +n: U32) -> Rd & U32:
  Rd{a, +base, +pos, over} = r
  rd.wrap(rd.peek.go(U32.is_le(n, pos), a, base, pos, n), base, pos, over)

def rd.skip(r: Rd, +n: U32) -> Rd:
  Rd{a, base, +pos, over} = r
  Rd{a, base, Bool.pick(U32, U32.is_le(n, pos), (pos - n : U32), 0), Bool.or(over, U32.is_lt(pos, n))}

def rd.skip.of(rv: Rd & U32, +n: U32) -> Rd & U32:
  (r, v) = rv
  (rd.skip(r, n), v)

def rd.bits(r: Rd, +n: U32) -> Rd & U32:
  rd.skip.of(rd.peek(r, n), n)

def rd.lo(rv: Rd & U32, +hi: U32) -> Rd & U32:
  (r, +lo) = rv
  (r, U32.or(U32.shln(hi, 16n), lo))

def rd.hi(rv: Rd & U32) -> Rd & U32:
  (r, +hi) = rv
  rd.lo(rd.bits(r, 16), hi)

def rd.big.go(+small: Bool, r: Rd, +n: U32) -> Rd & U32:
  match small:
    case True{}:
      rd.bits(r, n)
    case False{}:
      rd.hi(rd.bits(r, (n - 16 : U32)))

# Up to 31 bits.
def rd.big(r: Rd, +n: U32) -> Rd & U32:
  rd.big.go(U32.is_le(n, 24), r, n)

# The last byte holds a 1 bit above the stream's last bit; a zero last byte is corrupt.
def rd.init.of(av: Array<U32> & U32, +s: U32, +e: U32) -> Rd:
  (a, +last) = av
  Rd{a, s, ((e - 1 - s) * 8 + hib(last) : U32), Bool.or(U32.is_zero(last), U32.is_le(e, s))}

def rd.init(a: Array<U32>, +s: U32, +e: U32) -> Rd:
  rd.init.of(Array.get(U32, a, (e - 1 : U32)), s, e)

def rd.close(r: Rd) -> Array<U32> & Bool:
  Rd{a, base, +pos, +over} = r
  (a, Bool.and(U32.is_zero(pos), Bool.not(over)))

# FSE table description (§4.1.1). Each symbol's value c is its probability + 1: 0 means "less than 1".
type Fp is Type:
  Fp{a: Array<U32>, p: U32, rem: U32, thr: U32, nb: U32, sym: U32, acc: List<&2, U32>, zr: Bool, bad: Bool}

def fp.thr(k: Nat, +rem: U32, +thr: U32, +nb: U32) -> U32 & U32:
  match k:
    case 0n:
      (thr, nb)
    case 1n+f:
      +s = U32.is_lt(rem, thr)
      fp.thr(f, rem, Bool.pick(U32, s, U32.shr(thr), thr), Bool.pick(U32, s, (nb - 1 : U32), nb))

def fp.set(tn: U32 & U32, a: Array<U32>, +p: U32, +rem: U32, +sym: U32, acc: List<&2, U32>, +zr: Bool, +bad: Bool) -> Fp:
  (+thr, +nb) = tn
  Fp{a, p, rem, thr, nb, sym, acc, zr, bad}

def fp.val(+pk: U32, +thr: U32, +rem: U32) -> U32:
  +max = (2 * thr - 1 - rem : U32)
  +low = U32.and(pk, (thr - 1 : U32))
  +v = U32.and(pk, (2 * thr - 1 : U32))
  Bool.pick(U32, U32.is_lt(low, max), low, Bool.pick(U32, U32.is_le(thr, v), (v - max : U32), v))

def fp.used(+pk: U32, +thr: U32, +rem: U32, +nb: U32) -> U32:
  Bool.pick(U32, U32.is_lt(U32.and(pk, (thr - 1 : U32)), (2 * thr - 1 - rem : U32)), (nb - 1 : U32), nb)

def fp.sym.of(av: Array<U32> & U32, +p: U32, +rem: U32, +thr: U32, +nb: U32, +sym: U32, acc: List<&2, U32>, +bad: Bool) -> Fp:
  (a, +pk) = av
  +c = fp.val(pk, thr, rem)
  +w = Bool.pick(U32, U32.is_zero(c), 1, (c - 1 : U32))
  +rem2 = (rem - w : U32)
  fp.set(fp.thr(10n, rem2, thr, nb), a, (p + fp.used(pk, thr, rem, nb) : U32), rem2, (sym + 1 : U32), Con{c, acc}, U32.is_eq(c, 1), Bool.or(bad, U32.is_le(rem, w)))

def fp.rep.of(av: Array<U32> & U32, +p: U32, +rem: U32, +thr: U32, +nb: U32, +sym: U32, acc: List<&2, U32>, +bad: Bool) -> Fp:
  (a, +r) = av
  Fp{a, (p + 2 : U32), rem, thr, nb, (sym + r : U32), rep(bits(r), 1, acc), U32.is_eq(r, 3), bad}

def fp.step(+zr: Bool, a: Array<U32>, +p: U32, +rem: U32, +thr: U32, +nb: U32, +sym: U32, acc: List<&2, U32>, +bad: Bool) -> Fp:
  match zr:
    case True{}:
      fp.rep.of(fb(a, p, 2), p, rem, thr, nb, sym, acc, bad)
    case False{}:
      fp.sym.of(fb(a, p, nb), p, rem, thr, nb, sym, acc, bad)

def fp.more(+on: Bool, +zr: Bool, a: Array<U32>, +p: U32, +rem: U32, +thr: U32, +nb: U32, +sym: U32, acc: List<&2, U32>, +bad: Bool) -> Fp:
  match on:
    case True{}:
      fp.step(zr, a, p, rem, thr, nb, sym, acc, bad)
    case False{}:
      Fp{a, p, rem, thr, nb, sym, acc, zr, bad}

def fp.go(k: Nat, st: Fp) -> Fp:
  match k:
    case 0n:
      st
    case 1n+f:
      Fp{a, +p, +rem, +thr, +nb, +sym, acc, +zr, +bad} = st
      fp.go(f, fp.more(Bool.and(Bool.or(U32.is_lt(1, rem), zr), Bool.not(bad)), zr, a, p, rem, thr, nb, sym, acc, bad))

# A parsed table description: accuracy log, the values, the byte just past it, and whether it was valid.
type Fd is Data:
  Fd{al: U32, cs: List<&2, U32>, next: U32, ok: Bool}

def fd.of(st: Fp, +al: U32, +p0: U32, +maxal: U32, +maxsym: U32) -> Array<U32> & Fd:
  Fp{a, +p, +rem, thr, nb, +sym, acc, zr, +bad} = st
  (a, Fd{al, List.reverse(&2, U32, acc), U32.shrn((p + 7 : U32), 3n), Bool.and(Bool.and(Bool.not(bad), U32.is_eq(rem, 1)), Bool.and(U32.is_le(sym, (maxsym + 1 : U32)), U32.is_le(al, maxal)))})

def fd.head(av: Array<U32> & U32, +i: U32, +maxal: U32, +maxsym: U32) -> Array<U32> & Fd:
  (a, +b) = av
  +al = (U32.and(b, 15) + 5 : U32)
  +p = (i * 8 + 4 : U32)
  fd.of(fp.go(600n, Fp{a, p, (U32.shln(1, bits(al)) + 1 : U32), U32.shln(1, bits(al)), (al + 1 : U32), 0, Nil{}, False{}, False{}}), al, p, maxal, maxsym)

def fd.read(a: Array<U32>, +i: U32, +maxal: U32, +maxsym: U32) -> Array<U32> & Fd:
  fd.head(Array.get(U32, a, i), i, maxal, maxsym)

# FSE decoding table: entry = symbol | Number_of_Bits << 8 | Baseline << 16.
type Ft is Type:
  Ft{t: Array<U32>, nx: Array<U32>, high: U32, pos: U32}

def ft.p1.one(+neg: Bool, +c: U32, +s: U32, ft: Ft) -> Ft:
  match neg:
    case True{}:
      Ft{t, nx, +high, pos} = ft
      Ft{Array.set(U32, t, high, s), Array.set(U32, nx, s, 1), (high - 1 : U32), pos}
    case False{}:
      Ft{t, nx, high, pos} = ft
      Ft{t, Array.set(U32, nx, s, (c - 1 : U32)), high, pos}

# "Less than 1" symbols take the last cells.
def ft.p1(cs: List<&2, U32>, +s: U32, ft: Ft) -> Ft:
  match cs:
    case Nil{}:
      ft
    case Con{+c, r}:
      ft.p1(r, (s + 1 : U32), ft.p1.one(U32.is_zero(c), c, s, ft))

def ft.step(+pos: U32, +size: U32) -> U32:
  U32.and((pos + U32.shr(size) + U32.shrn(size, 3n) + 3 : U32), (size - 1 : U32))

def ft.adv(k: Nat, +over: Bool, +pos: U32, +high: U32, +size: U32) -> U32:
  match k:
    case 0n:
      pos
    case 1n+f:
      match over:
        case False{}:
          pos
        case True{}:
          +np = ft.step(pos, size)
          ft.adv(f, U32.is_lt(high, np), np, high, size)

def ft.place(k: Nat, +s: U32, +size: U32, ft: Ft) -> Ft:
  match k:
    case 0n:
      ft
    case 1n+f:
      Ft{t, nx, +high, +pos} = ft
      +np = ft.step(pos, size)
      ft.place(f, s, size, Ft{Array.set(U32, t, pos, s), nx, high, ft.adv(bits(size), U32.is_lt(high, np), np, high, size)})

def ft.p2(cs: List<&2, U32>, +s: U32, +size: U32, ft: Ft) -> Ft:
  match cs:
    case Nil{}:
      ft
    case Con{+c, r}:
      ft.p2(r, (s + 1 : U32), size, ft.place(bits(Bool.pick(U32, U32.is_le(2, c), (c - 1 : U32), 0)), s, size, ft))

def ft.p3b(xv: Array<U32> & U32, t: Array<U32>, +s: U32, +u: U32, +al: U32, +size: U32, +high: U32, +pos: U32) -> Ft:
  (nx, +x) = xv
  +nb = (al - hib(x) : U32)
  Ft{Array.set(U32, t, u, U32.or(U32.or(s, U32.shln(nb, 8n)), U32.shln((U32.shln(x, bits(nb)) - size : U32), 16n))), Array.set(U32, nx, s, (x + 1 : U32)), high, pos}

def ft.p3a(tv: Array<U32> & U32, nx: Array<U32>, +u: U32, +al: U32, +size: U32, +high: U32, +pos: U32) -> Ft:
  (t, +s) = tv
  ft.p3b(Array.get(U32, nx, s), t, s, u, al, size, high, pos)

def ft.p3(k: Nat, +u: U32, +al: U32, +size: U32, ft: Ft) -> Ft:
  match k:
    case 0n:
      ft
    case 1n+f:
      Ft{t, nx, +high, +pos} = ft
      ft.p3(f, (u + 1 : U32), al, size, ft.p3a(Array.get(U32, t, u), nx, u, al, size, high, pos))

def ft.tab(ft: Ft) -> Array<U32>:
  Ft{t, nx, high, pos} = ft
  t

def ft.build(+al: U32, +cs: List<&2, U32>) -> Array<U32>:
  +size = U32.shln(1, bits(al))
  ft.tab(ft.p3(bits(size), 0, al, size, ft.p2(cs, 0, size, ft.p1(cs, 0, Ft{Array.new(U32, 9n, 0), Array.new(U32, 6n, 0), (size - 1 : U32), 0}))))

# RLE mode: one symbol, no state bits.
def ft.rle(+s: U32) -> Array<U32>:
  Array.set(U32, Array.new(U32, 9n, 0), 0, s)

# §3.1.1.3.2.2: default distributions, as probability + 1.
def ll.dist() -> List<&2, U32>:
  [5, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 3, 2, 2, 2, 2, 2, 0, 0, 0, 0]

def ml.dist() -> List<&2, U32>:
  [2, 5, 4, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0]

def of.dist() -> List<&2, U32>:
  [2, 2, 2, 2, 2, 2, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0]

# §3.1.1.3.2.1.1: baselines and extra bits of the length codes.
def ll.base() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28, 32, 40, 48, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]

def ll.extra() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

def ml.base() -> List<&2, U32>:
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051, 4099, 8195, 16387, 32771, 65539]

def ml.extra() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

# Output: the window (indexes wrap), bytes out so far, and the bytes, reversed.
type Zo is Type:
  Zo{win: Array<U32>, n: U32, racc: String}

def zo.put(o: Zo, +c: U32) -> Zo:
  Zo{win, +n, racc} = o
  Zo{Array.set(U32, win, n, c), (n + 1 : U32), SCon{Chr{c}, racc}}

def zo.cp.of(av: Array<U32> & U32, +n: U32, racc: String) -> Zo:
  (win, +c) = av
  zo.put(Zo{win, n, racc}, c)

def zo.copy(k: Nat, o: Zo, +off: U32) -> Zo:
  match k:
    case 0n:
      o
    case 1n+f:
      Zo{win, +n, racc} = o
      zo.copy(f, zo.cp.of(Array.get(U32, win, (n - off : U32)), n, racc), off)

def zo.lits(xs: List<&2, U32>, o: Zo) -> Zo:
  match xs:
    case Nil{}:
      o
    case Con{+c, t}:
      zo.lits(t, zo.put(o, c))

# Tables kept across blocks: the Huffman table and its depth, and the three sequence tables with their accuracy logs.
type Tb is Type:
  Tb{huf: Array<U32>, hmb: U32, hok: Bool, ll: Array<U32>, lla: U32, of: Array<U32>, ofa: U32, ml: Array<U32>, mla: U32, sok: Bool}

def tb.new() -> Tb:
  Tb{Array.new(U32, 11n, 0), 0, False{}, Array.new(U32, 9n, 0), 0, Array.new(U32, 9n, 0), 0, Array.new(U32, 9n, 0), 0, False{}}

# Block state: input, tables, output, repeat offsets, window size, and whether it went wrong.
type Bs is Type:
  Bs{a: Array<U32>, tb: Tb, o: Zo, r1: U32, r2: U32, r3: U32, win: U32, bad: Bool}

def bs.fail(st: Bs) -> Bs:
  Bs{a, tb, o, r1, r2, r3, win, bad} = st
  Bs{a, tb, o, r1, r2, r3, win, True{}}

def bs.check(st: Bs, +ok: Bool) -> Bs:
  match ok:
    case True{}:
      st
    case False{}:
      bs.fail(st)

# Huffman weights (§4.2.1): direct 4-bit fields, or FSE with two interleaved states.
def hw.direct.of(av: Array<U32> & U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (a, +b) = av
  (a, Con{U32.and(b, 15), Con{U32.shrn(b, 4n), acc}})

def hw.direct(k: Nat, st: Array<U32> & List<&2, U32>, +i: U32) -> Array<U32> & List<&2, U32>:
  match k:
    case 0n:
      st
    case 1n+f:
      (a, acc) = st
      hw.direct(f, hw.direct.of(Array.get(U32, a, i), acc), (i + 1 : U32))

def take.n(k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, take.n(p, t)}

# Two-state weight decoder: the state to decode next, the other, and the weights so far (reversed).
type Hw is Type:
  Hw{r: Rd, t: Array<U32>, cur: U32, oth: U32, acc: List<&2, U32>, done: Bool}

def hw.sym(tv: Array<U32> & U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (t, +e) = tv
  (t, Con{U32.and(e, 255), acc})

def hw.fin(r: Rd, tl: Array<U32> & List<&2, U32>, +cur: U32, +oth: U32) -> Hw:
  (t, acc) = tl
  Hw{r, t, cur, oth, acc, True{}}

def hw.last(r: Rd, tl: Array<U32> & List<&2, U32>, +oth: U32, +cur: U32) -> Hw:
  (t, acc) = tl
  hw.fin(r, hw.sym(Array.get(U32, t, oth), acc), cur, oth)

def hw.next(+over: Bool, r: Rd, tl: Array<U32> & List<&2, U32>, +oth: U32, +cur: U32) -> Hw:
  match over:
    case True{}:
      hw.last(r, tl, oth, cur)
    case False{}:
      (t, acc) = tl
      Hw{r, t, oth, cur, acc, False{}}

def hw.upd.of(ro: Rd & Bool, tl: Array<U32> & List<&2, U32>, +oth: U32, +cur: U32) -> Hw:
  (r, over) = ro
  hw.next(over, r, tl, oth, cur)

def hw.over(r: Rd) -> Rd & Bool:
  Rd{a, base, pos, +over} = r
  (Rd{a, base, pos, over}, over)

def hw.upd(rv: Rd & U32, +base: U32, tl: Array<U32> & List<&2, U32>, +oth: U32) -> Hw:
  (r, +v) = rv
  hw.upd.of(hw.over(r), tl, oth, (base + v : U32))

def hw.step(tv: Array<U32> & U32, r: Rd, acc: List<&2, U32>, +oth: U32) -> Hw:
  (t, +e) = tv
  hw.upd(rd.bits(r, U32.and(U32.shrn(e, 8n), 31)), U32.shrn(e, 16n), (t, Con{U32.and(e, 255), acc}), oth)

def hw.go(k: Nat, st: Hw) -> Hw:
  match k:
    case 0n:
      st
    case 1n+f:
      Hw{r, t, +cur, +oth, acc, done} = st
      match done:
        case True{}:
          Hw{r, t, cur, oth, acc, True{}}
        case False{}:
          hw.go(f, hw.step(Array.get(U32, t, cur), r, acc, oth))

def hw.out(st: Hw) -> Array<U32> & List<&2, U32> & Bool:
  Hw{r, t, cur, oth, acc, +done} = st
  Rd{a, base, pos, over} = r
  (a, List.reverse(&2, U32, acc), done)

def hw.s2(rv: Rd & U32, t: Array<U32>, +s1: U32) -> Hw:
  (r, +s2) = rv
  Hw{r, t, s1, s2, Nil{}, False{}}

def hw.s1(rv: Rd & U32, t: Array<U32>, +al: U32) -> Hw:
  (r, +s1) = rv
  hw.s2(rd.bits(r, al), t, s1)

def hw.fse.ok(+ok: Bool, a: Array<U32>, +al: U32, cs: List<&2, U32>, +next: U32, +e: U32) -> Array<U32> & List<&2, U32> & Bool:
  match ok:
    case False{}:
      (a, Nil{}, False{})
    case True{}:
      hw.out(hw.go(256n, hw.s1(rd.bits(rd.init(a, next, e), al), ft.build(al, cs), al)))

def hw.fse.of(av: Array<U32> & Fd, +i: U32, +hb: U32) -> Array<U32> & List<&2, U32> & Bool:
  (a, fd) = av
  Fd{+al, cs, +next, +ok} = fd
  +e = (i + 1 + hb : U32)
  hw.fse.ok(Bool.and(ok, U32.is_lt(next, e)), a, al, cs, next, e)

def hw.dir.of(al: Array<U32> & List<&2, U32>, +n: U32) -> Array<U32> & List<&2, U32> & Bool:
  (a, acc) = al
  (a, take.n(bits(n), List.reverse(&2, U32, acc)), True{})

def hw.read.pick(+fse: Bool, a: Array<U32>, +i: U32, +hb: U32) -> Array<U32> & List<&2, U32> & Bool:
  match fse:
    case True{}:
      hw.fse.of(fd.read(a, (i + 1 : U32), 6, 255), i, hb)
    case False{}:
      +n = (hb - 127 : U32)
      hw.dir.of(hw.direct(bits(U32.shr((n + 1 : U32))), (a, Nil{}), (i + 1 : U32)), n)

# Weights of the symbols before the last, the header byte, and the size of the description.
def hw.read.of(av: Array<U32> & U32, +i: U32) -> Array<U32> & List<&2, U32> & Bool:
  (a, +hb) = av
  hw.read.pick(U32.is_lt(hb, 128), a, i, hb)

def hw.size(+hb: U32) -> U32:
  Bool.pick(U32, U32.is_lt(hb, 128), (hb + 1 : U32), (U32.shr((hb - 126 : U32)) + 1 : U32))

# Huffman decoding table (§4.2.1.3): entry = symbol | Number_of_Bits << 8, 2^(weight - 1) cells per symbol, lowest weights first.
def hf.sum(ws: List<&2, U32>, +acc: U32) -> U32:
  match ws:
    case Nil{}:
      acc
    case Con{+w, t}:
      hf.sum(t, (acc + Bool.pick(U32, U32.is_zero(w), 0, U32.shln(1, bits((w - 1 : U32)))) : U32))

def hf.cnt(ws: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}:
      a
    case Con{+w, t}:
      hf.cnt(t, ar.inc(a, w))

def hf.st.of(cv: Array<U32> & U32, sa: Array<U32>, +w: U32, +acc: U32) -> Array<U32> & Array<U32> & U32:
  (c, +n) = cv
  (c, Array.set(U32, sa, w, acc), (acc + U32.shln(n, bits((w - 1 : U32))) : U32))

def hf.st.step(st: Array<U32> & Array<U32> & U32, +w: U32) -> Array<U32> & Array<U32> & U32:
  (c, sa, acc) = st
  hf.st.of(Array.get(U32, c, w), sa, w, acc)

def hf.starts(k: Nat, +w: U32, st: Array<U32> & Array<U32> & U32) -> Array<U32> & Array<U32> & U32:
  match k:
    case 0n:
      st
    case 1n+f:
      hf.starts(f, (w + 1 : U32), hf.st.step(st, w))

def hf.run(k: Nat, +i: U32, +e: U32, t: Array<U32>) -> Array<U32>:
  match k:
    case 0n:
      t
    case 1n+f:
      hf.run(f, (i + 1 : U32), e, Array.set(U32, t, i, e))

def hf.put(sv: Array<U32> & U32, t: Array<U32>, +s: U32, +w: U32, +mb: U32) -> Array<U32> & Array<U32>:
  (sa, +b) = sv
  +len = U32.shln(1, bits((w - 1 : U32)))
  (Array.set(U32, sa, w, (b + len : U32)), hf.run(bits(len), b, U32.or(s, U32.shln((mb + 1 - w : U32), 8n)), t))

def hf.one(+zero: Bool, st: Array<U32> & Array<U32>, +s: U32, +w: U32, +mb: U32) -> Array<U32> & Array<U32>:
  match zero:
    case True{}:
      st
    case False{}:
      (sa, t) = st
      hf.put(Array.get(U32, sa, w), t, s, w, mb)

def hf.fill(ws: List<&2, U32>, +s: U32, +mb: U32, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  match ws:
    case Nil{}:
      st
    case Con{+w, r}:
      hf.fill(r, (s + 1 : U32), mb, hf.one(U32.is_zero(w), st, s, w, mb))

def hf.tab(st: Array<U32> & Array<U32>) -> Array<U32>:
  (sa, t) = st
  t

def hf.sa(st: Array<U32> & Array<U32> & U32) -> Array<U32>:
  (c, sa, acc) = st
  sa

# The last weight completes the sum to a power of two; that power is the maximum code length.
type Hu is Type:
  Hu{t: Array<U32>, mb: U32, ok: Bool}

def hf.build(+ws: List<&2, U32>, t: Array<U32>) -> Hu:
  +total = hf.sum(ws, 0)
  +mb = (hib(total) + 1 : U32)
  +left = (U32.shln(1, bits(mb)) - total : U32)
  +lw = (hib(left) + 1 : U32)
  +all = List.append(&2, U32, ws, [lw])
  +ok = Bool.and(Bool.and(U32.is_lt(0, total), U32.is_le(mb, 11)), U32.is_eq(left, U32.shln(1, bits(hib(left)))))
  Hu{hf.tab(hf.fill(all, 0, mb, (hf.sa(hf.starts(12n, 1, (hf.cnt(all, Array.new(U32, 4n, 0)), Array.new(U32, 4n, 0), 0))), t))), mb, ok}

# Huffman streams: k symbols each, read by peeking mb bits.
type Hd is Type:
  Hd{r: Rd, t: Array<U32>, acc: List<&2, U32>}

def hd.of(tv: Array<U32> & U32, r: Rd, acc: List<&2, U32>) -> Hd:
  (t, +e) = tv
  Hd{rd.skip(r, U32.shrn(e, 8n)), t, Con{U32.and(e, 255), acc}}

def hd.pk(rv: Rd & U32, t: Array<U32>, acc: List<&2, U32>) -> Hd:
  (r, +v) = rv
  hd.of(Array.get(U32, t, v), r, acc)

def hd.go(k: Nat, +mb: U32, st: Hd) -> Hd:
  match k:
    case 0n:
      st
    case 1n+f:
      Hd{r, t, acc} = st
      hd.go(f, mb, hd.pk(rd.peek(r, mb), t, acc))

def hd.fin.of(ab: Array<U32> & Bool, t: Array<U32>, acc: List<&2, U32>) -> Array<U32> & Array<U32> & List<&2, U32> & Bool:
  (a, ok) = ab
  (a, t, acc, ok)

# One stream over bytes s..e; answers the input, the table, the symbols so far (reversed), and whether the stream was used up exactly.
def hd.fin(st: Hd) -> Array<U32> & Array<U32> & List<&2, U32> & Bool:
  Hd{r, t, acc} = st
  hd.fin.of(rd.close(r), t, acc)

def hd.stream(a: Array<U32>, t: Array<U32>, +mb: U32, +s: U32, +e: U32, +k: U32, acc: List<&2, U32>) -> Array<U32> & Array<U32> & List<&2, U32> & Bool:
  hd.fin(hd.go(bits(k), mb, Hd{rd.init(a, s, e), t, acc}))

type Hs is Type:
  Hs{a: Array<U32>, t: Array<U32>, acc: List<&2, U32>, ok: Bool}

def hs.of(r: Array<U32> & Array<U32> & List<&2, U32> & Bool, +ok0: Bool) -> Hs:
  (a, t, acc, ok) = r
  Hs{a, t, acc, Bool.and(ok0, ok)}

def hs.next(st: Hs, +mb: U32, +s: U32, +e: U32, +k: U32) -> Hs:
  Hs{a, t, acc, ok} = st
  hs.of(hd.stream(a, t, mb, s, e, k, acc), ok)

def hs.four2(jv: Array<U32> & U32, t: Array<U32>, +mb: U32, +s: U32, +e: U32, +regen: U32, +z1: U32, +z2: U32, +k: U32) -> Hs:
  (a, +z3) = jv
  +b1 = (s + 6 : U32)
  +b2 = (b1 + z1 : U32)
  +b3 = (b2 + z2 : U32)
  +b4 = (b3 + z3 : U32)
  +ok = Bool.and(U32.is_le(b4, e), U32.is_le((3 * k : U32), regen))
  hs.next(hs.next(hs.next(hs.next(Hs{a, t, Nil{}, ok}, mb, b1, b2, k), mb, b2, b3, k), mb, b3, b4, k), mb, b4, e, (regen - 3 * k : U32))

def hs.four(jv: Array<U32> & U32, t: Array<U32>, +mb: U32, +s: U32, +e: U32, +regen: U32) -> Hs:
  (a, +j) = jv
  +z1 = U32.and(j, 65535)
  +z2 = U32.shrn(j, 16n)
  +k = U32.shrn((regen + 3 : U32), 2n)
  hs.four2(le(a, (s + 4 : U32), 2n), t, mb, s, e, regen, z1, z2, k)

def hs.streams(+four: Bool, a: Array<U32>, t: Array<U32>, +mb: U32, +s: U32, +e: U32, +regen: U32) -> Hs:
  match four:
    case True{}:
      hs.four(le(a, s, 4n), t, mb, s, e, regen)
    case False{}:
      hs.next(Hs{a, t, Nil{}, True{}}, mb, s, e, regen)

# Literals section (§3.1.1.3.1).
type Ls is Data:
  Ls{lits: List<&2, U32>, next: U32}

def lit.raw.of(av: Array<U32> & U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (a, +c) = av
  (a, Con{c, acc})

def lit.raw.go(k: Nat, st: Array<U32> & List<&2, U32>, +i: U32) -> Array<U32> & List<&2, U32>:
  match k:
    case 0n:
      st
    case 1n+f:
      (a, acc) = st
      lit.raw.go(f, lit.raw.of(Array.get(U32, a, i), acc), (i + 1 : U32))

def lit.rev(st: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (a, acc) = st
  (a, List.reverse(&2, U32, acc))

def lit.raw(k: Nat, a: Array<U32>, +i: U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  lit.rev(lit.raw.go(k, (a, acc), i))

def lit.bs(al: Array<U32> & List<&2, U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +next: U32, +e: U32) -> Bs & Ls:
  (a, lits) = al
  (bs.check(Bs{a, tb, o, r1, r2, r3, win, False{}}, U32.is_le(next, e)), Ls{lits, next})

def lit.rle(av: Array<U32> & U32, +regen: U32) -> Array<U32> & List<&2, U32>:
  (a, +c) = av
  (a, rep(bits(regen), c, Nil{}))

# Raw and RLE headers: sf is Size_Format.
def lit.hs(+sf: U32) -> U32:
  Bool.pick(U32, U32.is_eq(sf, 1), 2, Bool.pick(U32, U32.is_eq(sf, 3), 3, 1))

def lit.plain.go(+rle: Bool, a: Array<U32>, +p: U32, +hs: U32, +regen: U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +e: U32) -> Bs & Ls:
  match rle:
    case True{}:
      lit.bs(lit.rle(Array.get(U32, a, (p + hs : U32)), regen), tb, o, r1, r2, r3, win, (p + hs + 1 : U32), e)
    case False{}:
      lit.bs(lit.raw(bits(regen), a, (p + hs : U32), Nil{}), tb, o, r1, r2, r3, win, (p + hs + regen : U32), e)

def lit.plain(hv: Array<U32> & U32, +p: U32, +sf: U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +e: U32, +rle: Bool) -> Bs & Ls:
  (a, +h) = hv
  +hs = lit.hs(sf)
  lit.plain.go(rle, a, p, hs, Bool.pick(U32, U32.is_eq(hs, 1), U32.shrn(U32.and(h, 255), 3n), U32.shrn(U32.and(h, mask((8 * hs : U32))), 4n)), tb, o, r1, r2, r3, win, e)

def slen.u(xs: List<&2, U32>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      slen.u(t, (n + 1 : U32))

# Huffman literals: the table is new (Compressed) or kept (Treeless).
def lit.huf.done(st: Hs, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +next: U32, +e: U32, +mb: U32, +regen: U32, +ok0: Bool) -> Bs & Ls:
  Hs{a, t, acc, +ok} = st
  Tb{huf, hmb, hok, ll, lla, of, ofa, ml, mla, sok} = tb
  +lits = List.reverse(&2, U32, acc)
  (bs.check(Bs{a, Tb{t, mb, True{}, ll, lla, of, ofa, ml, mla, sok}, o, r1, r2, r3, win, False{}}, Bool.and(Bool.and(ok0, ok), Bool.and(U32.is_le(next, e), U32.is_eq(slen.u(lits, 0), regen)))), Ls{lits, next})

def lit.huf.go(+ok: Bool, a: Array<U32>, t: Array<U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +four: Bool, +mb: U32, +s: U32, +next: U32, +e: U32, +regen: U32) -> Bs & Ls:
  match ok:
    case True{}:
      lit.huf.done(hs.streams(four, a, t, mb, s, next, regen), tb, o, r1, r2, r3, win, next, e, mb, regen, True{})
    case False{}:
      lit.huf.done(Hs{a, t, Nil{}, False{}}, tb, o, r1, r2, r3, win, next, e, mb, regen, False{})

def lit.new.hu(hu: Hu, +wok: Bool, a: Array<U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +four: Bool, +hsz: U32, +q: U32, +next: U32, +e: U32, +regen: U32) -> Bs & Ls:
  Hu{t, +mb, +ok} = hu
  lit.huf.go(Bool.and(Bool.and(wok, ok), U32.is_le((q + hsz : U32), next)), a, t, tb, o, r1, r2, r3, win, four, mb, (q + hsz : U32), next, e, regen)

def lit.new.of(r: Array<U32> & List<&2, U32> & Bool, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +four: Bool, +hsz: U32, +q: U32, +next: U32, +e: U32, +regen: U32) -> Bs & Ls:
  (a, ws, wok) = r
  Tb{huf, hmb, hok, ll, lla, of, ofa, ml, mla, sok} = tb
  lit.new.hu(hf.build(ws, huf), wok, a, Tb{Array.new(U32, 0n, 0), hmb, hok, ll, lla, of, ofa, ml, mla, sok}, o, r1, r2, r3, win, four, hsz, q, next, e, regen)

def lit.hb(av: Array<U32> & U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +four: Bool, +q: U32, +next: U32, +e: U32, +regen: U32) -> Bs & Ls:
  (a, +hb) = av
  lit.new.of(hw.read.of((a, hb), q), tb, o, r1, r2, r3, win, four, hw.size(hb), q, next, e, regen)

def lit.old(a: Array<U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +four: Bool, +q: U32, +next: U32, +e: U32, +regen: U32) -> Bs & Ls:
  Tb{huf, +hmb, +hok, ll, lla, of, ofa, ml, mla, sok} = tb
  lit.huf.go(hok, a, huf, Tb{Array.new(U32, 0n, 0), hmb, hok, ll, lla, of, ofa, ml, mla, sok}, o, r1, r2, r3, win, four, hmb, q, next, e, regen)

def lit.fresh(+fresh: Bool, a: Array<U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +four: Bool, +q: U32, +next: U32, +e: U32, +regen: U32) -> Bs & Ls:
  match fresh:
    case True{}:
      lit.hb(Array.get(U32, a, q), tb, o, r1, r2, r3, win, four, q, next, e, regen)
    case False{}:
      lit.old(a, tb, o, r1, r2, r3, win, four, q, next, e, regen)

def lit.sizes2(cv: Array<U32> & U32, +p: U32, +sf: U32, +hs: U32, +regen: U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +e: U32, +fresh: Bool) -> Bs & Ls:
  (a, +comp) = cv
  +q = (p + hs : U32)
  lit.fresh(fresh, a, tb, o, r1, r2, r3, win, Bool.not(U32.is_zero(sf)), q, (q + comp : U32), e, regen)

def lit.sizes(+fresh: Bool, rv: Array<U32> & U32, +p: U32, +sf: U32, +hs: U32, +n: U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +e: U32) -> Bs & Ls:
  (a, +regen) = rv
  lit.sizes2(fb(a, (p * 8 + 4 + n : U32), n), p, sf, hs, regen, tb, o, r1, r2, r3, win, e, fresh)

def lit.coded(+fresh: Bool, hv: Array<U32> & U32, +p: U32, +sf: U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +e: U32) -> Bs & Ls:
  (a, +h) = hv
  +hs = Bool.pick(U32, U32.is_lt(sf, 2), 3, (sf + 2 : U32))
  +n = Bool.pick(U32, U32.is_lt(sf, 2), 10, (sf * 4 + 6 : U32))
  lit.sizes(fresh, fb(a, (p * 8 + 4 : U32), n), p, sf, hs, n, tb, o, r1, r2, r3, win, e)

def lit.kind(+lt: U32, hv: Array<U32> & U32, +p: U32, +sf: U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +e: U32, +plain: Bool) -> Bs & Ls:
  match plain:
    case True{}:
      lit.plain(hv, p, sf, tb, o, r1, r2, r3, win, e, U32.is_eq(lt, 1))
    case False{}:
      lit.coded(U32.is_eq(lt, 2), hv, p, sf, tb, o, r1, r2, r3, win, e)

def lit.head(hv: Array<U32> & U32, +p: U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +e: U32) -> Bs & Ls:
  (a, +h) = hv
  +lt = U32.and(h, 3)
  lit.kind(lt, (a, h), p, U32.and(U32.shrn(h, 2n), 3), tb, o, r1, r2, r3, win, e, U32.is_lt(lt, 2))

def lit.sec(st: Bs, +p: U32, +e: U32) -> Bs & Ls:
  Bs{a, tb, o, +r1, +r2, +r3, +win, bad} = st
  lit.head(le(a, p, 3n), p, tb, o, r1, r2, r3, win, e)

# Sequences (§3.1.1.3.2): literal length, offset value, match length.
type Sq is Data:
  Sq{ll: U32, ofv: U32, ml: U32}

type Sd is Type:
  Sd{r: Rd, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, sl: U32, so: U32, sm: U32, acc: List<&2, Sq>}

def sd.st(rv: Rd & U32, +e: U32) -> Rd & U32:
  (r, +v) = rv
  (r, (U32.shrn(e, 16n) + v : U32))

# Next state: Baseline plus Number_of_Bits read.
def sd.upd(r: Rd, +e: U32) -> Rd & U32:
  sd.st(rd.bits(r, U32.and(U32.shrn(e, 8n), 31)), e)

type Sx is Type:
  Sx{r: Rd, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, el: U32, eo: U32, em: U32, acc: List<&2, Sq>}

def sx.m(tv: Array<U32> & U32, r: Rd, ll: Array<U32>, of: Array<U32>, +el: U32, +eo: U32, acc: List<&2, Sq>) -> Sx:
  (ml, +em) = tv
  Sx{r, ll, of, ml, el, eo, em, acc}

def sx.o(tv: Array<U32> & U32, r: Rd, ll: Array<U32>, ml: Array<U32>, +sm: U32, +el: U32, acc: List<&2, Sq>) -> Sx:
  (of, +eo) = tv
  sx.m(Array.get(U32, ml, sm), r, ll, of, el, eo, acc)

def sx.l(tv: Array<U32> & U32, r: Rd, of: Array<U32>, ml: Array<U32>, +so: U32, +sm: U32, acc: List<&2, Sq>) -> Sx:
  (ll, +el) = tv
  sx.o(Array.get(U32, of, so), r, ll, ml, sm, el, acc)

# Extra bits: offset, then match length, then literal length.
def sv.ll(rv: Rd & U32, +ofv: U32, +mlv: U32, +lc: U32) -> Rd & Sq:
  (r, +x) = rv
  (r, Sq{(nth(ll.base(), lc) + x : U32), ofv, mlv})

def sv.ml(rv: Rd & U32, +ofv: U32, +mc: U32, +lc: U32) -> Rd & Sq:
  (r, +x) = rv
  sv.ll(rd.bits(r, nth(ll.extra(), lc)), ofv, (nth(ml.base(), mc) + x : U32), lc)

def sv.of(rv: Rd & U32, +oc: U32, +mc: U32, +lc: U32) -> Rd & Sq:
  (r, +x) = rv
  sv.ml(rd.bits(r, nth(ml.extra(), mc)), (U32.shln(1, bits(oc)) + x : U32), mc, lc)

def sv.read(r: Rd, +oc: U32, +mc: U32, +lc: U32) -> Rd & Sq:
  sv.of(rd.big(r, oc), oc, mc, lc)

# States update in the order literal length, match length, offset.
def su.o(rv: Rd & U32, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, +sl: U32, +sm: U32, acc: List<&2, Sq>) -> Sd:
  (r, +so) = rv
  Sd{r, ll, of, ml, sl, so, sm, acc}

def su.m(rv: Rd & U32, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, +sl: U32, +eo: U32, acc: List<&2, Sq>) -> Sd:
  (r, +sm) = rv
  su.o(sd.upd(r, eo), ll, of, ml, sl, sm, acc)

def su.l(rv: Rd & U32, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, +em: U32, +eo: U32, acc: List<&2, Sq>) -> Sd:
  (r, +sl) = rv
  su.m(sd.upd(r, em), ll, of, ml, sl, eo, acc)

def sd.after(rq: Rd & Sq, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, +el: U32, +eo: U32, +em: U32, acc: List<&2, Sq>, +last: Bool) -> Sd:
  (r, q) = rq
  match last:
    case True{}:
      Sd{r, ll, of, ml, 0, 0, 0, Con{q, acc}}
    case False{}:
      su.l(sd.upd(r, el), ll, of, ml, em, eo, Con{q, acc})

def sd.one(+last: Bool, x: Sx) -> Sd:
  Sx{r, ll, of, ml, +el, +eo, +em, acc} = x
  sd.after(sv.read(r, U32.and(eo, 255), U32.and(em, 255), U32.and(el, 255)), ll, of, ml, el, eo, em, acc, last)

def sd.go(k: Nat, +left: U32, st: Sd) -> Sd:
  match k:
    case 0n:
      st
    case 1n+f:
      Sd{r, ll, of, ml, +sl, +so, +sm, acc} = st
      sd.go(f, (left - 1 : U32), sd.one(U32.is_eq(left, 1), sx.l(Array.get(U32, ll, sl), r, of, ml, so, sm, acc)))

# Sequence execution (§3.1.1.4, §3.1.1.5).
type Ex is Type:
  Ex{o: Zo, lits: List<&2, U32>, r1: U32, r2: U32, r3: U32, win: U32, bad: Bool}

def ex.take(k: Nat, o: Zo, lits: List<&2, U32>, +bad: Bool) -> Zo & List<&2, U32> & Bool:
  match k:
    case 0n:
      (o, lits, bad)
    case 1n+f:
      match lits:
        case Nil{}:
          (o, Nil{}, True{})
        case Con{+c, t}:
          ex.take(f, zo.put(o, c), t, bad)

def ex.match(+ok: Bool, o: Zo, +ml: U32, +off: U32) -> Zo:
  match ok:
    case True{}:
      zo.copy(bits(ml), o, off)
    case False{}:
      o

def ex.fin(o: Zo, lits: List<&2, U32>, +ml: U32, +off: U32, +r2: U32, +r3: U32, +win: U32, +bad: Bool) -> Ex:
  Zo{w, +n, racc} = o
  +ok = Bool.and(Bool.and(U32.is_lt(0, off), U32.is_le(off, n)), Bool.and(U32.is_le(off, win), Bool.not(bad)))
  Ex{ex.match(ok, Zo{w, n, racc}, ml, off), lits, off, r2, r3, win, Bool.not(ok)}

def ex.lit(r: Zo & List<&2, U32> & Bool, +ml: U32, +off: U32, +r2: U32, +r3: U32, +win: U32) -> Ex:
  (o, lits, bad) = r
  ex.fin(o, lits, ml, off, r2, r3, win, bad)

def ex.one(+q: Sq, st: Ex) -> Ex:
  Sq{+ll, +ofv, +ml} = q
  Ex{o, lits, +r1, +r2, +r3, +win, bad} = st
  +big = U32.is_lt(3, ofv)
  +idx = (ofv - 1 + Bool.pick(U32, U32.is_zero(ll), 1, 0) : U32)
  +off = Bool.pick(U32, big, (ofv - 3 : U32), Bool.pick(U32, U32.is_zero(idx), r1, Bool.pick(U32, U32.is_eq(idx, 1), r2, Bool.pick(U32, U32.is_eq(idx, 2), r3, (r1 - 1 : U32)))))
  +n2 = Bool.pick(U32, big, r1, Bool.pick(U32, U32.is_zero(idx), r2, r1))
  +n3 = Bool.pick(U32, big, r2, Bool.pick(U32, U32.is_lt(idx, 2), r3, r2))
  ex.lit(ex.take(bits(ll), o, lits, bad), ml, off, n2, n3, win)

def ex.go(qs: List<&2, Sq>, st: Ex) -> Ex:
  match qs:
    case Nil{}:
      st
    case Con{+q, t}:
      ex.go(t, ex.one(q, st))

# Sequence tables: Predefined, RLE, FSE_Compressed, or Repeat (Symbol_Compression_Modes).
type Tm is Type:
  Tm{a: Array<U32>, t: Array<U32>, al: U32, next: U32, ok: Bool}

def tm.fse.of(av: Array<U32> & Fd, old: Array<U32>) -> Tm:
  (a, fd) = av
  Fd{+al, cs, +next, +ok} = fd
  Tm{a, ft.build(al, cs), al, next, ok}

def tm.rle.of(av: Array<U32> & U32, +i: U32) -> Tm:
  (a, +s) = av
  Tm{a, ft.rle(s), 0, (i + 1 : U32), True{}}

def tm.m2(+on: Bool, a: Array<U32>, old: Array<U32>, +oal: U32, +sok: Bool, +i: U32, +mal: U32, +ms: U32) -> Tm:
  match on:
    case True{}:
      tm.fse.of(fd.read(a, i, mal, ms), old)
    case False{}:
      Tm{a, old, oal, i, sok}

def tm.m1(+on: Bool, +mode: U32, a: Array<U32>, old: Array<U32>, +oal: U32, +sok: Bool, +i: U32, +mal: U32, +ms: U32) -> Tm:
  match on:
    case True{}:
      tm.rle.of(Array.get(U32, a, i), i)
    case False{}:
      tm.m2(U32.is_eq(mode, 2), a, old, oal, sok, i, mal, ms)

def tm.m0(+on: Bool, +mode: U32, a: Array<U32>, old: Array<U32>, +oal: U32, +sok: Bool, +i: U32, +dal: U32, +mal: U32, +ms: U32, +dist: List<&2, U32>) -> Tm:
  match on:
    case True{}:
      Tm{a, ft.build(dal, dist), dal, i, True{}}
    case False{}:
      tm.m1(U32.is_eq(mode, 1), mode, a, old, oal, sok, i, mal, ms)

# dal: default accuracy log; mal: the largest allowed; ms: the largest symbol.
def tm.read(+mode: U32, a: Array<U32>, old: Array<U32>, +oal: U32, +sok: Bool, +i: U32, +dal: U32, +mal: U32, +ms: U32, +dist: List<&2, U32>) -> Tm:
  tm.m0(U32.is_zero(mode), mode, a, old, oal, sok, i, dal, mal, ms, dist)

type Ts is Type:
  Ts{a: Array<U32>, tb: Tb, next: U32, ok: Bool}

def ts.ml(m: Tm, huf: Array<U32>, +hmb: U32, +hok: Bool, ll: Array<U32>, +lla: U32, of: Array<U32>, +ofa: U32, +ok: Bool) -> Ts:
  Tm{a, ml, +mla, +next, mok} = m
  Ts{a, Tb{huf, hmb, hok, ll, lla, of, ofa, ml, mla, True{}}, next, Bool.and(ok, mok)}

def ts.of(m: Tm, +mode: U32, huf: Array<U32>, +hmb: U32, +hok: Bool, ll: Array<U32>, +lla: U32, ml: Array<U32>, +mla: U32, +sok: Bool, +ok: Bool) -> Ts:
  Tm{a, of, +ofa, +next, mok} = m
  ts.ml(tm.read(U32.and(U32.shrn(mode, 2n), 3), a, ml, mla, sok, next, 6, 9, 52, ml.dist()), huf, hmb, hok, ll, lla, of, ofa, Bool.and(ok, mok))

def ts.ll(m: Tm, +mode: U32, huf: Array<U32>, +hmb: U32, +hok: Bool, of: Array<U32>, +ofa: U32, ml: Array<U32>, +mla: U32, +sok: Bool) -> Ts:
  Tm{a, ll, +lla, +next, ok} = m
  ts.of(tm.read(U32.and(U32.shrn(mode, 4n), 3), a, of, ofa, sok, next, 5, 8, 31, of.dist()), mode, huf, hmb, hok, ll, lla, ml, mla, sok, ok)

def ts.read(a: Array<U32>, tb: Tb, +mode: U32, +i: U32) -> Ts:
  Tb{huf, +hmb, hok, ll, +lla, of, +ofa, ml, +mla, +sok} = tb
  ts.ll(tm.read(U32.shrn(mode, 6n), a, ll, lla, sok, i, 6, 9, 35, ll.dist()), mode, huf, hmb, hok, of, ofa, ml, mla, sok)

# Initial states: literal length, then offset, then match length.
def si.m(rv: Rd & U32, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, +sl: U32, +so: U32) -> Sd:
  (r, +sm) = rv
  Sd{r, ll, of, ml, sl, so, sm, Nil{}}

def si.o(rv: Rd & U32, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, +sl: U32, +mla: U32) -> Sd:
  (r, +so) = rv
  si.m(rd.bits(r, mla), ll, of, ml, sl, so)

def si.l(rv: Rd & U32, ll: Array<U32>, of: Array<U32>, ml: Array<U32>, +ofa: U32, +mla: U32) -> Sd:
  (r, +sl) = rv
  si.o(rd.bits(r, ofa), ll, of, ml, sl, mla)

def sq.exec(ab: Array<U32> & Bool, tb: Tb, x: Ex, +ok: Bool) -> Bs:
  (a, rok) = ab
  Ex{o, lits, +r1, +r2, +r3, +win, +bad} = x
  Bs{a, tb, zo.lits(lits, o), r1, r2, r3, win, Bool.or(bad, Bool.not(Bool.and(ok, rok)))}

def sq.done(st: Sd, huf: Array<U32>, +hmb: U32, +hok: Bool, +lla: U32, +ofa: U32, +mla: U32, o: Zo, lits: List<&2, U32>, +r1: U32, +r2: U32, +r3: U32, +win: U32, +ok: Bool) -> Bs:
  Sd{r, ll, of, ml, sl, so, sm, acc} = st
  sq.exec(rd.close(r), Tb{huf, hmb, hok, ll, lla, of, ofa, ml, mla, True{}}, ex.go(List.reverse(&2, Sq, acc), Ex{o, lits, r1, r2, r3, win, False{}}), ok)

def sq.run(ts: Ts, +nseq: U32, +e: U32, o: Zo, lits: List<&2, U32>, +r1: U32, +r2: U32, +r3: U32, +win: U32) -> Bs:
  Ts{a, tb, +next, +ok} = ts
  Tb{huf, +hmb, hok, ll, +lla, of, +ofa, ml, +mla, sok} = tb
  sq.done(sd.go(bits(nseq), nseq, si.l(rd.bits(rd.init(a, next, e), lla), ll, of, ml, ofa, mla)), huf, hmb, hok, lla, ofa, mla, o, lits, r1, r2, r3, win, Bool.and(ok, U32.is_lt(next, e)))

def sq.checked(+ok: Bool, a: Array<U32>, tb: Tb, +m: U32, +nseq: U32, +i: U32, +e: U32, o: Zo, lits: List<&2, U32>, +r1: U32, +r2: U32, +r3: U32, +win: U32) -> Bs:
  match ok:
    case True{}:
      sq.run(ts.read(a, tb, m, (i + 1 : U32)), nseq, e, o, lits, r1, r2, r3, win)
    case False{}:
      Bs{a, tb, o, r1, r2, r3, win, True{}}

def sq.modes(mv: Array<U32> & U32, tb: Tb, +nseq: U32, +i: U32, +e: U32, o: Zo, lits: List<&2, U32>, +r1: U32, +r2: U32, +r3: U32, +win: U32) -> Bs:
  (a, +m) = mv
  sq.checked(U32.is_zero(U32.and(m, 3)), a, tb, m, nseq, i, e, o, lits, r1, r2, r3, win)

def sq.some(+none: Bool, a: Array<U32>, tb: Tb, +nseq: U32, +i: U32, +e: U32, o: Zo, lits: List<&2, U32>, +r1: U32, +r2: U32, +r3: U32, +win: U32) -> Bs:
  match none:
    case True{}:
      Bs{a, tb, zo.lits(lits, o), r1, r2, r3, win, Bool.not(U32.is_eq(i, e))}
    case False{}:
      sq.modes(Array.get(U32, a, i), tb, nseq, i, e, o, lits, r1, r2, r3, win)

# Number_of_Sequences: 1, 2, or 3 bytes.
def sq.count(hv: Array<U32> & U32, tb: Tb, +p: U32, +e: U32, o: Zo, lits: List<&2, U32>, +r1: U32, +r2: U32, +r3: U32, +win: U32) -> Bs:
  (a, +h) = hv
  +b0 = U32.and(h, 255)
  +b1 = U32.and(U32.shrn(h, 8n), 255)
  +b2 = U32.and(U32.shrn(h, 16n), 255)
  +nseq = Bool.pick(U32, U32.is_lt(b0, 128), b0, Bool.pick(U32, U32.is_lt(b0, 255), (U32.shln((b0 - 128 : U32), 8n) + b1 : U32), (b1 + U32.shln(b2, 8n) + 32512 : U32)))
  +hs = Bool.pick(U32, U32.is_lt(b0, 128), 1, Bool.pick(U32, U32.is_lt(b0, 255), 2, 3))
  sq.some(U32.is_zero(nseq), a, tb, nseq, (p + hs : U32), e, o, lits, r1, r2, r3, win)

def sq.bad(+bad: Bool, a: Array<U32>, tb: Tb, o: Zo, lits: List<&2, U32>, +next: U32, +e: U32, +r1: U32, +r2: U32, +r3: U32, +win: U32) -> Bs:
  match bad:
    case True{}:
      Bs{a, tb, o, r1, r2, r3, win, True{}}
    case False{}:
      sq.count(le(a, next, 3n), tb, next, e, o, lits, r1, r2, r3, win)

def sq.sec(bl: Bs & Ls, +e: U32) -> Bs:
  (st, ls) = bl
  Bs{a, tb, o, +r1, +r2, +r3, +win, +bad} = st
  Ls{lits, +next} = ls
  sq.bad(bad, a, tb, o, lits, next, e, r1, r2, r3, win)

# Blocks (§3.1.1.2): Raw, RLE, or Compressed.
def blk.raw.of(av: Array<U32> & U32, o: Zo) -> Array<U32> & Zo:
  (a, +c) = av
  (a, zo.put(o, c))

def blk.raw(k: Nat, st: Array<U32> & Zo, +i: U32) -> Array<U32> & Zo:
  match k:
    case 0n:
      st
    case 1n+f:
      (a, o) = st
      blk.raw(f, blk.raw.of(Array.get(U32, a, i), o), (i + 1 : U32))

def blk.rle.of(av: Array<U32> & U32, o: Zo, +k: U32) -> Array<U32> & Zo:
  (a, +c) = av
  (a, zo.lits(rep(bits(k), c, Nil{}), o))

def blk.pack(ao: Array<U32> & Zo, tb: Tb, +r1: U32, +r2: U32, +r3: U32, +win: U32, +ok: Bool) -> Bs:
  (a, o) = ao
  Bs{a, tb, o, r1, r2, r3, win, Bool.not(ok)}

def blk.t2(+on: Bool, a: Array<U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +p: U32, +size: U32, +n: U32) -> Bs:
  match on:
    case True{}:
      +e = (p + size : U32)
      bs.check(sq.sec(lit.sec(Bs{a, tb, o, r1, r2, r3, win, False{}}, p, e), e), Bool.and(U32.is_le(e, n), U32.is_le(size, 131072)))
    case False{}:
      Bs{a, tb, o, r1, r2, r3, win, True{}}

def blk.t1(+on: Bool, +bt: U32, a: Array<U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +p: U32, +size: U32, +n: U32) -> Bs:
  match on:
    case True{}:
      blk.pack(blk.rle.of(Array.get(U32, a, p), o, size), tb, r1, r2, r3, win, U32.is_lt(p, n))
    case False{}:
      blk.t2(U32.is_eq(bt, 2), a, tb, o, r1, r2, r3, win, p, size, n)

def blk.t0(+on: Bool, +bt: U32, a: Array<U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +p: U32, +size: U32, +n: U32) -> Bs:
  match on:
    case True{}:
      blk.pack(blk.raw(bits(size), (a, o), p), tb, r1, r2, r3, win, U32.is_le((p + size : U32), n))
    case False{}:
      blk.t1(U32.is_eq(bt, 1), bt, a, tb, o, r1, r2, r3, win, p, size, n)

def blk.body(+bt: U32, st: Bs, +p: U32, +size: U32, +n: U32) -> Bs:
  Bs{a, tb, o, +r1, +r2, +r3, +win, bad} = st
  blk.t0(U32.is_zero(bt), bt, a, tb, o, r1, r2, r3, win, p, size, n)

# Frame state: the block state, the next block's position, and whether the last block is done.
type Fs is Type:
  Fs{st: Bs, p: U32, last: Bool}

def fs.blk(hv: Array<U32> & U32, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +p: U32, +n: U32) -> Fs:
  (a, +h) = hv
  +bt = U32.and(U32.shrn(h, 1n), 3)
  +size = U32.shrn(h, 3n)
  +q = (p + 3 : U32)
  Fs{blk.body(bt, Bs{a, tb, o, r1, r2, r3, win, False{}}, q, size, n), (q + Bool.pick(U32, U32.is_eq(bt, 1), 1, size) : U32), U32.is_eq(U32.and(h, 1), 1)}

def fs.more(a: Array<U32>, tb: Tb, o: Zo, +r1: U32, +r2: U32, +r3: U32, +win: U32, +p: U32, +n: U32, +last: Bool, +bad: Bool, +stop: Bool) -> Fs:
  match stop:
    case True{}:
      Fs{Bs{a, tb, o, r1, r2, r3, win, bad}, p, last}
    case False{}:
      fs.blk(le(a, p, 3n), tb, o, r1, r2, r3, win, p, n)

def fs.go(k: Nat, +n: U32, st: Fs) -> Fs:
  match k:
    case 0n:
      st
    case 1n+f:
      Fs{bs, +p, +last} = st
      Bs{a, tb, o, +r1, +r2, +r3, +win, +bad} = bs
      fs.go(f, n, fs.more(a, tb, o, r1, r2, r3, win, p, n, last, bad, Bool.or(last, bad)))

# XXH64 (seed 0) over 64-bit words as hi and lo halves; a frame's Content_Checksum is its low 32 bits.
type W is Data:
  W{hi: U32, lo: U32}

def w.add(a: W, b: W) -> W:
  W{+ah, +al} = a
  W{+bh, +bl} = b
  +lo = (al + bl : U32)
  W{(ah + bh + Bool.pick(U32, U32.is_lt(lo, al), 1, 0) : U32), lo}

def w.xor(a: W, b: W) -> W:
  W{+ah, +al} = a
  W{+bh, +bl} = b
  W{U32.xor(ah, bh), U32.xor(al, bl)}

# The full 64-bit product of two 32-bit words, from 16-bit halves.
def w.m32(+a: U32, +b: U32) -> W:
  +a0 = U32.and(a, 65535)
  +a1 = U32.shrn(a, 16n)
  +b0 = U32.and(b, 65535)
  +b1 = U32.shrn(b, 16n)
  +p01 = (a0 * b1 : U32)
  +mid = (p01 + a1 * b0 : U32)
  +p00 = (a0 * b0 : U32)
  +lo = (p00 + U32.shln(mid, 16n) : U32)
  W{(a1 * b1 + U32.shrn(mid, 16n) + Bool.pick(U32, U32.is_lt(mid, p01), 65536, 0) + Bool.pick(U32, U32.is_lt(lo, p00), 1, 0) : U32), lo}

def w.mul.of(p: W, +ah: U32, +al: U32, +bh: U32, +bl: U32) -> W:
  W{+ph, +pl} = p
  W{(ph + al * bh + ah * bl : U32), pl}

def w.mul(a: W, b: W) -> W:
  W{+ah, +al} = a
  W{+bh, +bl} = b
  w.mul.of(w.m32(al, bl), ah, al, bh, bl)

# 0 < r < 32.
def w.rotl(a: W, +r: U32) -> W:
  W{+hi, +lo} = a
  +l = (32 - r : U32)
  W{U32.or(U32.shln(hi, bits(r)), U32.shrn(lo, bits(l))), U32.or(U32.shln(lo, bits(r)), U32.shrn(hi, bits(l)))}

def w.shr29(a: W) -> W:
  W{+hi, +lo} = a
  W{U32.shrn(hi, 29n), U32.or(U32.shrn(lo, 29n), U32.shln(hi, 3n))}

def w.shr32(a: W) -> W:
  W{+hi, lo} = a
  W{0, hi}

def w.shr33(a: W) -> W:
  W{+hi, lo} = a
  W{0, U32.shr(hi)}

def w.lo(+x: W) -> U32:
  W{hi, +lo} = x
  lo

def xx.p1() -> W:
  W{2654435761, 2246822535}

def xx.p2() -> W:
  W{3266489917, 668265295}

def xx.p3() -> W:
  W{374761393, 2654435833}

def xx.p4() -> W:
  W{2246822519, 3266489955}

def xx.p5() -> W:
  W{668265263, 374761413}

def xx.round(acc: W, x: W) -> W:
  w.mul(w.rotl(w.add(acc, w.mul(x, xx.p2())), 31), xx.p1())

def xx.merge(acc: W, +v: W) -> W:
  w.add(w.mul(w.xor(acc, xx.round(W{0, 0}, v)), xx.p1()), xx.p4())

type Xs is Data:
  Xs{v1: W, v2: W, v3: W, v4: W, s: String}

# Little-endian words at the front of s; a short s reads zeros.
def xx.w32(s: String) -> U32 & String:
  match s:
    case SCon{Chr{+a}, SCon{Chr{+b}, SCon{Chr{+c}, SCon{Chr{+d}, t}}}}:
      (U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n))), t)
    case SNil{}:
      (0, SNil{})
    case SCon{x, y}:
      (0, SNil{})

def xx.w64.of(r: U32 & String, +lo: U32) -> W & String:
  (+hi, t) = r
  (W{hi, lo}, t)

def xx.w64.lo(r: U32 & String) -> W & String:
  (+lo, t) = r
  xx.w64.of(xx.w32(t), lo)

def xx.w64(s: String) -> W & String:
  xx.w64.lo(xx.w32(s))

def xx.stripe.d(r: W & String, +v1: W, +v2: W, +v3: W, +v4: W) -> Xs:
  (x, t) = r
  Xs{v1, v2, v3, xx.round(v4, x), t}

def xx.stripe.c(r: W & String, +v1: W, +v2: W, +v3: W, +v4: W) -> Xs:
  (x, t) = r
  xx.stripe.d(xx.w64(t), v1, v2, xx.round(v3, x), v4)

def xx.stripe.b(r: W & String, +v1: W, +v2: W, +v3: W, +v4: W) -> Xs:
  (x, t) = r
  xx.stripe.c(xx.w64(t), v1, xx.round(v2, x), v3, v4)

def xx.stripe.a(r: W & String, +v1: W, +v2: W, +v3: W, +v4: W) -> Xs:
  (x, t) = r
  xx.stripe.b(xx.w64(t), xx.round(v1, x), v2, v3, v4)

def xx.stripe(st: Xs) -> Xs:
  Xs{+v1, +v2, +v3, +v4, s} = st
  xx.stripe.a(xx.w64(s), v1, v2, v3, v4)

def xx.stripes(k: Nat, st: Xs) -> Xs:
  match k:
    case 0n:
      st
    case 1n+f:
      xx.stripes(f, xx.stripe(st))

def xx.big(st: Xs) -> W & String:
  Xs{+v1, +v2, +v3, +v4, s} = st
  +h = w.add(w.add(w.rotl(v1, 1), w.rotl(v2, 7)), w.add(w.rotl(v3, 12), w.rotl(v4, 18)))
  (xx.merge(xx.merge(xx.merge(xx.merge(h, v1), v2), v3), v4), s)

def xx.w8.of(r: W & String, +h: W) -> W & String:
  (x, t) = r
  (w.add(w.mul(w.rotl(w.xor(h, xx.round(W{0, 0}, x)), 27), xx.p1()), xx.p4()), t)

def xx.w8(k: Nat, st: W & String) -> W & String:
  match k:
    case 0n:
      st
    case 1n+f:
      (h, s) = st
      xx.w8(f, xx.w8.of(xx.w64(s), h))

def xx.w4.of(+h: W, r: U32 & String) -> W & String:
  (+x, t) = r
  (w.add(w.mul(w.rotl(w.xor(h, w.mul(W{0, x}, xx.p1())), 23), xx.p2()), xx.p3()), t)

def xx.w4(+on: Bool, +h: W, s: String) -> W & String:
  match on:
    case True{}:
      xx.w4.of(h, xx.w32(s))
    case False{}:
      (h, s)

def xx.b1(s: String, +h: W) -> W:
  match s:
    case SNil{}:
      h
    case SCon{Chr{+c}, t}:
      xx.b1(t, w.mul(w.rotl(w.xor(h, w.mul(W{0, c}, xx.p5())), 11), xx.p1()))

def xx.tail3(r: W & String) -> W:
  (h, s) = r
  +h1 = xx.b1(s, h)
  +h2 = w.mul(w.xor(h1, w.shr33(h1)), xx.p2())
  +h3 = w.mul(w.xor(h2, w.shr29(h2)), xx.p3())
  w.xor(h3, w.shr32(h3))

def xx.tail2(r: W & String, +len: U32) -> W:
  (h, s) = r
  xx.tail3(xx.w4(U32.is_le(4, U32.and(len, 7)), h, s))

def xx.tail(r: W & String, +len: U32) -> W:
  (h, s) = r
  xx.tail2(xx.w8(bits(U32.shrn(U32.and(len, 31), 3n)), (w.add(h, W{0, len}), s)), len)

def xx.head(+big: Bool, +s: String, +len: U32) -> W & String:
  match big:
    case True{}:
      xx.big(xx.stripes(bits(U32.shrn(len, 5n)), Xs{W{1625958382, 2915087830}, xx.p2(), W{0, 0}, W{1640531534, 2048144761}, s}))
    case False{}:
      (xx.p5(), s)

def xxh64(+s: String, +len: U32) -> W:
  xx.tail(xx.head(U32.is_le(32, len), s, len), len)

# Frame header (§3.1.1.1), parsed from the 14 bytes after the magic number.
type Fh is Data:
  Fh{ok: Bool, ck: Bool, has: Bool, fcs: U32, win: U32, len: U32}

def le.list(k: Nat, +bs: List<&2, U32>, +i: U32, +sh: Nat) -> U32:
  match k:
    case 0n:
      0
    case 1n+f:
      U32.or(U32.shln(nth(bs, i), sh), le.list(f, bs, (i + 1 : U32), Nat.add(sh, 8n)))

def fh.parse(+bs: List<&2, U32>) -> Fh:
  +d = nth(bs, 0)
  +fcsf = U32.shrn(d, 6n)
  +ss = U32.is_eq(U32.and(U32.shrn(d, 5n), 1), 1)
  +didf = U32.and(d, 3)
  +wsz = Bool.pick(U32, ss, 0, 1)
  +dsz = Bool.pick(U32, U32.is_eq(didf, 3), 4, didf)
  +fsz = Bool.pick(U32, U32.is_zero(fcsf), Bool.pick(U32, ss, 1, 0), U32.shln(1, bits(fcsf)))
  +fo = (1 + wsz + dsz : U32)
  +raw = le.list(bits(umin(fsz, 4)), bs, fo, 0n)
  +fcs = Bool.pick(U32, U32.is_eq(fsz, 2), (raw + 256 : U32), raw)
  +wd = nth(bs, 1)
  +ex = U32.shrn(wd, 3n)
  +wb = U32.shln(1, bits(U32.and((10 + ex : U32), 31)))
  +win = Bool.pick(U32, ss, fcs, (wb + U32.shrn(wb, 3n) * U32.and(wd, 7) : U32))
  +ok = Bool.and(Bool.and(U32.is_zero(U32.and(d, 8)), U32.is_zero(le.list(bits(dsz), bs, (1 + wsz : U32), 0n))), Bool.and(U32.is_zero(Bool.pick(U32, U32.is_eq(fsz, 8), le.list(4n, bs, (fo + 4 : U32), 0n), 0)), Bool.and(Bool.or(ss, U32.is_le(ex, 13)), U32.is_le(win, 16777216))))
  Fh{ok, U32.is_eq(U32.and(U32.shrn(d, 2n), 1), 1), Bool.not(U32.is_zero(fsz)), fcs, win, (4 + fo + fsz : U32)}

type Fr is Data:
  Fr{out: String, next: U32, ok: Bool}

def fr.sum(cv: Array<U32> & U32, +out: String, +n: U32, +p: U32, +len: U32, +ok: Bool) -> Array<U32> & Fr:
  (a, +c) = cv
  (a, Fr{out, (p + 4 : U32), Bool.and(ok, Bool.and(U32.is_le((p + 4 : U32), len), U32.is_eq(c, w.lo(xxh64(out, n)))))})

def fr.ck(+ck: Bool, a: Array<U32>, +out: String, +n: U32, +p: U32, +len: U32, +ok: Bool) -> Array<U32> & Fr:
  match ck:
    case True{}:
      fr.sum(le(a, p, 4n), out, n, p, len, ok)
    case False{}:
      (a, Fr{out, p, ok})

def fr.end(st: Fs, +h: Fh, +len: U32) -> Array<U32> & Fr:
  Fs{bs, +p, +last} = st
  Bs{a, tb, o, r1, r2, r3, win, +bad} = bs
  Zo{w, +n, racc} = o
  Fh{hok, +ck, +has, +fcs, hwin, hlen} = h
  fr.ck(ck, a, String.reverse(racc), n, p, len, Bool.and(Bool.and(last, Bool.not(bad)), Bool.and(U32.is_le(p, len), Bool.or(Bool.not(has), U32.is_eq(n, fcs)))))

def fh.win(+h: Fh) -> U32:
  Fh{ok, ck, has, fcs, +win, len} = h
  win

def fh.len(+h: Fh) -> U32:
  Fh{ok, ck, has, fcs, win, +len} = h
  len

def fh.ok(+h: Fh) -> Bool:
  Fh{+ok, ck, has, fcs, win, len} = h
  ok

def fr.run(+ok: Bool, a: Array<U32>, +h: Fh, +i: U32, +len: U32) -> Array<U32> & Fr:
  match ok:
    case False{}:
      (a, Fr{"", len, False{}})
    case True{}:
      fr.end(fs.go(bits(len), len, Fs{Bs{a, tb.new(), Zo{Array.new(U32, depth(31n, 0n, fh.win(h)), 0), 0, ""}, 1, 4, 8, fh.win(h), False{}}, (i + fh.len(h) : U32), False{}}), h, len)

def fr.hdr2(a: Array<U32>, +h: Fh, +i: U32, +len: U32) -> Array<U32> & Fr:
  fr.run(Bool.and(fh.ok(h), U32.is_le((i + fh.len(h) : U32), len)), a, h, i, len)

def fr.hdr(al: Array<U32> & List<&2, U32>, +i: U32, +len: U32) -> Array<U32> & Fr:
  (a, bs) = al
  fr.hdr2(a, fh.parse(bs), i, len)

# One frame at i: a Zstandard frame, or a skippable one (§3.1.2), which yields no bytes.
def fr.skip(sv: Array<U32> & U32, +i: U32, +len: U32) -> Array<U32> & Fr:
  (a, +sz) = sv
  +next = (i + 8 + sz : U32)
  (a, Fr{"", next, Bool.and(U32.is_le(next, len), U32.is_le((i + 8 : U32), next))})

def fr.kind2(a: Array<U32>, +i: U32, +len: U32, +zs: Bool, +sk: Bool) -> Array<U32> & Fr:
  match zs:
    case True{}:
      fr.hdr(lit.raw(14n, a, (i + 4 : U32), Nil{}), i, len)
    case False{}:
      match sk:
        case True{}:
          fr.skip(le(a, (i + 4 : U32), 4n), i, len)
        case False{}:
          (a, Fr{"", len, False{}})

def fr.kind(mv: Array<U32> & U32, +i: U32, +len: U32) -> Array<U32> & Fr:
  (a, +m) = mv
  fr.kind2(a, i, len, U32.is_eq(m, 4247762216), U32.is_eq(U32.and(m, 4294967280), 407710288))

def zs.step(r: Array<U32> & Fr, +acc: String, +len: U32) -> Array<U32> & Fr:
  (a, fr) = r
  Fr{+out, +next, +ok} = fr
  (a, Fr{acc ++ out, next, Bool.and(ok, U32.is_le(next, len))})

def zs.more(+on: Bool, a: Array<U32>, +acc: String, +i: U32, +len: U32, +ok: Bool) -> Array<U32> & Fr:
  match on:
    case True{}:
      zs.step(fr.kind(le(a, i, 4n), i, len), acc, len)
    case False{}:
      (a, Fr{acc, i, ok})

# Frames follow one another to the end of the input.
def zs.go(k: Nat, st: Array<U32> & Fr, +len: U32) -> Array<U32> & Fr:
  match k:
    case 0n:
      st
    case 1n+f:
      (a, fr) = st
      Fr{+acc, +i, +ok} = fr
      zs.go(f, zs.more(Bool.and(ok, U32.is_lt(i, len)), a, acc, i, len, ok), len)

def zs.pick(+out: String, +ok: Bool) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{out}
    case False{}:
      None{}

def zs.out(r: Array<U32> & Fr, +len: U32) -> Maybe<&2, String>:
  (a, fr) = r
  Fr{+out, +next, +ok} = fr
  zs.pick(out, Bool.and(ok, U32.is_eq(next, len)))

# Zstandard frames (RFC 8878) to the end of s. None: malformed, cut short, corrupt, a dictionary, or a window over 16 MiB.
def decode(+s: String) -> Maybe<&2, String>:
  +len = slen(s, 0)
  zs.out(zs.go(bits(len), (src.fill(s, 0, Array.new(U32, depth(31n, 0n, (len + 8 : U32)), 0)), Fr{"", 0, U32.is_lt(0, len)}), len), len)
