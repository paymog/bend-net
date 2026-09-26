# DEFLATE, gzip, and zlib encoding and decoding (RFC 1951, 1952, 1950) over byte strings. Source: https://github.com/paymog/bend-kit/tree/main/zlib
import Base

# Bytes are one Char per octet (0..255), as everywhere in bend-kit.

def byte(h: Char) -> U32:
  Chr{c} = h
  c

def bits(+n: U32) -> Nat:
  U32.to_nat(n)

def mask(+n: U32) -> U32:
  (U32.shln(1, bits(n)) - 1 : U32)

# Bit reader. over counts bytes read past the end; any over means the input was cut short.
type Br is Data:
  Br{s: String, buf: U32, cnt: U32, over: U32}

def br.new(s: String) -> Br:
  Br{s, 0, 0, 0}

def br.pull(b: Br) -> Br:
  Br{s, +buf, +cnt, +over} = b
  match s:
    case SNil{}:
      Br{SNil{}, buf, (cnt + 8 : U32), (over + 1 : U32)}
    case SCon{h, t}:
      Br{t, U32.or(buf, U32.shln(byte(h), bits(cnt))), (cnt + 8 : U32), over}

def br.pull.if(b: Br, short: Bool) -> Br:
  match short:
    case True{}:
      br.pull(b)
    case False{}:
      b

def br.short(+b: Br, +n: U32) -> Bool:
  Br{s, buf, +cnt, over} = b
  U32.is_lt(cnt, n)

# n is at most 16, so three bytes always fill the buffer.
def br.fill(fuel: Nat, +b: Br, +n: U32) -> Br:
  match fuel:
    case 0n:
      b
    case 1n+f:
      br.fill(f, br.pull.if(b, br.short(b, n)), n)

def br.cut(b: Br, +n: U32) -> Br & U32:
  Br{s, +buf, cnt, over} = b
  (Br{s, U32.shrn(buf, bits(n)), (cnt - n : U32), over}, U32.and(buf, mask(n)))

def br.take(b: Br, +n: U32) -> Br & U32:
  br.cut(br.fill(3n, b, n), n)

def br.drop.of(r: Br & U32) -> Br:
  (b, v) = r
  b

def br.drop(b: Br, +n: U32) -> Br:
  br.drop.of(br.cut(b, n))

# RFC 1951 §3.2.4: a stored block starts on a byte boundary.
def br.align(+b: Br) -> Br:
  Br{s, buf, +cnt, over} = b
  br.drop(b, U32.mod(cnt, 8))

def br.ok(+b: Br) -> Bool:
  Br{s, buf, cnt, +over} = b
  U32.is_eq(over, 0)

def br.bytes(k: Nat, +buf: U32) -> String:
  match k:
    case 0n:
      SNil{}
    case 1n+p:
      SCon{Chr{U32.and(buf, 255)}, br.bytes(p, U32.shrn(buf, 8n))}

def br.rest.of(b: Br) -> String:
  Br{s, +buf, +cnt, over} = b
  br.bytes(bits(U32.div(cnt, 8)), buf) ++ s

# Whole bytes still in the buffer go back in front of the unread input.
def br.rest(+b: Br) -> String:
  br.rest.of(br.align(b))

# Huffman codes as a trie: one step per bit. A read bit picks o (1) or z (0).
# Bad: two codes collided, so the code set was over-subscribed.
type Ht is Data:
  HtNone{}
  HtBad{}
  HtLeaf{sym: U32}
  HtNode{z: Ht, o: Ht}

def ht.left(t: Ht) -> Ht:
  match t:
    case HtNode{z, o}:
      z
    case HtNone{}:
      HtNone{}
    case HtBad{}:
      HtBad{}
    case HtLeaf{s}:
      HtBad{}

def ht.right(t: Ht) -> Ht:
  match t:
    case HtNode{z, o}:
      o
    case HtNone{}:
      HtNone{}
    case HtBad{}:
      HtBad{}
    case HtLeaf{s}:
      HtBad{}

def ht.leaf(t: Ht, +sym: U32) -> Ht:
  match t:
    case HtNone{}:
      HtLeaf{sym}
    case HtBad{}:
      HtBad{}
    case HtLeaf{s}:
      HtBad{}
    case HtNode{z, o}:
      HtBad{}

def ht.ins(path: List<&2, Bool>, +t: Ht, +sym: U32) -> Ht:
  match path:
    case Nil{}:
      ht.leaf(t, sym)
    case Con{b, rest}:
      match b:
        case True{}:
          HtNode{ht.left(t), ht.ins(rest, ht.right(t), sym)}
        case False{}:
          HtNode{ht.ins(rest, ht.left(t), sym), ht.right(t)}

# The code's bits, most significant first: the order the stream sends them.
def ht.path(n: Nat, +code: U32, acc: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      acc
    case 1n+p:
      ht.path(p, U32.shr(code), Con{U32.is_eq(U32.and(code, 1), 1), acc})

# Canonical codes (RFC 1951 §3.2.2): count lengths, find each length's first code, then assign in symbol order.
def cnt.add(ar: Array<U32> & U32, +len: U32) -> Array<U32>:
  (a, v) = ar
  Array.set(U32, a, len, (v + 1 : U32))

def cnt.go(xs: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{+l, t}:
      cnt.go(t, cnt.add(Array.get(U32, a, l), l))

def nx.set(+i: U32, cv: Array<U32> & U32, n: Array<U32>, +code: U32) -> Array<U32> & Array<U32> & U32:
  (c, v) = cv
  +code2 = U32.shl((code + Bool.pick(U32, U32.is_eq(i, 1), 0, v) : U32))
  (c, Array.set(U32, n, i, code2), code2)

def nx.step(+i: U32, st: Array<U32> & Array<U32> & U32) -> Array<U32> & Array<U32> & U32:
  (c, n, code) = st
  nx.set(i, Array.get(U32, c, (i - 1 : U32)), n, code)

def nx.go(k: Nat, +i: U32, st: Array<U32> & Array<U32> & U32) -> Array<U32> & Array<U32> & U32:
  match k:
    case 0n:
      st
    case 1n+f:
      nx.go(f, (i + 1 : U32), nx.step(i, st))

def as.put(+l: U32, +sym: U32, nv: Array<U32> & U32, t: Ht) -> Array<U32> & Ht:
  (n, +code) = nv
  (Array.set(U32, n, l, (code + 1 : U32)), ht.ins(ht.path(bits(l), code, Nil{}), t, sym))

def as.one.nz(+l: U32, +sym: U32, n: Array<U32>, t: Ht, zero: Bool) -> Array<U32> & Ht:
  match zero:
    case True{}:
      (n, t)
    case False{}:
      as.put(l, sym, Array.get(U32, n, l), t)

def as.one(+l: U32, +sym: U32, st: Array<U32> & Ht) -> Array<U32> & Ht:
  (n, t) = st
  as.one.nz(l, sym, n, t, U32.is_zero(l))

def as.go(xs: List<&2, U32>, +sym: U32, st: Array<U32> & Ht) -> Array<U32> & Ht:
  match xs:
    case Nil{}:
      st
    case Con{+l, t}:
      as.go(t, (sym + 1 : U32), as.one(l, sym, st))

def ht.of(st: Array<U32> & Ht) -> Ht:
  (n, t) = st
  t

def ht.assign(xs: List<&2, U32>, st: Array<U32> & Array<U32> & U32) -> Ht:
  (c, n, code) = st
  ht.of(as.go(xs, 0, (n, HtNone{})))

# lens[i] is the code length of symbol i; 0 means the symbol is unused.
def ht.build(+lens: List<&2, U32>) -> Ht:
  ht.assign(lens, nx.go(15n, 1, (cnt.go(lens, Array.new(U32, 4n, 0)), Array.new(U32, 4n, 0), 0)))

# No code: 9999, never a symbol.
def ht.step(z: Ht, o: Ht, bv: Br & U32) -> Ht & Br:
  (b, +v) = bv
  (Bool.pick(Ht, U32.is_eq(v, 1), o, z), b)

# A code is at most 15 bits (§3.2.7), so 16 steps always reach a leaf or a miss.
def ht.dec(fuel: Nat, st: Ht & Br) -> Br & U32:
  match fuel:
    case 0n:
      (t, b) = st
      (b, 9999)
    case 1n+f:
      (t, b) = st
      match t:
        case HtLeaf{s}:
          (b, s)
        case HtNone{}:
          (b, 9999)
        case HtBad{}:
          (b, 9999)
        case HtNode{z, o}:
          ht.dec(f, ht.step(z, o, br.take(b, 1)))

def ht.decode(t: Ht, b: Br) -> Br & U32:
  ht.dec(16n, (t, b))

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

def drop.n(k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          drop.n(p, t)

# RFC 1951 §3.2.5
def len.base() -> List<&2, U32>:
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

def len.extra() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

def dist.base() -> List<&2, U32>:
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

def dist.extra() -> List<&2, U32>:
  [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

# RFC 1951 §3.2.6
def fixed.llens() -> List<&2, U32>:
  rep(144n, 8, rep(112n, 9, rep(24n, 7, rep(8n, 8, Nil{}))))

def fixed.dlens() -> List<&2, U32>:
  rep(30n, 5, Nil{})

def fixed.lit() -> Ht:
  ht.build(fixed.llens())

def fixed.dist() -> Ht:
  ht.build(fixed.dlens())

# Output: the 32 KiB window (indexes wrap), the write position, the byte count, and the bytes, reversed.
type Ow is Data:
  Ow{w: U32, n: U32, racc: String}

def out.put(win: Array<U32>, +c: U32, o: Ow) -> Array<U32> & Ow:
  Ow{+w, +n, racc} = o
  (Array.set(U32, win, w, c), Ow{(w + 1 : U32), (n + 1 : U32), SCon{Chr{c}, racc}})

type Mo is Data:
  MoHead{}
  MoCodes{lit: Ht, dist: Ht}
  MoDone{}
  MoBad{}

type Is is Data:
  Is{br: Br, o: Ow, mode: Mo, last: Bool}

def inf.next(last: Bool) -> Mo:
  match last:
    case True{}:
      MoDone{}
    case False{}:
      MoHead{}

def inf.bad(win: Array<U32>, b: Br, o: Ow) -> Array<U32> & Is:
  (win, Is{b, o, MoBad{}, True{}})

# Stored block (§3.2.4): LEN, then NLEN (its complement), then LEN raw bytes.
def sb.put2(p: Array<U32> & Ow, b: Br) -> Array<U32> & Br & Ow:
  (a, o) = p
  (a, b, o)

def sb.put(win: Array<U32>, bv: Br & U32, o: Ow) -> Array<U32> & Br & Ow:
  (b, +c) = bv
  sb.put2(out.put(win, c, o), b)

def sb.byte(st: Array<U32> & Br & Ow) -> Array<U32> & Br & Ow:
  (win, b, o) = st
  sb.put(win, br.take(b, 8), o)

def sb.go(k: Nat, st: Array<U32> & Br & Ow) -> Array<U32> & Br & Ow:
  match k:
    case 0n:
      st
    case 1n+f:
      sb.go(f, sb.byte(st))

def sb.done(t: Array<U32> & Br & Ow, +last: Bool) -> Array<U32> & Is:
  (win, b, o) = t
  (win, Is{b, o, inf.next(last), last})

def sb.ok(win: Array<U32>, b: Br, +len: U32, o: Ow, +last: Bool, ok: Bool) -> Array<U32> & Is:
  match ok:
    case False{}:
      inf.bad(win, b, o)
    case True{}:
      sb.done(sb.go(bits(len), (win, b, o)), last)

def sb.nlen(win: Array<U32>, bv: Br & U32, +len: U32, o: Ow, +last: Bool) -> Array<U32> & Is:
  (b, +nlen) = bv
  sb.ok(win, b, len, o, last, U32.is_eq(U32.xor(len, 65535), nlen))

def sb.len(win: Array<U32>, bv: Br & U32, o: Ow, +last: Bool) -> Array<U32> & Is:
  (b, +len) = bv
  sb.nlen(win, br.take(b, 16), len, o, last)

def inf.stored(win: Array<U32>, b: Br, o: Ow, +last: Bool) -> Array<U32> & Is:
  sb.len(win, br.take(br.align(b), 16), o, last)

# Dynamic block (§3.2.7): code lengths for the code-length code, then the lengths themselves.
# cl.slot[i]: where symbol i's length sits in the order the stream sends them.
def cl.slot() -> List<&2, U32>:
  [3, 17, 15, 13, 11, 9, 7, 5, 4, 6, 8, 10, 12, 14, 16, 18, 0, 1, 2]

def cl.place(xs: List<&2, U32>, +vals: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+i, t}:
      Con{nth(vals, i), cl.place(t, vals)}

def cl.push(bv: Br & U32, acc: List<&2, U32>) -> Br & List<&2, U32>:
  (b, v) = bv
  (b, Con{v, acc})

def cl.one(st: Br & List<&2, U32>) -> Br & List<&2, U32>:
  (b, acc) = st
  cl.push(br.take(b, 3), acc)

def cl.read(k: Nat, st: Br & List<&2, U32>) -> Br & List<&2, U32>:
  match k:
    case 0n:
      st
    case 1n+f:
      cl.read(f, cl.one(st))

# Lengths so far (reversed), how many, the last one (for code 16), and whether it went wrong.
type Cd is Data:
  Cd{br: Br, acc: List<&2, U32>, n: U32, prev: U32, bad: Bool}

def cd.fill(+b: Br, +acc: List<&2, U32>, +n: U32, +v: U32, +cnt: U32, +total: U32) -> Cd:
  Bool.pick(Cd, U32.is_lt(total, (n + cnt : U32)), Cd{b, acc, n, v, True{}}, Cd{b, rep(bits(cnt), v, acc), (n + cnt : U32), v, False{}})

def cd.rep(bv: Br & U32, +v: U32, +base: U32, acc: List<&2, U32>, +n: U32, +total: U32) -> Cd:
  (b, +e) = bv
  cd.fill(b, acc, n, v, (base + e : U32), total)

def cd.prev(b: Br, acc: List<&2, U32>, +n: U32, +prev: U32, +total: U32, ok: Bool) -> Cd:
  match ok:
    case False{}:
      Cd{b, acc, n, prev, True{}}
    case True{}:
      cd.rep(br.take(b, 2), prev, 3, acc, n, total)

def cd.z18(b: Br, acc: List<&2, U32>, +n: U32, +total: U32, ok: Bool) -> Cd:
  match ok:
    case True{}:
      cd.rep(br.take(b, 7), 0, 11, acc, n, total)
    case False{}:
      Cd{b, acc, n, 0, True{}}

def cd.z17(b: Br, acc: List<&2, U32>, +n: U32, +s: U32, +total: U32, ok: Bool) -> Cd:
  match ok:
    case True{}:
      cd.rep(br.take(b, 3), 0, 3, acc, n, total)
    case False{}:
      cd.z18(b, acc, n, total, U32.is_eq(s, 18))

def cd.c16(b: Br, acc: List<&2, U32>, +n: U32, +prev: U32, +s: U32, +total: U32, ok: Bool) -> Cd:
  match ok:
    case True{}:
      cd.prev(b, acc, n, prev, total, U32.is_lt(0, n))
    case False{}:
      cd.z17(b, acc, n, s, total, U32.is_eq(s, 17))

def cd.lit(b: Br, acc: List<&2, U32>, +n: U32, +prev: U32, +s: U32, +total: U32, ok: Bool) -> Cd:
  match ok:
    case True{}:
      Cd{b, Con{s, acc}, (n + 1 : U32), s, False{}}
    case False{}:
      cd.c16(b, acc, n, prev, s, total, U32.is_eq(s, 16))

def cd.sym(bv: Br & U32, acc: List<&2, U32>, +n: U32, +prev: U32, +total: U32) -> Cd:
  (b, +s) = bv
  cd.lit(b, acc, n, prev, s, total, U32.is_lt(s, 16))

def cd.step.go(+cl: Ht, +total: U32, stop: Bool, cs: Cd) -> Cd:
  match stop:
    case False{}:
      Cd{b, acc, +n, +prev, bad} = cs
      cd.sym(ht.decode(cl, b), acc, n, prev, total)
    case True{}:
      Cd{b, acc, n, prev, bad} = cs
      Cd{b, acc, n, prev, bad}

def cd.stop(+st: Cd, +total: U32) -> Bool:
  Cd{b, acc, +n, prev, +bad} = st
  Bool.or(bad, U32.is_le(total, n))

# Each step adds at least one length, so total steps suffice.
def cd.go(k: Nat, +cl: Ht, +total: U32, +st: Cd) -> Cd:
  match k:
    case 0n:
      st
    case 1n+f:
      cd.go(f, cl, total, cd.step.go(cl, total, cd.stop(st, total), st))

def dyn.tables(b: Br, +lens: List<&2, U32>, +hlit: U32, bad: Bool) -> Br & Mo:
  match bad:
    case True{}:
      (b, MoBad{})
    case False{}:
      (b, MoCodes{ht.build(take.n(bits(hlit), lens)), ht.build(drop.n(bits(hlit), lens))})

def dyn.done(st: Cd, +hlit: U32, +total: U32) -> Br & Mo:
  Cd{b, acc, +n, prev, +bad} = st
  dyn.tables(b, List.reverse(&2, U32, acc), hlit, Bool.or(bad, Bool.not(U32.is_eq(n, total))))

def dyn.lens(st: Br & List<&2, U32>, +hlit: U32, +hdist: U32) -> Br & Mo:
  (b, acc) = st
  +total = (hlit + hdist : U32)
  +clens = cl.place(cl.slot(), List.reverse(&2, U32, acc))
  dyn.done(cd.go(bits(total), ht.build(clens), total, Cd{b, Nil{}, 0, 0, False{}}), hlit, total)

def dyn.clen(bv: Br & U32, +hlit: U32, +hdist: U32) -> Br & Mo:
  (b, +hclen) = bv
  dyn.lens(cl.read(bits((hclen + 4 : U32)), (b, Nil{})), hlit, hdist)

def dyn.hdist(bv: Br & U32, +hlit: U32) -> Br & Mo:
  (b, +hd) = bv
  dyn.clen(br.take(b, 4), hlit, (hd + 1 : U32))

def dyn.hlit(bv: Br & U32) -> Br & Mo:
  (b, +hl) = bv
  dyn.hdist(br.take(b, 5), (hl + 257 : U32))

def dyn.read(b: Br) -> Br & Mo:
  dyn.hlit(br.take(b, 5))

# A match copies len bytes from d back; the window's indexes wrap, so w - d needs no mask.
def cp.put(av: Array<U32> & U32, o: Ow) -> Array<U32> & Ow:
  (a, +c) = av
  out.put(a, c, o)

def cp.one(+d: U32, st: Array<U32> & Ow) -> Array<U32> & Ow:
  (win, o) = st
  Ow{+w, n, racc} = o
  cp.put(Array.get(U32, win, (w - d : U32)), Ow{w, n, racc})

def cp.go(k: Nat, +d: U32, st: Array<U32> & Ow) -> Array<U32> & Ow:
  match k:
    case 0n:
      st
    case 1n+f:
      cp.go(f, d, cp.one(d, st))

def inf.codes(p: Array<U32> & Ow, b: Br, +lit: Ht, +dist: Ht, +last: Bool) -> Array<U32> & Is:
  (win, o) = p
  (win, Is{b, o, MoCodes{lit, dist}, last})

def ow.n(+o: Ow) -> U32:
  Ow{w, +n, racc} = o
  n

# RFC 1951 §3.2.5: a distance may not reach before the first byte out.
def inf.far(win: Array<U32>, b: Br, +o: Ow, +len: U32, +d: U32, +lit: Ht, +dist: Ht, +last: Bool, ok: Bool) -> Array<U32> & Is:
  match ok:
    case False{}:
      inf.bad(win, b, o)
    case True{}:
      inf.codes(cp.go(bits(len), d, (win, o)), b, lit, dist, last)

def inf.dx(win: Array<U32>, bv: Br & U32, +db: U32, +len: U32, +o: Ow, +lit: Ht, +dist: Ht, +last: Bool) -> Array<U32> & Is:
  (b, +e) = bv
  +d = (db + e : U32)
  inf.far(win, b, o, len, d, lit, dist, last, U32.is_le(d, ow.n(o)))

def inf.ds(win: Array<U32>, b: Br, +ds: U32, +len: U32, +o: Ow, +lit: Ht, +dist: Ht, +last: Bool, ok: Bool) -> Array<U32> & Is:
  match ok:
    case False{}:
      inf.bad(win, b, o)
    case True{}:
      inf.dx(win, br.take(b, nth(dist.extra(), ds)), nth(dist.base(), ds), len, o, lit, dist, last)

def inf.d(win: Array<U32>, bv: Br & U32, +len: U32, +o: Ow, +lit: Ht, +dist: Ht, +last: Bool) -> Array<U32> & Is:
  (b, +ds) = bv
  inf.ds(win, b, ds, len, o, lit, dist, last, U32.is_lt(ds, 30))

def inf.lx(win: Array<U32>, bv: Br & U32, +lb: U32, +o: Ow, +lit: Ht, +dist: Ht, +last: Bool) -> Array<U32> & Is:
  (b, +e) = bv
  inf.d(win, ht.decode(dist, b), (lb + e : U32), o, lit, dist, last)

def inf.ls(win: Array<U32>, b: Br, +s: U32, +o: Ow, +lit: Ht, +dist: Ht, +last: Bool, ok: Bool) -> Array<U32> & Is:
  match ok:
    case False{}:
      inf.bad(win, b, o)
    case True{}:
      +i = (s - 257 : U32)
      inf.lx(win, br.take(b, nth(len.extra(), i)), nth(len.base(), i), o, lit, dist, last)

def inf.end(win: Array<U32>, b: Br, +s: U32, +o: Ow, +lit: Ht, +dist: Ht, +last: Bool, eob: Bool) -> Array<U32> & Is:
  match eob:
    case True{}:
      (win, Is{b, o, inf.next(last), last})
    case False{}:
      inf.ls(win, b, s, o, lit, dist, last, U32.is_le(s, 285))

def inf.lit(win: Array<U32>, b: Br, +s: U32, +o: Ow, +lit: Ht, +dist: Ht, +last: Bool, ok: Bool) -> Array<U32> & Is:
  match ok:
    case True{}:
      inf.codes(out.put(win, s, o), b, lit, dist, last)
    case False{}:
      inf.end(win, b, s, o, lit, dist, last, U32.is_eq(s, 256))

def inf.sym(win: Array<U32>, bv: Br & U32, +o: Ow, +lit: Ht, +dist: Ht, +last: Bool) -> Array<U32> & Is:
  (b, +s) = bv
  inf.lit(win, b, s, o, lit, dist, last, U32.is_lt(s, 256))

def inf.dyn(win: Array<U32>, bm: Br & Mo, o: Ow, +last: Bool) -> Array<U32> & Is:
  (b, m) = bm
  (win, Is{b, o, m, last})

def inf.t2(win: Array<U32>, b: Br, o: Ow, +last: Bool, is2: Bool) -> Array<U32> & Is:
  match is2:
    case True{}:
      inf.dyn(win, dyn.read(b), o, last)
    case False{}:
      inf.bad(win, b, o)

def inf.t1(win: Array<U32>, b: Br, o: Ow, +last: Bool, +t: U32, is1: Bool) -> Array<U32> & Is:
  match is1:
    case True{}:
      (win, Is{b, o, MoCodes{fixed.lit(), fixed.dist()}, last})
    case False{}:
      inf.t2(win, b, o, last, U32.is_eq(t, 2))

def inf.t0(win: Array<U32>, b: Br, o: Ow, +last: Bool, +t: U32, is0: Bool) -> Array<U32> & Is:
  match is0:
    case True{}:
      inf.stored(win, b, o, last)
    case False{}:
      inf.t1(win, b, o, last, t, U32.is_eq(t, 1))

# §3.2.3: BFINAL, then BTYPE.
def inf.head(win: Array<U32>, bv: Br & U32, o: Ow) -> Array<U32> & Is:
  (b, +v) = bv
  +t = U32.shr(v)
  inf.t0(win, b, o, U32.is_eq(U32.and(v, 1), 1), t, U32.is_zero(t))

# Every step reads at least one bit, so 8 steps per input byte always finish a valid stream.
def inf.go(k: Nat, st: Array<U32> & Is) -> Array<U32> & Is:
  match k:
    case 0n:
      st
    case 1n+f:
      (win, ist) = st
      Is{b, o, mode, +last} = ist
      match mode:
        case MoHead{}:
          inf.go(f, inf.head(win, br.take(b, 3), o))
        case MoCodes{+lit, +dist}:
          inf.go(f, inf.sym(win, ht.decode(lit, b), o, lit, dist, last))
        case MoDone{}:
          (win, Is{b, o, MoDone{}, last})
        case MoBad{}:
          (win, Is{b, o, MoBad{}, last})

# out: the bytes; rest: the input after the stream; n: len(out) mod 2^32.
type Inflated is Data:
  Inflated{out: String, rest: String, n: U32}

def inf.fin(ok: Bool, b: Br, o: Ow) -> Maybe<&2, Inflated>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Ow{w, n, racc} = o
      Some{Inflated{String.reverse(racc), br.rest(b), n}}

def inf.result(st: Array<U32> & Is) -> Maybe<&2, Inflated>:
  (win, ist) = st
  Is{+b, o, mode, last} = ist
  match mode:
    case MoDone{}:
      inf.fin(br.ok(b), b, o)
    case MoHead{}:
      None{}
    case MoCodes{l, d}:
      None{}
    case MoBad{}:
      None{}

def inflate.rest(+s: String) -> Maybe<&2, Inflated>:
  inf.result(inf.go(Nat.add(Nat.mul(String.length(s), 8n), 8n), (Array.new(U32, 15n, 0), Is{br.new(s), Ow{0, 0, ""}, MoHead{}, False{}})))

def inflate.out(m: Maybe<&2, Inflated>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{Inflated{out, rest, n}}:
      Some{out}

# Raw DEFLATE. None: malformed or cut short.
def inflate(+s: String) -> Maybe<&2, String>:
  inflate.out(inflate.rest(s))

# CRC-32 (RFC 1952 §8), reflected, polynomial 0xEDB88320.
def crc.bit(+c: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.and(c, 1), 1), U32.xor(U32.shr(c), 3988292384), U32.shr(c))

def crc.bits(k: Nat, +c: U32) -> U32:
  match k:
    case 0n:
      c
    case 1n+p:
      crc.bits(p, crc.bit(c))

def crc.fill(k: Nat, +i: U32, a: Array<U32>) -> Array<U32>:
  match k:
    case 0n:
      a
    case 1n+p:
      crc.fill(p, (i + 1 : U32), Array.set(U32, a, i, crc.bits(8n, i)))

def crc.table() -> Array<U32>:
  crc.fill(256n, 0, Array.new(U32, 8n, 0))

def crc.mix(av: Array<U32> & U32, +c: U32) -> Array<U32> & U32:
  (a, +t) = av
  (a, U32.xor(t, U32.shrn(c, 8n)))

def crc.step(st: Array<U32> & U32, +b: U32) -> Array<U32> & U32:
  (a, +c) = st
  crc.mix(Array.get(U32, a, U32.and(U32.xor(c, b), 255)), c)

def crc.go(s: String, st: Array<U32> & U32) -> Array<U32> & U32:
  match s:
    case SNil{}:
      st
    case SCon{h, t}:
      crc.go(t, crc.step(st, byte(h)))

def crc.of(st: Array<U32> & U32) -> U32:
  (a, +c) = st
  U32.xor(c, 4294967295)

def crc32(s: String) -> U32:
  crc.of(crc.go(s, (crc.table(), 4294967295)))

# Adler-32 (RFC 1950 §9).
def adler.go(s: String, +a: U32, +b: U32) -> U32:
  match s:
    case SNil{}:
      U32.or(U32.shln(b, 16n), a)
    case SCon{h, t}:
      +a2 = U32.mod((a + byte(h) : U32), 65521)
      adler.go(t, a2, U32.mod((b + a2 : U32), 65521))

def adler32(s: String) -> U32:
  adler.go(s, 1, 0)

# Little- and big-endian 32-bit words at the front of s.
def le32(s: String) -> Maybe<&2, U32>:
  match s:
    case SCon{Chr{+a}, SCon{Chr{+b}, SCon{Chr{+c}, SCon{Chr{+d}, t}}}}:
      Some{U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n)))}
    case SNil{}:
      None{}
    case SCon{x, y}:
      None{}

def be32(s: String) -> Maybe<&2, U32>:
  match s:
    case SCon{Chr{+a}, SCon{Chr{+b}, SCon{Chr{+c}, SCon{Chr{+d}, t}}}}:
      Some{U32.or(U32.or(U32.shln(a, 24n), U32.shln(b, 16n)), U32.or(U32.shln(c, 8n), d))}
    case SNil{}:
      None{}
    case SCon{x, y}:
      None{}

def flag(+f: U32, +bit: U32) -> Bool:
  Bool.not(U32.is_zero(U32.and(f, bit)))

def check(ok: Bool, +out: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{out}
    case False{}:
      None{}

# RFC 1952 §2.3: after the fixed 10 bytes, optional FEXTRA, FNAME, FCOMMENT, FHCRC.
# hit: the byte just read was the terminating zero.
def gz.zstr(s: String, hit: Bool) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      match hit:
        case True{}:
          Some{SNil{}}
        case False{}:
          None{}
    case SCon{Chr{+c}, t}:
      match hit:
        case True{}:
          Some{SCon{Chr{c}, t}}
        case False{}:
          gz.zstr(t, U32.is_zero(c))

def gz.skip(k: Nat, s: String) -> Maybe<&2, String>:
  match k:
    case 0n:
      Some{s}
    case 1n+p:
      match s:
        case SNil{}:
          None{}
        case SCon{h, t}:
          gz.skip(p, t)

def gz.extra.len(s: String) -> Maybe<&2, String>:
  match s:
    case SCon{Chr{+a}, SCon{Chr{+b}, t}}:
      gz.skip(bits(U32.or(a, U32.shln(b, 8n))), t)
    case SNil{}:
      None{}
    case SCon{x, y}:
      None{}

def gz.fextra(on: Bool, +s: String) -> Maybe<&2, String>:
  match on:
    case True{}:
      gz.extra.len(s)
    case False{}:
      Some{s}

def gz.fstr(on: Bool, +s: String) -> Maybe<&2, String>:
  match on:
    case True{}:
      gz.zstr(s, False{})
    case False{}:
      Some{s}

def gz.fhcrc(on: Bool, +s: String) -> Maybe<&2, String>:
  match on:
    case True{}:
      gz.skip(2n, s)
    case False{}:
      Some{s}

def gz.flags(+f: U32, s: String) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    s1 : String <- gz.fextra(flag(f, 4), s)
    s2 : String <- gz.fstr(flag(f, 8), s1)
    s3 : String <- gz.fstr(flag(f, 16), s2)
    gz.fhcrc(flag(f, 2), s3)

def gz.head(s: String) -> Maybe<&2, String>:
  match s:
    case SCon{Chr{+id1}, SCon{Chr{+id2}, SCon{Chr{+cm}, SCon{Chr{+f}, t}}}}:
      Bool.pick(Maybe<&2, String>, Bool.and(Bool.and(U32.is_eq(id1, 31), U32.is_eq(id2, 139)), U32.is_eq(cm, 8)), gz.flags(f, String.drop(t, 6n)), None{})
    case SNil{}:
      None{}
    case SCon{x, y}:
      None{}

def gz.trail2(+out: String, +n: U32, crc: Maybe<&2, U32>, size: Maybe<&2, U32>) -> Maybe<&2, String>:
  do Maybe<&2, String>:
    c : U32 <- crc
    z : U32 <- size
    check(Bool.and(U32.is_eq(c, crc32(out)), U32.is_eq(z, n)), out)

def gz.trail(m: Maybe<&2, Inflated>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{Inflated{+out, +rest, +n}}:
      gz.trail2(out, n, le32(rest), le32(String.drop(rest, 4n)))

def gz.body(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      gz.trail(inflate.rest(s))

# One gzip member; the CRC-32 and ISIZE must match. None: malformed, cut short, or corrupt.
# ponytail: bytes after the first member are ignored; loop over members if a server concatenates them.
def gunzip(s: String) -> Maybe<&2, String>:
  gz.body(gz.head(s))

# RFC 1950: CMF and FLG, then DEFLATE, then Adler-32, big-endian.
def zl.sum(+out: String, a: Maybe<&2, U32>) -> Maybe<&2, String>:
  match a:
    case None{}:
      None{}
    case Some{+v}:
      check(U32.is_eq(v, adler32(out)), out)

def zl.trail(m: Maybe<&2, Inflated>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{Inflated{+out, +rest, n}}:
      zl.sum(out, be32(rest))

def zl.ok(+cmf: U32, +flg: U32) -> Bool:
  Bool.and(Bool.and(U32.is_eq(U32.and(cmf, 15), 8), U32.is_le(U32.shrn(cmf, 4n), 7)), Bool.and(U32.is_zero(U32.mod((cmf * 256 + flg : U32), 31)), Bool.not(flag(flg, 32))))

def unzlib(s: String) -> Maybe<&2, String>:
  match s:
    case SCon{Chr{+cmf}, SCon{Chr{+flg}, +t}}:
      Bool.pick(Maybe<&2, String>, zl.ok(cmf, flg), zl.trail(inflate.rest(t)), None{})
    case SNil{}:
      None{}
    case SCon{x, y}:
      None{}

# DEFLATE encoding: LZ77 over hash chains with lazy matching, then blocks of at most 16384 symbols.
# Each block is dynamic Huffman, fixed Huffman, or stored, whichever is smallest.

# Bit writer: bits wait in buf, least significant first; racc holds the bytes out, reversed.
type Bw is Data:
  Bw{buf: U32, cnt: U32, racc: String}

def bw.emit(w: Bw) -> Bw:
  Bw{+buf, cnt, racc} = w
  Bw{U32.shrn(buf, 8n), (cnt - 8 : U32), SCon{Chr{U32.and(buf, 255)}, racc}}

def bw.emit.if(w: Bw, full: Bool) -> Bw:
  match full:
    case True{}:
      bw.emit(w)
    case False{}:
      w

def bw.full(+w: Bw) -> Bool:
  Bw{buf, +cnt, racc} = w
  U32.is_le(8, cnt)

# A put adds at most 16 bits to at most 7, so two emits drain every whole byte.
def bw.drain(fuel: Nat, +w: Bw) -> Bw:
  match fuel:
    case 0n:
      w
    case 1n+f:
      bw.drain(f, bw.emit.if(w, bw.full(w)))

def bw.put(w: Bw, +v: U32, +n: U32) -> Bw:
  Bw{buf, +cnt, racc} = w
  bw.drain(2n, Bw{U32.or(buf, U32.shln(v, bits(cnt))), (cnt + n : U32), racc})

def bw.out(w: Bw) -> String:
  Bw{buf, cnt, racc} = w
  String.reverse(racc)

# Seven zero bits push out a partial last byte.
def bw.done(w: Bw) -> String:
  bw.out(bw.put(w, 0, 7))

# A Huffman code goes out most significant bit first, so it is reversed before the put.
def rev(k: Nat, +v: U32, +acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      rev(p, U32.shr(v), U32.or(U32.shl(acc), U32.and(v, 1)))

def umin(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), a, b)

def umax(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), b, a)

# The last index whose base is at most v, with that base and its extra-bit count; bases ascend.
type Cx is Data:
  Cx{i: U32, base: U32, extra: U32}

def cx.go(bs: List<&2, U32>, es: List<&2, U32>, +v: U32, +i: U32, +best: Cx) -> Cx:
  match bs:
    case Nil{}:
      best
    case Con{+b, bt}:
      match es:
        case Nil{}:
          best
        case Con{+e, et}:
          cx.go(bt, et, v, (i + 1 : U32), Bool.pick(Cx, U32.is_le(b, v), Cx{i, b, e}, best))

# A token is a literal byte (below 256), or a match: bit 31, length index at 26, distance index at 21, extra length bits at 13, extra distance bits at 0.
def tk.pack(lc: Cx, dc: Cx, +len: U32, +d: U32) -> U32:
  Cx{+li, +lb, le} = lc
  Cx{+di, +db, de} = dc
  U32.or(U32.or(U32.or(2147483648, U32.shln(li, 26n)), U32.or(U32.shln(di, 21n), U32.shln((len - lb : U32), 13n))), (d - db : U32))

def tk.match(+len: U32, +d: U32) -> U32:
  tk.pack(cx.go(len.base(), len.extra(), len, 0, Cx{0, 3, 0}), cx.go(dist.base(), dist.extra(), d, 0, Cx{0, 1, 0}), len, d)

def tk.li(+t: U32) -> U32:
  U32.and(U32.shrn(t, 26n), 31)

def tk.di(+t: U32) -> U32:
  U32.and(U32.shrn(t, 21n), 31)

# Match finder: the input, the newest position + 1 per hash, and per position the previous one with its hash (0: none).
type Lz is Type:
  Lz{src: Array<U32>, head: Array<U32>, prev: Array<U32>}

def lz.at.of(r: Array<U32> & U32, head: Array<U32>, prev: Array<U32>) -> Lz & U32:
  (src, v) = r
  (Lz{src, head, prev}, v)

def lz.at(z: Lz, +i: U32) -> Lz & U32:
  Lz{src, head, prev} = z
  lz.at.of(Array.get(U32, src, i), head, prev)

def lz.drop(r: Lz & U32) -> Lz:
  (z, v) = r
  z

def lz.h3(r: Lz & U32, +a: U32, +b: U32) -> Lz & U32:
  (z, +c) = r
  (z, U32.and(U32.xor(U32.xor(U32.shln(a, 10n), U32.shln(b, 5n)), c), 32767))

def lz.h2(r: Lz & U32, +i: U32, +a: U32) -> Lz & U32:
  (z, +b) = r
  lz.h3(lz.at(z, (i + 2 : U32)), a, b)

def lz.h1(r: Lz & U32, +i: U32) -> Lz & U32:
  (z, +a) = r
  lz.h2(lz.at(z, (i + 1 : U32)), i, a)

def lz.hash(z: Lz, +i: U32) -> Lz & U32:
  lz.h1(lz.at(z, i), i)

def lz.link(r: Array<U32> & U32, +i: U32, +h: U32, src: Array<U32>, prev: Array<U32>) -> Lz & U32:
  (head, +old) = r
  (Lz{src, Array.set(U32, head, h, (i + 1 : U32)), Array.set(U32, prev, U32.and(i, 32767), old)}, old)

def lz.ins.of(r: Lz & U32, +i: U32) -> Lz & U32:
  (z, +h) = r
  Lz{src, head, prev} = z
  lz.link(Array.get(U32, head, h), i, h, src, prev)

# Links position i into the chain for its next three bytes; answers the chain's previous head.
def lz.insert(z: Lz, +i: U32) -> Lz & U32:
  lz.ins.of(lz.hash(z, i), i)

# Match length: bytes at a + k and b + k compared so far, and whether the last pair was equal.
type Ml is Type:
  Ml{z: Lz, a: U32, b: U32, k: U32, eq: Bool}

def ml.cmp(r: Lz & U32, +a: U32, +b: U32, +k: U32, +x: U32) -> Ml:
  (z, +y) = r
  Ml{z, a, b, (k + 1 : U32), U32.is_eq(x, y)}

def ml.read(r: Lz & U32, +a: U32, +b: U32, +k: U32) -> Ml:
  (z, +x) = r
  ml.cmp(lz.at(z, (b + k : U32)), a, b, k, x)

def ml.len(+k: U32, eq: Bool) -> U32:
  match eq:
    case True{}:
      k
    case False{}:
      (k - 1 : U32)

# Counts equal bytes from a and from b, up to fuel.
def ml.go(fuel: Nat, st: Ml) -> Lz & U32:
  match fuel:
    case 0n:
      Ml{z, a, b, +k, eq} = st
      (z, ml.len(k, eq))
    case 1n+f:
      Ml{z, +a, +b, +k, eq} = st
      match eq:
        case True{}:
          ml.go(f, ml.read(lz.at(z, (a + k : U32)), a, b, k))
        case False{}:
          (z, (k - 1 : U32))

# Chain walk at i: candidate c (position + 1), the longest match so far, and whether to go on.
# The walk stops once a match reaches nice.
type Ch is Type:
  Ch{z: Lz, i: U32, c: U32, max: U32, nice: U32, blen: U32, bdist: U32, go: Bool}

# RFC 1951 §3.2.5: a distance is at most 32768.
def ch.ok(+i: U32, +c: U32, +nice: U32, +blen: U32) -> Bool:
  Bool.and(Bool.and(U32.is_lt(0, c), U32.is_lt((i - c : U32), 32768)), U32.is_lt(blen, nice))

def ch.next(r: Array<U32> & U32, src: Array<U32>, head: Array<U32>, +i: U32, +max: U32, +nice: U32, +blen: U32, +bdist: U32) -> Ch:
  (prev, +c) = r
  Ch{Lz{src, head, prev}, i, c, max, nice, blen, bdist, ch.ok(i, c, nice, blen)}

def ch.best(r: Lz & U32, +i: U32, +p: U32, +max: U32, +nice: U32, +blen: U32, +bdist: U32) -> Ch:
  (z, +len) = r
  Lz{src, head, prev} = z
  +more = U32.is_lt(blen, len)
  ch.next(Array.get(U32, prev, U32.and(p, 32767)), src, head, i, max, nice, Bool.pick(U32, more, len, blen), Bool.pick(U32, more, (i - p : U32), bdist))

def ch.go(fuel: Nat, st: Ch) -> Ch:
  match fuel:
    case 0n:
      st
    case 1n+f:
      Ch{z, +i, +c, +max, +nice, +blen, +bdist, go} = st
      match go:
        case True{}:
          +p = (c - 1 : U32)
          ch.go(f, ch.best(ml.go(bits(max), Ml{z, i, p, 0, True{}}), i, p, max, nice, blen, bdist))
        case False{}:
          Ch{z, i, c, max, nice, blen, bdist, False{}}

# Extra bits of each literal/length symbol, and of each code-length symbol.
def lext() -> List<&2, U32>:
  rep(257n, 0, List.append(&2, U32, len.extra(), [0, 0]))

def clext() -> List<&2, U32>:
  rep(16n, 0, [2, 3, 7])

# RFC 1951 §3.2.7: the order the code-length code lengths are sent in.
def cl.order() -> List<&2, U32>:
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

def dot(xs: List<&2, U32>, ys: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{+x, xt}:
      match ys:
        case Nil{}:
          acc
        case Con{+y, yt}:
          dot(xt, yt, (acc + x * y : U32))

# One past the last nonzero entry.
def lastnz(xs: List<&2, U32>, +i: U32, +best: U32) -> U32:
  match xs:
    case Nil{}:
      best
    case Con{+x, t}:
      lastnz(t, (i + 1 : U32), Bool.pick(U32, U32.is_zero(x), best, (i + 1 : U32)))

def ladd(k: Nat, xs: List<&2, U32>, +dv: U32) -> List<&2, U32>:
  match k:
    case 0n:
      match xs:
        case Nil{}:
          Nil{}
        case Con{+h, t}:
          Con{(h + dv : U32), t}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, ladd(p, t, dv)}

def ar.push(av: Array<U32> & U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (a, v) = av
  (a, Con{v, acc})

# The first k entries, read from index i = k - 1 down.
def ar.list(k: Nat, +i: U32, st: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      (a, acc) = st
      acc
    case 1n+p:
      (a, acc) = st
      ar.list(p, (i - 1 : U32), ar.push(Array.get(U32, a, i), acc))

def ar.fill(xs: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{v, t}:
      ar.fill(t, (i + 1 : U32), Array.set(U32, a, i, v))

# Huffman code lengths: a two-queue merge over leaves sorted by weight, since merged weights only grow.
type Hn is Data:
  HnLeaf{}
  HnNode{l: Hn, r: Hn}

type Hw is Data:
  Hw{w: U32, t: Hn}

# A popped node, the leaves left, and the merged queue as a front list and a reversed back list.
type Hq is Data:
  Hq{x: Hw, ls: List<&2, Hw>, qf: List<&2, Hw>, qb: List<&2, Hw>}

type Hs is Data:
  Hs{ls: List<&2, Hw>, qf: List<&2, Hw>, qb: List<&2, Hw>}

def hw.w(+h: Hw) -> U32:
  Hw{+w, t} = h
  w

def hq.q(qf: List<&2, Hw>, qb: List<&2, Hw>) -> Hq:
  match qf:
    case Nil{}:
      Hq{Hw{0, HnLeaf{}}, Nil{}, Nil{}, qb}
    case Con{x, xt}:
      Hq{x, Nil{}, xt, qb}

# Ties take the leaf, which keeps codes short.
def hq.pick(q: Bool, l: Hw, lt: List<&2, Hw>, x: Hw, xt: List<&2, Hw>, qb: List<&2, Hw>) -> Hq:
  match q:
    case True{}:
      Hq{x, Con{l, lt}, xt, qb}
    case False{}:
      Hq{l, lt, Con{x, xt}, qb}

def hq.lq2(qf: List<&2, Hw>, +l: Hw, lt: List<&2, Hw>, qb: List<&2, Hw>) -> Hq:
  match qf:
    case Nil{}:
      Hq{l, lt, Nil{}, qb}
    case Con{+x, xt}:
      hq.pick(U32.is_lt(hw.w(x), hw.w(l)), l, lt, x, xt, qb)

def hq.lq(ls: List<&2, Hw>, qf: List<&2, Hw>, qb: List<&2, Hw>) -> Hq:
  match ls:
    case Nil{}:
      hq.q(qf, qb)
    case Con{l, lt}:
      hq.lq2(qf, l, lt, qb)

def hq.pop(qf: List<&2, Hw>, ls: List<&2, Hw>, qb: List<&2, Hw>) -> Hq:
  match qf:
    case Nil{}:
      hq.lq(ls, List.reverse(&2, Hw, qb), Nil{})
    case Con{x, xt}:
      hq.lq(ls, Con{x, xt}, qb)

def hc.join(a: Hw, b: Hw) -> Hw:
  Hw{+wa, ta} = a
  Hw{+wb, tb} = b
  Hw{(wa + wb : U32), HnNode{ta, tb}}

def hc.m2(a: Hw, q: Hq) -> Hs:
  Hq{b, ls, qf, qb} = q
  Hs{ls, qf, Con{hc.join(a, b), qb}}

def hc.m1(q: Hq) -> Hs:
  Hq{a, ls, qf, qb} = q
  hc.m2(a, hq.pop(qf, ls, qb))

def hc.merge(s: Hs) -> Hs:
  Hs{ls, qf, qb} = s
  hc.m1(hq.pop(qf, ls, qb))

def hc.root(q: Hq) -> Hn:
  Hq{x, ls, qf, qb} = q
  Hw{w, t} = x
  t

def hc.last(s: Hs) -> Hn:
  Hs{ls, qf, qb} = s
  hc.root(hq.pop(qf, ls, qb))

# k leaves need k - 1 merges.
def hc.go(k: Nat, s: Hs) -> Hn:
  match k:
    case 0n:
      hc.last(s)
    case 1n+f:
      hc.go(f, hc.merge(s))

def hc.dep(t: Hn, +d: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match t:
    case HnLeaf{}:
      Con{d, acc}
    case HnNode{l, r}:
      hc.dep(l, (d + 1 : U32), hc.dep(r, (d + 1 : U32), acc))

# Leaf keys: weight << 9 | symbol, so a sort by key is a sort by weight.
def hc.keys(fl: List<&2, U32>, +i: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match fl:
    case Nil{}:
      acc
    case Con{+f, t}:
      hc.keys(t, (i + 1 : U32), Bool.pick(List<&2, U32>, U32.is_zero(f), acc, Con{U32.or(U32.shln(f, 9n), i), acc}))

def hc.leaves(ks: List<&2, U32>) -> List<&2, Hw>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, t}:
      Con{Hw{U32.shrn(k, 9n), HnLeaf{}}, hc.leaves(t)}

def hc.nz(fl: List<&2, U32>, +acc: U32) -> U32:
  match fl:
    case Nil{}:
      acc
    case Con{+f, t}:
      hc.nz(t, Bool.pick(U32, U32.is_zero(f), acc, (acc + 1 : U32)))

def hc.bump1(fl: List<&2, U32>) -> List<&2, U32>:
  match fl:
    case Nil{}:
      Nil{}
    case Con{+b, t}:
      Con{umax(b, 1), t}

def hc.bump2(fl: List<&2, U32>) -> List<&2, U32>:
  match fl:
    case Nil{}:
      Nil{}
    case Con{+a, t}:
      Con{umax(a, 1), hc.bump1(t)}

# zlib and RFC 1951 decoders want at least two codes, so symbols 0 and 1 stand in when fewer are used.
def hc.bump(on: Bool, fl: List<&2, U32>) -> List<&2, U32>:
  match on:
    case True{}:
      hc.bump2(fl)
    case False{}:
      fl

def hc.len1(ks: List<&2, U32>) -> Nat:
  match ks:
    case Nil{}:
      0n
    case Con{k, t}:
      List.length(&2, U32, t)

# cs[l]: how many codes have length l, with depths past lim cut to lim.
def hc.hist(ds: List<&2, U32>, +lim: U32, cs: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      cs
    case Con{+d, t}:
      hc.hist(t, lim, ladd(bits(umin(d, lim)), cs, 1))

# Kraft sum, scaled by 2^lim: a complete code sums to exactly 2^lim.
def hc.kraft(cs: List<&2, U32>, +i: U32, +lim: U32, +acc: U32) -> U32:
  match cs:
    case Nil{}:
      acc
    case Con{+c, t}:
      hc.kraft(t, (i + 1 : U32), lim, (acc + U32.shln(c, bits((lim - i : U32))) : U32))

def hc.top(cs: List<&2, U32>, +i: U32, +lim: U32, +best: U32) -> U32:
  match cs:
    case Nil{}:
      best
    case Con{+c, t}:
      hc.top(t, (i + 1 : U32), lim, Bool.pick(U32, Bool.and(Bool.and(U32.is_lt(0, c), U32.is_lt(0, i)), U32.is_lt(i, lim)), i, best))

# zlib's overflow fix: move a code from the deepest length b below lim down to b + 1, pair it with one code at lim; each step drops the sum by 1.
def hc.fix(k: Nat, over: Bool, +cs: List<&2, U32>, +kr: U32, +lim: U32) -> List<&2, U32>:
  match k:
    case 0n:
      cs
    case 1n+f:
      match over:
        case False{}:
          cs
        case True{}:
          +b = hc.top(cs, 0, lim, 0)
          +k2 = (kr - 1 : U32)
          hc.fix(f, U32.is_lt(U32.shln(1, bits(lim)), k2), ladd(bits(lim), ladd(bits((b + 1 : U32)), ladd(bits(b), cs, 4294967295), 2), 4294967295), k2, lim)

# Lengths, longest first.
def hc.exp(cs: List<&2, U32>, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case Con{+c, t}:
      hc.exp(t, (i + 1 : U32), rep(bits(c), i, acc))

# The rarest symbols take the longest lengths.
def hc.sc(ks: List<&2, U32>, ls: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match ks:
    case Nil{}:
      a
    case Con{+k, t}:
      match ls:
        case Nil{}:
          a
        case Con{+l, lt}:
          hc.sc(t, lt, Array.set(U32, a, U32.and(k, 511), l))

# Code lengths of at most lim bits for ns symbols with frequencies fl.
def hc.lens(+fl: List<&2, U32>, +ns: U32, +lim: U32) -> List<&2, U32>:
  +ks = List.sort(~U32, ~U32.is_le, hc.keys(hc.bump(U32.is_lt(hc.nz(fl, 0), 2), fl), 0, Nil{}))
  +cs = hc.hist(hc.dep(hc.go(hc.len1(ks), Hs{hc.leaves(ks), Nil{}, Nil{}}), 0, Nil{}), lim, rep(bits((lim + 1 : U32)), 0, Nil{}))
  +kr = hc.kraft(cs, 0, lim, 0)
  +cs2 = hc.fix(320n, U32.is_lt(U32.shln(1, bits(lim)), kr), cs, kr, lim)
  ar.list(bits(ns), (ns - 1 : U32), (hc.sc(ks, hc.exp(cs2, 0, Nil{}), Array.new(U32, 9n, 0)), Nil{}))

# Canonical codes (RFC 1951 §3.2.2) for the encoder: each entry is the reversed code, its length at bit 16, and its extra-bit count at bit 20.
def enc.put(nv: Array<U32> & U32, +l: U32, +x: U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (n, +code) = nv
  (Array.set(U32, n, l, (code + 1 : U32)), Con{U32.or(U32.or(rev(bits(l), code, 0), U32.shln(l, 16n)), U32.shln(x, 20n)), acc})

def enc.one(nz: Bool, +l: U32, +x: U32, st: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match nz:
    case False{}:
      (n, acc) = st
      (n, Con{0, acc})
    case True{}:
      (n, acc) = st
      enc.put(Array.get(U32, n, l), l, x, acc)

def enc.go(lens: List<&2, U32>, xs: List<&2, U32>, st: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match lens:
    case Nil{}:
      st
    case Con{+l, lt}:
      match xs:
        case Nil{}:
          enc.go(lt, Nil{}, enc.one(U32.is_lt(0, l), l, 0, st))
        case Con{+x, xt}:
          enc.go(lt, xt, enc.one(U32.is_lt(0, l), l, x, st))

def enc.list(st: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  (n, acc) = st
  List.reverse(&2, U32, acc)

def enc.next(st: Array<U32> & Array<U32> & U32, +lens: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  (c, n, code) = st
  enc.list(enc.go(lens, xs, (n, Nil{})))

def enc.codes(+lens: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  enc.next(nx.go(15n, 1, (cnt.go(lens, Array.new(U32, 4n, 0)), Array.new(U32, 4n, 0), 0)), lens, xs)

# Writes symbol idx from table a, then ev in its extra bits.
def sym.w(av: Array<U32> & U32, w: Bw, +ev: U32) -> Array<U32> & Bw:
  (a, +e) = av
  (a, bw.put(bw.put(w, U32.and(e, 65535), U32.and(U32.shrn(e, 16n), 15)), ev, U32.shrn(e, 20n)))

def sym.put(st: Array<U32> & Bw, +idx: U32, +ev: U32) -> Array<U32> & Bw:
  (a, w) = st
  sym.w(Array.get(U32, a, idx), w, ev)

# Literal/length symbols sit at 0..285 of the table, distance symbols at 286..315.
def tk.one(lit: Bool, +t: U32, st: Array<U32> & Bw) -> Array<U32> & Bw:
  match lit:
    case True{}:
      sym.put(st, t, 0)
    case False{}:
      sym.put(sym.put(st, (257 + tk.li(t) : U32), U32.and(U32.shrn(t, 13n), 31)), (286 + tk.di(t) : U32), U32.and(t, 8191))

def tk.go(toks: List<&2, U32>, st: Array<U32> & Bw) -> Array<U32> & Bw:
  match toks:
    case Nil{}:
      st
    case Con{+t, r}:
      tk.go(r, tk.one(U32.is_lt(t, 256), t, st))

def fq.one(lit: Bool, +t: U32, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  match lit:
    case True{}:
      (lf, df) = st
      (cnt.add(Array.get(U32, lf, t), t), df)
    case False{}:
      (lf, df) = st
      +li = (257 + tk.li(t) : U32)
      +di = tk.di(t)
      (cnt.add(Array.get(U32, lf, li), li), cnt.add(Array.get(U32, df, di), di))

def fq.go(toks: List<&2, U32>, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  match toks:
    case Nil{}:
      st
    case Con{+t, r}:
      fq.go(r, fq.one(U32.is_lt(t, 256), t, st))

# Code-length tokens: symbol in the low byte, extra-bit value above it.
def clf.go(cs: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match cs:
    case Nil{}:
      a
    case Con{+t, r}:
      +s = U32.and(t, 255)
      clf.go(r, cnt.add(Array.get(U32, a, s), s))

# RFC 1951 §3.2.7 run-length codes: 16 repeats the last length 3..6 times, 17 and 18 repeat zero 3..10 and 11..138 times.
def rl.take(+c: U32, +v: U32) -> U32:
  Bool.pick(U32, U32.is_lt(c, 3), umin(c, 1), Bool.pick(U32, U32.is_zero(v), umin(c, 138), umin(c, 6)))

def rl.sym(+c: U32, +v: U32) -> U32:
  +zs = Bool.pick(U32, U32.is_lt(c, 11), U32.or(17, U32.shln((c - 3 : U32), 8n)), U32.or(18, U32.shln((umin(c, 138) - 11 : U32), 8n)))
  Bool.pick(U32, U32.is_lt(c, 3), v, Bool.pick(U32, U32.is_zero(v), zs, U32.or(16, U32.shln((umin(c, 6) - 3 : U32), 8n))))

def rl.z(k: Nat, +v: U32, +c: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+f:
      rl.z(f, v, (c - rl.take(c, v) : U32), Bool.pick(List<&2, U32>, U32.is_zero(c), acc, Con{rl.sym(c, v), acc}))

# A run of c copies of v; a nonzero run sends v once before any repeat code.
def rl.run(empty: Bool, zero: Bool, +v: U32, +c: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match empty:
    case True{}:
      acc
    case False{}:
      match zero:
        case True{}:
          rl.z(bits(c), 0, c, acc)
        case False{}:
          rl.z(bits(c), v, (c - 1 : U32), Con{v, acc})

def rl.go(xs: List<&2, U32>, +v: U32, +c: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      rl.run(U32.is_zero(c), U32.is_zero(v), v, c, acc)
    case Con{+x, t}:
      +same = U32.is_eq(x, v)
      rl.go(t, x, Bool.pick(U32, same, (c + 1 : U32), 1), Bool.pick(List<&2, U32>, same, acc, rl.run(U32.is_zero(c), U32.is_zero(v), v, c, acc)))

def cl.ordered(os: List<&2, U32>, +cll: List<&2, U32>) -> List<&2, U32>:
  match os:
    case Nil{}:
      Nil{}
    case Con{+o, t}:
      Con{nth(cll, o), cl.ordered(t, cll)}

def cl.put(k: Nat, co: List<&2, U32>, w: Bw) -> Bw:
  match k:
    case 0n:
      w
    case 1n+f:
      match co:
        case Nil{}:
          w
        case Con{+v, t}:
          cl.put(f, t, bw.put(w, v, 3))

def ct.go(cs: List<&2, U32>, st: Array<U32> & Bw) -> Array<U32> & Bw:
  match cs:
    case Nil{}:
      st
    case Con{+t, r}:
      ct.go(r, sym.put(st, U32.and(t, 255), U32.shrn(t, 8n)))

def bk.eob(st: Array<U32> & Bw) -> Bw:
  (a, w) = st
  w

def bk.fin(+final: Bool) -> U32:
  Bool.pick(U32, final, 1, 0)

# Header bits are BFINAL, then BTYPE: 01 fixed, 10 dynamic.
def bk.fixed(z: Lz, w: Bw, +final: Bool, rt: List<&2, U32>) -> Lz & Bw:
  tab = ar.fill(List.append(&2, U32, take.n(286n, enc.codes(fixed.llens(), lext())), enc.codes(fixed.dlens(), dist.extra())), 0, Array.new(U32, 9n, 0))
  (z, bk.eob(sym.put(tk.go(rt, (tab, bw.put(w, U32.or(bk.fin(final), 2), 3))), 256, 0)))

def bk.dyn(z: Lz, w: Bw, +final: Bool, rt: List<&2, U32>, +ll: List<&2, U32>, +dl: List<&2, U32>, cs: List<&2, U32>, +cll: List<&2, U32>, co: List<&2, U32>, +hlit: U32, +hdist: U32, +hclen: U32) -> Lz & Bw:
  +w1 = bw.put(bw.put(bw.put(bw.put(w, U32.or(bk.fin(final), 4), 3), (hlit - 257 : U32), 5), (hdist - 1 : U32), 5), (hclen - 4 : U32), 4)
  ctab = ar.fill(enc.codes(cll, clext()), 0, Array.new(U32, 5n, 0))
  +w2 = bk.eob(ct.go(cs, (ctab, cl.put(bits(hclen), co, w1))))
  tab = ar.fill(List.append(&2, U32, enc.codes(ll, lext()), enc.codes(dl, dist.extra())), 0, Array.new(U32, 9n, 0))
  (z, bk.eob(sym.put(tk.go(rt, (tab, w2)), 256, 0)))

# Stored blocks (§3.2.4) hold at most 65535 bytes each.
def bw.align(w: Bw) -> Bw:
  Bw{buf, +cnt, racc} = w
  bw.put(Bw{buf, cnt, racc}, 0, U32.and((8 - cnt : U32), 7))

def sw.b(r: Lz & U32, w: Bw) -> Lz & Bw:
  (z, +c) = r
  (z, bw.put(w, c, 8))

def sw.bytes(k: Nat, st: Lz & Bw, +p: U32) -> Lz & Bw:
  match k:
    case 0n:
      st
    case 1n+f:
      (z, w) = st
      sw.bytes(f, sw.b(lz.at(z, p), w), (p + 1 : U32))

def sw.chunk(st: Lz & Bw, +p: U32, +len: U32, +last: Bool) -> Lz & Bw:
  (z, w) = st
  sw.bytes(bits(len), (z, bw.put(bw.put(bw.align(bw.put(w, bk.fin(last), 3)), len, 16), U32.xor(len, 65535), 16)), p)

def sw.go(k: Nat, st: Lz & Bw, +p: U32, +left: U32, +final: Bool) -> Lz & Bw:
  match k:
    case 0n:
      st
    case 1n+f:
      +len = umin(left, 65535)
      sw.go(f, sw.chunk(st, p, len, Bool.and(final, U32.is_le(left, 65535))), (p + len : U32), (left - len : U32), final)

def bk.pick(sto: Bool, dyn: Bool, z: Lz, w: Bw, +final: Bool, rt: List<&2, U32>, +ll: List<&2, U32>, +dl: List<&2, U32>, cs: List<&2, U32>, +cll: List<&2, U32>, co: List<&2, U32>, +hlit: U32, +hdist: U32, +hclen: U32, +bs: U32, +m: U32, +chunks: U32) -> Lz & Bw:
  match sto:
    case True{}:
      sw.go(bits(chunks), (z, w), bs, m, final)
    case False{}:
      match dyn:
        case True{}:
          bk.dyn(z, w, final, rt, ll, dl, cs, cll, co, hlit, hdist, hclen)
        case False{}:
          bk.fixed(z, w, final, rt)

# Sizes in bits; ties go to fixed, then to Huffman over stored.
def bk.plan(+final: Bool, z: Lz, w: Bw, +rt: List<&2, U32>, +lfl: List<&2, U32>, +dfl: List<&2, U32>, +bs: U32, +e: U32) -> Lz & Bw:
  +ll = hc.lens(lfl, 286, 15)
  +dl = hc.lens(dfl, 30, 15)
  +hlit = umax(257, lastnz(ll, 0, 0))
  +hdist = umax(1, lastnz(dl, 0, 0))
  +cs = List.reverse(&2, U32, rl.go(List.append(&2, U32, take.n(bits(hlit), ll), take.n(bits(hdist), dl)), 999, 0, Nil{}))
  +cf = ar.list(19n, 18, (clf.go(cs, Array.new(U32, 5n, 0)), Nil{}))
  +cll = hc.lens(cf, 19, 7)
  +co = cl.ordered(cl.order(), cll)
  +hclen = umax(4, lastnz(co, 0, 0))
  +x = (dot(lfl, lext(), 0) + dot(dfl, dist.extra(), 0) : U32)
  +dyn = (17 + 3 * hclen + dot(cf, cll, 0) + dot(cf, clext(), 0) + dot(lfl, ll, 0) + dot(dfl, dl, 0) + x : U32)
  +fix = (3 + dot(lfl, fixed.llens(), 0) + dot(dfl, fixed.dlens(), 0) + x : U32)
  +m = (e - bs : U32)
  +chunks = umax(1, U32.div((m + 65534 : U32), 65535))
  +sto = (40 * chunks + 8 * m + 7 : U32)
  bk.pick(U32.is_lt(sto, umin(dyn, fix)), U32.is_lt(dyn, fix), z, w, final, rt, ll, dl, cs, cll, co, hlit, hdist, hclen, bs, m, chunks)

def bk.freq(st: Array<U32> & Array<U32>, +final: Bool, z: Lz, w: Bw, +rt: List<&2, U32>, +bs: U32, +e: U32) -> Lz & Bw:
  (lf, df) = st
  bk.plan(final, z, w, rt, ar.list(286n, 285, (lf, Nil{})), ar.list(30n, 29, (df, Nil{})), bs, e)

# Writes the tokens (reversed) for input bytes bs..e as one block.
def bk.flush(+final: Bool, z: Lz, w: Bw, toks: List<&2, U32>, +bs: U32, +e: U32) -> Lz & Bw:
  +rt = List.reverse(&2, U32, toks)
  bk.freq(fq.go(rt, (cnt.add(Array.get(U32, Array.new(U32, 9n, 0), 256), 256), Array.new(U32, 5n, 0))), final, z, w, rt, bs, e)

# Encoder: match finder, bit writer, tokens of the open block (reversed) and their count, the block's first byte,
# the end of the bytes already tokenized, position, input length, and a pending match (length plen, distance pdist) at i - 1.
type Es is Type:
  Es{z: Lz, w: Bw, toks: List<&2, U32>, nt: U32, bs: U32, e: U32, i: U32, n: U32, av: Bool, plen: U32, pdist: U32}

def ins.one(ok: Bool, z: Lz, +j: U32) -> Lz:
  match ok:
    case True{}:
      lz.drop(lz.insert(z, j))
    case False{}:
      z

# Positions inside a match join their chains too, when three bytes remain.
def ins.go(k: Nat, z: Lz, +j: U32, +n: U32) -> Lz:
  match k:
    case 0n:
      z
    case 1n+f:
      ins.go(f, ins.one(U32.is_le((j + 3 : U32), n), z, j), (j + 1 : U32), n)

# zlib level 6: chains of 128 (32 once the pending match reaches 8), stop at 128, no search past a pending 16.
# A length-3 match farther than 4096 costs more than its literals.
def mf.of(st: Ch) -> Lz & U32 & U32:
  Ch{z, i, c, max, nice, +blen, +bdist, go} = st
  (z, Bool.pick(U32, Bool.and(U32.is_eq(blen, 3), U32.is_lt(4096, bdist)), 0, blen), bdist)

def mf.chain(r: Lz & U32, +i: U32, +n: U32, +plen: U32) -> Lz & U32 & U32:
  (z, +c) = r
  +max = umin((n - i : U32), 258)
  +nice = umin(max, 128)
  mf.of(ch.go(Bool.pick(Nat, U32.is_lt(plen, 8), 128n, 32n), Ch{z, i, c, max, nice, 0, 0, ch.ok(i, c, nice, 0)}))

def mf.none(r: Lz & U32) -> Lz & U32 & U32:
  (z, c) = r
  (z, 0, 0)

def mf.lazy(on: Bool, r: Lz & U32, +i: U32, +n: U32, +plen: U32) -> Lz & U32 & U32:
  match on:
    case True{}:
      mf.chain(r, i, n, plen)
    case False{}:
      mf.none(r)

def mf.find(short: Bool, z: Lz, +i: U32, +n: U32, +plen: U32) -> Lz & U32 & U32:
  match short:
    case True{}:
      (z, 0, 0)
    case False{}:
      mf.lazy(U32.is_lt(plen, 16), lz.insert(z, i), i, n, plen)

def es.lit.of(r: Lz & U32, w: Bw, toks: List<&2, U32>, +nt: U32, +bs: U32, +i: U32, +n: U32, +l: U32, +d: U32) -> Es:
  (z, +c) = r
  Es{z, w, Con{c, toks}, (nt + 1 : U32), bs, i, (i + 1 : U32), n, True{}, l, d}

# The pending match wins unless the match at i is longer; then the byte at i - 1 goes out as a literal.
def es.hit(hit: Bool, z: Lz, w: Bw, toks: List<&2, U32>, +nt: U32, +bs: U32, +i: U32, +n: U32, +plen: U32, +pdist: U32, +l: U32, +d: U32) -> Es:
  match hit:
    case True{}:
      +j = (i - 1 + plen : U32)
      Es{ins.go(bits((plen - 2 : U32)), z, (i + 1 : U32), n), w, Con{tk.match(plen, pdist), toks}, (nt + 1 : U32), bs, j, j, n, False{}, 0, 0}
    case False{}:
      es.lit.of(lz.at(z, (i - 1 : U32)), w, toks, nt, bs, i, n, l, d)

def es.decide(av: Bool, z: Lz, w: Bw, toks: List<&2, U32>, +nt: U32, +bs: U32, +e: U32, +i: U32, +n: U32, +plen: U32, +pdist: U32, +l: U32, +d: U32) -> Es:
  match av:
    case True{}:
      es.hit(Bool.and(U32.is_le(3, plen), U32.is_le(l, plen)), z, w, toks, nt, bs, i, n, plen, pdist, l, d)
    case False{}:
      Es{z, w, toks, nt, bs, e, (i + 1 : U32), n, True{}, l, d}

def es.step(r: Lz & U32 & U32, w: Bw, toks: List<&2, U32>, +nt: U32, +bs: U32, +e: U32, +i: U32, +n: U32, av: Bool, +plen: U32, +pdist: U32) -> Es:
  (z, l, d) = r
  es.decide(av, z, w, toks, nt, bs, e, i, n, plen, pdist, l, d)

def es.pos(z: Lz, w: Bw, toks: List<&2, U32>, +nt: U32, +bs: U32, +e: U32, +i: U32, +n: U32, av: Bool, +plen: U32, +pdist: U32) -> Es:
  es.step(mf.find(U32.is_lt((n - i : U32), 3), z, i, n, plen), w, toks, nt, bs, e, i, n, av, plen, pdist)

def es.after(r: Lz & Bw, +e: U32, +i: U32, +n: U32, av: Bool, +plen: U32, +pdist: U32) -> Es:
  (z, w) = r
  es.pos(z, w, Nil{}, 0, e, e, i, n, av, plen, pdist)

def es.full(full: Bool, z: Lz, w: Bw, toks: List<&2, U32>, +nt: U32, +bs: U32, +e: U32, +i: U32, +n: U32, av: Bool, +plen: U32, +pdist: U32) -> Es:
  match full:
    case True{}:
      es.after(bk.flush(False{}, z, w, toks, bs, e), e, i, n, av, plen, pdist)
    case False{}:
      es.pos(z, w, toks, nt, bs, e, i, n, av, plen, pdist)

def es.more(more: Bool, z: Lz, w: Bw, toks: List<&2, U32>, +nt: U32, +bs: U32, +e: U32, +i: U32, +n: U32, av: Bool, +plen: U32, +pdist: U32) -> Es:
  match more:
    case True{}:
      es.full(U32.is_le(16384, nt), z, w, toks, nt, bs, e, i, n, av, plen, pdist)
    case False{}:
      Es{z, w, toks, nt, bs, e, i, n, av, plen, pdist}

# Each step moves i on by at least one, so n steps finish.
def es.go(fuel: Nat, st: Es) -> Es:
  match fuel:
    case 0n:
      st
    case 1n+f:
      Es{z, w, toks, +nt, +bs, +e, +i, +n, av, +plen, +pdist} = st
      es.go(f, es.more(U32.is_lt(i, n), z, w, toks, nt, bs, e, i, n, av, plen, pdist))

def es.done(r: Lz & Bw) -> String:
  (z, w) = r
  bw.done(w)

def es.last(r: Lz & U32, w: Bw, toks: List<&2, U32>, +bs: U32, +n: U32) -> String:
  (z, +c) = r
  es.done(bk.flush(True{}, z, w, Con{c, toks}, bs, n))

# A pending byte at the end has fewer than three bytes after it, so it goes out as a literal.
def es.tail(av: Bool, z: Lz, w: Bw, toks: List<&2, U32>, +bs: U32, +n: U32) -> String:
  match av:
    case True{}:
      es.last(lz.at(z, (n - 1 : U32)), w, toks, bs, n)
    case False{}:
      es.done(bk.flush(True{}, z, w, toks, bs, n))

def es.out(st: Es) -> String:
  Es{z, w, toks, nt, +bs, e, i, +n, av, plen, pdist} = st
  es.tail(av, z, w, toks, bs, n)

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

# Raw DEFLATE.
def deflate(+s: String) -> String:
  +n = slen(s, 0)
  src = src.fill(s, 0, Array.new(U32, depth(31n, 0n, n), 0))
  es.out(es.go(bits(n), Es{Lz{src, Array.new(U32, 15n, 0), Array.new(U32, 15n, 0)}, Bw{0, 0, ""}, Nil{}, 0, 0, 0, 0, n, False{}, 0, 0}))

def str.of(xs: List<&2, U32>, t: String) -> String:
  match xs:
    case Nil{}:
      t
    case Con{c, r}:
      SCon{Chr{c}, str.of(r, t)}

def le32.put(+v: U32, t: String) -> String:
  str.of([U32.and(v, 255), U32.and(U32.shrn(v, 8n), 255), U32.and(U32.shrn(v, 16n), 255), U32.shrn(v, 24n)], t)

def be32.put(+v: U32, t: String) -> String:
  str.of([U32.shrn(v, 24n), U32.and(U32.shrn(v, 16n), 255), U32.and(U32.shrn(v, 8n), 255), U32.and(v, 255)], t)

# One gzip member (RFC 1952): no flags, mtime 0, OS unknown.
def gzip(+s: String) -> String:
  str.of([31, 139, 8, 0, 0, 0, 0, 0, 0, 255], deflate(s) ++ le32.put(crc32(s), le32.put(slen(s, 0), "")))

# RFC 1950: CMF 0x78 (32 KiB window), FLG 0x01 (fastest), then DEFLATE, then Adler-32.
def zlib(+s: String) -> String:
  str.of([120, 1], deflate(s) ++ be32.put(adler32(s), ""))
