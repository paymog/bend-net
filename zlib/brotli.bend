# Brotli (RFC 7932) decoding over byte strings.
import Base

import ./brdict.bend as D

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

def umax(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), b, a)

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
def hib.go(k: Nat, z: Bool, +v: U32, +acc: U32) -> U32:
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

# A prefix code goes out most significant bit first, so its table index is the code reversed.
def rev(k: Nat, +v: U32, +acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+p:
      rev(p, U32.shr(v), U32.or(U32.shl(acc), U32.and(v, 1)))

def lset(k: Nat, xs: List<&2, U32>, +v: U32) -> List<&2, U32>:
  match k:
    case 0n:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{v, t}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, lset(p, t, v)}

def lmax(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      lmax(t, umax(x, acc))

def ar.fill(xs: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{v, t}:
      ar.fill(t, (i + 1 : U32), Array.set(U32, a, i, v))

# Little-endian bytes and bits: n bits (at most 24) from bit p.
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

def fb.of(av: Array<U32> & U32, +p: U32, +n: U32) -> Array<U32> & U32:
  (a, +w) = av
  (a, U32.and(U32.shrn(w, bits(U32.and(p, 7))), mask(n)))

def fb(a: Array<U32>, +p: U32, +n: U32) -> Array<U32> & U32:
  fb.of(le.go(4n, (a, 0), U32.shrn(p, 3n), 0n), p, n)

# Input and prefix codes: the bytes and the bit position, then every code's cells in one table.
# dir[k] = offset of code k | its longest code length << 24; a cell is symbol | length << 16.
type Io is Type:
  Io{a: Array<U32>, p: U32, t: Array<U32>, td: U32, fill: U32, dir: Array<U32>}

def io.bits.of(av: Array<U32> & U32, +p: U32, +n: U32, t: Array<U32>, +td: U32, +fill: U32, dir: Array<U32>) -> Io & U32:
  (a, v) = av
  (Io{a, (p + n : U32), t, td, fill, dir}, v)

def io.bits(io: Io, +n: U32) -> Io & U32:
  Io{a, +p, t, +td, +fill, dir} = io
  io.bits.of(fb(a, p, n), p, n, t, td, fill, dir)

def io.sym.t(tv: Array<U32> & U32, a: Array<U32>, +p: U32, +td: U32, +fill: U32, dir: Array<U32>) -> Io & U32:
  (t, +x) = tv
  (Io{a, (p + U32.shrn(x, 16n) : U32), t, td, fill, dir}, U32.and(x, 65535))

def io.sym.v(av: Array<U32> & U32, +off: U32, +p: U32, t: Array<U32>, +td: U32, +fill: U32, dir: Array<U32>) -> Io & U32:
  (a, +v) = av
  io.sym.t(Array.get(U32, t, (off + v : U32)), a, p, td, fill, dir)

def io.sym.d(dv: Array<U32> & U32, a: Array<U32>, +p: U32, t: Array<U32>, +td: U32, +fill: U32) -> Io & U32:
  (dir, +e) = dv
  io.sym.v(fb(a, p, U32.shrn(e, 24n)), U32.and(e, 16777215), p, t, td, fill, dir)

def io.sym(io: Io, +k: U32) -> Io & U32:
  Io{a, +p, t, +td, +fill, dir} = io
  io.sym.d(Array.get(U32, dir, k), a, p, t, td, fill)

# The cell table doubles until it holds need cells.
def gr.mv(ov: Array<U32> & U32, nw: Array<U32>, +i: U32) -> Array<U32> & Array<U32>:
  (old, +v) = ov
  (old, Array.set(U32, nw, i, v))

def gr.copy(k: Nat, st: Array<U32> & Array<U32>, +i: U32) -> Array<U32> & Array<U32>:
  match k:
    case 0n:
      st
    case 1n+f:
      (old, nw) = st
      gr.copy(f, gr.mv(Array.get(U32, old, i), nw, i), (i + 1 : U32))

def gr.new(st: Array<U32> & Array<U32>) -> Array<U32>:
  (old, nw) = st
  nw

def gr.go(k: Nat, +over: Bool, t: Array<U32>, +d: U32, +need: U32) -> Array<U32> & U32:
  match k:
    case 0n:
      (t, d)
    case 1n+f:
      match over:
        case False{}:
          (t, d)
        case True{}:
          +nd = (d + 1 : U32)
          gr.go(f, U32.is_lt(U32.shln(1, bits(nd)), need), gr.new(gr.copy(bits(U32.shln(1, bits(d))), (t, Array.new(U32, bits(nd), 0)), 0)), nd, need)

def grow(t: Array<U32>, +d: U32, +need: U32) -> Array<U32> & U32:
  gr.go(25n, U32.is_lt(U32.shln(1, bits(d)), need), t, d, need)

# Canonical codes (RFC 7932 §3.2) from keys length << 16 | symbol, sorted: each code fills every cell its reversed bits select.
def tc.put(k: Nat, +i: U32, +step: U32, +e: U32, t: Array<U32>) -> Array<U32>:
  match k:
    case 0n:
      t
    case 1n+f:
      tc.put(f, (i + step : U32), step, e, Array.set(U32, t, i, e))

def tc.fill(ks: List<&2, U32>, +code: U32, +cur: U32, +off: U32, +ml: U32, t: Array<U32>) -> Array<U32>:
  match ks:
    case Nil{}:
      t
    case Con{+k, r}:
      +l = U32.shrn(k, 16n)
      +c = U32.shln(code, bits((l - cur : U32)))
      tc.fill(r, (c + 1 : U32), l, off, ml, tc.put(bits(U32.shln(1, bits((ml - l : U32)))), (off + rev(bits(l), c, 0) : U32), U32.shln(1, bits(l)), U32.or(U32.and(k, 65535), U32.shln(l, 16n)), t))

def io.code.of(gv: Array<U32> & U32, a: Array<U32>, +p: U32, +fill: U32, dir: Array<U32>, +k: U32, +ks: List<&2, U32>, +ml: U32) -> Io:
  (t, +td) = gv
  Io{a, p, tc.fill(ks, 0, 0, fill, ml, t), td, (fill + U32.shln(1, bits(ml)) : U32), Array.set(U32, dir, k, U32.or(fill, U32.shln(ml, 24n)))}

def io.code(io: Io, +k: U32, +ks: List<&2, U32>, +ml: U32) -> Io:
  Io{a, +p, t, +td, +fill, dir} = io
  io.code.of(grow(t, td, (fill + U32.shln(1, bits(ml)) : U32)), a, p, fill, dir, k, ks, ml)

# Output: the window, which doubles up to 2^wmax, the bytes out, the bytes reversed, and the last two bytes.
type Ob is Type:
  Ob{w: Array<U32>, wd: U32, wmax: U32, n: U32, racc: String, p1: U32, p2: U32}

def ob.grow(on: Bool, w: Array<U32>, +wd: U32) -> Array<U32> & U32:
  match on:
    case True{}:
      +nd = (wd + 1 : U32)
      (gr.new(gr.copy(bits(U32.shln(1, bits(wd))), (w, Array.new(U32, bits(nd), 0)), 0)), nd)
    case False{}:
      (w, wd)

def ob.set(gv: Array<U32> & U32, +wmax: U32, +n: U32, racc: String, +p1: U32, +c: U32) -> Ob:
  (w, +wd) = gv
  Ob{Array.set(U32, w, n, c), wd, wmax, (n + 1 : U32), SCon{Chr{c}, racc}, c, p1}

def ob.put(o: Ob, +c: U32) -> Ob:
  Ob{w, +wd, +wmax, +n, racc, +p1, p2} = o
  ob.set(ob.grow(Bool.and(U32.is_lt(wd, wmax), U32.is_eq(n, U32.shln(1, bits(wd)))), w, wd), wmax, n, racc, p1, c)

def ob.cp.of(av: Array<U32> & U32, +wd: U32, +wmax: U32, +n: U32, racc: String, +p1: U32, +p2: U32) -> Ob:
  (w, +c) = av
  ob.put(Ob{w, wd, wmax, n, racc, p1, p2}, c)

def ob.copy(k: Nat, o: Ob, +d: U32) -> Ob:
  match k:
    case 0n:
      o
    case 1n+f:
      Ob{w, +wd, +wmax, +n, racc, +p1, +p2} = o
      ob.copy(f, ob.cp.of(Array.get(U32, w, (n - d : U32)), wd, wmax, n, racc, p1, p2), d)

def ob.str(s: String, o: Ob) -> Ob:
  match s:
    case SNil{}:
      o
    case SCon{Chr{+c}, t}:
      ob.str(t, ob.put(o, c))

# Context maps, literal context modes, and the context lookup tables Lut0, Lut1, Lut2 (§7.1) at 0, 256, 512.
type Mp is Type:
  Mp{cml: Array<U32>, cmd: Array<U32>, cmode: Array<U32>, lut: Array<U32>}

# Block switch state (§6): number of types, current type, previous type, count left.
type Bk is Data:
  Bk{n: U32, t: U32, pt: U32, len: U32}

# Meta-block parameters and stream state: block switches, distance parameters, the first code of each group,
# the last four distances, the window size, the bytes left in the meta-block, and whether it went wrong.
type Ps is Data:
  Ps{bl: Bk, bi: Bk, bd: Bk, npost: U32, ndir: U32, litb: U32, icb: U32, db: U32, d1: U32, d2: U32, d3: U32, d4: U32, wsize: U32, left: U32, bad: Bool}

type St is Type:
  St{io: Io, o: Ob, mp: Mp, ps: Ps}

def st.io.of(r: Io & U32, o: Ob, mp: Mp, +ps: Ps) -> St & U32:
  (io, v) = r
  (St{io, o, mp, ps}, v)

def st.bits(st: St, +n: U32) -> St & U32:
  St{io, o, mp, +ps} = st
  st.io.of(io.bits(io, n), o, mp, ps)

def st.sym(st: St, +k: U32) -> St & U32:
  St{io, o, mp, +ps} = st
  st.io.of(io.sym(io, k), o, mp, ps)

def st.code(st: St, +k: U32, +ks: List<&2, U32>, +ml: U32) -> St:
  St{io, o, mp, +ps} = st
  St{io.code(io, k, ks, ml), o, mp, ps}

def st.ps(st: St) -> St & Ps:
  St{io, o, mp, +ps} = st
  (St{io, o, mp, ps}, ps)

def st.set(st: St, +ps: Ps) -> St:
  St{io, o, mp, old} = st
  St{io, o, mp, ps}

def st.fail(st: St) -> St:
  St{io, o, mp, +ps} = st
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, bad} = ps
  St{io, o, mp, Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, True{}}}

def st.check(st: St, +ok: Bool) -> St:
  match ok:
    case True{}:
      st
    case False{}:
      st.fail(st)

def st.bad(st: St) -> St & Bool:
  St{io, o, mp, +ps} = st
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, +bad} = ps
  (St{io, o, mp, ps}, bad)

def st.put(st: St, +c: U32) -> St:
  St{io, o, mp, +ps} = st
  St{io, ob.put(o, c), mp, ps}

def st.str(st: St, s: String) -> St:
  St{io, o, mp, +ps} = st
  St{io, ob.str(s, o), mp, ps}

def st.copy(st: St, +len: U32, +d: U32) -> St:
  St{io, o, mp, +ps} = st
  St{io, ob.copy(bits(len), o, d), mp, ps}

def st.n(st: St) -> St & U32:
  St{io, o, mp, +ps} = st
  Ob{w, wd, wmax, +n, racc, p1, p2} = o
  (St{io, Ob{w, wd, wmax, n, racc, p1, p2}, mp, ps}, n)

def st.p12(st: St) -> St & U32:
  St{io, o, mp, +ps} = st
  Ob{w, wd, wmax, n, racc, +p1, +p2} = o
  (St{io, Ob{w, wd, wmax, n, racc, p1, p2}, mp, ps}, U32.or(p1, U32.shln(p2, 8n)))

def st.align(st: St) -> St:
  St{io, o, mp, +ps} = st
  Io{a, +p, t, td, fill, dir} = io
  St{Io{a, U32.and((p + 7 : U32), 4294967288), t, td, fill, dir}, o, mp, ps}

def st.skip(st: St, +n: U32) -> St:
  St{io, o, mp, +ps} = st
  Io{a, +p, t, td, fill, dir} = io
  St{Io{a, (p + n : U32), t, td, fill, dir}, o, mp, ps}

def st.reset(st: St) -> St:
  St{io, o, mp, +ps} = st
  Io{a, p, t, td, fill, dir} = io
  St{Io{a, p, t, td, 0, dir}, o, mp, ps}

def mp.r0(av: Array<U32> & U32, io: Io, o: Ob, cmd: Array<U32>, cmode: Array<U32>, lut: Array<U32>, +ps: Ps) -> St & U32:
  (cml, v) = av
  (St{io, o, Mp{cml, cmd, cmode, lut}, ps}, v)

def mp.r1(av: Array<U32> & U32, io: Io, o: Ob, cml: Array<U32>, cmode: Array<U32>, lut: Array<U32>, +ps: Ps) -> St & U32:
  (cmd, v) = av
  (St{io, o, Mp{cml, cmd, cmode, lut}, ps}, v)

def mp.r2(av: Array<U32> & U32, io: Io, o: Ob, cml: Array<U32>, cmd: Array<U32>, lut: Array<U32>, +ps: Ps) -> St & U32:
  (cmode, v) = av
  (St{io, o, Mp{cml, cmd, cmode, lut}, ps}, v)

def mp.r3(av: Array<U32> & U32, io: Io, o: Ob, cml: Array<U32>, cmd: Array<U32>, cmode: Array<U32>, +ps: Ps) -> St & U32:
  (lut, v) = av
  (St{io, o, Mp{cml, cmd, cmode, lut}, ps}, v)

def st.map.pick(+w0: Bool, +w1: Bool, +w2: Bool, +i: U32, io: Io, o: Ob, cml: Array<U32>, cmd: Array<U32>, cmode: Array<U32>, lut: Array<U32>, +ps: Ps) -> St & U32:
  match w0:
    case True{}:
      mp.r0(Array.get(U32, cml, i), io, o, cmd, cmode, lut, ps)
    case False{}:
      match w1:
        case True{}:
          mp.r1(Array.get(U32, cmd, i), io, o, cml, cmode, lut, ps)
        case False{}:
          match w2:
            case True{}:
              mp.r2(Array.get(U32, cmode, i), io, o, cml, cmd, lut, ps)
            case False{}:
              mp.r3(Array.get(U32, lut, i), io, o, cml, cmd, cmode, ps)

# Reads map which (0 cml, 1 cmd, 2 cmode, 3 lut) at i.
def st.map(st: St, +which: U32, +i: U32) -> St & U32:
  St{io, o, mp, +ps} = st
  Mp{cml, cmd, cmode, lut} = mp
  st.map.pick(U32.is_zero(which), U32.is_eq(which, 1), U32.is_eq(which, 2), i, io, o, cml, cmd, cmode, lut, ps)

def st.maps(st: St, cml: Array<U32>, cmd: Array<U32>, cmode: Array<U32>) -> St:
  St{io, o, mp, +ps} = st
  Mp{a, b, c, lut} = mp
  St{io, o, Mp{cml, cmd, cmode, lut}, ps}

def st.peek.of(av: Array<U32> & U32, +p: U32, t: Array<U32>, +td: U32, +fill: U32, dir: Array<U32>, o: Ob, mp: Mp, +ps: Ps) -> St & U32:
  (a, v) = av
  (St{Io{a, p, t, td, fill, dir}, o, mp, ps}, v)

def st.peek(st: St, +n: U32) -> St & U32:
  St{io, o, mp, +ps} = st
  Io{a, +p, t, td, fill, dir} = io
  st.peek.of(fb(a, p, n), p, t, td, fill, dir, o, mp, ps)

def st.push(r: St & U32, acc: List<&2, U32>) -> St & List<&2, U32>:
  (st, v) = r
  (st, Con{v, acc})

def st.list(k: Nat, r: St & List<&2, U32>, +n: U32) -> St & List<&2, U32>:
  match k:
    case 0n:
      r
    case 1n+f:
      (st, acc) = r
      st.list(f, st.push(st.bits(st, n), acc), n)

# A parsed prefix code: sorted keys (length << 16 | symbol), the longest length, and whether it was valid.
type Pc is Data:
  Pc{ks: List<&2, U32>, ml: U32, ok: Bool}

def pc.keys(ls: List<&2, U32>, +i: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      acc
    case Con{+l, t}:
      pc.keys(t, (i + 1 : U32), Bool.pick(List<&2, U32>, U32.is_zero(l), acc, Con{U32.or(U32.shln(l, 16n), i), acc}))

def pc.zip(ss: List<&2, U32>, ls: List<&2, U32>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+s, st}:
      match ls:
        case Nil{}:
          Nil{}
        case Con{+l, lt}:
          Con{U32.or(U32.shln(l, 16n), s), pc.zip(st, lt)}

def pc.sort(+ks: List<&2, U32>) -> List<&2, U32>:
  List.sort(~U32, ~U32.is_le, ks)

# Symbols below size and all different.
def pc.fine(ss: List<&2, U32>, +prev: U32, +size: U32) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{+s, t}:
      Bool.and(Bool.and(U32.is_lt(s, size), Bool.not(U32.is_eq(s, prev))), pc.fine(t, s, size))

# Simple prefix codes (§3.4).
def sp.lens(+n: U32, +ts: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_eq(n, 1), [0], Bool.pick(List<&2, U32>, U32.is_eq(n, 2), [1, 1], Bool.pick(List<&2, U32>, U32.is_eq(n, 3), [1, 2, 2], Bool.pick(List<&2, U32>, U32.is_zero(ts), [2, 2, 2, 2], [1, 2, 3, 3]))))

def sp.done(r: St & U32, +ss: List<&2, U32>, +n: U32, +size: U32) -> St & Pc:
  (st, +ts) = r
  +ls = sp.lens(n, ts)
  (st, Pc{pc.sort(pc.zip(ss, ls)), lmax(ls, 0), pc.fine(pc.sort(ss), 4294967295, size)})

def sp.ts(four: Bool, r: St & List<&2, U32>, +n: U32, +size: U32) -> St & Pc:
  match four:
    case True{}:
      (st, acc) = r
      sp.done(st.bits(st, 1), List.reverse(&2, U32, acc), n, size)
    case False{}:
      (st, acc) = r
      sp.done((st, 0), List.reverse(&2, U32, acc), n, size)

def sp.read(r: St & U32, +size: U32) -> St & Pc:
  (st, +v) = r
  +n = (v + 1 : U32)
  sp.ts(U32.is_eq(n, 4), st.list(bits(n), (st, Nil{}), (hib((size - 1 : U32)) + 1 : U32)), n, size)

# Complex prefix codes (§3.5). The code length code lengths use a fixed code: symbol | length << 8 by the next 4 bits.
def cl.fixed(+v: U32) -> U32:
  +lo = U32.and(v, 3)
  Bool.pick(U32, U32.is_zero(lo), 512, Bool.pick(U32, U32.is_eq(lo, 1), 516, Bool.pick(U32, U32.is_eq(lo, 2), 515, Bool.pick(U32, U32.is_eq(U32.and(v, 7), 3), 770, Bool.pick(U32, U32.is_eq(v, 7), 1025, 1029)))))

def cl.order() -> List<&2, U32>:
  [1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15]

type Cc is Data:
  Cc{ls: List<&2, U32>, space: U32, num: U32, done: Bool, bad: Bool}

def cc.got(r: St & U32, +o: U32, c: Cc) -> St & Cc:
  (st, +v) = r
  Cc{ls, +space, +num, done, bad} = c
  +e = cl.fixed(v)
  +s = U32.and(e, 255)
  +w = Bool.pick(U32, U32.is_zero(s), 0, U32.shrn(32, bits(s)))
  +over = U32.is_lt(space, w)
  +left = (space - w : U32)
  (st.skip(st, U32.shrn(e, 8n)), Cc{lset(bits(o), ls, s), left, Bool.pick(U32, U32.is_zero(s), num, (num + 1 : U32)), Bool.or(over, U32.is_zero(left)), over})

def cc.step(done: Bool, r: St & Cc, +o: U32) -> St & Cc:
  match done:
    case True{}:
      r
    case False{}:
      (st, c) = r
      cc.got(st.peek(st, 4), o, c)

def cc.done(+c: Cc) -> Bool:
  Cc{ls, space, num, +done, bad} = c
  done

def cc.go(os: List<&2, U32>, r: St & Cc) -> St & Cc:
  match os:
    case Nil{}:
      r
    case Con{+o, t}:
      (st, +c) = r
      cc.go(t, cc.step(cc.done(c), (st, c), o))

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

def pc.count(ls: List<&2, U32>, +acc: U32) -> U32:
  match ls:
    case Nil{}:
      acc
    case Con{+l, t}:
      pc.count(t, Bool.pick(U32, U32.is_zero(l), acc, (acc + 1 : U32)))

# One code length alone means a code of one symbol and no bits.
def pc.of(+ls: List<&2, U32>, +ok: Bool) -> Pc:
  +one = U32.is_eq(pc.count(ls, 0), 1)
  +ks = pc.sort(pc.keys(ls, 0, Nil{}))
  Pc{Bool.pick(List<&2, U32>, one, [U32.and(nth(ks, 0), 65535)], ks), Bool.pick(U32, one, 0, lmax(ls, 0)), ok}

# Symbol code lengths: symbols so far, the last nonzero length, the repeat count and its length, the space left, the lengths (reversed).
type Sl is Data:
  Sl{sym: U32, prev: U32, rep: U32, rlen: U32, space: U32, acc: List<&2, U32>, bad: Bool, done: Bool}

def sl.fin(+sym: U32, +prev: U32, +rep: U32, +rlen: U32, +space: U32, +acc: List<&2, U32>, +bad: Bool, +size: U32) -> Sl:
  Sl{sym, prev, rep, rlen, space, acc, bad, Bool.or(bad, Bool.or(U32.is_le(size, sym), U32.is_zero(space)))}

def sl.lit(+c: U32, s: Sl, +size: U32) -> Sl:
  Sl{+sym, +prev, rep, rlen, +space, acc, bad, done} = s
  +w = Bool.pick(U32, U32.is_zero(c), 0, U32.shrn(32768, bits(c)))
  sl.fin((sym + 1 : U32), Bool.pick(U32, U32.is_zero(c), prev, c), 0, rlen, (space - w : U32), Con{c, acc}, Bool.or(bad, U32.is_lt(space, w)), size)

def sl.rep(r: St & U32, +c: U32, s: Sl, +size: U32) -> St & Sl:
  (st, +x) = r
  Sl{+sym, +prev, +rp, +rlen, +space, acc, +bad, done} = s
  +eb = Bool.pick(U32, U32.is_eq(c, 16), 2, 3)
  +nl = Bool.pick(U32, U32.is_eq(c, 16), prev, 0)
  +old = Bool.pick(U32, U32.is_eq(rlen, nl), rp, 0)
  +nrep = (Bool.pick(U32, U32.is_zero(old), 0, U32.shln((old - 2 : U32), bits(eb))) + x + 3 : U32)
  +delta = (nrep - old : U32)
  +over = U32.is_lt(size, (sym + delta : U32))
  +d2 = Bool.pick(U32, over, 0, delta)
  +w = Bool.pick(U32, U32.is_zero(nl), 0, U32.shln(d2, bits((15 - nl : U32))))
  (st, sl.fin((sym + d2 : U32), prev, nrep, nl, (space - w : U32), rep(bits(d2), nl, acc), Bool.or(Bool.or(bad, over), U32.is_lt(space, w)), size))

def sl.sym(lit: Bool, r: St & U32, s: Sl, +size: U32) -> St & Sl:
  match lit:
    case True{}:
      (st, +c) = r
      (st, sl.lit(c, s, size))
    case False{}:
      (st, +c) = r
      sl.rep(st.bits(st, Bool.pick(U32, U32.is_eq(c, 16), 2, 3)), c, s, size)

def sl.got(r: St & U32, s: Sl, +size: U32) -> St & Sl:
  (st, +c) = r
  sl.sym(U32.is_lt(c, 16), (st, c), s, size)

def sl.step(done: Bool, r: St & Sl, +size: U32) -> St & Sl:
  match done:
    case True{}:
      r
    case False{}:
      (st, s) = r
      sl.got(st.sym(st, 1023), s, size)

def sl.done(+s: Sl) -> Bool:
  Sl{sym, prev, rep, rlen, space, acc, bad, +done} = s
  done

def sl.go(k: Nat, r: St & Sl, +size: U32) -> St & Sl:
  match k:
    case 0n:
      r
    case 1n+f:
      (st, +s) = r
      sl.go(f, sl.step(sl.done(s), (st, s), size), size)

def sl.pc(r: St & Sl) -> St & Pc:
  (st, s) = r
  Sl{sym, prev, rep, rlen, +space, acc, +bad, done} = s
  (st, pc.of(List.reverse(&2, U32, acc), Bool.and(Bool.not(bad), U32.is_zero(space))))

def cx.syms(ok: Bool, st: St, +size: U32) -> St & Pc:
  match ok:
    case True{}:
      sl.pc(sl.go(Nat.add(bits(size), 1n), (st, Sl{0, 8, 0, 0, 32768, Nil{}, False{}, False{}}), size))
    case False{}:
      (st, Pc{Nil{}, 0, False{}})

def cx.code(p: Pc, st: St, +ok: Bool, +size: U32) -> St & Pc:
  Pc{+ks, +ml, v} = p
  cx.syms(ok, st.code(st, 1023, ks, ml), size)

# The code length code sits in scratch slot 1023.
def cx.lens(r: St & Cc, +size: U32) -> St & Pc:
  (st, c) = r
  Cc{+ls, +space, +num, done, +bad} = c
  cx.code(pc.of(ls, True{}), st, Bool.and(Bool.not(bad), Bool.or(U32.is_eq(num, 1), U32.is_zero(space))), size)

def cx.read(st: St, +hskip: U32, +size: U32) -> St & Pc:
  cx.lens(cc.go(drop.n(bits(hskip), cl.order()), (st, Cc{rep(18n, 0, Nil{}), 32, 0, False{}, False{}})), size)

def pf.kind(simple: Bool, r: St & U32, +size: U32) -> St & Pc:
  match simple:
    case True{}:
      (st, h) = r
      sp.read(st.bits(st, 2), size)
    case False{}:
      (st, +h) = r
      cx.read(st, h, size)

def pf.hskip(r: St & U32, +size: U32) -> St & Pc:
  (st, +h) = r
  pf.kind(U32.is_eq(h, 1), (st, h), size)

def pf.build(r: St & Pc, +k: U32) -> St:
  (st, p) = r
  Pc{+ks, +ml, +ok} = p
  st.check(st.code(st, k, ks, ml), ok)

# Reads a prefix code over size symbols into slot k.
def rd.code(st: St, +k: U32, +size: U32) -> St:
  pf.build(pf.hskip(st.bits(st, 2), size), k)

# Ps fields by block category c: 0 literal, 1 insert-and-copy, 2 distance.
def ps.bk(+ps: Ps, +c: U32) -> Bk:
  Ps{+bl, +bi, +bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, bad} = ps
  Bool.pick(Bk, U32.is_zero(c), bl, Bool.pick(Bk, U32.is_eq(c, 1), bi, bd))

def ps.setbk(+ps: Ps, +c: U32, +b: Bk) -> Ps:
  Ps{+bl, +bi, +bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, bad} = ps
  Ps{Bool.pick(Bk, U32.is_zero(c), b, bl), Bool.pick(Bk, U32.is_eq(c, 1), b, bi), Bool.pick(Bk, U32.is_eq(c, 2), b, bd), npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, bad}

def ps.left(+ps: Ps) -> U32:
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, +left, bad} = ps
  left

def ps.setleft(+ps: Ps, +left: U32) -> Ps:
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, old, bad} = ps
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, bad}

def ps.litb(+ps: Ps) -> U32:
  Ps{bl, bi, bd, npost, ndir, +litb, icb, db, d1, d2, d3, d4, wsize, left, bad} = ps
  litb

def ps.icb(+ps: Ps) -> U32:
  Ps{bl, bi, bd, npost, ndir, litb, +icb, db, d1, d2, d3, d4, wsize, left, bad} = ps
  icb

def ps.db(+ps: Ps) -> U32:
  Ps{bl, bi, bd, npost, ndir, litb, icb, +db, d1, d2, d3, d4, wsize, left, bad} = ps
  db

def ps.d1(+ps: Ps) -> U32:
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, +d1, d2, d3, d4, wsize, left, bad} = ps
  d1

def ps.wsize(+ps: Ps) -> U32:
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, +wsize, left, bad} = ps
  wsize

def ps.push(+ps: Ps, +d: U32) -> Ps:
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, +d1, +d2, +d3, d4, wsize, left, bad} = ps
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d, d1, d2, d3, wsize, left, bad}

def bk.t(+b: Bk) -> U32:
  Bk{n, +t, pt, len} = b
  t

def bk.n(+b: Bk) -> U32:
  Bk{+n, t, pt, len} = b
  n

def bk.len(+b: Bk) -> U32:
  Bk{n, t, pt, +len} = b
  len

# Block counts (§6).
def bc.base() -> List<&2, U32>:
  [1, 5, 9, 13, 17, 25, 33, 41, 49, 65, 81, 97, 113, 145, 177, 209, 241, 305, 369, 497, 753, 1265, 2289, 4337, 8433, 16625]

def bc.extra() -> List<&2, U32>:
  [2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 7, 8, 9, 10, 11, 12, 13, 24]

def bc.of(r: St & U32, +s: U32) -> St & U32:
  (st, +x) = r
  (st, (nth(bc.base(), s) + x : U32))

def bc.sym(r: St & U32) -> St & U32:
  (st, +s) = r
  bc.of(st.bits(st, nth(bc.extra(), s)), s)

def bc.read(st: St, +k: U32) -> St & U32:
  bc.sym(st.sym(st, k))

# Block switch: type code 0 is the previous type, 1 the current type + 1, n + 2 type n.
def bs.cnt(r: St & U32, +n: U32, +nt: U32, +t: U32, +ok: Bool) -> St & Bk:
  (st, +cnt) = r
  (st.check(st, ok), Bk{n, nt, t, cnt})

def bs.new(r: St & U32, +b: Bk, +c: U32) -> St & Bk:
  (st, +s) = r
  Bk{+n, +t, +pt, len} = b
  +up = (t + 1 : U32)
  +nt = Bool.pick(U32, U32.is_zero(s), pt, Bool.pick(U32, U32.is_eq(s, 1), Bool.pick(U32, U32.is_eq(up, n), 0, up), (s - 2 : U32)))
  bs.cnt(bc.read(st, (2 * c + 1 : U32)), n, nt, t, U32.is_lt(nt, n))

def bs.sw(zero: Bool, st: St, +b: Bk, +c: U32) -> St & Bk:
  match zero:
    case True{}:
      bs.new(st.sym(st, (2 * c : U32)), b, c)
    case False{}:
      (st, b)

def bs.dec(r: St & Bk) -> St & Bk:
  (st, b) = r
  Bk{n, t, pt, +len} = b
  (st, Bk{n, t, pt, (len - 1 : U32)})

def bs.need(st: St, +b: Bk, +c: U32) -> St & Bk:
  bs.dec(bs.sw(U32.is_zero(bk.len(b)), st, b, c))

# Literals (§7.1): the tree comes from the block type and the context of the last two bytes.
def lit.put(r: St & U32) -> St:
  (st, +c) = r
  st.put(st, c)

def lit.tree(r: St & U32, +litb: U32) -> St:
  (st, +tr) = r
  lit.put(st.sym(st, (litb + tr : U32)))

def lit.cid(+mode: U32, +p1: U32, +p2: U32, +la: U32, +lb: U32) -> U32:
  Bool.pick(U32, U32.is_zero(mode), U32.and(p1, 63), Bool.pick(U32, U32.is_eq(mode, 1), U32.shrn(p1, 2n), Bool.pick(U32, U32.is_eq(mode, 2), U32.or(la, lb), U32.or(U32.shln(la, 3n), lb))))

def lit.lb(r: St & U32, +t: U32, +mode: U32, +p1: U32, +p2: U32, +la: U32, +litb: U32) -> St:
  (st, +lb) = r
  lit.tree(st.map(st, 0, (64 * t + lit.cid(mode, p1, p2, la, lb) : U32)), litb)

def lit.la(r: St & U32, +t: U32, +mode: U32, +p1: U32, +p2: U32, +litb: U32) -> St:
  (st, +la) = r
  lit.lb(st.map(st, 3, Bool.pick(U32, U32.is_eq(mode, 2), (256 + p2 : U32), (512 + p2 : U32))), t, mode, p1, p2, la, litb)

def lit.pp(r: St & U32, +t: U32, +mode: U32, +litb: U32) -> St:
  (st, +pp) = r
  +p1 = U32.and(pp, 255)
  lit.la(st.map(st, 3, Bool.pick(U32, U32.is_eq(mode, 2), p1, (512 + p1 : U32))), t, mode, p1, U32.shrn(pp, 8n), litb)

def lit.mode(r: St & U32, +t: U32, +litb: U32) -> St:
  (st, +mode) = r
  lit.pp(st.p12(st), t, mode, litb)

def lit.bk(r: St & Bk, +ps: Ps) -> St:
  (st, +b) = r
  lit.mode(st.map(st.set(st, ps.setbk(ps, 0, b)), 2, bk.t(b)), bk.t(b), ps.litb(ps))

def lit.start(r: St & Ps) -> St:
  (st, +ps) = r
  lit.bk(bs.need(st, ps.bk(ps, 0), 0), ps)

def lit.go(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+f:
      lit.go(f, lit.start(st.ps(st)))

# Distances (§4): a distance, its code, and whether it was valid.
type Dv is Data:
  Dv{d: U32, code: U32, ok: Bool}

def ds.special(+dc: U32, +d1: U32, +d2: U32, +d3: U32, +d4: U32) -> Dv:
  +base = Bool.pick(U32, U32.is_lt(dc, 4), Bool.pick(U32, U32.is_zero(dc), d1, Bool.pick(U32, U32.is_eq(dc, 1), d2, Bool.pick(U32, U32.is_eq(dc, 2), d3, d4))), Bool.pick(U32, U32.is_lt(dc, 10), d1, d2))
  +k = Bool.pick(U32, U32.is_lt(dc, 10), (dc - 4 : U32), (dc - 10 : U32))
  +mag = (U32.shr(k) + 1 : U32)
  +plus = U32.is_eq(U32.and(k, 1), 1)
  +small = U32.is_lt(dc, 4)
  Dv{Bool.pick(U32, small, base, Bool.pick(U32, plus, (base + mag : U32), (base - mag : U32))), dc, Bool.or(Bool.or(small, plus), U32.is_lt(mag, base))}

def ds.long(r: St & U32, +x: U32, +nb: U32, +npost: U32, +ndir: U32, +dc: U32) -> St & Dv:
  (st, +ex) = r
  +hcode = U32.shrn(x, bits(npost))
  +off = (U32.shln((2 + U32.and(hcode, 1) : U32), bits(nb)) - 4 : U32)
  (st, Dv{(U32.shln((off + ex : U32), bits(npost)) + U32.and(x, mask(npost)) + ndir + 1 : U32), dc, True{}})

def ds.kind(sp: Bool, direct: Bool, st: St, +dc: U32, +ps: Ps) -> St & Dv:
  match sp:
    case True{}:
      Ps{bl, bi, bd, npost, ndir, litb, icb, db, +d1, +d2, +d3, +d4, wsize, left, bad} = ps
      (st, ds.special(dc, d1, d2, d3, d4))
    case False{}:
      match direct:
        case True{}:
          (st, Dv{(dc - 15 : U32), dc, True{}})
        case False{}:
          Ps{bl, bi, bd, +npost, +ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, bad} = ps
          +x = (dc - ndir - 16 : U32)
          +nb = (1 + U32.shrn(x, bits((npost + 1 : U32))) : U32)
          ds.long(st.bits(st, nb), x, nb, npost, ndir, dc)

def ds.code(r: St & U32, +ps: Ps) -> St & Dv:
  (st, +dc) = r
  Ps{bl, bi, bd, npost, +ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, bad} = ps
  ds.kind(U32.is_lt(dc, 16), U32.is_lt(dc, (16 + ndir : U32)), st, dc, ps)

def ds.c(r: St & U32, +ps: Ps) -> St & Dv:
  (st, +tr) = r
  ds.code(st.sym(st, (ps.db(ps) + tr : U32)), ps)

def ds.b(r: St & Bk, +ps: Ps, +clen: U32) -> St & Dv:
  (st, +b) = r
  +ps2 = ps.setbk(ps, 2, b)
  ds.c(st.map(st.set(st, ps2), 1, (4 * bk.t(b) + Bool.pick(U32, U32.is_lt(4, clen), 3, (clen - 2 : U32)) : U32)), ps2)

def ds.a(r: St & Ps, +clen: U32) -> St & Dv:
  (st, +ps) = r
  ds.b(bs.need(st, ps.bk(ps, 2), 2), ps, clen)

def ds.read(st: St, +clen: U32) -> St & Dv:
  ds.a(st.ps(st), clen)

# Takes k off the bytes left in the meta-block.
def st.sub.of(r: St & Ps, +k: U32) -> St:
  (st, +ps) = r
  st.set(st, ps.setleft(ps, (ps.left(ps) - k : U32)))

def st.sub(st: St, +k: U32) -> St:
  st.sub.of(st.ps(st), k)

# Static dictionary reference (§8): word length clen, word id past the largest distance.
def ndbits() -> List<&2, U32>:
  [0, 0, 0, 0, 10, 10, 11, 11, 10, 10, 10, 10, 10, 9, 9, 8, 7, 7, 8, 7, 7, 6, 6, 5, 5]

def dict.put(st: St, +w: String, +ok: Bool) -> St:
  +n = slen(w, 0)
  st.sub(st.str(st.check(st, ok), Bool.pick(String, ok, w, "")), Bool.pick(U32, ok, n, 0))

def dict.ref(st: St, +d: U32, +clen: U32, +maxd: U32, +left: U32) -> St:
  +nb = nth(ndbits(), clen)
  +wid = (d - maxd - 1 : U32)
  +tid = U32.shrn(wid, bits(nb))
  +okw = Bool.and(Bool.and(U32.is_le(4, clen), U32.is_le(clen, 24)), U32.is_le(tid, 120))
  +w = D.transform(tid, D.word(clen, U32.and(wid, mask(nb))))
  dict.put(st, w, Bool.and(okw, U32.is_le(slen(w, 0), left)))

def cmd.copy(dict: Bool, st: St, +d: U32, +clen: U32, +maxd: U32, +left: U32) -> St:
  match dict:
    case True{}:
      dict.ref(st, d, clen, maxd, left)
    case False{}:
      +ok = U32.is_le(clen, left)
      +k = Bool.pick(U32, ok, clen, 0)
      st.sub(st.copy(st.check(st, ok), k, d), k)

# A distance past what is out so far (or past the window) names a dictionary word and is not remembered.
def cmd.run3(r: St & Ps, +dv: Dv, +clen: U32, +n: U32) -> St:
  (st, +ps) = r
  Dv{+d, +code, +ok} = dv
  +maxd = umin(ps.wsize(ps), n)
  +dict = U32.is_lt(maxd, d)
  +push = Bool.and(Bool.not(U32.is_zero(code)), Bool.not(dict))
  cmd.copy(dict, st.check(st.set(st, Bool.pick(Ps, push, ps.push(ps, d), ps)), ok), d, clen, maxd, ps.left(ps))

def cmd.run2(r: St & U32, +dv: Dv, +clen: U32) -> St:
  (st, +n) = r
  cmd.run3(st.ps(st), dv, clen, n)

def cmd.dist(r: St & Dv, +clen: U32) -> St:
  (st, +dv) = r
  cmd.run2(st.n(st), dv, clen)

def cmd.d0(r: St & Ps, +clen: U32) -> St:
  (st, +ps) = r
  cmd.run2(st.n(st), Dv{ps.d1(ps), 0, True{}}, clen)

def cmd.h(end: Bool, d0: Bool, st: St, +clen: U32) -> St:
  match end:
    case True{}:
      st
    case False{}:
      match d0:
        case True{}:
          cmd.d0(st.ps(st), clen)
        case False{}:
          cmd.dist(ds.read(st, clen), clen)

# When the literals finish the meta-block, the copy is ignored.
def cmd.g(r: St & Ps, +d0: Bool, +clen: U32, +ilen: U32) -> St:
  (st, +ps) = r
  +left = (ps.left(ps) - ilen : U32)
  cmd.h(U32.is_zero(left), d0, st.set(st, ps.setleft(ps, left)), clen)

def cmd.f(r: St & Ps, +d0: Bool, +ilen: U32, +clen: U32) -> St:
  (st, +ps) = r
  +ok = U32.is_le(ilen, ps.left(ps))
  +k = Bool.pick(U32, ok, ilen, 0)
  cmd.g(st.ps(lit.go(bits(k), st.check(st, ok))), d0, clen, k)

# Insert-and-copy codes (§5): insert and copy code bases by the code's 64-value cell.
def ic.ins() -> List<&2, U32>:
  [0, 0, 0, 0, 8, 8, 0, 16, 8, 16, 16]

def ic.cp() -> List<&2, U32>:
  [0, 8, 0, 8, 0, 8, 16, 0, 16, 8, 16]

def ins.base() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 18, 26, 34, 50, 66, 98, 130, 194, 322, 578, 1090, 2114, 6210, 22594]

def ins.extra() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 12, 14, 24]

def cp.base() -> List<&2, U32>:
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18, 22, 30, 38, 54, 70, 102, 134, 198, 326, 582, 1094, 2118]

def cp.extra() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 24]

def cmd.e(r: St & U32, +ic: U32, +ilen: U32, +cc: U32) -> St:
  (st, +cx) = r
  cmd.f(st.ps(st), U32.is_lt(ic, 128), ilen, (nth(cp.base(), cc) + cx : U32))

def cmd.d(r: St & U32, +ic: U32, +icode: U32, +cc: U32) -> St:
  (st, +ix) = r
  cmd.e(st.bits(st, nth(cp.extra(), cc)), ic, (nth(ins.base(), icode) + ix : U32), cc)

def cmd.c(r: St & U32) -> St:
  (st, +ic) = r
  +cell = U32.shrn(ic, 6n)
  +icode = (nth(ic.ins(), cell) + U32.and(U32.shrn(ic, 3n), 7) : U32)
  cmd.d(st.bits(st, nth(ins.extra(), icode)), ic, icode, (nth(ic.cp(), cell) + U32.and(ic, 7) : U32))

def cmd.b(r: St & Bk, +ps: Ps) -> St:
  (st, +b) = r
  +ps2 = ps.setbk(ps, 1, b)
  cmd.c(st.sym(st.set(st, ps2), (ps.icb(ps2) + bk.t(b) : U32)))

def cmd.a(r: St & Ps) -> St:
  (st, +ps) = r
  cmd.b(bs.need(st, ps.bk(ps, 1), 1), ps)

def cmd.step(on: Bool, st: St) -> St:
  match on:
    case True{}:
      cmd.a(st.ps(st))
    case False{}:
      st

def cmd.loop(r: St & Ps) -> St:
  (st, +ps) = r
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, +left, +bad} = ps
  cmd.step(Bool.and(U32.is_lt(0, left), Bool.not(bad)), st)

# Each command writes at least one byte, so left + 1 steps finish.
def cmd.go(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+f:
      cmd.go(f, cmd.loop(st.ps(st)))

# Numbers of block types and trees (§9.2): 1, 2, then 2^n + 1 + n more bits.
def vl.e(r: St & U32, +n: U32) -> St & U32:
  (st, +x) = r
  (st, (U32.shln(1, bits(n)) + 1 + x : U32))

def vl.d(zero: Bool, st: St, +n: U32) -> St & U32:
  match zero:
    case True{}:
      (st, 2)
    case False{}:
      vl.e(st.bits(st, n), n)

def vl.c(r: St & U32) -> St & U32:
  (st, +n) = r
  vl.d(U32.is_zero(n), st, n)

def vl.b(zero: Bool, st: St) -> St & U32:
  match zero:
    case True{}:
      (st, 1)
    case False{}:
      vl.c(st.bits(st, 3))

def vl.a(r: St & U32) -> St & U32:
  (st, +b) = r
  vl.b(U32.is_zero(b), st)

def vl.read(st: St) -> St & U32:
  vl.a(st.bits(st, 1))

# A block category's header: count, then (with two or more types) the type and count codes and the first count.
def bk.i3(r: St & U32, +n: U32) -> St & Bk:
  (st, +cnt) = r
  (st, Bk{n, 0, 1, cnt})

def bk.i2(many: Bool, st: St, +n: U32, +c: U32) -> St & Bk:
  match many:
    case True{}:
      bk.i3(bc.read(rd.code(rd.code(st, (2 * c : U32), (n + 2 : U32)), (2 * c + 1 : U32), 26), (2 * c + 1 : U32)), n)
    case False{}:
      (st, Bk{1, 0, 1, 16777216})

def bk.i1(r: St & U32, +c: U32) -> St & Bk:
  (st, +n) = r
  bk.i2(U32.is_le(2, n), st, n, c)

def bk.init(st: St, +c: U32) -> St & Bk:
  bk.i1(vl.read(st), c)

def cmode.set(r: St & U32, a: Array<U32>, +i: U32) -> St & Array<U32>:
  (st, +v) = r
  (st, Array.set(U32, a, i, v))

def cmode.go(k: Nat, r: St & Array<U32>, +i: U32) -> St & Array<U32>:
  match k:
    case 0n:
      r
    case 1n+f:
      (st, a) = r
      cmode.go(f, cmode.set(st.bits(st, 2), a, i), (i + 1 : U32))

# Context maps (§7.3): run lengths of zeros, then an optional inverse move-to-front.
type Cm is Type:
  Cm{st: St, a: Array<U32>, i: U32}

def cm.run(r: St & U32, a: Array<U32>, +i: U32, +s: U32, +size: U32) -> Cm:
  (st, +x) = r
  +ni = (i + U32.shln(1, bits(s)) + x : U32)
  Cm{st.check(st, U32.is_le(ni, size)), a, umin(ni, size)}

def cm.kind(zero: Bool, run: Bool, st: St, a: Array<U32>, +i: U32, +s: U32, +size: U32, +rlemax: U32) -> Cm:
  match zero:
    case True{}:
      Cm{st, a, (i + 1 : U32)}
    case False{}:
      match run:
        case True{}:
          cm.run(st.bits(st, s), a, i, s, size)
        case False{}:
          Cm{st, Array.set(U32, a, i, (s - rlemax : U32)), (i + 1 : U32)}

def cm.sym(r: St & U32, a: Array<U32>, +i: U32, +size: U32, +rlemax: U32) -> Cm:
  (st, +s) = r
  cm.kind(U32.is_zero(s), U32.is_le(s, rlemax), st, a, i, s, size, rlemax)

def cm.more(on: Bool, st: St, a: Array<U32>, +i: U32, +size: U32, +rlemax: U32) -> Cm:
  match on:
    case True{}:
      cm.sym(st.sym(st, 1022), a, i, size, rlemax)
    case False{}:
      Cm{st, a, i}

def cm.go(k: Nat, c: Cm, +size: U32, +rlemax: U32) -> Cm:
  match k:
    case 0n:
      c
    case 1n+f:
      Cm{st, a, +i} = c
      cm.go(f, cm.more(U32.is_lt(i, size), st, a, i, size, rlemax), size, rlemax)

def ilist(k: Nat, +i: U32) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+f:
      Con{i, ilist(f, (i + 1 : U32))}

def ldel(k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          t
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, ldel(p, t)}

def mtf.one(av: Array<U32> & U32, +m: List<&2, U32>, +i: U32) -> Array<U32> & List<&2, U32>:
  (a, +v) = av
  +val = nth(m, v)
  (Array.set(U32, a, i, val), Con{val, ldel(bits(v), m)})

def mtf.go(k: Nat, st: Array<U32> & List<&2, U32>, +i: U32) -> Array<U32> & List<&2, U32>:
  match k:
    case 0n:
      st
    case 1n+f:
      (a, +m) = st
      mtf.go(f, mtf.one(Array.get(U32, a, i), m, i), (i + 1 : U32))

def mtf.fin(st: Array<U32> & List<&2, U32>) -> Array<U32>:
  (a, m) = st
  a

def cm.mtf2(on: Bool, st: St, a: Array<U32>, +size: U32) -> St & Array<U32>:
  match on:
    case True{}:
      (st, mtf.fin(mtf.go(bits(size), (a, ilist(256n, 0)), 0)))
    case False{}:
      (st, a)

def cm.mtf(r: St & U32, a: Array<U32>, +size: U32) -> St & Array<U32>:
  (st, +b) = r
  cm.mtf2(U32.is_eq(b, 1), st, a, size)

def cm.max.of(av: Array<U32> & U32, +m: U32) -> Array<U32> & U32:
  (a, +v) = av
  (a, umax(v, m))

def cm.max(k: Nat, st: Array<U32> & U32, +i: U32) -> Array<U32> & U32:
  match k:
    case 0n:
      st
    case 1n+f:
      (a, +m) = st
      cm.max(f, cm.max.of(Array.get(U32, a, i), m), (i + 1 : U32))

def cm.chk2(am: Array<U32> & U32, st: St, +ntrees: U32) -> St & Array<U32>:
  (a, +m) = am
  (st.check(st, U32.is_lt(m, ntrees)), a)

# Every value must name one of the ntrees trees.
def cm.check(r: St & Array<U32>, +size: U32, +ntrees: U32) -> St & Array<U32>:
  (st, a) = r
  cm.chk2(cm.max(bits(size), (a, 0), 0), st, ntrees)

def cm.r4(c: Cm, +ntrees: U32, +size: U32) -> St & Array<U32>:
  Cm{st, a, i} = c
  cm.check(cm.mtf(st.bits(st, 1), a, size), size, ntrees)

# RLEMAX: one 0 bit, or a 1 bit and four more bits (§7.3). The map's code sits in scratch slot 1022.
def cm.r3(r: St & U32, a: Array<U32>, +ntrees: U32, +size: U32, +on: U32) -> St & Array<U32>:
  (st, +x) = r
  +rlemax = Bool.pick(U32, U32.is_eq(on, 1), (x + 1 : U32), 0)
  cm.r4(cm.go(bits(size), Cm{rd.code(st, 1022, (ntrees + rlemax : U32)), a, 0}, size, rlemax), ntrees, size)

def cm.r2(on: Bool, st: St, a: Array<U32>, +ntrees: U32, +size: U32) -> St & Array<U32>:
  match on:
    case True{}:
      cm.r3(st.bits(st, 4), a, ntrees, size, 1)
    case False{}:
      cm.r3((st, 0), a, ntrees, size, 0)

def cm.r1(r: St & U32, a: Array<U32>, +ntrees: U32, +size: U32) -> St & Array<U32>:
  (st, +b) = r
  cm.r2(U32.is_eq(b, 1), st, a, ntrees, size)

def cm.r0(many: Bool, st: St, a: Array<U32>, +ntrees: U32, +size: U32) -> St & Array<U32>:
  match many:
    case True{}:
      cm.r1(st.bits(st, 1), a, ntrees, size)
    case False{}:
      (st, a)

def cm.read(st: St, +ntrees: U32, +size: U32) -> St & Array<U32>:
  cm.r0(U32.is_le(2, ntrees), st, Array.new(U32, depth(31n, 0n, size), 0), ntrees, size)

def codes.go(k: Nat, st: St, +slot: U32, +size: U32) -> St:
  match k:
    case 0n:
      st
    case 1n+f:
      codes.go(f, rd.code(st, slot, size), (slot + 1 : U32), size)

# Compressed meta-block (§9.2): block categories, distance parameters, context modes and maps, then the prefix codes.
def mb.c11(r: St & Ps, +bl: Bk, +bi: Bk, +bd: Bk, +np: U32, +ndir: U32, +icb: U32, +db: U32, +mlen: U32) -> St:
  (st, ps) = r
  Ps{a, b, c, e, f, g, h, i, +d1, +d2, +d3, +d4, +wsize, left, +bad} = ps
  cmd.go(Nat.add(bits(mlen), 1n), st.set(st, Ps{bl, bi, bd, np, ndir, 6, icb, db, d1, d2, d3, d4, wsize, mlen, bad}))

def mb.c10(r: St & Array<U32>, cmode: Array<U32>, cml: Array<U32>, +ntl: U32, +ntd: U32, +bl: Bk, +bi: Bk, +bd: Bk, +np: U32, +ndir: U32, +mlen: U32) -> St:
  (st, cmd) = r
  +icb = (6 + ntl : U32)
  +db = (icb + bk.n(bi) : U32)
  mb.c11(st.ps(codes.go(bits(ntd), codes.go(bits(bk.n(bi)), codes.go(bits(ntl), st.maps(st, cml, cmd, cmode), 6, 256), icb, 704), db, (16 + ndir + U32.shln(48, bits(np)) : U32))), bl, bi, bd, np, ndir, icb, db, mlen)

def mb.c9(r: St & U32, cmode: Array<U32>, cml: Array<U32>, +ntl: U32, +bl: Bk, +bi: Bk, +bd: Bk, +np: U32, +ndir: U32, +mlen: U32) -> St:
  (st, +ntd) = r
  mb.c10(cm.read(st.check(st, U32.is_le(ntd, 256)), ntd, (4 * bk.n(bd) : U32)), cmode, cml, ntl, ntd, bl, bi, bd, np, ndir, mlen)

def mb.c8(r: St & Array<U32>, cmode: Array<U32>, +ntl: U32, +bl: Bk, +bi: Bk, +bd: Bk, +np: U32, +ndir: U32, +mlen: U32) -> St:
  (st, cml) = r
  mb.c9(vl.read(st), cmode, cml, ntl, bl, bi, bd, np, ndir, mlen)

def mb.c7(r: St & U32, cmode: Array<U32>, +bl: Bk, +bi: Bk, +bd: Bk, +np: U32, +ndir: U32, +mlen: U32) -> St:
  (st, +ntl) = r
  mb.c8(cm.read(st.check(st, U32.is_le(ntl, 256)), ntl, (64 * bk.n(bl) : U32)), cmode, ntl, bl, bi, bd, np, ndir, mlen)

def mb.c6(r: St & Array<U32>, +bl: Bk, +bi: Bk, +bd: Bk, +np: U32, +ndir: U32, +mlen: U32) -> St:
  (st, cmode) = r
  mb.c7(vl.read(st), cmode, bl, bi, bd, np, ndir, mlen)

def mb.c5(r: St & U32, +bl: Bk, +bi: Bk, +bd: Bk, +np: U32, +mlen: U32) -> St:
  (st, +nd) = r
  mb.c6(cmode.go(bits(bk.n(bl)), (st, Array.new(U32, 8n, 0)), 0), bl, bi, bd, np, U32.shln(nd, bits(np)), mlen)

def mb.c4(r: St & U32, +bl: Bk, +bi: Bk, +bd: Bk, +mlen: U32) -> St:
  (st, +np) = r
  mb.c5(st.bits(st, 4), bl, bi, bd, np, mlen)

def mb.c3(r: St & Bk, +bl: Bk, +bi: Bk, +mlen: U32) -> St:
  (st, +bd) = r
  mb.c4(st.bits(st, 2), bl, bi, bd, mlen)

def mb.c2(r: St & Bk, +bl: Bk, +mlen: U32) -> St:
  (st, +bi) = r
  mb.c3(bk.init(st, 2), bl, bi, mlen)

def mb.c1(r: St & Bk, +mlen: U32) -> St:
  (st, +bl) = r
  mb.c2(bk.init(st, 1), bl, mlen)

def mb.comp(st: St, +mlen: U32) -> St:
  mb.c1(bk.init(st.reset(st), 0), mlen)

# Uncompressed meta-block: MLEN raw bytes from the next byte boundary.
def unc.go(k: Nat, st: St) -> St:
  match k:
    case 0n:
      st
    case 1n+f:
      unc.go(f, lit.put(st.bits(st, 8)))

# Metadata meta-block: skipped.
def meta.c(r: St & U32, +sb: U32, +rsv: U32) -> St:
  (st, +sl) = r
  +n = Bool.pick(U32, U32.is_zero(sb), 0, (sl + 1 : U32))
  st.check(st.skip(st.align(st), (8 * n : U32)), U32.is_zero(rsv))

def meta.b(r: St & U32, +rsv: U32) -> St:
  (st, +sb) = r
  meta.c(st.bits(st, (8 * sb : U32)), sb, rsv)

def meta.a(r: St & U32) -> St:
  (st, +rsv) = r
  meta.b(st.bits(st, 2), rsv)

# A meta-block (§9.2); answers 1 after the last one.
def mb.u2(unc: Bool, st: St, +mlen: U32) -> St & U32:
  match unc:
    case True{}:
      (unc.go(bits(mlen), st.align(st)), 0)
    case False{}:
      (mb.comp(st, mlen), 0)

def mb.u1(r: St & U32, +mlen: U32) -> St & U32:
  (st, +u) = r
  mb.u2(U32.is_eq(u, 1), st, mlen)

def mb.l2(last: Bool, st: St, +mlen: U32) -> St & U32:
  match last:
    case True{}:
      (mb.comp(st, mlen), 1)
    case False{}:
      mb.u1(st.bits(st, 1), mlen)

def mb.len(r: St & U32, +nib: U32, +last: Bool) -> St & U32:
  (st, +m) = r
  mb.l2(last, st.check(st, Bool.or(U32.is_le(nib, 4), Bool.not(U32.is_zero(U32.shrn(m, bits((4 * nib - 4 : U32))))))), (m + 1 : U32))

def mb.n2(meta: Bool, st: St, +mn: U32, +last: Bool) -> St & U32:
  match meta:
    case True{}:
      (meta.a(st.bits(st, 1)), Bool.pick(U32, last, 1, 0))
    case False{}:
      mb.len(st.bits(st, (4 * mn + 16 : U32)), (mn + 4 : U32), last)

def mb.n1(r: St & U32, +last: Bool) -> St & U32:
  (st, +mn) = r
  mb.n2(U32.is_eq(mn, 3), st, mn, last)

def mb.nib(st: St, +last: Bool) -> St & U32:
  mb.n1(st.bits(st, 2), last)

def mb.r4(empty: Bool, st: St) -> St & U32:
  match empty:
    case True{}:
      (st, 1)
    case False{}:
      mb.nib(st, True{})

def mb.r3(r: St & U32) -> St & U32:
  (st, +e) = r
  mb.r4(U32.is_eq(e, 1), st)

def mb.r2(last: Bool, st: St) -> St & U32:
  match last:
    case True{}:
      mb.r3(st.bits(st, 1))
    case False{}:
      mb.nib(st, False{})

def mb.r1(r: St & U32) -> St & U32:
  (st, +last) = r
  mb.r2(U32.is_eq(last, 1), st)

def mb.read(st: St) -> St & U32:
  mb.r1(st.bits(st, 1))

def br.step(stop: Bool, st: St, +last: U32) -> St & U32:
  match stop:
    case True{}:
      (st, last)
    case False{}:
      mb.read(st)

def br.chk(r: St & Bool, +last: U32) -> St & U32:
  (st, +bad) = r
  br.step(Bool.or(bad, U32.is_eq(last, 1)), st, last)

# Each meta-block uses at least one byte of input.
def br.go(k: Nat, r: St & U32) -> St & U32:
  match k:
    case 0n:
      r
    case 1n+f:
      (st, +last) = r
      br.go(f, br.chk(st.bad(st), last))

# WBITS (§9.1): 0 means the reserved pattern.
def wb.c(r: St & U32) -> St & U32:
  (st, +m) = r
  (st, Bool.pick(U32, U32.is_zero(m), 17, Bool.pick(U32, U32.is_eq(m, 1), 0, (8 + m : U32))))

def wb.b2(zero: Bool, st: St, +n: U32) -> St & U32:
  match zero:
    case True{}:
      wb.c(st.bits(st, 3))
    case False{}:
      (st, (17 + n : U32))

def wb.b(r: St & U32) -> St & U32:
  (st, +n) = r
  wb.b2(U32.is_zero(n), st, n)

def wb.a2(zero: Bool, st: St) -> St & U32:
  match zero:
    case True{}:
      (st, 16)
    case False{}:
      wb.b(st.bits(st, 3))

def wb.a(r: St & U32) -> St & U32:
  (st, +b) = r
  wb.a2(U32.is_zero(b), st)

def lut() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 12, 16, 12, 12, 20, 12, 16, 24, 28, 12, 12, 32, 12, 36, 12, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 32, 32, 24, 40, 28, 12, 12, 48, 52, 52, 52, 48, 52, 52, 52, 48, 52, 52, 52, 52, 52, 48, 52, 52, 52, 52, 52, 48, 52, 52, 52, 52, 52, 24, 12, 28, 12, 12, 12, 56, 60, 60, 60, 56, 60, 60, 60, 56, 60, 60, 60, 60, 60, 56, 60, 60, 60, 60, 60, 56, 60, 60, 60, 60, 60, 24, 12, 28, 12, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7]

def br.pick(+out: String, ok: Bool) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{out}
    case False{}:
      None{}

# The stream must end with the last meta-block, on the input's last byte.
def br.fin(r: St & U32, +len: U32) -> Maybe<&2, String>:
  (st, +last) = r
  St{io, o, mp, +ps} = st
  Io{a, +p, t, td, fill, dir} = io
  Ob{w, wd, wmax, n, racc, p1, p2} = o
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, +bad} = ps
  br.pick(String.reverse(racc), Bool.and(Bool.and(Bool.not(bad), U32.is_eq(last, 1)), U32.is_eq(U32.shrn((p + 7 : U32), 3n), len)))

def br.start(r: St & U32, +len: U32) -> Maybe<&2, String>:
  (st, +wb) = r
  St{io, o, mp, +ps} = st
  Ob{w, wd, wmax, n, racc, p1, p2} = o
  Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, wsize, left, bad} = ps
  br.fin(br.go(Nat.add(Nat.mul(bits(len), 8n), 2n), (St{io, Ob{w, wd, wb, n, racc, p1, p2}, mp, Ps{bl, bi, bd, npost, ndir, litb, icb, db, d1, d2, d3, d4, (U32.shln(1, bits(wb)) - 16 : U32), left, U32.is_zero(wb)}}, 0)), len)

# A brotli stream (RFC 7932). None: malformed, cut short, or followed by more bytes.
def decode(+s: String) -> Maybe<&2, String>:
  +len = slen(s, 0)
  +bk = {Bk{1, 0, 1, 16777216} : Bk}
  +ps = {Ps{bk, bk, bk, 0, 0, 6, 6, 6, 4, 11, 15, 16, 0, 0, False{}} : Ps}
  io = {Io{src.fill(s, 0, Array.new(U32, depth(31n, 0n, (len + 8 : U32)), 0)), 0, Array.new(U32, 10n, 0), 10, 0, Array.new(U32, 10n, 0)} : Io}
  br.start(wb.a(st.bits(St{io, Ob{Array.new(U32, 10n, 0), 10, 10, 0, "", 0, 0}, Mp{Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), ar.fill(lut(), 0, Array.new(U32, 10n, 0))}, ps}, 1)), len)
