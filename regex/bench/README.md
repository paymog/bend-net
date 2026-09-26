# Regex benchmark

Times `Regex.is_match` and `Regex.find` on fixed inputs against POSIX `regex.h`, Python `re`, and JavaScript `RegExp`.

## Run

```sh
python3 run.py      # 3 runs per case, median; Bend smoke (4096 code points) first
python3 run.py 5    # 5 runs
```

You need `bend`, `clang`, `python3`, `bun`, and `node`. Binaries go to `out/`, which git ignores. `run.py` exits non-zero if a build fails or the checksums disagree. The `redos` case uses a 10 s per-run timeout; backtracking engines that hang are recorded as `timeout`.

## Input

Text is built deterministically at **N = 2^20** code points (about 1 MiB of ASCII):

1. Fill with `x`.
2. At **N − 50**, write `user@host.com` (13 code points).
3. At **N − 20**, write `helloworld12` (12 code points).

The ReDoS input is **100 000** `a` with no trailing `b`. The `large` input is **1000** `x` then one `y`.

## Cases

| case | Bend / Python / JS pattern | POSIX ERE (C) | work | checksum |
|---|---|---|---|---|
| `is_match` | `hello\w+` | `hello[[:alnum:]_]+` | leftmost match of the hello prefix | u32 hash of group-0 start/end (0 if no match) |
| `find_captures` | `(\w+)@(\w+)\.com` | `([[:alnum:]_]+)@([[:alnum:]_]+)\.com` | leftmost match with two captures | hash of groups 0–2 spans |
| `redos` | `(a*)*b` | `(a*)*b` | no match on 100k `a` | 0 |
| `large` | `(?:x?){1000}y` | `((x?){250}){4}y` | about 2000 instructions; each char walks a closure over most of them | u32 hash of group-0 span |

Hash: for each group, if missing then `h = h * 31`; else `h = h * 31 + start` then `h = h * 31 + end` (u32 wrap). Positions are code-point indexes in Bend and byte indexes in the other languages; the input is ASCII so they agree.

Compile the pattern **outside** the timed region. Bend uses a native build (`bend bench.bend -o out/bend`); the checker runner is not used for the 1 MiB input.

## Rust

Rust's standard library has no regular expression engine, so Rust is left out.

## Results

Apple M4 Pro, macOS, 2026-09-26. Median of three runs (`python3 run.py 3`). Times are ms for one match on the 1 MiB text (or 100k `a` for `redos`, 1001 chars for `large`).

Versions: Bend 2.0.29, Apple clang 17.0.0, Python 3.14.6, Bun 1.3.14, Node v24.0.1.

| op | C | Python | Bun | Node | Bend |
|---|---:|---:|---:|---:|---:|
| is_match | 0.0 | 0.3 | 0.2 | 0.2 | 172.0 |
| find_captures | 17.6 | 2.8 | 0.8 | 0.7 | 757.0 |
| redos | 3.0 | timeout | 858.5 | timeout | 116.0 |
| large | 2,317.8 | 0.0 | 0.1 | 0.1 | 894.0 |

Checksums: `is_match` 33553812, `find_captures` 3021334545, `redos` 0, `large` 1001. All non-timeout variants agree.

### Program size

The program and the visited set are binary tries keyed by pc, so a closure step costs O(log pc), not O(m). `(?:x?){k}y` on 200 `x` then `y`, Bend ms, one run each:

| k | 125 | 250 | 500 | 1000 |
|---|---:|---:|---:|---:|
| list (0.1.0.0) | 149 | 600 | 2537 | 15224 |
| trie (0.2.0.0) | 17 | 38 | 88 | 222 |

The list grows about 4–6× per doubling of k (m²); the trie grows about 2.3× (m log m). On `large`, 0.1.0.0 takes 65 374 ms. The trie costs a little on tiny patterns, where every hot pc is near the list head: `is_match` was about 140 ms with lists.

## Caveats

- Bend strings are `Char` lists; the gap on large inputs is mostly allocation layout, not just the Pike VM.
- POSIX ERE has no `\w`; `[[:alnum:]_]` is the documented equivalent for ASCII word characters.
- `IO.now` in Bend is whole milliseconds; C and the scripting languages use sub-ms clocks.
