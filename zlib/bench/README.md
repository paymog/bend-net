# Zlib benchmark

This times `gunzip` on one fixed gzip member, `gzip` on its plain text, and zstd and brotli decoding of the same text, in Bend and in JavaScript (Bun and Node) and Python.

## Run

```sh
python3 run.py      # 3 runs per variant, median, 4 MiB plain
python3 run.py 5    # 5 runs
python3 run.py 1 65536   # 1 run on 64 KiB plain; check RSS and checksum first after a change
```

You need `bend`, `bun`, `node`, `python3` (3.14, for `compression.zstd`), and `gzip`. `run.py` writes the plain text to `out/plain.bin`, the gzip member to `out/payload.gz`, the zstd frame to `out/payload.zst`, the brotli stream to `out/payload.br`, and the Bend binary to `out/`, which git ignores. The run takes about half a minute. It exits non-zero if a build fails, if two checksums differ, or if system `gzip -d` does not turn Bend's output (`out/bend.gz`) back into the plain text.

C and Rust are omitted: neither standard library ships gzip, DEFLATE, zstd, or brotli. Python has no brotli column: its standard library has no brotli.

## Input

`run.py` builds **N = 4,194,304** bytes (4 MiB) of deterministic ASCII text:

- Seed **0xDEADBEEF** drives an LCG that builds **1024** unique sentences from a fixed **247-word** vocabulary (6–17 words each, period-terminated).
- Seed **0xC0FFEE01** walks the plain text: append a sentence (space-separated), a newline, or a raw byte from the LCG (~3% random bytes, ~1.5% newlines).
- Gzip level **6**, **mtime=0**. Wire size **1,050,286** bytes; compression ratio **3.99×** (plain ÷ gzip).
- Zstd level **3** with a content checksum (Python `compression.zstd`): **213,883** bytes, **19.61×**. Brotli quality **11**, window 22 (Node `brotliCompressSync` defaults): **187,159** bytes, **22.41×**.

Each program reads its inputs before any timer starts. The timed ops:

- **`inflate`**: one `gunzip` / `gzip.decompress` / `gunzipSync` call on `out/payload.gz`.
- **`deflate`**: one `gzip` / `gzip.compress` / `gzipSync` call on `out/plain.bin`, level 6 where the library has levels. Bend's `gzip` has no levels.
- **`zstd`**: one `Zstd.decode` / `compression.zstd.decompress` / `zstdDecompressSync` call on `out/payload.zst`.
- **`brotli`**: one `Brotli.decode` / `brotliDecompressSync` call on `out/payload.br`.

After each timer stops, the program prints a checksum of the plain bytes: `h = h*31 + b` in wrapping u32. For `deflate`, that is the checksum of its own output gunzipped again. Expected for every op: **2339964736**.

Throughput in the table is plain bytes per second (decimal MB/s). **gzip bytes** is the size of each language's `deflate` output.

Bend reads the files with `File.read_bytes` so the bytes are not UTF-8 decoded. Bend peak RSS was about **249 MB** on the 4 MiB run, over all four ops.

## Results

M4 Pro, macOS 26.6.2, arm64, 2026-09-26. Median of five runs (`python3 run.py 5`). Times are in ms; Bend's clock counts whole milliseconds.

| variant | inflate ms | inflate MB/s | deflate ms | deflate MB/s | gzip bytes | ratio |
|---:|---:|---:|---:|---:|---:|---:|
| Bun | 8.1 | 521 | 41.1 | 102 | 1,063,003 | 3.95x |
| Node | 6.7 | 622 | 79.4 | 53 | 1,045,511 | 4.01x |
| Python | 2.9 | 1,462 | 123.2 | 34 | 1,050,286 | 3.99x |
| Bend | 255.0 | 16 | 1,009.0 | 4 | 1,422,023 | 2.95x |

| variant | zstd ms | zstd MB/s | brotli ms | brotli MB/s |
|---:|---:|---:|---:|---:|
| Bun | 1.6 | 2,551 | 2.0 | 2,089 |
| Node | 1.9 | 2,236 | 1.9 | 2,195 |
| Python | 1.3 | 3,339 | — | — |
| Bend | 131.0 | 32 | 229.0 | 18 |

Bend's ratio is lower because it writes one fixed-Huffman block with greedy matching; the others use dynamic Huffman trees and lazy matching.

Versions: Bend 2.0.29, Bun 1.3.14, Node 24.0.1, Python 3.14.6.
