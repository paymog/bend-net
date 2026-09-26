# Zlib benchmark

This times `gunzip` on one fixed gzip member and `gzip` on its plain text, in Bend and in JavaScript (Bun and Node) and Python.

## Run

```sh
python3 run.py      # 3 runs per variant, median, 4 MiB plain
python3 run.py 5    # 5 runs
python3 run.py 1 65536   # 1 run on 64 KiB plain; check RSS and checksum first after a change
```

You need `bend`, `bun`, `node`, `python3`, and `gzip`. `run.py` writes the plain text to `out/plain.bin`, the gzip member to `out/payload.gz`, and the Bend binary to `out/`, which git ignores. The run takes about ten seconds. It exits non-zero if a build fails, if two languages print different checksums, or if system `gzip -d` does not turn Bend's output (`out/bend.gz`) back into the plain text.

C and Rust are omitted: neither standard library ships gzip or DEFLATE.

## Input

`run.py` builds **N = 4,194,304** bytes (4 MiB) of deterministic ASCII text:

- Seed **0xDEADBEEF** drives an LCG that builds **1024** unique sentences from a fixed **247-word** vocabulary (6–17 words each, period-terminated).
- Seed **0xC0FFEE01** walks the plain text: append a sentence (space-separated), a newline, or a raw byte from the LCG (~3% random bytes, ~1.5% newlines).
- Gzip level **6**, **mtime=0**. Wire size **1,050,286** bytes; compression ratio **3.99×** (plain ÷ gzip).

Each program reads its inputs before any timer starts. The timed ops:

- **`inflate`**: one `gunzip` / `gzip.decompress` / `gunzipSync` call on `out/payload.gz`.
- **`deflate`**: one `gzip` / `gzip.compress` / `gzipSync` call on `out/plain.bin`, level 6 where the library has levels. Bend's `gzip` has no levels; its settings follow zlib level 6.

After each timer stops, the program prints a checksum of the plain bytes: `h = h*31 + b` in wrapping u32. For `deflate`, that is the checksum of its own output gunzipped again. Expected for both: **2339964736**.

Throughput in the table is plain bytes per second (decimal MB/s). **gzip bytes** is the size of each language's `deflate` output.

Bend reads the files with `File.read_bytes` so the bytes are not UTF-8 decoded. Bend peak RSS was about **217 MB** on the 4 MiB run.

## Results

M4 Pro, macOS 26.6.2, arm64, 2026-09-26. Median of five runs (`python3 run.py 5`). Times are in ms.

| variant | inflate ms | inflate MB/s | deflate ms | deflate MB/s | gzip bytes | ratio |
|---:|---:|---:|---:|---:|---:|---:|
| Bun | 6.4 | 652 | 41.1 | 102 | 1,063,003 | 3.95x |
| Node | 6.3 | 664 | 76.4 | 55 | 1,045,511 | 4.01x |
| Python | 2.8 | 1,489 | 118.6 | 35 | 1,050,286 | 3.99x |
| Bend | 205.0 | 20 | 840.0 | 5 | 1,046,915 | 4.01x |

Bend's `deflate` uses lazy matching and picks dynamic Huffman, fixed Huffman, or stored for each block of 16384 symbols.

Versions: Bend 2.0.29, Bun 1.3.14, Node 24.0.1, Python 3.14.6.
