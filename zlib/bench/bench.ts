// Run with node or bun, from this folder, after run.py has written out/payload.gz and out/plain.bin.
import { readFileSync } from "node:fs";
import { brotliDecompressSync, gunzipSync, gzipSync, zstdDecompressSync } from "node:zlib";

const gz = readFileSync("out/payload.gz");
const zst = readFileSync("out/payload.zst");
const br = readFileSync("out/payload.br");
const plain = readFileSync("out/plain.bin");

function chk(b: Buffer): number {
  let h = 0;
  for (let i = 0; i < b.length; i++) h = (Math.imul(h, 31) + b[i]!) >>> 0;
  return h;
}

let t0 = performance.now();
const out = gunzipSync(gz);
let ms = performance.now() - t0;
console.log(`inflate\t${ms.toFixed(3)}\t${chk(out)}`);

t0 = performance.now();
const packed = gzipSync(plain, { level: 6 });
ms = performance.now() - t0;
console.log(`deflate\t${ms.toFixed(3)}\t${chk(gunzipSync(packed))}`);
console.log(`size\t0\t${packed.length}`);

t0 = performance.now();
const unz = zstdDecompressSync(zst);
ms = performance.now() - t0;
console.log(`zstd\t${ms.toFixed(3)}\t${chk(unz)}`);

t0 = performance.now();
const unbr = brotliDecompressSync(br);
ms = performance.now() - t0;
console.log(`brotli\t${ms.toFixed(3)}\t${chk(unbr)}`);
