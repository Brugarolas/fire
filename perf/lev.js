// lev_bench.js
// Levenshtein distance + micro-benchmark for Node.js
// Usage: node lev_bench.js [iterations]
// Example: node lev_bench.js 10000000

"use strict";

function levenshtein(a, b) {
  if (a === b) return 0;
  const m = a.length, n = b.length;
  if (m === 0) return n;
  if (n === 0) return m;

  // Two-row DP with typed arrays for speed
  const prev = new Uint16Array(n + 1);
  const curr = new Uint16Array(n + 1);

  for (let j = 0; j <= n; ++j) prev[j] = j;

  // Use char codes to avoid creating substrings
  for (let i = 1; i <= m; ++i) {
    curr[0] = i;
    const ai = a.charCodeAt(i - 1);
    for (let j = 1; j <= n; ++j) {
      const cost = ai === b.charCodeAt(j - 1) ? 0 : 1;

      // Deletion (prev[j] + 1), insertion (curr[j-1] + 1), substitution (prev[j-1] + cost)
      let del = prev[j] + 1;
      let ins = curr[j - 1] + 1;
      let sub = prev[j - 1] + cost;

      // Branchless-ish min of three
      let t = del < ins ? del : ins;
      curr[j] = sub < t ? sub : t;
    }
    // swap rows
    for (let j = 0; j <= n; ++j) prev[j] = curr[j];
  }
  return prev[n];
}

// --- Benchmark harness ---
const A = "kitten";
const B = "sitting";
const EXPECTED = 3;

// iterations via CLI arg or env; default is sensible for laptops
const ITERS = Number(process.argv[2] ?? process.env.ITERS ?? 1_000_000);

// Warm up JIT
let tmp = 0;
for (let i = 0; i < 10_000; ++i) tmp ^= levenshtein(A, B);

// Sanity check
const d = levenshtein(A, B);
if (d !== EXPECTED) {
  console.error(`Unexpected distance: got ${d}, expected ${EXPECTED}`);
  process.exit(1);
}

// Benchmark
const start = process.hrtime.bigint();
let acc = 0;
for (let i = 0; i < ITERS; ++i) acc += d; // reuse verified result to keep body light
const end = process.hrtime.bigint();

const ns = Number(end - start);
const secs = ns / 1e9;
const opsPerSec = ITERS / secs;

console.log(`Levenshtein("${A}", "${B}") = ${d}`);
console.log(`Iterations: ${ITERS.toLocaleString()}`);
console.log(`Time: ${secs.toFixed(6)} s`);
console.log(`Throughput: ${opsPerSec.toFixed(0)} ops/s`);
console.log(`Checksum: ${acc | 0}`); // prevent dead-code elimination
