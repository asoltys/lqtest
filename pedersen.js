import { ProjectivePoint, etc, utils, CURVE } from "@noble/secp256k1";

const scalarFromSigned30 = (a) => {
  const r = new Uint32Array(8);

  const a0 = a.v[0],
    a1 = a.v[1],
    a2 = a.v[2],
    a3 = a.v[3],
    a4 = a.v[4],
    a5 = a.v[5],
    a6 = a.v[6],
    a7 = a.v[7],
    a8 = a.v[8];

  // The output from secp256k1_modinv32{_var} should be normalized to range [0,modulus),
  // and have limbs in [0,2^30). The modulus is < 2^256, so the top limb must be below 2^(256-30*8).
  if (
    a0 >> 30 !== 0 ||
    a1 >> 30 !== 0 ||
    a2 >> 30 !== 0 ||
    a3 >> 30 !== 0 ||
    a4 >> 30 !== 0 ||
    a5 >> 30 !== 0 ||
    a6 >> 30 !== 0 ||
    a7 >> 30 !== 0 ||
    a8 >> 16 !== 0
  ) {
    throw new Error("Input out of range");
  }

  r[0] = a0 | (a1 << 30);
  r[1] = (a1 >> 2) | (a2 << 28);
  r[2] = (a2 >> 4) | (a3 << 26);
  r[3] = (a3 >> 6) | (a4 << 24);
  r[4] = (a4 >> 8) | (a5 << 22);
  r[5] = (a5 >> 10) | (a6 << 20);
  r[6] = (a6 >> 12) | (a7 << 18);
  r[7] = (a7 >> 14) | (a8 << 16);

  return r;
};

// Constants
const MODINV32_INV256 = new Uint8Array(128); // This array should be initialized with appropriate values

// Function to count trailing zeros in a 32-bit integer
const ctz32 = (x) => {
  let n = 0;
  if ((x & 0xffff) === 0) {
    x >>= 16;
    n += 16;
  }
  if ((x & 0xff) === 0) {
    x >>= 8;
    n += 8;
  }
  if ((x & 0xf) === 0) {
    x >>= 4;
    n += 4;
  }
  if ((x & 0x3) === 0) {
    x >>= 2;
    n += 2;
  }
  if ((x & 0x1) === 0) {
    x >>= 1;
    n += 1;
  }
  return n;
};

// Function to compute transition matrix and eta for 30 posdivsteps
const modinv32Posdivsteps30Var = (eta, f0, g0, t, jacp) => {
  let u = 1,
    v = 0,
    q = 0,
    r = 1;
  let f = f0,
    g = g0,
    m;
  let i = 30,
    limit,
    zeros;
  let jac = jacp;

  while (true) {
    // Count trailing zeros
    zeros = ctz32(g | (UINT32_MAX << i));
    // Perform zeros divsteps at once; they all just divide g by two
    g >>= zeros;
    u <<= zeros;
    v <<= zeros;
    eta -= zeros;
    i -= zeros;
    // Update the bottom bit of jac
    jac ^= zeros & ((f >> 1) ^ (f >> 2));
    // Check if we're done
    if (i === 0) break;
    if ((f & 1) !== 1 || (g & 1) !== 1) throw new Error("Invalid state");

    // If eta is negative, negate it and replace f, g with g, f
    if (eta < 0) {
      eta = -eta;
      jac ^= (f & g) >> 1;
      [f, g] = [g, f];
      [u, q] = [q, u];
      [v, r] = [r, v];
    }

    // Calculate limit
    limit = Math.min(eta + 1, i);
    // Calculate mask
    m = (UINT32_MAX >> (32 - limit)) & 255;
    // Find multiple of f to add to g to cancel its bottom bits
    const w = (g * MODINV32_INV256[(f >> 1) & 127]) & m;
    // Update g, q, and r
    g += f * w;
    q += u * w;
    r += v * w;

    if ((g & m) !== 0) throw new Error("Invalid state");
  }

  // Set transition matrix
  t.u = u;
  t.v = v;
  t.q = q;
  t.r = r;

  // Verify determinant
  if (Math.abs(t.u * t.r - t.v * t.q) !== 1 << 30)
    throw new Error("Invalid determinant");

  // Update jacp
  jacp = jac;
  return eta;
};

// Usage example
let testmodinv32Posdivsteps30Var = () => {
  const eta = 1;
  const f0 = 12345678; // Example value
  const g0 = 87654321; // Example value
  const t = new Trans2x2();
  let jacp = 0;

  const finalEta = modinv32Posdivsteps30Var(eta, f0, g0, t, jacp);
  console.log(`Final eta: ${finalEta}`);
  console.log(`Transition matrix: u=${t.u}, v=${t.v}, q=${t.q}, r=${t.r}`);
  console.log(`Jacobi symbol: ${jacp}`);
};

const M30 = 0x3FFFFFFF; // (UINT32_MAX >> 2)
const UINT32_MAX = 0xFFFFFFFF;

// Helper function to verify a condition
const VERIFY_CHECK = (condition, message) => {
  if (!condition) {
    throw new Error(message || "Verification failed");
  }
};

// A signed 30-bit limb representation of integers in JavaScript
class ModInv32Signed30 {
  constructor() {
    this.v = new Int32Array(9);
  }
}

// Transformation matrix class
class Trans2x2 {
  constructor() {
    this.u = 1;
    this.v = 0;
    this.q = 0;
    this.r = 1;
  }
}

// Helper function to convert uint16 to signed30
const uint16ToSigned30 = (out, inp) => {
  for (let i = 0; i < 9; i++) {
    out.v[i] = 0;
  }
  for (let i = 0; i < 16; i++) {
    const j = Math.floor(i / 2);
    if (i % 2 === 0) {
      out.v[j] += inp[i];
    } else {
      out.v[j] += inp[i] << 16;
    }
  }
  console.log(`Before normalization: ${out.v}`);
  // Normalize the values to ensure they fit within 30 bits
  for (let i = 0; i < 9; i++) {
    VERIFY_CHECK(out.v[i] <= M30, `Value out of range: ${out.v[i]} at index ${i}`);
    out.v[i] &= M30;
  }
  console.log(`uint16ToSigned30 output for input ${inp}: ${out.v}`);
};


// Function to normalize the input values
const normalizeSigned30 = (value) => {
  const result = new Int32Array(9);
  for (let i = 0; i < value.length; ++i) {
    result[i] = value[i] & M30;
  }
  return result;
};

// Function to update f and g using a transition matrix t
const modinv32UpdateFg30Var = (len, f, g, t) => {
  const u = t.u,
    v = t.v,
    q = t.q,
    r = t.r;
  let fi, gi;
  let cf, cg;
  let i;

  VERIFY_CHECK(len > 0);

  // Start computing t*[f,g]
  fi = f.v[0];
  gi = g.v[0];
  cf = BigInt(u) * BigInt(fi) + BigInt(v) * BigInt(gi);
  cg = BigInt(q) * BigInt(fi) + BigInt(r) * BigInt(gi);

  console.log(`Initial cf: ${cf}, cg: ${cg}`);
  console.log(`Mask M30: ${BigInt(M30)}`);

  // Verify that the bottom 30 bits of the result are zero, and then throw them away
  console.log(`Bottom 30 bits of cf: ${Number(cf & BigInt(M30))}`);
  VERIFY_CHECK((cf & BigInt(M30)) === 0n, `Initial cf verification failed: ${cf}`);
  cf >>= 30n;
  console.log(`Bottom 30 bits of cg: ${Number(cg & BigInt(M30))}`);
  VERIFY_CHECK((cg & BigInt(M30)) === 0n, `Initial cg verification failed: ${cg}`);
  cg >>= 30n;

  // Iteratively compute limb i=1..len of t*[f,g], and store them in output limb i-1 (shifting down by 30 bits)
  for (i = 1; i < len; ++i) {
    fi = f.v[i];
    gi = g.v[i];
    console.log(`Iteration ${i} before: cf=${cf}, cg=${cg}, fi=${fi}, gi=${gi}`);
    cf += BigInt(u) * BigInt(fi) + BigInt(v) * BigInt(gi);
    cg += BigInt(q) * BigInt(fi) + BigInt(r) * BigInt(gi);
    console.log(`Iteration ${i} after: cf=${cf}, cg=${cg}`);
    f.v[i - 1] = Number(cf & BigInt(M30));
    console.log(`f.v[${i - 1}]: ${f.v[i - 1]}`);
    cf >>= 30n;
    g.v[i - 1] = Number(cg & BigInt(M30));
    console.log(`g.v[${i - 1}]: ${g.v[i - 1]}`);
    cg >>= 30n;
  }

  // What remains is limb (len) of t*[f,g]; store it as output limb (len-1)
  f.v[len - 1] = Number(cf);
  g.v[len - 1] = Number(cg);
};

const testModinv32UpdateFg30Var = () => {
  const inArray = new Uint16Array([1, 2, 3, 4, 5, 6, 7, 8, 9]);
  const modArray = new Uint16Array([9, 8, 7, 6, 5, 4, 3, 2, 1]);
  const outArray = new Uint16Array(9);

  const f = new ModInv32Signed30();
  const g = new ModInv32Signed30();
  const t = new Trans2x2();

  uint16ToSigned30(f, inArray);
  uint16ToSigned30(g, modArray);

  console.log("Initial f:", f);
  console.log("Initial g:", g);

  // Properly initialize t
  t.u = 1;
  t.v = 0;
  t.q = 0;
  t.r = 1;

  modinv32UpdateFg30Var(9, f, g, t);

  signed30ToUint16(outArray, f);
  console.log("Output f:", outArray);
  signed30ToUint16(outArray, g);
  console.log("Output g:", outArray);
};

testModinv32UpdateFg30Var();

// Function to convert signed30 to uint16 for verification
const signed30ToUint16 = (out, inp) => {
  for (let i = 0; i < 16; i++) {
    const j = Math.floor(i / 2);
    if (i % 2 === 0) {
      out[i] = inp.v[j] & 0xFFFF;
    } else {
      out[i] = (inp.v[j] >> 16) & 0xFFFF;
    }
  }
};

// Run the test
testModinv32UpdateFg30Var();

// compute Jacobi symbol
const jacobiSymbol = (a, n) => {
  if (a === 0n) return 0;
  if (a === 1n) return 1;

  a = etc.mod(a, n);
  let s = 1;
  while (a !== 0n) {
    while (a % 2n === 0n) {
      a /= 2n;
      const nMod8 = n % 8n;
      if (nMod8 === 3n || nMod8 === 5n) s = -s;
    }
    [a, n] = [n, a];
    if (a % 4n === 3n && n % 4n === 3n) s = -s;
    a = etc.mod(a, n);
  }
  return n === 1n ? s : 0;
};

// compute square root in a finite field
const sqrt = (n) => {
  let r = 1n;
  for (let num = n, e = (P + 1n) / 4n; e > 0n; e >>= 1n) {
    if (e & 1n) r = (r * num) % P;
    num = (num * num) % P;
  }
  return mod(r * r) === n ? r : err("sqrt invalid");
};

// normalize and convert field element to bytes
function normalizeAndConvertToBytes(fe) {
  return etc.numberToBytesBE(fe).slice(0, 32);
}

// check if a field element is a quadratic residue
function isSquare(fe) {
  const normalized = etc.mod(fe, CURVE.p);

  if (normalized === 0n) return true;

  const jacobi = jacobiSymbol(normalized, CURVE.p);
  if (jacobi === -1) {
    return false;
  } else if (jacobi === 1) {
    return true;
  } else {
    const sqrtResult = sqrt(normalized);
    return sqrtResult ** 2n % CURVE.p === normalized;
  }
}

function pedersenCommitment(p) {
  const xBytes = normalizeAndConvertToBytes(p.x);
  const yIsSquare = isSquare(p.y);
  const prefixByte = 9 ^ (yIsSquare ? 1 : 0);

  let d = new Uint8Array(33);
  d[0] = prefixByte;
  d.set(xBytes, 1);
  return d;
}

const print = (label, p) =>
  console.log(label, {
    hex: p.toHex(true),
    x: p.x.toString(16),
    y: p.y.toString(16),
  });

const blindHex =
  "8b5d87d94b9f54dc5dd9f31df5dffedc974fc4d5bf0d2ee1297e5aba504ccc26";
const blindBytes = etc.hexToBytes(blindHex);
const blindingFactor = etc.bytesToNumberBE(blindBytes);
const B = ProjectivePoint.BASE.multiply(blindingFactor);

const genHex =
  "02a4fd25e0e2108e55aec683810a8652f9b067242419a1f7cc0f01f92b4b078252";
const value = 10000n;

const G2 = ProjectivePoint.fromHex(genHex);
const V = G2.multiply(value);
const S = V.add(B);

print("B", B);
print("V", V);
print("S = B + V", S);

const commitment = pedersenCommitment(S);
console.log("Commitment:", etc.bytesToHex(commitment));
