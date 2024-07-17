import { ProjectivePoint, etc, utils, CURVE } from "@noble/secp256k1";

// Modular exponentiation function
const modPow = (base, exp, mod) => {
  let result = 1n;
  base = etc.mod(base, mod);
  while (exp > 0) {
    if (exp % 2n === 1n) {
      result = etc.mod(result * base, mod);
    }
    exp = exp >> 1n;
    base = etc.mod(base * base, mod);
  }
  return result;
}

// Function to compute Jacobi symbol
const jacobiSymbol = (a, n) => {
  if (a === 0n) return 0;
  if (a === 1n) return 1;

  let s;
  if (a % 2n === 0n) {
    s = jacobiSymbol(a / 2n, n);
    if ((n % 8n === 3n) || (n % 8n === 5n)) s = -s;
  } else {
    s = jacobiSymbol(n % a, a);
    if ((a % 4n === 3n) && (n % 4n === 3n)) s = -s;
  }
  return s;
}

// Function to compute square root in a finite field
const sqrt = (n) => {
  return modPow(n, (CURVE.p + 1n) / 4n, CURVE.p);
}

// Function to normalize and convert field element to bytes
function normalizeAndConvertToBytes(fe) {
  return etc.numberToBytesBE(fe).slice(0, 32);
}

// Function to check if a field element is a quadratic residue
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

// JavaScript implementation of secp256k1_pedersen_commitment_save
function pedersenCommitmentSave(commit, ge) {
  // Normalize x-coordinate and convert to bytes
  const xBytes = normalizeAndConvertToBytes(ge.x);

  // Check if y-coordinate is a square
  const yIsSquare = isSquare(ge.y);

  // Set the prefix byte
  const prefixByte = 9 ^ (yIsSquare ? 1 : 0);

  // Prepare the commitment data
  commit.data = new Uint8Array(33);
  commit.data[0] = prefixByte;
  commit.data.set(xBytes, 1);
}

// Example usage
const print = (label, p) => console.log(label, { hex: p.toHex(true), x: p.x.toString(16), y: p.y.toString(16) });

const blindHex = "8b5d87d94b9f54dc5dd9f31df5dffedc974fc4d5bf0d2ee1297e5aba504ccc26";
const blindBytes = etc.hexToBytes(blindHex);
const blindingFactor = etc.bytesToNumberBE(blindBytes);
const B = ProjectivePoint.BASE.multiply(blindingFactor);
const expectedHex = "08a9de5e391458abf4eb6ff0cc346fa0a8b5b0806b2ee9261dde54d436423c1982";

const genHex = "02a4fd25e0e2108e55aec683810a8652f9b067242419a1f7cc0f01f92b4b078252";
const value = 10000n;

const G2 = ProjectivePoint.fromHex(genHex);
const V = G2.multiply(value);

// print("B", B);
// print("V", V);
// print("B + V", V.add(B));

// Save the commitment
const commitment = {};
pedersenCommitmentSave(commitment, V.add(B));

console.log("Commitment matches expected:", etc.bytesToHex(commitment.data) === expectedHex);
