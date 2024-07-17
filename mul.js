const UINT32_MAX = 0xFFFFFFFF;
const M30 = 0x3FFFFFFF; // (UINT32_MAX >> 2)

const VERIFY_CHECK = (condition, message) => {
  if (!condition) {
    throw new Error(message || "Verification failed");
  }
};

class ModInv32Signed30 {
  constructor() {
    this.v = new Int32Array(9);
  }
}

class Trans2x2 {
  constructor() {
    this.u = 0;
    this.v = 0;
    this.q = 0;
    this.r = 0;
  }
}

// Function to update f and g using a transition matrix t
const modinv32UpdateFg30Var = (len, f, g, t) => {
  const u = t.u, v = t.v, q = t.q, r = t.r;
  let fi, gi;
  let cf, cg;
  let i;

  VERIFY_CHECK(len > 0);

  // Start computing t*[f,g]
  fi = f.v[0];
  gi = g.v[0];
  cf = BigInt(u) * BigInt(fi) + BigInt(v) * BigInt(gi);
  cg = BigInt(q) * BigInt(fi) + BigInt(r) * BigInt(gi);

  console.log("Initial f.v[0]:", fi);
  console.log("Initial g.v[0]:", gi);
  console.log("Initial cf:", cf);
  console.log("Initial cg:", cg);
  console.log("Mask M30:", BigInt(M30));
  console.log("Bottom 30 bits of cf:", cf & BigInt(M30));
  console.log("Bottom 30 bits of cg:", cg & BigInt(M30));

  // Verify that the bottom 30 bits of the result are zero, and then throw them away
  VERIFY_CHECK((cf & BigInt(M30)) === 0n, `Initial cf verification failed: ${cf}`);
  cf >>= 30n;
  VERIFY_CHECK((cg & BigInt(M30)) === 0n, `Initial cg verification failed: ${cg}`);
  cg >>= 30n;

  // Iteratively compute limb i=1..len of t*[f,g], and store them in output limb i-1 (shifting down by 30 bits)
  for (i = 1; i < len; ++i) {
    fi = f.v[i];
    gi = g.v[i];
    cf += BigInt(u) * BigInt(fi) + BigInt(v) * BigInt(gi);
    cg += BigInt(q) * BigInt(fi) + BigInt(r) * BigInt(gi);
    console.log(`Iteration ${i}, cf:`, cf, `cg:`, cg);
    f.v[i - 1] = Number(cf & BigInt(M30));
    cf >>= 30n;
    g.v[i - 1] = Number(cg & BigInt(M30));
    cg >>= 30n;
  }

  // What remains is limb (len) of t*[f,g]; store it as output limb (len-1)
  f.v[len - 1] = Number(cf);
  g.v[len - 1] = Number(cg);
};

// Test function
const testModinv32UpdateFg30Var = () => {
  const f = new ModInv32Signed30();
  const g = new ModInv32Signed30();
  const t = new Trans2x2();
  
  f.v = Int32Array.from([1, 0, 0, 0, 0, 0, 0, 0, 0]);
  g.v = Int32Array.from([0, 0, 0, 0, 0, 0, 0, 0, 0]);
  
  t.u = 1;
  t.v = 0;
  t.q = 0;
  t.r = 1;

  console.log("Initial f:", f);
  console.log("Initial g:", g);

  modinv32UpdateFg30Var(9, f, g, t);
  console.log("Updated f:", f.v);
  console.log("Updated g:", g.v);
};

testModinv32UpdateFg30Var();
