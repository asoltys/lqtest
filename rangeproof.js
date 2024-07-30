import { ProjectivePoint, etc, CURVE, hmacDrbg } from "@noble/secp256k1";
import { sha256 } from "@noble/hashes/sha256";
const {
  bytesToHex: b2h,
  bytesToNumberBE: b2n,
  hexToBytes: h2b,
  numberToBytesBE: n2b,
  hmacSha256Async,
} = etc;
const { BASE: G, ZERO: I } = ProjectivePoint;
const { n: N } = CURVE;

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
};

// Function to compute Jacobi symbol
const jacobiSymbol = (a, n) => {
  if (a === 0n) return 0;
  if (a === 1n) return 1;

  let s;
  if (a % 2n === 0n) {
    s = jacobiSymbol(a / 2n, n);
    if (n % 8n === 3n || n % 8n === 5n) s = -s;
  } else {
    s = jacobiSymbol(n % a, a);
    if (a % 4n === 3n && n % 4n === 3n) s = -s;
  }
  return s;
};

// Function to compute square root in a finite field
const sqrt = (n) => {
  return modPow(n, (CURVE.p + 1n) / 4n, CURVE.p);
};

// Function to normalize and convert field element to bytes
function normalizeAndConvertToBytes(fe) {
  return n2b(fe).slice(0, 32);
}

// Function to serialize a point according to the custom format
function serializePoint(point) {
  const data = new Uint8Array(33);

  // Check if y is a square
  const yBigInt = BigInt(point.y);
  data[0] = isSquare(yBigInt) ? 0x00 : 0x01;

  // Normalize x
  const xBigInt = BigInt(point.x);
  const xHex = xBigInt.toString(16).padStart(64, "0"); // Convert x to 32-byte hex string
  const xBytes = Uint8Array.from(Buffer.from(xHex, "hex")); // Convert hex string to Uint8Array

  // Serialize x
  data.set(xBytes, 1);

  return data;
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
function pedersenCommitment(ge) {
  // Normalize x-coordinate and convert to bytes
  const xBytes = normalizeAndConvertToBytes(ge.x);

  // Check if y-coordinate is a square
  const yIsSquare = isSquare(ge.y);

  // Set the prefix byte
  const prefixByte = 9 ^ (yIsSquare ? 1 : 0);

  // Prepare the commitment data
  let commit = new Uint8Array(33);
  commit[0] = prefixByte;
  commit.set(xBytes, 1);
  return commit;
}

const print = (label, p) =>
  console.log(label, {
    hex: p.toHex(true),
    x: p.x.toString(16),
    y: p.y.toString(16),
  });

function testPedersen() {
  const blindHex =
    "8b5d87d94b9f54dc5dd9f31df5dffedc974fc4d5bf0d2ee1297e5aba504ccc26";
  const blindBytes = h2b(blindHex);
  const blindingFactor = b2n(blindBytes);
  const B = G.multiply(blindingFactor);
  const expectedHex =
    "08a9de5e391458abf4eb6ff0cc346fa0a8b5b0806b2ee9261dde54d436423c1982";

  const genHex =
    "02a4fd25e0e2108e55aec683810a8652f9b067242419a1f7cc0f01f92b4b078252";
  const value = 10000n;

  const G2 = ProjectivePoint.fromHex(genHex);
  const V = G2.multiply(value);

  // print("B", B);
  // print("V", V);
  // print("B + V", V.add(B));

  // Save the commitment
  let commit = pedersenCommitment(V.add(B));
  console.log("Commitment matches expected:", b2h(commit) === expectedHex);
}

function borromeanHash(m, e, ridx, eidx) {
  const ring = new Uint8Array(4);
  const epos = new Uint8Array(4);

  const writeBe32 = (buffer, value) => {
    buffer[0] = (value >> 24) & 0xff;
    buffer[1] = (value >> 16) & 0xff;
    buffer[2] = (value >> 8) & 0xff;
    buffer[3] = value & 0xff;
  };

  writeBe32(ring, ridx);
  writeBe32(epos, eidx);

  const sha256Context = sha256.create();
  sha256Context.update(e);
  sha256Context.update(m);
  sha256Context.update(ring);
  sha256Context.update(epos);

  return sha256Context.digest();
}

function testBorromeanHash() {
  const msg = new Uint8Array([
    /* msg data */
  ]);
  const e = new Uint8Array([
    /* e data */
  ]);
  const ridx = 1; // example ring index
  const eidx = 2; // example element index

  hash = borromeanHash(msg, e, ridx, eidx);
  console.log(b2h(hash));
}

function clz64(x) {
  if (x === 0n) return 64;
  let n = 0;
  while ((x & 0x8000000000000000n) === 0n) {
    x <<= 1n;
    n++;
  }
  return n;
}

function rangeProveParams(minBits, minValue, exp, value) {
  let i, v;
  let rsizes = new Array(32);
  let secidx = new Array(32);
  let rings = 1;
  rsizes[0] = 1;
  secidx[0] = 0;
  let scale = 1n;
  let mantissa = 0;
  let npub = 0;

  if (minValue === 0xffffffffffffffffn) {
    exp = -1;
  }

  if (exp >= 0) {
    let maxBits;
    let v2;
    if (
      (minValue && value > 0x7fffffffffffffffn) ||
      (value && minValue >= 0x7fffffffffffffffn)
    ) {
      return 0;
    }
    maxBits = minValue ? clz64(BigInt(minValue)) : 64;
    if (minBits > maxBits) {
      minBits = maxBits;
    }
    if (minBits > 61 || value > 0x7fffffffffffffffn) {
      exp = 0;
    }
    v = value - BigInt(minValue);
    v2 = minBits ? 0xffffffffffffffffn >> BigInt(64 - minBits) : 0n;
    for (i = 0; i < exp && v2 <= 0xffffffffffffffffn / 10n; i++) {
      v /= 10n;
      v2 *= 10n;
    }
    exp = i;
    v2 = v;
    for (i = 0; i < exp; i++) {
      v2 *= 10n;
      scale *= 10n;
    }
    minValue = value - v2;
    mantissa = v ? 64 - clz64(v) : 1;
    if (minBits > mantissa) {
      mantissa = minBits;
    }
    rings = (mantissa + 1) >> 1;
    for (i = 0; i < rings; i++) {
      rsizes[i] = i < rings - 1 || !(mantissa & 1) ? 4 : 2;
      npub += rsizes[i];
      secidx[i] = Number((v >> BigInt(i * 2)) & 3n);
    }
    if (mantissa <= 0) throw new Error("Invalid mantissa value");
    if ((v & ~(0xffffffffffffffffn >> BigInt(64 - mantissa))) !== 0n)
      throw new Error("Did not get all the bits");
  } else {
    exp = 0;
    minValue = value;
    v = 0n;
    npub = 2;
  }

  if (v * scale + minValue !== value) throw new Error("Invalid value");
  if (rings <= 0 || rings > 32) throw new Error("Invalid number of rings");
  if (npub > 128) throw new Error("Invalid number of public keys");

  return {
    rings,
    rsizes,
    npub,
    secidx,
    minValue,
    mantissa,
    scale,
    minBits,
    v,
    exp,
  };
}

function borromeanSign(e0, s, pubs, k, sec, rsizes, secidx, nrings, m) {
  let rgej;
  let tmp = new Uint8Array(33);
  let count = 0;

  if (!e0 || !s || !pubs || !k || !sec || !rsizes || !secidx || !nrings || !m) {
    throw new Error("Invalid input");
  }

  // console.log("Parameters:");
  // for (let i = 0; i < nrings; i++) {
  //   console.log("I", i);
  //   console.log("s:", b2h(s[i]));
  //   console.log("pubs:", pubs[i].toHex(true));
  //   console.log("k:", k[i].toString(16));
  //   console.log("sec:", b2h(sec[i]));
  // }
  // console.log("rsizes:", rsizes);
  // console.log("secidx:", secidx);
  // console.log("nrings:", nrings);
  // console.log("m:", b2h(m));
  // console.log("mlen:", m.length);

  const sha256_e0 = sha256.create();
  for (let i = 0; i < nrings; i++) {
    if (Number.MAX_SAFE_INTEGER - count < rsizes[i]) {
      throw new Error("Integer overflow");
    }

    rgej = G.mul(k[i]);
    if (rgej.equals(ProjectivePoint.ZERO)) {
      console.log("zero");
      return 0;
    }

    tmp = rgej.toRawBytes(true);

    for (let j = secidx[i] + 1; j < rsizes[i]; j++) {
      tmp = borromeanHash(m, tmp, i, j);
      let ens = b2n(tmp);
      if (ens >= CURVE.n) ens = ens % CURVE.n;

      rgej = pubs[count + j].multiply(ens).add(G.mul(b2n(s[count + j])));
      if (rgej.equals(ProjectivePoint.ZERO)) {
        console.log("rgej = 0");
        return 0;
      }

      tmp = rgej.toRawBytes(true);
    }

    sha256_e0.update(tmp);
    count += rsizes[i];
  }

  console.log("last m", b2h(m));
  sha256_e0.update(m);
  let digest = sha256_e0.digest();
  e0.set(digest);

  count = 0;
  for (let i = 0; i < nrings; i++) {
    if (Number.MAX_SAFE_INTEGER - count < rsizes[i]) {
      throw new Error("Integer overflow");
    }

    borromeanHash(tmp, m, e0, i, 0);
    let ens = b2n(tmp);

    if (ens === 0n || ens >= CURVE.n) {
      return 0;
    }

    for (let j = 0; j < secidx[i]; j++) {
      rgej = pubs[count + j].multiply(ens).add(G.mul(s[count + j]));
      if (rgej.equals(ProjectivePoint.ZERO)) {
        return 0;
      }

      tmp = rgej.toRawBytes(true);
      borromeanHash(tmp, m, tmp, i, j + 1);
      ens = b2n(tmp);

      if (ens === 0n || ens >= CURVE.n) {
        return 0;
      }
    }

    const secScalar = b2n(sec[i]);
    const kScalar = k[i];
    const newS = mod(ens * secScalar + kScalar, CURVE.n);
    s[count + secidx[i]] = n2b(newS, 32);

    if (newS === 0n) {
      return 0;
    }

    count += rsizes[i];
  }

  // console.log("Final s values:");
  // for (let i = 0; i < count; i++) {
  //   console.log("s:", b2h(s[i]));
  // }

  return 1;
}

function testBorromeanSign() {
  const e0 = new Uint8Array([
    0xf7, 0x0c, 0x00, 0x80, 0x98, 0xc2, 0xbc, 0x1d, 0xad, 0x00, 0x00, 0x93,
    0x4c, 0x56, 0x04, 0xd5, 0x3d, 0x13, 0x00, 0xa3, 0x36, 0xa0, 0x0f, 0x08,
    0x49, 0x00, 0x00, 0x00, 0x97, 0x4e, 0xe3, 0x15,
  ]);

  const s = [
    "3c7eb2d4f120236cb0dfe3945b696be77c47cf1a29e235c35804f23ff1ac8525",
    "a60a040d5f0780eda7b71fe2d956ccaa5dd7f9fe4db310e46fa19f0b493f7a90",
    "a66afd71fc5e84b9f39c814ecbc0605bb3b0efb78424846d0f1b831bbccd8e0f",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "cd6e071a6de624f16c92328177ee48e8e35445b5b330aed000daa2f4ebe5c17e",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "2384a600c39a57b71044fee0d976022e376fcdc2d83544330e5bc94384d089de",
    "45c1872f40a3961e8fd6f4cbf3ac131a44688a7214c15325ba89ac7a55aa8790",
    "4f6f33828e1f432bb8f0f040d8403c87300a7ac0a146dd87af4f1aff96f428f4",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "839bb1efdef78234c6d07c75891e9a0a9dfd9f2de5cdd4a6b898dad80254afb6",
    "ae9d763bc3860e0b19ae7de55a27d935576e8b7575846d2befd251d8d4b0f62b",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "2f103749933db21486130a56be1bcaee78137ef8306dc5bec2b3afe9afcc4344",
    "d4aca0e4f173d503583872141f4da19a45aa2b0f2fb1a15dc3d9e2f6a189948e",
    "ee285da37968cc35b34c93db92421003893ff6aca7c90c89d46b771669cd43ae",
    "3f4d4a2e047183bc15ae38cac485b7ea050150013547506b3fffb38ca9f4f433",
    "624aedf0ee54feb5e140225116e869fe1d3c5e45c0564d130fa1a6b13191ed59",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "98bd230af3a180ebe57f559632cb65a0dc806fd34b6f2d57da6e385207cfb903",
    "68f5efbaa6fc7a118e6b8805628321bef76db29aafc4edf9c76a10f66bf18fd8",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "a5fa59141dc32bddb9c6167a01a612413b3c2d830c3d0d4c1631994556180c5f",
    "ba28ee3780875cfb43525b1cc586901aa6b933be18d514975f84ca40ba080686",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "3dbd798d1faaf31e6f6c3ec7e374132475d2fc05d29e5b7b43d8d8f342a71520",
    "8ce598893efae6991d1b49c94687e31a0b8749740b70e58e4d0ccb053ab0d8cd",
    "470f9ad08fe66ea91c3d1b56ccc6f2d98d054783d5bc7c57b9660cd316a61485",
    "e96be30379537859a58021734e4b4357c3a196a17e089299cd22023cfa3e7b25",
    "08ee70b904fea821df6edd03d8fdaccf4b4560388c00681c47b9462697897a46",
    "1f4247ab69207a9e1316781daf3eb32a22bdd60dc7b9f9e3bff087e137a65714",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "dfd7f8de1289e30c3cd531afeabac4202541ca7dae26877fd2e184a9911e0cf2",
    "95be51d2febcedcfce480abcf7ce1bf7e4c0a311ab9542f4869e3e78b5638a07",
    "fe304f14d2aa7ca1577ca87bfc8e6de0ee8f6f2c10223bcc51eb13b2683373ad",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "e5012ffcff45b70917abcd429aa7d1c432ef7e0be417c989a59a3264edc2a731",
    "fe9ed0b2296cfaf2c27f5b225b018f190c6d37f177427875bf362c8197e5c984",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "dfa81312edd35d125580e55b82fe6a99688bd7ac2082d33cac20b1f5ca5b52b1",
    "2ba1846ff4c942b04fae07a0b12d61449ed750cc366e865dc28a96a75761e824",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "895e4b81c17656452caa74709191029ce41c962f3d8619d67445ab3debe5c75e",
    "6c128d618b9b98f1808a2b88a004996daa07d16e616ab1d6a1af563c3779a08a",
    "2f0dd2c9574ff7843907a20474d2ca34b1bddc999dad355a28178ed6c0f254ce",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "ce3230dc498ccf189e596e50fef40f975f8be9369da5abc372f367c84e0844d7",
    "32c761cd192dd9f83cf8e5470b5b13d5c480354a9cc03f1e96799cb1d5cc9ea3",
    "80dd99e14d2c66bc735899562d74666b2d2e1515d4b50fb3c1b40530d2d3d389",
    "91be8e03305ef3d54111642614f24106658bcf0ee766085fc74b5199f15584de",
    "faeab8d22a0b05d352d3762a55a86d056b8b0006bff5d94ace6fab9bb10049fe",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "1f292743977c36202088586ba7db1b7295eeb2ab76d2c31d87bb3acc10a44a39",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "af968ebe3f27b7ffd5c44b5a4eeb62aa8bd530fa3b87412c8f635e116f9c05ce",
    "66ad0b735e84af5078be9d9efd41037c593fda7d58b73a7080fc6151fc3ba5b0",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "f6cad01ca89e92ff57f7707c54d1c6550e0686122cbdb16bc2983002c55aa23f",
    "659945af8b0cf8c37838d7607aa1215a0e2fbc3f403489902141245966007a80",
    "0f3686558e565a67c9f51dfa878450e3abee41c1fe5ffa57a37eebbb657bce26",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "3805a38547846ba9490b1eaa7da50db123a1ff201b272309f9442f22630aeeaf",
    "46950f2fc825403eb337b8737677f5afcd822cb137a547d203015a0e7455bda6",
    "0b93676852484647f0d49d57b8e7c8eabdb7a736585b501001114b4e2cf304f0",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "644cbb3eb45843c7bae6ab436cadbfedc3da860da7092301b05055569ce3ba6c",
    "3425cf295845366554c0e4108188a0441326923d69777ae9761c99ed6a78782f",
    "a15c1c2d708a4fde61fdc8cff4e1534eacc15229041415a19d89c975294558f4",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "37e808816573f7c73b3f225d09b29e03fe9ae9f79c40e69eb466fc3cafc5cdc0",
    "450b46d575fdee83001a755b61fe4e4cd98fa880ebd4b6f3904716ac3a619a42",
    "e1800c7360563410f703163e2b8975cd8d272f58768ebed263ee8a8381054d81",
  ].map(h2b);

  const pubs = [
    "03f0954c84cd6f383a536677e4279108eed11f62d2a5b1e3f15c622c850c0ad11f",
    "021dd1b9db1912154b766ccf8a32d6c5a73f186ff48408cdf6185f245bd78a3c80",
    "02dbbec7f6a645d6054113528b37b080e58ad8050b75693cabe9d6c5a77b3af565",
    "0275a43ddd49ae6feb90b4c8f8867d9726d2e3644f3f20e1981b77bf021279278e",
    "03da43884cf1a0b356adddc9027b0ae6fb5ff044cd0494d863c0edf46a22306e37",
    "038e1a9b2222c6c406e940e9c976f683fbde26ffc18567efefa7345e241280b6ba",
    "037c50358f784ccf5430d815115da2757768d70d090b5013c895dd8a58bfe2597d",
    "02c86f91e217c2aa6b303255bd6fc23c1914f3e32d166aab789a9945ce3ed88c06",
    "0393062df327e14382a45c7a78a6ba60eb54938d891fd7816fda940332d67484b3",
    "036175aaeea13901f675fc65cbfacd0038172efd32659aca772d3e36063a004497",
    "026b2904cc2497456d683f00bf5b62d62699ad320b71731c75ad5858958cf961d7",
    "0398d43fbd0b3b3584e6e7b6653b1bdaecd769aaf2ce4dc7e04f898c24112b9b2d",
    "02b9c153501f84a175d756f109272cf03333ee2c9351d01c6762d797e0ba0a9e84",
    "03d9d292e6c33d8a082dabe3a7a677897a988f25bca023ba632ba8f409a0614c8b",
    "03e8611ed94f9f523913fc241088a4aaa7ca1365ee90c9b8a879a8fd0e95b6c915",
    "02bfe3727efe30181dc30814681d6e45fdccc4b717367ea2c776198535fd847ecb",
    "02881fcc79dafb887c5bcc244bc0f23e8aee40cfbeaf4df937bc4ab04874769a39",
    "03965e0ada3ecf7783bb4f9c38285159c57a090da96bb419bec2c06d004431b1c0",
    "0262b317414f2f635dd141fe35708adcbd3f98097b964eb3839e24fa3f46745702",
    "02034c4d9b26db46d05716d145dd0a4aa0252e95edb19428cc3454b3f8a7b83f11",
    "03a7f364b5f7b824c4cbdfab1240efe46d58b9057f14a459575825eb5261841818",
    "03a62584af13a946a2bb5441a7801078db62b6faeb644911bdc294668617e8cb67",
    "03517221db90b66bbaa770b1cbc01f447c4c53ad71e7be62c256bd2e198defbb8f",
    "02c8a8585e0e04017c63de487ec4c9e54fae905ca69f7caf646f3673ac7a95950a",
    "0303f05ba3e369b9d4084e2754faf1813db09f8120f3c871a3fbf35ee31f602798",
    "020ea1a8ff22e8aa71b5cdb2903c5f398d2e9b7d535a623cac3614bd2036d22936",
    "0250acaabb76db943f5bf08c2bf0f03277da21bec0766474c5ceb447e632b27e89",
    "0330df158684e670875fe47d2b21a630e889d837e3e07e47c0efccc8b32aeee797",
    "030fdfa80758b564b7501384bd5e1af005f76e6f1e388a25c02ddc290a97fe2d05",
    "030027eccfc6cff4c52b62e0f8ff393aeff3776d5da57e3790609f2fa778fc2b6d",
    "023b86c924e829cd71fc69d4f35f51c233bd8c4c93dd64eb78a4d2d5d4c8d2d562",
    "0372ae04f2035a93d7be0185543ac8158f208c26e5d2f59d0898419029f91f3300",
    "02b744d0ff5107a6912c4a766c3485eafd8c04c6cc99283adea66d8b8c88a124a2",
    "020af21f6819ca86131899dd533e32fce3a63df7c2adeb66b6269621578201b7e9",
    "030617e762ea65127df9ae165503bf536c67836d73a4e3362607fe31e128b10e89",
    "0219fa37777a39c19e9d1c144c9ef963fe0becc25b7e4a71d6c9e9e804541aaa2c",
    "0396a78ac10b3a82ec3ff6eca5b7b330d56ed59ebd003bbde7915dedb5794c5063",
    "031224d40199ac60fe7a4dcecfa23b149f48b10bb14ecfc32c5b48e2f0ae73efdd",
    "021643af9f6e2f69cbefb5d2aa51917634238360e5a0210dd98969026e6e33df0e",
    "034bad6dcd8376916839c8962650688ec9cb71ced456ea0144417a31e2b05fc689",
    "0220f9172e58b58082aa20b5bcbf2ed57a9d0f1bd5ecf8bed80392731cd82176c4",
    "0396e2858b24792397239e876d2642136036dac3b82e1e9b1a70f05f737d60f182",
    "024528d2d634c449ab232dbaa7bc990e99ef7e14bf9a07c94d7c0e376c416e538e",
    "03e230734e1f2c20f3a490f9a9d103d4614d2dcf8a462e6bc26ae519ec9d4326b7",
    "035457077e96b4a4a992975feccd2c8ce2e423e85b5455561e2d31a6c68b17f2ab",
    "02cee4c9ee95457232432c8c1802693156111dd3a2e9e394d1095ff8bc7b6ec4ac",
    "022967486a48544a737a8dc9b0cd527f5a092edf2785f0de7c3ea9a54d3104b982",
    "02b006ca3b0cde4c28da4ada375e376682466ce698491c40bc5d7f746b1211b1e8",
    "03addbff1a065da052bb83327966a96dc3f252b0c3f91868d30cb1f0d90b75a194",
    "0319c1f374958a9d3169877027807da9aee002264b52fe9a16b32d58301d465c60",
    "0207f234a396b433d92d533b34d332e8452a154b4d62285fa7e7a1fb04bc131467",
    "03fcacb98f6825372670eb03dc093eb9121c9de18ada3f73f92ce97f15c609a169",
    "02bdf96058158897d596941d5675f5b9de37f3e9243f454611dad3acee6cbceb1a",
    "02741584e8ce06a32450d110d6e7a666cde8857edd3c73a931b9099f5245c49caa",
    "0272684f4f0b10f3f144c92fa32fbbce3b9fcb06ecadec71418807bff688a614bd",
    "02f89f1fe8f9e80affa3f28d0a117439b796ba068963a0a5de32ebe1ee31513de1",
    "025ac1ef0b03f8b512166cdf8386d5492e7b591f5b3daf33658a6f2c4f9a028d08",
    "0220af385719ebf9b31d233c5e596f6a98d4a397ddb8d2f7628ac1e1a03fb55f2e",
    "03d92c7a75922810a8d0bcff8c59765909203bc59db4729388a5ce035c8a8f5104",
    "0216259955d080fda979be4381d68867b272838fc841fbc89820f608bddc755f2a",
    "0283f1349f73a28ebc1630165e500d59503c1ca4c203ee53b881eb42c2d8097f80",
    "02f38490ef042cab039b656d6f54165bd6042449aa44d877efa52001f1f31fc21f",
    "034e6dfbaedb3a1c860f276f27e57ca0f42394135b696a3a89f294ccbcd8fad407",
    "0376654bd761bffeb82d2e916a629d6d68d6940e4e93ef7a4dd259072d998d4ef3",
    "026183ce2628247485d85d87b113d1309d26332ffb734355b17cfe41c1f82fbd6d",
    "02482cfca898bdbb9a71bf22bfb062c8d602cccd4082f2858f596b74e9519ab87e",
    "035a13a3bd13865c35af6b2e16a567a6deee9f53b5ee48b865b9866b1c512f2801",
    "0353bed1d794ddad62944956e65df881b1b6aa7c7bc6c30fc6cd38b69310dc6aa9",
    "03192ad5a7c9e91560c7772c849c20e3b44c9171341606f55d0c4696beec8a4a3e",
    "023e4f1890a8211a3d4bd12aa9c7c63beda02cb1358dc924b090539e4693ee15ae",
    "027871f7757637af9ed579c351b9c444d75e7ce442460df1bc87641a2e4ab7974c",
    "03702eb874afda8e5178dc7e51e181a232388718d11a4fe689723b10ea5217709f",
  ].map(ProjectivePoint.fromHex);

  const k = [
    "1308fb12e8f1f7e99d899e6867ed39df23a2703ae53c362de203a2341a1d5dc4",
    "b7339eead9990dbc466fb65139acffc22729c27d247b6de56384068379493b0e",
    "a21c74de462d4adfd6c723cf241f04be1f3afe1227cab76711e9e25f3e4345f3",
    "62f7dbb49a68b6ba4a71497d250212292906530c51df3ef1e38155fb7b0a1dc6",
    "bd60bf9f7fa1ee6ec89acdbf795e57c55c6291aa410653ee9eee15eb73c3f483",
    "195c72f9dc3fc9ae4709cd551a2af6830d05c5449c28399dc8f0563cdbed53d3",
    "edc2aafd1de7c74f89a55465a3e5c86829a62c944d70c3e647957a9f4b6a3134",
    "703a436c08b49a627011bf6424a57c1c4aecf136a1e16341786a8ad139c03c1d",
    "5e6fdff8ca42c5dd7a5a6a60912fa436a90f4b77e9e37651d8a12724ff9fec5e",
    "ddf9a128c5e2e57f122267ac2f0226ee99c4e88e6960e0fdf39e5d3b8b711541",
    "a8abe91d98ee0779e16cfec159148ca6be7ff8c971f1d20d3862299f124f0408",
    "ee5d08be93c4b11445e6e4a21a8928bd92914a98b80242ac55e0e083fdc94ef8",
    "7022d05f640bf99aac35eca3d8228bb25e8e237a91749f83c3c6b4d3a6d4ddad",
    "6cbefb501c14c6f1b07ad1e32e8b387774c8202cea72017316818527f8f120f4",
    "a2cf1eb56ce7fecf7e2372d1d3c097a7c6525c998b14e53a2f597d848b2f95a0",
    "03e0723e12d7ea3cae33c77a277f61a78b0cbd4a156e312c124c34422538f326",
    "c80d7abae240c92faa6985ed51d9038ad7ae905ee8521770cff252de21fe83cc",
    "b292abfb9e08bf06c4cb38ba178421ac93f3d050cc3133253b05c64c7a987fb8",
  ]
    .map(h2b)
    .map(b2n);

  const sec = [
    "fcd1e9fba166f36d78f934a4d2719c641e7d5dcd6cba35ccb981fbe364a12ca2",
    "bc5edd518207b730d2193aa9fb641b0715545a17847b87c7dea5c57cbfc7afef",
    "dbac69bc80a484e85e5077954d16ce42eaa0a717531fbae9e5b122b74e006e55",
    "170a286b5eb59f9e8037e009836ba80866eea34bb21c0fd2d6434beeb6067b5f",
    "6281c219cf0fba5737b72bb21a9ec47ad7a5e257f3084ff65c14cc76476ac636",
    "1cdc2eb2e0fd95cee7c78a48157689d5c6c3a62e12d954198782cdcd9d7b45a4",
    "fd691781cc5c00082e484625eec1c02ebb916cf545d7573de61101210212ee0f",
    "33f155f9a50b9a540eefefa5a3b1ab55b86f2b693815bede11f3e4d700d82e4f",
    "519fef0e3876536e38c0c87045612e35153de68fd40d56faeb116db8897bbc1f",
    "62096f12f8430be29057295cbaa9157f763896c337317ca37005ac1fc71da235",
    "bdc3e9ab7c0fe1ca83d82408ca6c137318ad0a4de889db53fb7ed82d5bbcf412",
    "4f9ae271da1e3a7907823e2ff442612f72289d55a8153fd84827a56f7e97820f",
    "74f6307104ecea896c0fad18bf1e92352208f5e5825d1422b94b8052b227aa0e",
    "5531c67d80c3a54875d4948ff1102d444345be35986cf10696d995f34e81f666",
    "97bbee1e80479c9b3198c6461428b2aa1e74824306a62e6d0163c732af7eb168",
    "a1df09eec44924ad0b5d9853b7e325f9a8e9e75c6e15e56706da2444567d66e5",
    "88eea0de4485a181ed41a2fd0e2bdecc409ddca9221e2298744f2d2b831e9c38",
    "33c96c89a5f874eec54b6e9c7b66fe46364b58dce0b1bfa5eb3f6ae71d71ac6a",
  ].map(h2b);

  const rsizes = [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4];
  const secidx = [3, 1, 1, 0, 2, 1, 0, 3, 3, 2, 1, 1, 3, 1, 0, 0, 0, 0];
  const nrings = 18;

  const m = new Uint8Array([
    0x0f, 0x6f, 0x44, 0xb3, 0xc1, 0x2f, 0x82, 0x5f, 0x72, 0x82, 0x13, 0x7b,
    0x88, 0x70, 0x69, 0x15, 0xe0, 0x5f, 0xaf, 0xad, 0x5a, 0xbd, 0x89, 0x00,
    0xff, 0xd8, 0x99, 0xe0, 0xe3, 0x88, 0x7d, 0xc2,
  ]);

  const e0Final =
    "a5ebba7c91664a2f7be6863e9eccbb2b925d8b0451bc2333f860d21e18c1d071";

  const finalS = [
    "3c7eb2d4f120236cb0dfe3945b696be77c47cf1a29e235c35804f23ff1ac8525",
    "a60a040d5f0780eda7b71fe2d956ccaa5dd7f9fe4db310e46fa19f0b493f7a90",
    "a66afd71fc5e84b9f39c814ecbc0605bb3b0efb78424846d0f1b831bbccd8e0f",
    "d4fc0f4aeafe4893208cd84ebc75f5619f9af9e0f68adc0484b71b23018bbeef",
    "cd6e071a6de624f16c92328177ee48e8e35445b5b330aed000daa2f4ebe5c17e",
    "8532b9c5a0ab4a477c1cdc32e0125506d159816011cf581924ef9b138cdca823",
    "2384a600c39a57b71044fee0d976022e376fcdc2d83544330e5bc94384d089de",
    "45c1872f40a3961e8fd6f4cbf3ac131a44688a7214c15325ba89ac7a55aa8790",
    "4f6f33828e1f432bb8f0f040d8403c87300a7ac0a146dd87af4f1aff96f428f4",
    "dbb1dd35538b44b0de4076793b2f1c70cc5d3916d6bd70e770bd891f8461a27a",
    "839bb1efdef78234c6d07c75891e9a0a9dfd9f2de5cdd4a6b898dad80254afb6",
    "ae9d763bc3860e0b19ae7de55a27d935576e8b7575846d2befd251d8d4b0f62b",
    "3f78436439ffab4cb4edc663d58c053474f3631d98cddcae7c9342cbac6bc2e5",
    "2f103749933db21486130a56be1bcaee78137ef8306dc5bec2b3afe9afcc4344",
    "d4aca0e4f173d503583872141f4da19a45aa2b0f2fb1a15dc3d9e2f6a189948e",
    "ee285da37968cc35b34c93db92421003893ff6aca7c90c89d46b771669cd43ae",
    "3f4d4a2e047183bc15ae38cac485b7ea050150013547506b3fffb38ca9f4f433",
    "624aedf0ee54feb5e140225116e869fe1d3c5e45c0564d130fa1a6b13191ed59",
    "2a9bf0c49198db1a62d1a6da7ed7cd3027937c4f8817888678514b1c503f013c",
    "98bd230af3a180ebe57f559632cb65a0dc806fd34b6f2d57da6e385207cfb903",
    "68f5efbaa6fc7a118e6b8805628321bef76db29aafc4edf9c76a10f66bf18fd8",
    "b3cac4c9ef23574272d4b89f055d2cd1f5759d027b93301c7b3bbe7cd137c9dc",
    "a5fa59141dc32bddb9c6167a01a612413b3c2d830c3d0d4c1631994556180c5f",
    "ba28ee3780875cfb43525b1cc586901aa6b933be18d514975f84ca40ba080686",
    "6d48b62419ccb92f97a67538387529959de7df9b5760a11d669a666f7d069426",
    "3dbd798d1faaf31e6f6c3ec7e374132475d2fc05d29e5b7b43d8d8f342a71520",
    "8ce598893efae6991d1b49c94687e31a0b8749740b70e58e4d0ccb053ab0d8cd",
    "470f9ad08fe66ea91c3d1b56ccc6f2d98d054783d5bc7c57b9660cd316a61485",
    "e96be30379537859a58021734e4b4357c3a196a17e089299cd22023cfa3e7b25",
    "08ee70b904fea821df6edd03d8fdaccf4b4560388c00681c47b9462697897a46",
    "1f4247ab69207a9e1316781daf3eb32a22bdd60dc7b9f9e3bff087e137a65714",
    "abcfd47f493b9cdb1f844e7f117499150a8a3d5380c982d65e42a4366f683ef4",
    "dfd7f8de1289e30c3cd531afeabac4202541ca7dae26877fd2e184a9911e0cf2",
    "95be51d2febcedcfce480abcf7ce1bf7e4c0a311ab9542f4869e3e78b5638a07",
    "fe304f14d2aa7ca1577ca87bfc8e6de0ee8f6f2c10223bcc51eb13b2683373ad",
    "f10cd50098848c1e7640831db154c63c55655f610c03dbc83d7e761003d8ffb9",
    "e5012ffcff45b70917abcd429aa7d1c432ef7e0be417c989a59a3264edc2a731",
    "fe9ed0b2296cfaf2c27f5b225b018f190c6d37f177427875bf362c8197e5c984",
    "ad483142310e351e42697339305bc9885a9d9da9a16b96a9a72d279f2b1be829",
    "dfa81312edd35d125580e55b82fe6a99688bd7ac2082d33cac20b1f5ca5b52b1",
    "2ba1846ff4c942b04fae07a0b12d61449ed750cc366e865dc28a96a75761e824",
    "09fd055d24410228d1599ec5781c33eb6f0cea57a7982e13adeb81d2a0f6e052",
    "895e4b81c17656452caa74709191029ce41c962f3d8619d67445ab3debe5c75e",
    "6c128d618b9b98f1808a2b88a004996daa07d16e616ab1d6a1af563c3779a08a",
    "2f0dd2c9574ff7843907a20474d2ca34b1bddc999dad355a28178ed6c0f254ce",
    "bbd64e8ba30f11394d40a6bbe63aed53ed3d08a1a561801857e8648fe8621c34",
    "ce3230dc498ccf189e596e50fef40f975f8be9369da5abc372f367c84e0844d7",
    "32c761cd192dd9f83cf8e5470b5b13d5c480354a9cc03f1e96799cb1d5cc9ea3",
    "80dd99e14d2c66bc735899562d74666b2d2e1515d4b50fb3c1b40530d2d3d389",
    "91be8e03305ef3d54111642614f24106658bcf0ee766085fc74b5199f15584de",
    "faeab8d22a0b05d352d3762a55a86d056b8b0006bff5d94ace6fab9bb10049fe",
    "4128852a4190a9cc42a7a89a5bf191b776e2cf39f784d21d3fa9d4cd7e2328c8",
    "1f292743977c36202088586ba7db1b7295eeb2ab76d2c31d87bb3acc10a44a39",
    "b67565ab4320951a7969d3ab50fbef9215c162fb4b5260ea70e34ec023494334",
    "af968ebe3f27b7ffd5c44b5a4eeb62aa8bd530fa3b87412c8f635e116f9c05ce",
    "66ad0b735e84af5078be9d9efd41037c593fda7d58b73a7080fc6151fc3ba5b0",
    "ca175b3da4e8b602735ebe7a6c2b82fa5903604917eb84542679c90a0151dfa3",
    "f6cad01ca89e92ff57f7707c54d1c6550e0686122cbdb16bc2983002c55aa23f",
    "659945af8b0cf8c37838d7607aa1215a0e2fbc3f403489902141245966007a80",
    "0f3686558e565a67c9f51dfa878450e3abee41c1fe5ffa57a37eebbb657bce26",
    "ca32bfcd7a4c587ba65a15d9280cbd50acfbc876d3f062eed1099c6519e84a30",
    "3805a38547846ba9490b1eaa7da50db123a1ff201b272309f9442f22630aeeaf",
    "46950f2fc825403eb337b8737677f5afcd822cb137a547d203015a0e7455bda6",
    "0b93676852484647f0d49d57b8e7c8eabdb7a736585b501001114b4e2cf304f0",
    "73e543420410ed180adbf5a87e1c11b332a08e29a93241c17532c880e493b14c",
    "644cbb3eb45843c7bae6ab436cadbfedc3da860da7092301b05055569ce3ba6c",
    "3425cf295845366554c0e4108188a0441326923d69777ae9761c99ed6a78782f",
    "a15c1c2d708a4fde61fdc8cff4e1534eacc15229041415a19d89c975294558f4",
    "abcc5de2d7231ee7b5e0ef7ba1ffb3c2f8891e24002d14254d81db63fc804a10",
    "37e808816573f7c73b3f225d09b29e03fe9ae9f79c40e69eb466fc3cafc5cdc0",
    "450b46d575fdee83001a755b61fe4e4cd98fa880ebd4b6f3904716ac3a619a42",
    "e1800c7360563410f703163e2b8975cd8d272f58768ebed263ee8a8381054d81",
  ];

  // Example usage
  const result = borromeanSign(e0, s, pubs, k, sec, rsizes, secidx, nrings, m);
  console.log("e0 expected", e0Final);
  console.log("e0 actual", b2h(e0));
}

// testBorromeanSign();

/*
async function rangeproofGenrand(
  sec,
  s,
  message,
  rsizes,
  rings,
  nonce,
  commit,
  proof,
  len,
  gen,
) {
  let tmp = new Uint8Array(32);
  let rngseed = new Uint8Array(32 + 33 + 33 + len);
  let acc = 0n;
  let overflow;
  let ret = 1;
  let npub = 0;

  if (len > 10) {
    throw new Error("Invalid length");
  }

  let genP = ProjectivePoint.fromHex(gen);
  let commitP = ProjectivePoint.fromHex(commit);
  rngseed.set(h2b(nonce).slice(0, 32), 0);
  rngseed.set(serializePoint(commitP), 32);
  rngseed.set(serializePoint(genP), 32 + 33);
  rngseed.set(proof.slice(0, len), 32 + 33 + 33);

  console.log("nonce", nonce)
  console.log("commit", commit)
  console.log("gen", gen)

  let expectedRngseed =
    "f295f2c7a42274f8f90a9d7f8649d78b67e693703246bf6086653c8646a363f50153c4bf412d07fad5e05fe0f5ea2107a546f9cfef38ef2b962ffd84a89de03d7f008d276fa2ab45fed0f622f818be77f456baa2f3b90456e30d2c561446b25b545860230000000000000001";
  console.log("EXPECT", expectedRngseed)
  console.log("ACTUAL", b2h(rngseed))
  for (let i = 0; i < expectedRngseed.length; i++) {
    if (expectedRngseed[i] !== b2h(rngseed)[i]) console.log("MISMATCH", i, expectedRngseed[i], b2h(rngseed)[i]);
  }

  let rng = await sha256(rngseed);

  console.log("RINGS", rings);
  console.log("rsizes", rsizes);
  console.log("RNG", b2h(rng));

  for (let i = 0; i < rings; i++) {
    if (i < rings - 1) {
      tmp = await sha256(rng);
      console.log("tmp", i, b2h(tmp))
      do {
        tmp = await sha256(rng);
        sec[i] = b2n(tmp) % N;
      } while (sec[i] === 0n);
      acc += sec[i];

      console.log(`SEC[${i}]`, b2h(n2b(sec[i])))
    } else {
      sec[i] = -acc % N;
    }

    for (let j = 0; j < rsizes[i]; j++) {
      tmp = await sha256(rng);
      if (message) {
        for (let b = 0; b < 32; b++) {
          tmp[b] ^= message[(i * 4 + j) * 32 + b];
          message[(i * 4 + j) * 32 + b] = tmp[b];
        }
      }
      s[npub] = b2n(tmp);
      ret &= !(s[npub] === 0n);
      npub++;
    }
  }
  acc = 0n;
  return ret;
}
*/

function rangeproofPubExpand(pubs, exp, rsizes, rings, genp) {
  var base = ProjectivePoint.fromAffine(genp);
  var i, j, npub;
  if (exp < 0) {
    exp = 0;
  }

  base = base.negate();

  while (exp--) {
    // Multiplication by 10
    var tmp = base.double();
    base = tmp.double().add(tmp);
  }

  npub = 0;
  for (i = 0; i < rings; i++) {
    for (j = 1; j < rsizes[i]; j++) {
      pubs[npub + j] = pubs[npub + j - 1].add(base);
    }
    if (i < rings - 1) {
      base = base.double().double();
    }
    npub += rsizes[i];
  }
}

async function rangeproofSign(
  minValue,
  commit,
  blind,
  nonce,
  exp,
  minBits,
  value,
  msg,
  extraCommit,
  genp,
) {
  let proof = new Uint8Array(5134);
  var pubs = new Array(128);
  var s = new Array(128);
  var sec = new Array(32);
  var k = new Array(32);
  var sha256M = sha256.create();
  var prep = new Uint8Array(4096);
  var tmp = new Uint8Array(33);
  var signs;
  var len;
  var i;

  len = 0;
  if (minValue > value || minBits > 64 || minBits < 0 || exp < -1 || exp > 18) {
    return 0;
  }

  let v, rings, rsizes, npub, secidx, mantissa, scale;
  ({ v, rings, rsizes, npub, secidx, mantissa, scale, exp, minBits, minValue } =
    await rangeProveParams(minBits, minValue, exp, value));
  if (!v) return 0;

  proof[len] = (rsizes[0] > 1 ? 64 | exp : 0) | (minValue ? 32 : 0);
  len++;
  if (rsizes[0] > 1) {
    if (mantissa <= 0 || mantissa > 64) {
      throw new Error("Mantissa out of range");
    }
    proof[len] = mantissa - 1;
    len++;
  }
  if (minValue) {
    for (i = 0; i < 8; i++) {
      proof[len + i] = Number((minValue >> BigInt((7 - i) * 8)) & BigInt(255));
    }
    len += 8;
  }
  if (msg.length > 0 && msg.length > 128 * (rings - 1)) {
    return 0;
  }

  sha256M.update(commit);
  sha256M.update(genp);
  sha256M.update(proof.slice(0, len));

  prep.fill(0);
  if (msg != null) {
    prep.set(msg.slice(0, msg.length));
  }
  if (rsizes[rings - 1] > 1) {
    var idx;
    idx = rsizes[rings - 1] - 1;
    idx -= secidx[rings - 1] == idx;
    idx = ((rings - 1) * 4 + idx) * 32;
    for (i = 0; i < 8; i++) {
      prep[8 + i + idx] =
        prep[16 + i + idx] =
        prep[24 + i + idx] =
          Number((v >> BigInt(56 - i * 8)) & BigInt(255));
      prep[i + idx] = 0;
    }
    prep[idx] = 128;
  }

  if (
    !(await rangeproofGenrand(
      sec,
      s,
      prep,
      rsizes,
      rings,
      nonce,
      commit,
      proof,
      len,
      genp,
    ))
  ) {
    return 0;
  }

  prep.fill(0);
  for (i = 0; i < rings; i++) {
    k[i] = s[i * 4 + secidx[i]];
    s[i * 4 + secidx[i]] = 0n;
  }

  sec[rings - 1] = sec[rings-1] + b2n(blind) % CURVE.n;
  signs = proof.slice(len);
  for (i = 0; i < (rings + 6) >> 3; i++) {
    signs[i] = 0;
    len++;
  }
  npub = 0;
  for (i = 0; i < rings; i++) {
    // console.log("i", i);
    // console.log("idx", secidx[i]);
    // console.log("scale", scale);
    let scalar = (BigInt(secidx[i]) * scale) << BigInt(i * 2);
    // console.log("scalar", scalar);
    console.log(i, sec[i])
    console.log("sec", i, b2h(n2b(sec[i])));
    // console.log("curve n", CURVE.n);
    let P1 = sec[i] ? ProjectivePoint.fromHex(genp).mul(sec[i]) : I;
    let P2 = secidx[i] ? G.mul(scalar) : I;
    pubs[npub] = P1.add(P2);
    if (pubs[npub].equals(I)) {
      return 0;
    }
    if (i < rings - 1) {
      var tmpc = pubs[npub].toRawBytes(true);
      var quadness = tmpc[0];
      sha256M.update(tmpc);
      signs[i >> 3] |= quadness << (i & 7);
      proof.set(tmpc.slice(1), len);
      len += 32;
    }
    npub += rsizes[i];
  }
  rangeproofPubExpand(pubs, exp, rsizes, rings, genp);
  if (extraCommit != null) {
    sha256M.update(extraCommit);
  }
  sha256M = sha256M.digest();
  if (
    !(await borromeanSign(
      proof.slice(len),
      s,
      pubs,
      k,
      sec,
      rsizes,
      secidx,
      rings,
      sha256M,
    ))
  ) {
    return 0;
  }
  len += 32;
  for (let i = 0; i < npub; i++) {
    proof.set(n2b(s[i], 32), len);
    len += 32;
  }
  return proof;
}

async function testRangeproof() {
  const value = 123455000n;
  const minval = 1;
  const exp = 0;
  const bits = 36;
  const genp =
    "038d276fa2ab45fed0f622f818be77f456baa2f3b90456e30d2c561446b25b5458"; // asset commitment as parsed generator point
  // 0a8d276fa2ab45fed0f622f818be77f456baa2f3b90456e30d2c561446b25b5458
  const blind =
    "de22de5f5fe49cc6ac2bb8952567151c7c36b42e2e2f2aa587d4ed2060b2ba4d";
  const nonce =
    "f295f2c7a42274f8f90a9d7f8649d78b67e693703246bf6086653c8646a363f5";
  const script = "a914d7da691a2b7256aa3bce759ef2b8ff5213fa327987";
  const msg =
    "25b251070e29ca19043cf33ccd7324e2ddab03ecc4ae0b5e77c4fc0e5cf6c95ac4681a2583b714a31c5a0b997a6c107a96be4aef4847d9cde3035e8ef23642bf";
  const commit =
    "0253c4bf412d07fad5e05fe0f5ea2107a546f9cfef38ef2b962ffd84a89de03d7f"; // value commitment as parsed pedersen commitment
  // 0953c4bf412d07fad5e05fe0f5ea2107a546f9cfef38ef2b962ffd84a89de03d7f
  const expected =
    "60230000000000000001a33701f0954c84cd6f383a536677e4279108eed11f62d2a5b1e3f15c622c850c0ad11fda43884cf1a0b356adddc9027b0ae6fb5ff044cd0494d863c0edf46a22306e3793062df327e14382a45c7a78a6ba60eb54938d891fd7816fda940332d67484b3b9c153501f84a175d756f109272cf03333ee2c9351d01c6762d797e0ba0a9e84881fcc79dafb887c5bcc244bc0f23e8aee40cfbeaf4df937bc4ab04874769a39a7f364b5f7b824c4cbdfab1240efe46d58b9057f14a459575825eb526184181803f05ba3e369b9d4084e2754faf1813db09f8120f3c871a3fbf35ee31f6027980fdfa80758b564b7501384bd5e1af005f76e6f1e388a25c02ddc290a97fe2d05b744d0ff5107a6912c4a766c3485eafd8c04c6cc99283adea66d8b8c88a124a296a78ac10b3a82ec3ff6eca5b7b330d56ed59ebd003bbde7915dedb5794c506320f9172e58b58082aa20b5bcbf2ed57a9d0f1bd5ecf8bed80392731cd82176c45457077e96b4a4a992975feccd2c8ce2e423e85b5455561e2d31a6c68b17f2abaddbff1a065da052bb83327966a96dc3f252b0c3f91868d30cb1f0d90b75a194bdf96058158897d596941d5675f5b9de37f3e9243f454611dad3acee6cbceb1a5ac1ef0b03f8b512166cdf8386d5492e7b591f5b3daf33658a6f2c4f9a028d0883f1349f73a28ebc1630165e500d59503c1ca4c203ee53b881eb42c2d8097f806183ce2628247485d85d87b113d1309d26332ffb734355b17cfe41c1f82fbd6da5ebba7c91664a2f7be6863e9eccbb2b925d8b0451bc2333f860d21e18c1d0713c7eb2d4f120236cb0dfe3945b696be77c47cf1a29e235c35804f23ff1ac8525a60a040d5f0780eda7b71fe2d956ccaa5dd7f9fe4db310e46fa19f0b493f7a90a66afd71fc5e84b9f39c814ecbc0605bb3b0efb78424846d0f1b831bbccd8e0fd4fc0f4aeafe4893208cd84ebc75f5619f9af9e0f68adc0484b71b23018bbeefcd6e071a6de624f16c92328177ee48e8e35445b5b330aed000daa2f4ebe5c17e8532b9c5a0ab4a477c1cdc32e0125506d159816011cf581924ef9b138cdca8232384a600c39a57b71044fee0d976022e376fcdc2d83544330e5bc94384d089de45c1872f40a3961e8fd6f4cbf3ac131a44688a7214c15325ba89ac7a55aa87904f6f33828e1f432bb8f0f040d8403c87300a7ac0a146dd87af4f1aff96f428f4dbb1dd35538b44b0de4076793b2f1c70cc5d3916d6bd70e770bd891f8461a27a839bb1efdef78234c6d07c75891e9a0a9dfd9f2de5cdd4a6b898dad80254afb6ae9d763bc3860e0b19ae7de55a27d935576e8b7575846d2befd251d8d4b0f62b3f78436439ffab4cb4edc663d58c053474f3631d98cddcae7c9342cbac6bc2e52f103749933db21486130a56be1bcaee78137ef8306dc5bec2b3afe9afcc4344d4aca0e4f173d503583872141f4da19a45aa2b0f2fb1a15dc3d9e2f6a189948eee285da37968cc35b34c93db92421003893ff6aca7c90c89d46b771669cd43ae3f4d4a2e047183bc15ae38cac485b7ea050150013547506b3fffb38ca9f4f433624aedf0ee54feb5e140225116e869fe1d3c5e45c0564d130fa1a6b13191ed592a9bf0c49198db1a62d1a6da7ed7cd3027937c4f8817888678514b1c503f013c98bd230af3a180ebe57f559632cb65a0dc806fd34b6f2d57da6e385207cfb90368f5efbaa6fc7a118e6b8805628321bef76db29aafc4edf9c76a10f66bf18fd8b3cac4c9ef23574272d4b89f055d2cd1f5759d027b93301c7b3bbe7cd137c9dca5fa59141dc32bddb9c6167a01a612413b3c2d830c3d0d4c1631994556180c5fba28ee3780875cfb43525b1cc586901aa6b933be18d514975f84ca40ba0806866d48b62419ccb92f97a67538387529959de7df9b5760a11d669a666f7d0694263dbd798d1faaf31e6f6c3ec7e374132475d2fc05d29e5b7b43d8d8f342a715208ce598893efae6991d1b49c94687e31a0b8749740b70e58e4d0ccb053ab0d8cd470f9ad08fe66ea91c3d1b56ccc6f2d98d054783d5bc7c57b9660cd316a61485e96be30379537859a58021734e4b4357c3a196a17e089299cd22023cfa3e7b2508ee70b904fea821df6edd03d8fdaccf4b4560388c00681c47b9462697897a461f4247ab69207a9e1316781daf3eb32a22bdd60dc7b9f9e3bff087e137a65714abcfd47f493b9cdb1f844e7f117499150a8a3d5380c982d65e42a4366f683ef4dfd7f8de1289e30c3cd531afeabac4202541ca7dae26877fd2e184a9911e0cf295be51d2febcedcfce480abcf7ce1bf7e4c0a311ab9542f4869e3e78b5638a07fe304f14d2aa7ca1577ca87bfc8e6de0ee8f6f2c10223bcc51eb13b2683373adf10cd50098848c1e7640831db154c63c55655f610c03dbc83d7e761003d8ffb9e5012ffcff45b70917abcd429aa7d1c432ef7e0be417c989a59a3264edc2a731fe9ed0b2296cfaf2c27f5b225b018f190c6d37f177427875bf362c8197e5c984ad483142310e351e42697339305bc9885a9d9da9a16b96a9a72d279f2b1be829dfa81312edd35d125580e55b82fe6a99688bd7ac2082d33cac20b1f5ca5b52b12ba1846ff4c942b04fae07a0b12d61449ed750cc366e865dc28a96a75761e82409fd055d24410228d1599ec5781c33eb6f0cea57a7982e13adeb81d2a0f6e052895e4b81c17656452caa74709191029ce41c962f3d8619d67445ab3debe5c75e6c128d618b9b98f1808a2b88a004996daa07d16e616ab1d6a1af563c3779a08a2f0dd2c9574ff7843907a20474d2ca34b1bddc999dad355a28178ed6c0f254cebbd64e8ba30f11394d40a6bbe63aed53ed3d08a1a561801857e8648fe8621c34ce3230dc498ccf189e596e50fef40f975f8be9369da5abc372f367c84e0844d732c761cd192dd9f83cf8e5470b5b13d5c480354a9cc03f1e96799cb1d5cc9ea380dd99e14d2c66bc735899562d74666b2d2e1515d4b50fb3c1b40530d2d3d38991be8e03305ef3d54111642614f24106658bcf0ee766085fc74b5199f15584defaeab8d22a0b05d352d3762a55a86d056b8b0006bff5d94ace6fab9bb10049fe4128852a4190a9cc42a7a89a5bf191b776e2cf39f784d21d3fa9d4cd7e2328c81f292743977c36202088586ba7db1b7295eeb2ab76d2c31d87bb3acc10a44a39b67565ab4320951a7969d3ab50fbef9215c162fb4b5260ea70e34ec023494334af968ebe3f27b7ffd5c44b5a4eeb62aa8bd530fa3b87412c8f635e116f9c05ce66ad0b735e84af5078be9d9efd41037c593fda7d58b73a7080fc6151fc3ba5b0ca175b3da4e8b602735ebe7a6c2b82fa5903604917eb84542679c90a0151dfa3f6cad01ca89e92ff57f7707c54d1c6550e0686122cbdb16bc2983002c55aa23f659945af8b0cf8c37838d7607aa1215a0e2fbc3f403489902141245966007a800f3686558e565a67c9f51dfa878450e3abee41c1fe5ffa57a37eebbb657bce26ca32bfcd7a4c587ba65a15d9280cbd50acfbc876d3f062eed1099c6519e84a303805a38547846ba9490b1eaa7da50db123a1ff201b272309f9442f22630aeeaf46950f2fc825403eb337b8737677f5afcd822cb137a547d203015a0e7455bda60b93676852484647f0d49d57b8e7c8eabdb7a736585b501001114b4e2cf304f073e543420410ed180adbf5a87e1c11b332a08e29a93241c17532c880e493b14c644cbb3eb45843c7bae6ab436cadbfedc3da860da7092301b05055569ce3ba6c3425cf295845366554c0e4108188a0441326923d69777ae9761c99ed6a78782fa15c1c2d708a4fde61fdc8cff4e1534eacc15229041415a19d89c975294558f4abcc5de2d7231ee7b5e0ef7ba1ffb3c2f8891e24002d14254d81db63fc804a1037e808816573f7c73b3f225d09b29e03fe9ae9f79c40e69eb466fc3cafc5cdc0450b46d575fdee83001a755b61fe4e4cd98fa880ebd4b6f3904716ac3a619a42e1800c7360563410f703163e2b8975cd8d272f58768ebed263ee8a8381054d81";

  let proof = await rangeproofSign(
    minval,
    commit,
    blind,
    nonce,
    exp,
    bits,
    value,
    msg,
    script,
    genp,
  );

  console.log("PROOF", proof);
}

testRangeproof();

const SECP256K1_N = BigInt(
  "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
);

function secp256k1_scalar_check_overflow(a) {
  const SECP256K1_N_0 = BigInt("0xBFD25E8CD0364141");
  const SECP256K1_N_1 = BigInt("0xAF48A03BBFD25E8C");
  const SECP256K1_N_2 = BigInt("0xFFFFFFFFFFFFFFFE");
  const SECP256K1_N_3 = BigInt("0xFFFFFFFFFFFFFFFF");

  let no = 0;
  let yes = 0;

  no |= a[3] < SECP256K1_N_3 ? 1 : 0;
  no |= a[2] < SECP256K1_N_2 ? 1 : 0;
  yes |= a[2] > SECP256K1_N_2 && !no ? 1 : 0;
  no |= a[1] < SECP256K1_N_1 ? 1 : 0;
  yes |= a[1] > SECP256K1_N_1 && !no ? 1 : 0;
  yes |= a[0] >= SECP256K1_N_0 && !no ? 1 : 0;

  return BigInt(yes);
}

function secp256k1_scalar_reduce(r, overflow) {
  const SECP256K1_N_C_0 = BigInt("0x0");
  const SECP256K1_N_C_1 = BigInt("0x0");
  const SECP256K1_N_C_2 = BigInt("0x0");

  let t = BigInt(r[0]);
  console.log("OF", overflow, typeof overlow);
  t += overflow * SECP256K1_N_C_0;
  r[0] = t & BigInt("0xFFFFFFFFFFFFFFFF");
  t >>= 64n;

  t += BigInt(r[1]);
  t += overflow * SECP256K1_N_C_1;
  r[1] = t & BigInt("0xFFFFFFFFFFFFFFFF");
  t >>= 64n;

  t += BigInt(r[2]);
  t += overflow * SECP256K1_N_C_2;
  r[2] = t & BigInt("0xFFFFFFFFFFFFFFFF");
  t >>= 64n;

  t += BigInt(r[3]);
  r[3] = t & BigInt("0xFFFFFFFFFFFFFFFF");

  return overflow;
}

// Write a uint64_t in big endian
function secp256k1_write_be64(x) {
  // Convert the BigInt to a buffer
  const buf = Buffer.alloc(8);
  buf.writeBigUInt64BE(BigInt(x));
  return buf;
}

function secp256k1_scalar_get_b32(a) {
  let bin = new Uint8Array(32);

  console.log("GETTING", a);

  let d3Bytes = secp256k1_write_be64(a[3]);
  let d2Bytes = secp256k1_write_be64(a[2]);
  let d1Bytes = secp256k1_write_be64(a[1]);
  let d0Bytes = secp256k1_write_be64(a[0]);

  console.log(d2Bytes);

  bin.set(d3Bytes, 0);
  bin.set(d2Bytes, 8);
  bin.set(d1Bytes, 16);
  bin.set(d0Bytes, 24);

  return bin;
}

function secp256k1_scalar_set_b32(b32) {
  let r = [0n, 0n, 0n, 0n];
  let overflow = [0n];

  r[0] = BigInt("0x" + b32.slice(24, 32).toString("hex"));
  r[1] = BigInt("0x" + b32.slice(16, 24).toString("hex"));
  r[2] = BigInt("0x" + b32.slice(8, 16).toString("hex"));
  r[3] = BigInt("0x" + b32.slice(0, 8).toString("hex"));

  console.log("R", r);
  const over = secp256k1_scalar_reduce(r, secp256k1_scalar_check_overflow(r));
  if (overflow !== undefined) {
    overflow[0] = over;
  }
  console.log("R", r);

  return { r, overflow };
}

class RNG {
  constructor(k, v, retry = false) {
    this.k = k;
    this.v = v;
    this.retry = retry;
  }

  static async create(key) {
    const zero = new Uint8Array([0x00]);
    const one = new Uint8Array([0x01]);

    let v = new Uint8Array(32).fill(0x01); // RFC6979 3.2.b.
    let k = new Uint8Array(32).fill(0x00); // RFC6979 3.2.c.

    // RFC6979 3.2.d.
    k = await hmacSha256Async(k, v, zero, key);
    v = await hmacSha256Async(k, v);

    // RFC6979 3.2.f.
    k = await hmacSha256Async(k, v, one, key);
    v = await hmacSha256Async(k, v);

    return new RNG(k, v, false);
  }

  async generate(out, outlen) {
    const zero = new Uint8Array([0x00]);
    if (this.retry) {
      this.k = await hmacSha256Async(this.k, this.v, zero);
      this.v = await hmacSha256Async(this.k, this.v);
    }

    while (outlen > 0) {
      let now = outlen > 32 ? 32 : outlen;
      this.v = await hmacSha256Async(this.k, this.v);
      out.set(this.v.slice(0, now), out.length - outlen);
      outlen -= now;
    }

    this.retry = true;
  }

  finalize() {
    this.k.fill(0);
    this.v.fill(0);
    this.retry = false;
  }
}

let negateScalar = (a) => (a === 0n ? 0n : (CURVE.n - a) % CURVE.n);

async function rangeproofGenrand(
  sec,
  s,
  message,
  rsizes,
  rings,
  nonce,
  commit,
  proof,
  len,
  gen,
) {
  let tmp = new Uint8Array(32);
  let rngseed = new Uint8Array(32 + 33 + 33 + len);
  let acc = 0n;
  let overflow;
  let ret = 1;
  let npub = 0;

  if (len > 10) {
    throw new Error("Invalid length");
  }

  const genP = ProjectivePoint.fromHex(gen);
  const commitP = ProjectivePoint.fromHex(commit);
  rngseed.set(h2b(nonce).slice(0, 32), 0);
  rngseed.set(serializePoint(commitP), 32);
  rngseed.set(serializePoint(genP), 32 + 33);
  rngseed.set(proof.slice(0, len), 32 + 33 + 33);

  let rng = await RNG.create(rngseed);

  for (let i = 0; i < rings; i++) {
    if (i < rings - 1) {
      await rng.generate(tmp, 32);
      do {
        await rng.generate(tmp, 32);
        sec[i] = b2n(tmp) % CURVE.n;
      } while (b2n(tmp) > CURVE.n || sec[i] === 0n);
      acc = (acc + sec[i]) % CURVE.n;
    } else {
      sec[i] = negateScalar(acc);
    }

    console.log("i:", i);
    console.log(sec[i])
    console.log("sec", b2h(n2b(sec[i])));

    for (let j = 0; j < rsizes[i]; j++) {
      await rng.generate(tmp, 32);
      if (message) {
        for (let b = 0; b < 32; b++) {
          tmp[b] ^= message[(i * 4 + j) * 32 + b];
          message[(i * 4 + j) * 32 + b] = tmp[b];
        }
      }
      s[npub] = b2n(tmp) % CURVE.n;
      ret &= s[npub] !== 0n;
      npub++;
    }
  }
  acc = 0n;

  console.log("17", sec[17])

  return ret;
}
