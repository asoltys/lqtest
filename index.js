import hex from "./hex.js";
import wif from "wif";
import * as btc from "@scure/btc-signer";
import {
  isUint8Array,
  hexToUint8Array,
  uint8ArrayToHex,
} from "uint8array-extras";
import {
  address as Address,
  Creator,
  Updater,
  Transaction,
  Pset,
  PsetInput,
  PsetOutput,
  Extractor,
  Finalizer,
  Signer,
  script,
} from "liquidjs-lib";
import { ecc, ECPair } from "./ecc.js";

Error.stackTraceLimit = Infinity;

const LBTC = "5ac9f65c0efcc4775e0baec4ec03abdde22473cd3cf33c0419ca290e0751b225";
let btx = Transaction.fromHex(hex);
let nonWitnessUtxo = hexToUint8Array(hex);
let stx = btc.Transaction.fromRaw(nonWitnessUtxo);
let sh = stx.hex;

let network = {
  bech32: "ert",
  pubKeyHash: 0xeb,
  scriptHash: 0x4b,
  wif: 0xef,
};

let pk = "cTMgtKAELWHfmJaTh4fAhU6RutQumLnt9jz9k3EYq1x8Le8qocmy";

let privkey = btc.WIF(network).decode(pk);
let destination = "ert1qp600lypu8un6fnlcszanangupml0xs9r96cgfc";
let decimal = 0.001;
let amount = 207900;

let i = 0;
let fee = 2100;
let tx = new btc.Transaction();
let txid = "19ad779b460cc58a3423897d8b6a82be6adfa46a8ea131586f92dc17704e6737";
let index = 1;
let nonce = Buffer.alloc(1);

tx.addInput({
  txid,
  index,
  nonWitnessUtxo,
});

tx.addOutputAddress(destination, BigInt(amount), LBTC, network);

tx.addFee(BigInt(fee));

tx.signIdx(privkey, 0);
tx.finalize();

let scureResult = tx.hex

let reverse = (s) => {
  let b = Buffer.from(s, "hex");
  let rev = Buffer.alloc(b.length);
  for (let i = 0; i < b.length; i++) {
    rev[b.length - i - 1] = b[i];
  }
  return rev;
};

let p = Creator.newPset();

let updater = new Updater(p);
updater.addInputs([{ txid, txIndex: index, witnessUtxo: btx.outs[1], sighashType: 0x01 }]);
updater.addOutputs([
  {
    amount,
    asset: LBTC,
    script: Address.toOutputScript(destination),
  },
  { amount: fee, asset: LBTC },
]);

let kp = ECPair.fromPrivateKey(wif.decode(pk).privateKey);

const signer = new Signer(p);

const preimage = p.getInputPreimage(i, 0x01);
const partialSig = {
  partialSig: {
    pubkey: kp.publicKey,
    signature: script.signature.encode(kp.sign(preimage), 0x01),
  },
};
signer.addSignature(i, partialSig, Pset.ECDSASigValidator(ecc));

if (!p.validateAllSignatures(Pset.ECDSASigValidator(ecc))) {
  throw new Error("Failed to sign pset");
}

const finalizer = new Finalizer(p);
finalizer.finalize();
let ljsResult = Extractor.extract(p).toHex()
console.log(scureResult)
console.log(ljsResult)
console.log(scureResult === ljsResult)
