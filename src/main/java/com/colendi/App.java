package com.colendi;

import org.bouncycastle.asn1.sec.SECNamedCurves;
import org.bouncycastle.asn1.x9.X9ECParameters;
import org.bouncycastle.asn1.x9.X9IntegerConverter;
import org.bouncycastle.crypto.params.ECDomainParameters;
import org.bouncycastle.jce.provider.BouncyCastleProvider;
import org.bouncycastle.math.ec.ECAlgorithms;
import org.bouncycastle.math.ec.ECPoint;
import org.bouncycastle.math.ec.custom.sec.SecP256K1Curve;
import org.bouncycastle.util.Arrays;
import org.bouncycastle.util.BigIntegers;
import org.bouncycastle.util.encoders.Hex;
import org.web3j.abi.datatypes.generated.Bytes32;
import org.web3j.abi.datatypes.generated.Uint8;
import org.web3j.crypto.ECDSASignature;
import org.web3j.crypto.ECKeyPair;
import org.web3j.crypto.Hash;
import org.web3j.crypto.Sign;
import org.web3j.utils.Numeric;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.security.Security;

public class App
{
    private static final String CURVE_NAME = "secp256k1";

    static ECDomainParameters CURVE;
    static BigInteger CURVE_ORDER;
    static BigInteger HALF_CURVE_ORDER;

    static X9ECParameters x9ECParameters;
    static final String MESSAGE_PREFIX = "\u0019Ethereum Signed Message:\n";



    public static void main( String[] args ) throws Exception {
        Security.addProvider(new BouncyCastleProvider());
        curveInit();
        testSign();

    }

    public static void testSign() throws IOException {
        String privateKey = "f50af650dae67a932fe05bd187e8dc01742d592baeb22a8e3bd4217e93de7738";
        ECKeyPair ecKeyPair = ECKeyPair.create(new BigInteger(privateKey, 16));

        String walletAddress = "9171426EDF931Cd53C669D9fF850eB6b6804e1aA";
        String contractAddress = "d1fb5ff170827da090cc2fc58f37d7329ea1c406";
        int nonce = 0;

        byte[] walletBytes = Hex.decode(walletAddress);
        byte[] contractBytes = Hex.decode(contractAddress);
        byte[] preNonceBytes = BigIntegers.asUnsignedByteArray(new BigInteger(String.valueOf(nonce)));

        byte[] nonceBytes = new byte[32];
        System.arraycopy(preNonceBytes,0,nonceBytes,32-preNonceBytes.length, preNonceBytes.length);

        ByteArrayOutputStream bos = new ByteArrayOutputStream();

        bos.write(contractBytes);
        bos.write(walletBytes);
        bos.write(nonceBytes);

        byte[] messageToSign = bos.toByteArray();

        byte[] outHash = Hash.sha3(messageToSign);



        Sign.SignatureData signMessage = signPrefixedMessage(outHash, ecKeyPair);

        Uint8 v = new Uint8(signMessage.getV());
        Bytes32 r = new Bytes32(signMessage.getR());
        Bytes32 s = new Bytes32(signMessage.getS());

        ByteArrayOutputStream bosSignature = new ByteArrayOutputStream();

        bosSignature.write(r.getValue());
        bosSignature.write(s.getValue());
        bosSignature.write(BigIntegers.asUnsignedByteArray(v.getValue()));


        byte[] signature = bosSignature.toByteArray();

        System.out.println(new String(Hex.encode(signature)));

    }

    static byte[] getEthereumMessagePrefix(int messageLength) {
        return MESSAGE_PREFIX.concat(String.valueOf(messageLength)).getBytes();
    }

    static byte[] getEthereumMessageHash(byte[] message) {
        byte[] prefix = getEthereumMessagePrefix(message.length);
        byte[] result = new byte[prefix.length + message.length];
        System.arraycopy(prefix, 0, result, 0, prefix.length);
        System.arraycopy(message, 0, result, prefix.length, message.length);
        return Hash.sha3(result);
    }

    public static Sign.SignatureData signPrefixedMessage(byte[] message, ECKeyPair keyPair) {
        return signMessage(getEthereumMessageHash(message), keyPair, false);
    }

    public static Sign.SignatureData signMessage(byte[] message, ECKeyPair keyPair, boolean needToHash) {
        BigInteger publicKey = keyPair.getPublicKey();
        byte[] messageHash;
        if (needToHash) {
            messageHash = Hash.sha3(message);
        } else {
            messageHash = message;
        }

        ECDSASignature sig = keyPair.sign(messageHash);
        int recId = -1;

        int headerByte;
        for(headerByte = 0; headerByte < 4; ++headerByte) {
            BigInteger k = recoverFromSignature(headerByte, sig, messageHash);
            if (k != null && k.equals(publicKey)) {
                recId = headerByte;
                break;
            }
        }

        if (recId == -1) {
            throw new RuntimeException("Could not construct a recoverable key. Are your credentials valid?");
        } else {
            headerByte = recId + 27;
            byte v = (byte)headerByte;
            byte[] r = Numeric.toBytesPadded(sig.r, 32);
            byte[] s = Numeric.toBytesPadded(sig.s, 32);
            return new Sign.SignatureData(v, r, s);
        }
    }

    public static BigInteger recoverFromSignature(int recId, ECDSASignature sig, byte[] message) {

        // 1.0 For j from 0 to h   (h == recId here and the loop is outside this function)
        //   1.1 Let x = r + jn
        BigInteger n = CURVE.getN();  // Curve order.
        BigInteger i = BigInteger.valueOf((long) recId / 2);
        BigInteger x = sig.r.add(i.multiply(n));
        //   1.2. Convert the integer x to an octet string X of length mlen using the conversion
        //        routine specified in Section 2.3.7, where mlen = ⌈(log2 p)/8⌉ or mlen = ⌈m/8⌉.
        //   1.3. Convert the octet string (16 set binary digits)||X to an elliptic curve point R
        //        using the conversion routine specified in Section 2.3.4. If this conversion
        //        routine outputs "invalid", then do another iteration of Step 1.
        //
        // More concisely, what these points mean is to use X as a compressed public key.
        BigInteger prime = SecP256K1Curve.q;
        if (x.compareTo(prime) >= 0) {
            // Cannot have point co-ordinates larger than this as everything takes place modulo Q.
            return null;
        }
        // Compressed keys require you to know an extra bit of data about the y-coord as there are
        // two possibilities. So it's encoded in the recId.
        ECPoint R = decompressKey(x, (recId & 1) == 1);
        //   1.4. If nR != point at infinity, then do another iteration of Step 1 (callers
        //        responsibility).
        if (!R.multiply(n).isInfinity()) {
            return null;
        }
        //   1.5. Compute e from M using Steps 2 and 3 of ECDSA signature verification.
        BigInteger e = new BigInteger(1, message);
        //   1.6. For k from 1 to 2 do the following.   (loop is outside this function via
        //        iterating recId)
        //   1.6.1. Compute a candidate public key as:
        //               Q = mi(r) * (sR - eG)
        //
        // Where mi(x) is the modular multiplicative inverse. We transform this into the following:
        //               Q = (mi(r) * s ** R) + (mi(r) * -e ** G)
        // Where -e is the modular additive inverse of e, that is z such that z + e = 0 (mod n).
        // In the above equation ** is point multiplication and + is point addition (the EC group
        // operator).
        //
        // We can find the additive inverse by subtracting e from zero then taking the mod. For
        // example the additive inverse of 3 modulo 11 is 8 because 3 + 8 mod 11 = 0, and
        // -3 mod 11 = 8.
        BigInteger eInv = BigInteger.ZERO.subtract(e).mod(n);
        BigInteger rInv = sig.r.modInverse(n);
        BigInteger srInv = rInv.multiply(sig.s).mod(n);
        BigInteger eInvrInv = rInv.multiply(eInv).mod(n);
        ECPoint q = ECAlgorithms.sumOfTwoMultiplies(CURVE.getG(), eInvrInv, R, srInv);

        byte[] qBytes = q.getEncoded(false);
        // We remove the prefix
        return new BigInteger(1, Arrays.copyOfRange(qBytes, 1, qBytes.length));
    }

    private static ECPoint decompressKey(BigInteger xBN, boolean yBit) {
        X9IntegerConverter x9 = new X9IntegerConverter();
        byte[] compEnc = x9.integerToBytes(xBN, 1 + x9.getByteLength(CURVE.getCurve()));
        compEnc[0] = (byte)(yBit ? 0x03 : 0x02);
        return CURVE.getCurve().decodePoint(compEnc);
    }

    public static void curveInit(){
        try {
            Class.forName("org.bouncycastle.asn1.sec.SECNamedCurves");
        } catch (ClassNotFoundException e) {
            throw new IllegalStateException(
                    "BouncyCastle is not available on the classpath, see https://www.bouncycastle.org/latest_releases.html");
        }
        x9ECParameters = SECNamedCurves.getByName(CURVE_NAME);
        CURVE = new ECDomainParameters(x9ECParameters.getCurve(), x9ECParameters.getG(), x9ECParameters.getN(), x9ECParameters.getH());
        CURVE_ORDER = CURVE.getN();
        HALF_CURVE_ORDER = CURVE_ORDER.shiftRight(1);
        if (CURVE_ORDER.compareTo(SecP256K1Curve.q) >= 0) {
            throw new IllegalStateException("secp256k1.n should be smaller than secp256k1.q, but is not");
        }

    }
}
