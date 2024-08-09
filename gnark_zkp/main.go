package main

import (
	"bytes"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"flag"
	"fmt"
	"io"
	"math/big"
	"strconv"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	gnarkHash "github.com/consensys/gnark-crypto/hash"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/hash/mimc"
	"github.com/rs/zerolog"
	"github.com/rs/zerolog/log"
	"golang.org/x/crypto/hkdf"
)

type zkOpenWrapper2 struct {
	InMap      [][32]frontend.Variable
	DummyMask  frontend.Variable
	Plaintext  []frontend.Variable
	Ciphertext []frontend.Variable   `gnark:",public"`
	Parity     [16]frontend.Variable `gnark:",public"`
	Hash       frontend.Variable     `gnark:",public"`
}

// Define declares the circuit's constraints
func (circuit *zkOpenWrapper2) Define(api frontend.API) error {

	// init mimc
	mimc, _ := mimc.NewMiMC(api)

	// init parity sum
	parity1 := make([]frontend.Variable, 128)
	for i := 0; i < 128; i++ {
		parity1[i] = 0
	}

	// init ciphertext prime
	cipherPrime := make([]frontend.Variable, len(circuit.Plaintext))
	dummyMaskBits := api.ToBinary(circuit.DummyMask, 128)

	// loop over bytes
	for i := 0; i < len(circuit.InMap); i++ {

		// rearrange input to match mimc input requirements
		ddd := make([]frontend.Variable, 256)
		for j := 0; j < 32; j++ {

			// get bits of ecb input, little endian!
			myBits := api.ToBinary(circuit.InMap[i][j], 8)

			bitsPlaintext := api.ToBinary(circuit.Plaintext[(i*32)+j], 8)
			x := make([]frontend.Variable, 8)
			for k := 7; k >= 0; k-- {
				ddd[(31-j)*8+(k)] = myBits[k]

				// xor ecb data with plaintext
				x[k] = api.Xor(bitsPlaintext[k], myBits[k])
			}

			cipherPrime[(i*32)+j] = api.FromBinary(x...)
		}

		// input data into mimc
		varSum := api.FromBinary(ddd...)
		mimc.Write(varSum)

		// compute parity
		for j := 0; j < 128; j++ {
			// tmp := api.And(ddd[j])
			parity1[j] = api.Xor(parity1[j], api.And(ddd[j], dummyMaskBits[j]))
		}
		for j := 128; j < 256; j++ {
			parity1[j-128] = api.Xor(parity1[j-128], api.And(ddd[j], dummyMaskBits[j-128]))
		}
	}

	// mimc hash constraints check
	result := mimc.Sum()
	api.AssertIsEqual(circuit.Hash, result)

	// check ciphertextPrime against public input ciphertext
	for i := 0; i < len(circuit.Plaintext); i++ {
		api.AssertIsEqual(cipherPrime[i], circuit.Ciphertext[i])
	}

	// parity check
	for i := 0; i < 16; i++ {

		// byte reconstruction
		bits := make([]frontend.Variable, 8)
		for j := 0; j < 8; j++ {
			idx := (i * 8) + j
			bits[j] = parity1[idx]
		}
		parityByte := api.FromBinary(bits...)
		// compare parity checksum
		api.AssertIsEqual(circuit.Parity[15-i], parityByte)
	}

	return nil
}

// execution of circuit function of program
func EvaluateZkOpen2(in []big.Int, hash []byte, plain, cipher string) (map[string]time.Duration, error) {

	log.Debug().Msg("EvaluateZkOpen2")

	// dummy mask
	mask := "4647eb76ffd794580046acf096d6b7a2"
	maskBytes, _ := hex.DecodeString(mask)

	// compute parity checksum on input
	var parityBytes [16]byte
	for i := 0; i < len(in); i++ {
		for j := 0; j < len(parityBytes); j++ {
			parityBytes[j] = (parityBytes[j] ^ (in[i].Bytes()[:16][j])&maskBytes[j]) ^ (in[i].Bytes()[16:][j] & maskBytes[j])
		}
	}

	// hash dummy data evaluation
	t1 := time.Now()
	plainBs, _ := hex.DecodeString(plain)
	sha256.Sum256(plainBs)
	fmt.Println("hash computation took:", time.Since(t1))
	// t2 := time.Since(t1)

	// add mask
	// mask := "4647eb76ffd794580046acf096d6b7a2"
	// maskBytes, _ := hex.DecodeString(mask)
	// for j := 0; j < len(parityBytes); j++ {
	// 	parityBytes[j] = parityBytes[j] ^ maskBytes[j]
	// }

	byteSlice, _ := hex.DecodeString(plain)
	plainByteLen := len(byteSlice)
	byteSlice, _ = hex.DecodeString(cipher)
	cipherByteLen := len(byteSlice)

	parity := hex.EncodeToString(parityBytes[:])
	// maskAssign := StrToIntSlice(mask, true)
	parityAssign := StrToIntSlice(parity, true)
	plainAssign := StrToIntSlice(plain, true)
	cipherAssign := StrToIntSlice(cipher, true)
	inByteLen := len(in)

	maskBigInt := new(big.Int).SetBytes(maskBytes)

	log.Debug().Str("length", strconv.Itoa(inByteLen)).Msg("zkOpen input size")

	assignment := zkOpenWrapper2{
		InMap:      make([][32]frontend.Variable, inByteLen),
		Hash:       hash,
		DummyMask:  maskBigInt.String(),
		Parity:     [16]frontend.Variable{},
		Ciphertext: make([]frontend.Variable, cipherByteLen),
		Plaintext:  make([]frontend.Variable, plainByteLen),
	}

	// for i := 0; i < 16; i++ {
	// 	assignment.DummyMask[i] = maskAssign[i]
	// }
	for i := 0; i < inByteLen; i++ {
		byteSlice := in[i].Bytes()
		for j := 0; j < len(byteSlice); j++ {
			assignment.InMap[i][j] = int(byteSlice[j])
		}
	}
	for i := 0; i < 16; i++ {
		assignment.Parity[i] = parityAssign[i]
	}
	for i := 0; i < cipherByteLen; i++ {
		assignment.Ciphertext[i] = cipherAssign[i]
	}
	for i := 0; i < plainByteLen; i++ {
		assignment.Plaintext[i] = plainAssign[i]
	}

	// var circuit kdcServerKey
	circuit := zkOpenWrapper2{
		InMap:      make([][32]frontend.Variable, inByteLen),
		Ciphertext: make([]frontend.Variable, cipherByteLen),
		Plaintext:  make([]frontend.Variable, plainByteLen),
	}

	data, err := ProofWithBackend(&circuit, &assignment, ecc.BN254)

	return data, err
}

func main() {

	// checks for -evaluate-constraints flag
	iterations := flag.Int("iterations", 0, "indicates the iterations of the same evaluation")

	// size of data in bytes to generate and evaluate in circuit (applies only to circuits with dynamic input, e.g. gcm, sha256)
	byte_size := flag.Int("byte-size", 0, "indicates size of bytes to evaluate in circuit. applies only to circuits with dynamic input (e.g. gcm, sha256). byte-size mod 16 must be zero")
	// checks logging flag if program is called as ./main.go -debug
	debug := flag.Bool("debug", false, "sets log level to debug")

	// individual evaluation flags
	zkopen_circuit := flag.Bool("tls13-zkopen", false, "evaluates zkopen circuit")

	flag.Parse()

	zerolog.SetGlobalLevel(zerolog.InfoLevel)
	if *debug {
		zerolog.SetGlobalLevel(zerolog.DebugLevel)
	}
	// logging settings
	zerolog.TimeFieldFormat = zerolog.TimeFormatUnix

	// zkopen evaluation
	if *zkopen_circuit {
		data := map[string]string{}
		data["iterations"] = strconv.Itoa(*iterations)
		// data["backend"] = *ps
		if *byte_size != 0 {
			data["data_size"] = strconv.Itoa(*byte_size)
		} else {
			data["data_size"] = "default"
		}

		// generate data for evaluation
		curve := ecc.BN254
		modulus := curve.ScalarField()
		fmt.Println("modulus:", modulus)
		size := *byte_size / 32
		// size limit= 19360,
		// this number is divisible by 32 (19360/32=605) and size=19359 still works
		// so possible to hash 16 kb in mimc, takes 1.06s to prove
		if size%32 == 0 {
			size += 1
		}
		fmt.Println("size mimc:", size)

		// random input generation
		hash := sha256.New
		sString := "The quick brown fox jumps over the lazy dog"
		salt := make([]byte, 32)
		io.ReadFull(rand.Reader, salt)
		info := []byte("")
		secret := []byte(sString)
		kdf := hkdf.New(hash, secret, salt, info)
		fmt.Println("kdf:", kdf)

		// generate input
		hashInput := make([]big.Int, size)
		zkInput := make([]big.Int, size)

		// generate random plaintext
		plainBytes := make([]byte, size*32)
		cipherBytes := make([]byte, size*32)
		rand.Read(plainBytes)
		plain := hex.EncodeToString(plainBytes)

		// generate random input
		for i := 0; i < size; i++ {

			// hkdf
			// key2 := make([]byte, 32)
			// io.ReadFull(kdf, key2)
			// s := hex.EncodeToString(key2)

			s := "4647eb76ffd794580046acf096d6b7a22147cb7623d7145101461c1016162734"
			key2, _ := hex.DecodeString(s)
			// var s string
			// var key2 []byte
			if i%3 == 0 {
				s = "16374b76af2734585056ac5095d5b5a52542cb1613173413034615159626a734"
				key2, _ = hex.DecodeString(s)
			}

			// hash data
			hashInput[i].SetString(s, 16)
			zkInput[i].SetString(s, 16)
			hashInput[i].Mod(&hashInput[i], modulus)

			// encryption data
			for j := 0; j < 32; j++ {
				cipherBytes[(i*32)+j] = plainBytes[(i*32)+j] ^ key2[j]
			}
		}
		// hashInput := make([]big.Int, size)
		// hashInput[0].Sub(modulus, big.NewInt(1))
		// for i := 1; i < size; i++ {
		// 	hashInput[i].Add(&hashInput[i-1], &hashInput[i-1]).Mod(&hashInput[i], modulus)
		// }

		// get cipher as hex string
		cipher := hex.EncodeToString(cipherBytes)

		// byteArray := make([]byte, *byte_size)
		// in := hex.EncodeToString(byteArray)
		// running MiMC (Go)
		hashFunc := gnarkHash.MIMC_BN254
		goMimc := hashFunc.New()
		for i := 0; i < size; i++ {

			goMimc.Write(hashInput[i].Bytes()) // hashInput[i].Bytes()
		}
		expectedh := goMimc.Sum(nil)

		var s []map[string]time.Duration
		for i := *iterations; i > 0; i-- {
			data, err := EvaluateZkOpen2(zkInput, expectedh, plain, cipher)
			if err != nil {
				log.Error().Msg("e.EvaluateZkOpen2()")
			}
			s = append(s, data)
		}
	}
}

// non-gnark zk system evalaution functions
func ProofWithBackend(circuit frontend.Circuit, assignment frontend.Circuit, curveID ecc.ID) (map[string]time.Duration, error) {

	// time measures
	data := map[string]time.Duration{}

	// generate witness
	witness, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		log.Error().Msg("frontend.NewWitness")
		return nil, err
	}

	// init builders
	// var builder frontend.NewBuilder
	// var srs kzg.SRS
	builder := r1cs.NewBuilder

	// generate CompiledConstraintSystem
	start := time.Now()
	ccs, err := frontend.Compile(curveID.ScalarField(), builder, circuit)
	if err != nil {
		log.Error().Msg("frontend.Compile")
		return nil, err
	}
	elapsed := time.Since(start)
	log.Debug().Str("elapsed", elapsed.String()).Msg("compile constraint system time.")

	data["compile"] = elapsed

	// measure byte size
	var buf bytes.Buffer
	bytesWritten, err := ccs.WriteTo(&buf)
	if err != nil {
		log.Error().Msg("ccs serialization error")
		return nil, err
	}
	log.Debug().Str("written", strconv.FormatInt(bytesWritten, 10)).Msg("compiled constraint system bytes")

	// setup
	start = time.Now()
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		log.Error().Msg("groth16.Setup")
		return nil, err
	}
	elapsed = time.Since(start)
	log.Debug().Str("elapsed", elapsed.String()).Msg("groth16.Setup time.")

	data["setup"] = elapsed

	// measure byte size
	var buf1 bytes.Buffer
	bytesWritten1, err := pk.WriteTo(&buf1)
	if err != nil {
		log.Error().Msg("ccs serialization error")
		return nil, err
	}
	log.Debug().Str("written", strconv.FormatInt(bytesWritten1, 10)).Msg("prover key bytes")
	var buf2 bytes.Buffer
	bytesWritten2, err := vk.WriteTo(&buf2)
	if err != nil {
		log.Error().Msg("ccs serialization error")
		return nil, err
	}
	log.Debug().Str("written", strconv.FormatInt(bytesWritten2, 10)).Msg("verifier key bytes")

	// prove
	start = time.Now()
	proof, err := groth16.Prove(ccs, pk, witness) // backend.WithHints(emulated.GetHints()...)
	if err != nil {
		log.Error().Msg("groth16.Prove")
		return nil, err
	}
	elapsed = time.Since(start)
	log.Debug().Str("elapsed", elapsed.String()).Msg("groth16.Prove time.")

	data["prove"] = elapsed

	var buf3 bytes.Buffer
	bytesWritten3, err := proof.WriteTo(&buf3)
	if err != nil {
		log.Error().Msg("proof serialization error")
		return nil, err
	}
	log.Debug().Str("written", strconv.FormatInt(bytesWritten3, 10)).Msg("proof bytes")

	// generate public witness
	publicWitness, _ := witness.Public()

	witnessBytes, err := publicWitness.MarshalBinary()
	if err != nil {
		log.Error().Msg("witness marshal binary error")
		return nil, err
	}
	log.Debug().Str("written", strconv.Itoa(len(witnessBytes)/8)).Msg("witness bytes")

	// verification
	start = time.Now()
	err = groth16.Verify(proof, vk, publicWitness)
	if err != nil {
		log.Error().Msg("groth16.Verify")
		return nil, err
	}
	elapsed = time.Since(start)
	log.Debug().Str("elapsed", elapsed.String()).Msg("groth16.Verify time.")

	data["verify"] = elapsed

	return data, nil
}

// non-gnark str to int conversion
func StrToIntSlice(inputData string, hexRepresentation bool) []int {

	// check if inputData in hex representation
	var byteSlice []byte
	if hexRepresentation {
		hexBytes, err := hex.DecodeString(inputData)
		if err != nil {
			log.Error().Msg("hex.DecodeString error.")
		}
		byteSlice = hexBytes
	} else {
		byteSlice = []byte(inputData)
	}

	// convert byte slice to int numbers which can be passed to gnark frontend.Variable
	var data []int
	for i := 0; i < len(byteSlice); i++ {
		data = append(data, int(byteSlice[i]))
	}

	return data
}
