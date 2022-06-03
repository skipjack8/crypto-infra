use crypto::bellman::pairing::Engine;
use crypto::bellman::{ConstraintSystem, SynthesisError};
use crypto::circuit::boolean::Boolean;
use crypto::circuit::multieq::MultiEq;
use crypto::circuit::uint32::UInt32;

const IV: [u32; 8] = [
    0x7380166f, 0x4914b2b9, 0x172442d7, 0xda8a0600, 0xa96f30bc, 0x163138aa, 0xe38dee4d, 0xb0fb0e4e,
];

const T: [u32; 2] = [0x79cc4519, 0x7a879d8a];

// for 0 <= j <= 15
#[allow(non_snake_case)]
fn FF0<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    x: &UInt32,
    y: &UInt32,
    z: &UInt32,
) -> Result<UInt32, SynthesisError> {
    let x_xor_y = x.xor(&mut cs.namespace(|| "x xor y"), y)?;

    let result = x_xor_y.xor(&mut cs.namespace(|| "x xor y xor z"), z)?;

    Ok(result)
}

// for 0 <= j <= 15
#[allow(non_snake_case)]
fn GG0<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    x: &UInt32,
    y: &UInt32,
    z: &UInt32,
) -> Result<UInt32, SynthesisError> {
    let x_xor_y = x.xor(&mut cs.namespace(|| "x xor y"), y)?;

    let result = x_xor_y.xor(&mut cs.namespace(|| "x xor y xor z"), z)?;

    Ok(result)
}

#[allow(non_snake_case)]
fn P0<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    x: &UInt32,
) -> Result<UInt32, SynthesisError> {
    let tmp = x.xor(&mut cs.namespace(|| "x xor (x <<< 9)"), &x.rotl(9))?;

    let result = tmp.xor(
        &mut cs.namespace(|| "x xor (x <<< 9) xor (x <<< 17)"),
        &x.rotl(17),
    )?;

    Ok(result)
}

#[allow(non_snake_case)]
fn P1<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    x: &UInt32,
) -> Result<UInt32, SynthesisError> {
    let tmp = x.xor(&mut cs.namespace(|| "x xor (x <<< 15)"), &x.rotl(15))?;

    let result = tmp.xor(
        &mut cs.namespace(|| "x xor (x <<< 15) xor (x <<< 23)"),
        &x.rotl(23),
    )?;

    Ok(result)
}

pub fn sm3<E, CS>(mut cs: CS, input: &[Boolean]) -> Result<Vec<Boolean>, SynthesisError>
where
    E: Engine,
    CS: ConstraintSystem<E>,
{
    assert!(input.len() % 8 == 0);

    let mut padded = input.to_vec();
    let l = padded.len() as u64;
    // append a single '1' bit
    padded.push(Boolean::constant(true));
    // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K + 64 is a multiple of 512
    while (padded.len() + 64) % 512 != 0 {
        padded.push(Boolean::constant(false));
    }
    // append L as a 64-bit big-endian integer, making the total post-processed length a multiple of 512 bits
    for b in (0..64).rev().map(|i| (l >> i) & 1 == 1) {
        padded.push(Boolean::constant(b));
    }
    assert!(padded.len() % 512 == 0);

    let mut cur = get_iv();
    for (i, block) in padded.chunks(512).enumerate() {
        cur = sm3_compress(cs.namespace(|| format!("block {}", i)), block, &cur)?;
    }

    Ok(cur.into_iter().flat_map(|e| e.into_bits_be()).collect())
}

pub fn get_iv() -> Vec<UInt32> {
    IV.iter().map(|&v| UInt32::constant(v)).collect()
}

pub fn sm3_compress<E, CS>(
    cs: CS,
    input: &[Boolean],
    current_hash_value: &[UInt32],
) -> Result<Vec<UInt32>, SynthesisError>
where
    E: Engine,
    CS: ConstraintSystem<E>,
{
    assert_eq!(input.len(), 512);
    assert_eq!(current_hash_value.len(), 8);

    // expansion
    let mut w = input
        .chunks(32)
        .map(|e| UInt32::from_bits_be(e))
        .collect::<Vec<_>>();

    let mut cs = MultiEq::new(cs);

    for j in 16..68 {
        let cs = &mut cs.namespace(|| format!("w extension {}", j));

        // w[j] := P1(w[j-16] xor w[j-9] xor (w[j-3] <<< 15)) xor (w[j-13] <<< 7) xor w[j-6]
        let mut p1 = w[j - 16].xor(cs.namespace(|| "first xor for p1"), &w[j - 9])?;
        p1 = p1.xor(cs.namespace(|| "second xor for p1"), &w[j - 3].rotl(15))?;

        let mut tmp = P1(cs.namespace(|| "P1"), &p1)?;
        tmp = tmp.xor(cs.namespace(|| "first xor for wj"), &w[j - 13].rotl(7))?;
        tmp = tmp.xor(cs.namespace(|| "second xor for wj"), &w[j - 6])?;

        w.push(tmp);
    }
    assert_eq!(w.len(), 68);

    let mut w1 = vec![];
    for j in 0..64 {
        let tmp = w[j].xor(cs.namespace(|| format!("w1extension w1{}", j)), &w[j + 4])?;
        w1.push(tmp);
    }

    let mut a = current_hash_value[0].clone();
    let mut b = current_hash_value[1].clone();
    let mut c = current_hash_value[2].clone();
    let mut d = current_hash_value[3].clone();
    let mut e = current_hash_value[4].clone();
    let mut f = current_hash_value[5].clone();
    let mut g = current_hash_value[6].clone();
    let mut h = current_hash_value[7].clone();

    for j in 0..64 {
        let cs = &mut cs.namespace(|| format!("compression round {}", j));
        let t = if j < 16 { T[0] } else { T[1] };

        let ss1 = UInt32::addmany(
            cs.namespace(|| "ss1 add"),
            &[a.rotl(12), e.clone(), UInt32::constant(t).rotl(j)],
        )?
        .rotl(7);

        let ss2 = ss1.xor(cs.namespace(|| "ss2"), &a.rotl(12))?;

        let ff = if j < 16 {
            FF0(cs.namespace(|| "ff0"), &a, &b, &c)?
        } else {
            UInt32::sm3_ff1(cs.namespace(|| "ff1"), &a, &b, &c)?
        };
        let tt1 = UInt32::addmany(cs.namespace(|| "tt1"), &[ff, d.clone(), ss2, w1[j].clone()])?;

        let gg = if j < 16 {
            GG0(cs.namespace(|| "gg0"), &e, &f, &g)?
        } else {
            UInt32::sm3_gg1(cs.namespace(|| "gg1"), &e, &f, &g)?
        };
        let tt2 = UInt32::addmany(cs.namespace(|| "tt2"), &[gg, h.clone(), ss1, w[j].clone()])?;

        d = c.clone();
        c = b.rotl(9);
        b = a.clone();
        a = tt1.clone();
        h = g.clone();
        g = f.rotl(19);
        f = e.clone();
        e = P0(cs.namespace(|| "P0"), &tt2)?;
    }

    /*
        Add the compressed chunk to the current hash value:
        h0 := h0 + a
        h1 := h1 + b
        h2 := h2 + c
        h3 := h3 + d
        h4 := h4 + e
        h5 := h5 + f
        h6 := h6 + g
        h7 := h7 + h
    */

    let h0 = a.xor(cs.namespace(|| "new h0"), &current_hash_value[0])?;
    let h1 = b.xor(cs.namespace(|| "new h1"), &current_hash_value[1])?;
    let h2 = c.xor(cs.namespace(|| "new h2"), &current_hash_value[2])?;
    let h3 = d.xor(cs.namespace(|| "new h3"), &current_hash_value[3])?;
    let h4 = e.xor(cs.namespace(|| "new h4"), &current_hash_value[4])?;
    let h5 = f.xor(cs.namespace(|| "new h5"), &current_hash_value[5])?;
    let h6 = g.xor(cs.namespace(|| "new h6"), &current_hash_value[6])?;
    let h7 = h.xor(cs.namespace(|| "new h7"), &current_hash_value[7])?;

    Ok(vec![h0, h1, h2, h3, h4, h5, h6, h7])
}

#[cfg(test)]
mod test {
    use super::*;
    use crypto::bellman::bls12_381::Bls12;
    use crypto::circuit::boolean::AllocatedBit;
    use crypto::circuit::test::TestConstraintSystem;
    use rand::{Rng, SeedableRng, XorShiftRng};

    #[test]
    fn test_blank_hash() {
        let iv = get_iv();

        let mut cs = TestConstraintSystem::<Bls12>::new();
        let mut input_bits: Vec<_> = (0..512).map(|_| Boolean::Constant(false)).collect();
        input_bits[0] = Boolean::Constant(true);
        let out = sm3_compress(&mut cs, &input_bits, &iv).unwrap();
        let out_bits: Vec<_> = out.into_iter().flat_map(|e| e.into_bits_be()).collect();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        let expected =
            hex::decode("1AB21D8355CFA17F8E61194831E81A8F22BEC8C728FEFB747ED035EB5082AA2B")
                .unwrap();

        let mut out = out_bits.into_iter();
        for b in expected.iter() {
            for i in (0..8).rev() {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    /// sm3("abc")=0x66C7F0F462EEEDD9D1F2D46BDC10E4E24167C4875CF2F7A2297DA02B8F4BA8E0
    #[test]
    fn test_sm3_standards() {
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let input = vec![
            Boolean::constant(false),
            Boolean::constant(true),
            Boolean::constant(true),
            Boolean::constant(false),
            Boolean::constant(false),
            Boolean::constant(false),
            Boolean::constant(false),
            Boolean::constant(true),
            Boolean::constant(false),
            Boolean::constant(true),
            Boolean::constant(true),
            Boolean::constant(false),
            Boolean::constant(false),
            Boolean::constant(false),
            Boolean::constant(true),
            Boolean::constant(false),
            Boolean::constant(false),
            Boolean::constant(true),
            Boolean::constant(true),
            Boolean::constant(false),
            Boolean::constant(false),
            Boolean::constant(false),
            Boolean::constant(true),
            Boolean::constant(true),
        ];
        let out_bits = sm3(&mut cs, &input).unwrap();

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        let expected =
            hex::decode("66C7F0F462EEEDD9D1F2D46BDC10E4E24167C4875CF2F7A2297DA02B8F4BA8E0")
                .unwrap();

        let mut out = out_bits.into_iter();
        for b in expected.iter() {
            for i in (0..8).rev() {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_against_vectors() {
        use sm3::{Digest, Sm3};

        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for input_len in (0..32).chain((32..256).filter(|a| a % 8 == 0)) {
            let mut h = Sm3::new();
            let data: Vec<u8> = (0..input_len).map(|_| rng.gen()).collect();
            h.update(&data);
            let hash_result = h.finalize();

            let mut cs = TestConstraintSystem::<Bls12>::new();
            let mut input_bits = vec![];

            for (byte_i, input_byte) in data.into_iter().enumerate() {
                for bit_i in (0..8).rev() {
                    let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

                    input_bits.push(
                        AllocatedBit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8))
                            .unwrap()
                            .into(),
                    );
                }
            }

            let r = sm3(&mut cs, &input_bits).unwrap();

            assert!(cs.is_satisfied());

            let mut s = hash_result[..]
                .iter()
                .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

            for b in r {
                match b {
                    Boolean::Is(b) => {
                        assert_eq!(s.next().unwrap(), b.get_value().unwrap());
                    }
                    Boolean::Not(b) => {
                        assert_ne!(s.next().unwrap(), b.get_value().unwrap());
                    }
                    Boolean::Constant(b) => {
                        assert_eq!(input_len, 0);
                        assert_eq!(s.next().unwrap(), b);
                    }
                }
            }
        }
    }
}
