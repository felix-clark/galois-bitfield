use std::ops;

/// The Galois field GF(2^N) with primitive polynomial set by the bits of P
#[derive(Debug, Clone, Copy)]
pub struct Gf2<const N: u8, const P: u64> {
    encoded: u64,
}

impl<const N: u8, const P: u64> Gf2<N, P> {
    pub const fn validate_type() -> bool {
        // NOTE: Should this be 64/2 to handle multiplication before modulo? Maybe with an extra
        // bit?
        let a = N > 0 && N as u32 <= u64::BITS / 2;
        // The irreducible polynomial must be of degree N+1
        let b = N as u32 + 1 == u64::BITS - P.leading_zeros();
        let c = Self::is_irreducible(P);
        a && b && c
    }

    pub fn validate_value(&self) -> bool {
        (self.encoded >> N) == 0
    }

    // TODO: Maybe should use TryFrom to check value
    pub fn from_bits(encoded: u64) -> Self {
        Self { encoded }
    }

    /// Returns true iff the polynomial represented by p is irreducible using Rabin's algorithm
    /// specialized for GF[2^N].
    const fn is_irreducible(p: u64) -> bool {
        // Since 2^N has only one prime factor, there is less to check.
        let x_2_nm1 = _x_2nm1_mod(N, p);
        // h = x^(2^(N-1)) - x
        let h: u64 = x_2_nm1 ^ 0b10;
        let g = bitwise_gcd(h, p);
        // NOTE: This isn't actually big enough for N > 6 or so.
        let g_full: u64 = bitwise_mod(carryless_mul(x_2_nm1, x_2_nm1), p) ^ 0b10;
        (g == 1) && (bitwise_mod(g_full, p) == 0)
    }
}

/// Returns x^(2^(N-1)) mod p by repeated squaring (n-1 times)
const fn _x_2nm1_mod(mut n: u8, p: u64) -> u64 {
    let mut x_k: u64 = 0b10;
    while n > 1 {
        x_k = bitwise_mod(carryless_mul(x_k, x_k), p);
        n -= 1;
    }
    x_k
}

impl<const N: u8, const P: u64> ops::Add for Gf2<N, P> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::from_bits(self.encoded ^ rhs.encoded)
    }
}
impl<const N: u8, const P: u64> ops::Sub for Gf2<N, P> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::from_bits(self.encoded ^ rhs.encoded)
    }
}
impl<const N: u8, const P: u64> ops::Mul for Gf2<N, P> {
    type Output = Self;

    // To make this cryptographically secure, we'd need to make bitwise_mod so, or apply the
    // modulation at each loop to a << 1.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut p: u64 = 0;
        let mut a = self.encoded;
        let mut b = rhs.encoded;
        let mut ctr = N;
        while ctr > 0 {
            // if the 0th bit is set, b & 1 = 1, and the wrapping negative is 2^64 - 1 or
            // 0b11...11. Thus this operation either XORs w/ a, or does nothing, depending on if
            // the ones bit of b is set.
            p ^= (b & 1).wrapping_neg() & a;
            a <<= 1;
            b >>= 1;
            ctr -= 1;
        }
        Self {
            encoded: bitwise_mod(p, P),
        }
    }
}

/// Modulo function using GF[2^N] bitwise long division
const fn bitwise_mod(a: u64, n: u64) -> u64 {
    if n == 0 {
        panic!("Divide by zero in bitwise mod");
    }
    // division by zero means a quotient is undefined, but the modulo can just be the input.
    let quot_zeros = n.leading_zeros();
    let mut r = a;
    while let Some(d) = quot_zeros.checked_sub(r.leading_zeros()) {
        r ^= n << d;
    }
    r
}

const fn bitwise_euclid(a: u64, n: u64) -> (u64, u64) {
    if n == 0 {
        panic!("Divide by zero in bitwise euclid");
    }
    let quot_zeros = n.leading_zeros();
    let mut q = 0;
    let mut r = a;
    while let Some(d) = quot_zeros.checked_sub(r.leading_zeros()) {
        q |= 1 << d;
        r ^= n << d;
    }
    (q, r)
}

const fn bitwise_gcd(a: u64, b: u64) -> u64 {
    if b.leading_zeros() < a.leading_zeros() {
        // if b > a { // Just checking leading zeros should be sufficient
        return bitwise_gcd(b, a);
    }
    if b == 0 {
        return a;
    }
    let r = bitwise_mod(a, b);
    bitwise_gcd(b, r)
}

/// Carryless multiplication without modulation.
/// Susceptible to timing and other attacks.
// TODO: This probably has issues with invalid inputs, e.g. too many bits.
const fn carryless_mul(mut a: u64, mut b: u64) -> u64 {
    // TODO: Check this condition; should it be strictly greater than?
    assert!(a.leading_zeros() + b.leading_zeros() >= u64::BITS);
    // accumulator
    let mut p = 0;
    while b != 0 {
        // if the 0th bit is set, b & 1 = 1, and the wrapping negative is 2^64 - 1 or 0b11...11.
        // Thus this operation either XORs w/ a, or does nothing, depending on if the ones bit of b
        // is set.
        p ^= (b & 1).wrapping_neg() & a;
        a <<= 1;
        b >>= 1;
    }
    p
}

/// Rijndael's finite field, used in AES encryption.
// GF[2^8] with x^8 + x^4 + x^3 + x + 1
pub type Rijndael = Gf2<8, 0b1_0001_1011>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valtype() {
        type F = Rijndael;
        assert!(F::validate_type());
        assert!(
            !Gf2::<4, 0b0100>::validate_type(),
            "validate_type() should catch reducible poly"
        );
        let a = F::from_bits(53);
        assert!(a.validate_value());
    }

    #[test]
    #[should_panic]
    fn div_by_zero() {
        bitwise_mod(0b10010, 0);
    }

    #[test]
    fn xor_mul() {
        let a = 0b0010;
        let b = 0b0110;
        let c = 0b1100;
        assert_eq!(c, carryless_mul(a, b));
        // example from wikipedia
        let a = 0b1010_0010;
        let b = 0b1001_0110;
        let c = 0b0101_1000_1110_1100;
        assert_eq!(c, carryless_mul(a, b));
        assert_eq!(c, carryless_mul(b, a));
    }

    #[test]
    fn bw_euclid() {
        assert_eq!(bitwise_mod(0b011, 0b100), 0b11);
        assert_eq!(bitwise_mod(0b101, 0b100), 0b01);
        assert_eq!(bitwise_mod(0b111, 0b100), 0b11);
        assert_eq!(bitwise_mod(0b1101, 0b110), 0b01);
        assert_eq!(bitwise_euclid(0b100, 0b10), (0b10, 0));
    }
}
