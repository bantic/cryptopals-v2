mod utils {
  // top (leftmost) `hi` bits of v
  pub fn top_bits(v: u8, hi: u8) -> u8 {
    let lo = 8 - hi;
    (v >> lo) & ((1 << hi) - 1)
  }

  // bottom (rightmost) `lo` bits of v
  pub fn bottom_bits(v: u8, lo: u8) -> u8 {
    v & ((1 << lo) - 1)
  }
}

mod xor {
  pub fn fixed(lhs: &str, rhs: &str) -> Vec<u8> {
    let lhs = super::hex::from_str(lhs);
    let rhs = super::hex::from_str(rhs);

    if lhs.len() != rhs.len() {
      panic!("Different lengths for input strings");
    }

    let mut result = vec![];
    for idx in 0..lhs.len() {
      result.push(lhs[idx] ^ rhs[idx]);
    }

    result
  }

  pub fn fixed_to_str(lhs: &str, rhs: &str) -> String {
    super::hex::to_str(fixed(lhs, rhs))
  }
}

mod hex {
  // hex string -> [u8]
  pub fn from_str(s: &str) -> Vec<u8> {
    to_u8(s)
  }

  pub fn to_str(data: Vec<u8>) -> String {
    from_u8(data)
  }

  fn from_u8(data: Vec<u8>) -> String {
    use super::utils::{bottom_bits, top_bits};
    let mut result = String::new();

    for d in data {
      result.push(char_val(top_bits(d, 4)));
      result.push(char_val(bottom_bits(d, 4)));
    }

    result
  }

  // convert len-2 input
  fn to_u8(s: &str) -> Vec<u8> {
    if s.len() % 2 != 0 {
      panic!("Expected string of len % 2 = 0");
    }
    let mut bytes = vec![];

    for chars in s.chars().collect::<Vec<_>>().chunks(2) {
      bytes.push(hex_val(chars[0] as u8) << 4 | hex_val(chars[1] as u8));
    }

    bytes
  }

  // to lower hex val
  fn char_val(d: u8) -> char {
    match d {
      0...9 => (b'0' + d) as char,
      10...15 => (b'a' + (d - 10)) as char,
      _ => panic!("Encountered invalid u8 for hex char val {}", d),
    }
  }

  fn hex_val(c: u8) -> u8 {
    match c {
      b'A'...b'F' => c - b'A' + 10,
      b'a'...b'f' => c - b'a' + 10,
      b'0'...b'9' => c - b'0',
      _ => panic!("Unexpected char: {}", c),
    }
  }
}

mod base64 {
  const BASE64_CHARS: [char; 64] = [
    'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S',
    'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l',
    'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '0', '1', '2', '3', '4',
    '5', '6', '7', '8', '9', '+', '/',
  ];

  pub fn to_base64(data: Vec<u8>) -> String {
    let mut s = String::new();
    let padding = dbg!(match data.len() % 3 {
      0 => 0,
      x => 3 - x,
    });
    let data_6bit = dbg!(u8_8bit_to_6bit(data));

    for d in data_6bit {
      s.push(base64_val(d));
    }

    for _ in 0..padding {
      s.push('=');
    }
    s
  }

  pub fn u8_8bit_to_6bit(data: Vec<u8>) -> Vec<u8> {
    use super::utils::{bottom_bits, top_bits};
    let mut result = vec![];
    let mut val6bit;

    let mut remainder_bits = 0;
    let mut remainder = 0;

    for val8bit in data {
      let needed_bits = 6 - remainder_bits;

      val6bit = (remainder << needed_bits) | top_bits(val8bit, needed_bits);

      result.push(val6bit);

      remainder_bits = 8 - needed_bits;
      remainder = bottom_bits(val8bit, remainder_bits);

      if remainder_bits == 6 {
        result.push(remainder);
        remainder = 0;
        remainder_bits = 0;
      }
    }

    if remainder_bits > 0 {
      // Pad with 0s
      result.push(remainder << (6 - remainder_bits));
    }

    result
  }

  fn base64_val(c: u8) -> char {
    BASE64_CHARS[c as usize]
  }
}

#[cfg(test)]
mod test {
  use super::base64::*;
  use super::hex::*;
  use super::xor;

  #[test]
  fn test_u8_to_base64() {
    assert_eq!(to_base64(vec![b'M', b'a', b'n']), "TWFu");
    assert_eq!(to_base64(vec![b'M', b'a']), "TWE=");
    assert_eq!(to_base64(vec![b'M']), "TQ==");
  }

  #[test]
  fn test_8bit_to_6bit() {
    assert_eq!(u8_8bit_to_6bit(vec![77, 97, 110]), vec![19, 22, 5, 46]);
    assert_eq!(u8_8bit_to_6bit(vec![77, 97]), vec![19, 22, 4]);
    assert_eq!(u8_8bit_to_6bit(vec![77]), vec![19, 16]);
  }

  #[test]
  fn test_single_byte_string_to_u8() {
    assert_eq!(from_str("00"), vec![0]);
    assert_eq!(from_str("01"), vec![1]);
    assert_eq!(from_str("10"), vec![16]);
    assert_eq!(from_str("20"), vec![32]);
    assert_eq!(from_str("0F"), vec![15]);
    assert_eq!(from_str("FF"), vec![255]);
  }

  #[test]
  fn test_multi_byte_from_str_to_u8() {
    assert_eq!(from_str("0000"), vec![0, 0]);
    assert_eq!(from_str("0101"), vec![1, 1]);
    assert_eq!(from_str("FF10"), vec![255, 16]);
    assert_eq!(from_str("fF10"), vec![255, 16]);
    assert_eq!(from_str("ff10"), vec![255, 16]);
    assert_eq!(from_str("Ff10"), vec![255, 16]);
  }

  #[test]
  fn challenge1() {
    assert_eq!(
      to_base64(from_str("49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d")),
      "SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"
    );
  }

  #[test]
  fn challenge2() {
    assert_eq!(
      xor::fixed_to_str(
        "1c0111001f010100061a024b53535009181c",
        "686974207468652062756c6c277320657965"
      ),
      "746865206b696420646f6e277420706c6179"
    );
  }
}
