mod set1;

fn main() {
  println!("Hello, world!");
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn it_works() {
    assert_eq!(1, 1);
  }
}
