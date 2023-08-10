
use std::marker::PhantomData;
use group::ff::Field;
use halo2_proofs::{
  circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value},
  plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector, Expression},
  poly::Rotation,
};


/// This examples creates a circuit that proves knowledge of a fibonacci number 
/// A Fibonacci sequence is defined by a0 = 0, a1 = 1, a_i = a_{i-2} + a_{i-1} for i > 1
/// 
/// Created with the following halo2 fibonacci examples:
/// https://github.com/therealyingtong/halo2-hope/blob/main/src/fibonacci.rs
/// https://github.com/icemelon/halo2-tutorial/blob/master/src/example1.rs

// return fibonacci sequence of length len
pub fn get_fibonacci_seq(len: usize) -> Vec<u64> {
  let mut res = Vec::new();
  res.push(0);
  res.push(1);
  
  for i in 2..len {
    res.push(res.get(i-2).unwrap() + res.get(i-1).unwrap());
  }
  res
}

// Chip state
// this is required at circuit synthesis time
#[derive(Clone, Debug)]
struct FibonacciConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    i: Column<Instance>, // pub value
    s: Selector,
}

struct FibonacciChip<F: Field> {
  config: FibonacciConfig,
  _marker: PhantomData<F>,
}

// Implementing necessary things to make it a Halo2 chip
impl<F: Field> Chip<F> for FibonacciChip<F> {
    // Configuration for the chip, and any other state it may need
    type Config = FibonacciConfig;

    // Any general chip state that must be loaded at start
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: Field> FibonacciChip<F> {

  fn construct(config: FibonacciConfig) -> Self {
    Self {
        config,
        _marker: PhantomData,
    }
}

  // Define the workings of the chip
  ///
  /// | a | b | c | selector
  /// 
  fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
    // Columns layout
    let a = meta.advice_column();
    let b = meta.advice_column();
    let c = meta.advice_column();

    let i = meta.instance_column();
    
    let selector = meta.selector();

    // Enable the ability to enforce equality over cells in these columns
    meta.enable_equality(a);
    meta.enable_equality(b);
    meta.enable_equality(c);
    meta.enable_equality(i);

    // Define the gate
    meta.create_gate("fibonacci", |virtual_cells| {
      let s: Expression<F> = virtual_cells.query_selector(selector);
      let lhs = virtual_cells.query_advice(a, Rotation::cur());
      let rhs = virtual_cells.query_advice(b, Rotation::cur());
      let out = virtual_cells.query_advice(c, Rotation::cur());
      vec![(lhs+rhs-out) * s]
    });

    FibonacciConfig { a, b, c, i, s: selector}

  }

  // How the initial row is created
  fn set_initial_values(
    &self,
    mut layouter: impl Layouter<F>,
    a: Value<F>,
    b: Value<F>) -> Result<(AssignedCell<F,F>, AssignedCell<F,F>), Error>{
      layouter.assign_region(|| "first row", | mut region | {
        self.config.s.enable(&mut region, 0)?;

        let cell_a = region.assign_advice(
          || "a",
          self.config.a,
          0,
          || a)?;

        let cell_b = region.assign_advice(
          || "b",
          self.config.b,
          0,
          || b)?;

        let cell_c = region.assign_advice(
          || "c",
          self.config.c,
          0,
          || a+b)?;
          
        Ok((cell_b, cell_c))
      })
    }

    // Create a new row
  fn load_row(
    &self,
    mut layouter: impl Layouter<F>,
    a: &AssignedCell<F, F>,
    b: &AssignedCell<F, F>
  ) -> Result<AssignedCell<F, F>, Error> { 

    layouter.assign_region(|| "a row", | mut region | {
      self.config.s.enable(&mut region, 0)?;
      let prev_a = a.copy_advice(|| "copy a", &mut region, self.config.a, 0)?;
      let prev_b = b.copy_advice(|| "copy b", &mut region, self.config.b, 0)?;
      let c = prev_a.value_field().evaluate() + prev_b.value_field().evaluate();

      let cell_c = region.assign_advice(
        || "c",
        self.config.c,
        0,
        || c)?;
      Ok(cell_c)
    })
  }

  fn expose_public(
    &self,
    mut layouter: impl Layouter<F>,
    num: AssignedCell<F, F>,
    row: usize,
  ) -> Result<(), Error> {
      layouter.constrain_instance(num.cell(), self.config.i, row)
  }
}

// The complete circuit
#[derive(Default)]
struct FibonacciCircuit<F: Field> {
  a: Value<F>, // private
  b: Value<F>, // private
  sequence_length: usize // public
}

// The Circuit trait provides implementations so the backend prover can ask the circuit to 
//   synthesize using some given constraintsystem
impl<F:  Field> Circuit<F> for FibonacciCircuit<F> {
  // This circuit consists of 1 chip, so it's equal to the chip config
    type Config = FibonacciConfig;

    // "Floor planning strategy"
    type FloorPlanner = SimpleFloorPlanner;

    // Returns a copy of the circuit with all witnesses set to None
    fn without_witnesses(&self) -> Self {
      Self::default()
    }

    // Describe gate & column arrangements, etc
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FibonacciChip::configure(meta)
    }

    // Given the constraintsystem, synthesize the circuit
    fn synthesize(&self, config: Self::Config, mut layouter: impl halo2_proofs::circuit::Layouter<F>) -> Result<(), Error> {
        let chip = FibonacciChip::construct(config);
        // The first row initializes the chip
        let (mut b, mut c) = chip.set_initial_values(layouter.namespace(|| "first row"), self.a, self.b)?;
        // All subsequent rows work with previous values
        for _ in 3..self.sequence_length {
          let next_c = chip.load_row(
            layouter.namespace(|| "a row"),
            &b,
            &c)?;
          b = c;
          c = next_c;
        }
        chip.expose_public(layouter.namespace(|| "expose last c"), c, 0)?;
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use halo2_proofs::{pasta::Fp, circuit::Value, dev::MockProver};

    use super::{get_fibonacci_seq, FibonacciCircuit};


  #[test]
  fn test_fib_sequence() {
    let s = get_fibonacci_seq(10);
    println!("{:?}", s);
  }

  #[test]
  fn test_fibonacci_circuit1() {
    let sequence_length = 5;
    let s = get_fibonacci_seq(sequence_length);

    let circuit = FibonacciCircuit {
      a: Value::known(Fp::from(s[0])),
      b: Value::known(Fp::from(s[1])),
      sequence_length
    };


    let pub_input = vec![Fp::from(s[sequence_length-1])];
    let prover_correct = MockProver::run(4, &circuit, vec![pub_input]).unwrap();
    assert_eq!(prover_correct.verify(), Ok(()));

    let prover_wrong = MockProver::run(4, &circuit, vec![vec![Fp::from(12)]]).unwrap();
    assert!(prover_wrong.verify().is_err());
  }
}