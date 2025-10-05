// A Hash-able wrapper for f64, stored as u64 bits.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Default, PartialOrd, Ord)]
pub struct BoxedF64(u64);

impl BoxedF64 {
    /// Creates a new BoxedF64 from an f64.
    pub fn new(f: f64) -> Self {
        Self(f.to_bits())
    }

    /// Reinterprets the internal bits as f64.
    pub fn float(&self) -> f64 {
        f64::from_bits(self.0)
    }

    /// Saves an f64 by reinterpreting it as bits.
    pub fn save(&mut self, f: f64) {
        self.0 = f.to_bits();
    }

    /// Operations with a closure.
    pub fn op<F>(&mut self, f: F)
    where
        F: FnOnce(f64) -> f64,
    {
        let v = self.float();
        let r = f(v);
        self.save(r);
    }
}

impl From<f64> for BoxedF64 {
    fn from(f: f64) -> Self {
        Self::new(f)
    }
}

impl From<u64> for BoxedF64 {
    fn from(u: u64) -> Self {
        Self(u)
    }
}
