use crate::std::boxed::Box;
use crate::std::string::String;
use ark_std::error::Error;

/// Common errors for the `AccumulationScheme` trait.
#[derive(Debug)]
pub enum ASError {
    /// The accumulator was corrupted or malformed.
    MalformedAccumulator(String),

    /// The input was corrupted or malformed.
    MalformedInput(String),

    /// There are no inputs nor accumulators and nothing else can be done.
    MissingAccumulatorsAndInputs(String),

    /// An RngCore was expected, but was not passed in.
    MissingRng(String),
}

impl core::fmt::Display for ASError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let error_text = match self {
            ASError::MalformedAccumulator(err) => format!("MalformedAccumulator: {}", err),
            ASError::MalformedInput(err) => format!("MalformedInput: {}", err),
            ASError::MissingAccumulatorsAndInputs(err) => format!("NothingToAccumulate: {}", err),
            ASError::MissingRng(err) => format!("MissingRng: {}", err),
        };

        write!(f, "{}", error_text)
    }
}
impl Error for ASError {}

/// Wrapper struct holding any ark_std error
#[derive(Debug)]
pub struct BoxedError(pub Box<dyn Error>);

impl BoxedError {
    /// Converts from a static error into the boxed form
    pub fn new(err: impl Error + 'static) -> Self {
        Self(Box::new(err))
    }
}

impl core::fmt::Display for BoxedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(self.0.as_ref(), f)
    }
}

impl Error for BoxedError {}
