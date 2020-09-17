use crate::std::string::String;

/// The basic error of the `AccumulationScheme` trait.
#[derive(Debug)]
pub enum Error {
    /// The accumulator was corrupted or malformed.
    MalformedAccumulator(String),

    /// The input was corrupted or malformed.
    MalformedInput(String),

    /// There are no inputs nor accumulators and nothing else can be done.
    MissingAccumulatorsAndInputs(String),

    /// An RngCore was expected, but was not passed in.
    MissingRng(String),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let error_text = match self {
            Error::MalformedAccumulator(err) => format!("MalformedAccumulator: {}", err),
            Error::MalformedInput(err) => format!("MalformedInput: {}", err),
            Error::MissingAccumulatorsAndInputs(err) => format!("NothingToAccumulate: {}", err),
            Error::MissingRng(err) => format!("MissingRng: {}", err),
        };

        write!(f, "{}", error_text)
    }
}

impl algebra_core::Error for Error {}
