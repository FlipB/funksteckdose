#![cfg_attr(not(feature = "std"), no_std)]
/// Copyright © 2019 Felix Obenhuber
///
/// Permission is hereby granted, free of charge, to any person obtaining a copy
/// of this software and associated documentation files (the "Software"), to deal
/// in the Software without restriction, including without limitation the rights
/// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
/// copies of the Software, and to permit persons to whom the Software is
/// furnished to do so, subject to the following conditions:
///
/// The above copyright notice and this permission notice shall be included in all
/// copies or substantial portions of the Software.
//
/// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
/// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
/// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
/// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
/// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
/// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
/// SOFTWARE.
use core::marker::PhantomData;
use core::str;
use error::Error;

#[cfg(all(not(feature = "std"), feature = "wiringpi"))]
compile_error!("feature \"wiringpi\" requires feature \"std\"");

/// Error
pub mod error {
    use core::fmt::Debug;

    #[cfg(feature = "error-context")]
    use failure::Fail;

    #[derive(Debug)]
    #[cfg_attr(feature = "error-context", derive(Fail))]
    pub enum Error {
        #[cfg_attr(
            feature = "error-context",
            fail(display = "invalid group identifier: {}", _0)
        )]
        InvalidGroup(ErrorData),
        #[cfg_attr(
            feature = "error-context",
            fail(display = "invalid device identifier: {}", _0)
        )]
        InvalidDevice(ErrorData),
        #[cfg_attr(
            feature = "error-context",
            fail(display = "invalid state: {}. Try on, off, 1, 0, true, false", _0)
        )]
        InvalidState(ErrorData),
        /// GpioError indicates failure setting gpio state during signal output
        #[cfg_attr(feature = "error-context", fail(display = "gpio error"))]
        GpioError,
    }

    /// ErrorData newtype wraps the error context.
    /// ErrorData contains only empty unit type unless feature "error-context" is enabled.
    #[cfg(feature = "error-context")]
    pub struct ErrorData(String);

    /// ErrorData newtype wraps the error context.
    /// ErrorData contains only empty unit type unless feature "error-context" is enabled.
    #[cfg(not(feature = "error-context"))]
    pub struct ErrorData(());

    impl From<&str> for ErrorData {
        #[cfg(not(feature = "error-context"))]
        fn from(_input: &str) -> Self {
            ErrorData(()) // Discard the error context message
        }

        #[cfg(feature = "error-context")]
        fn from(input: &str) -> Self {
            ErrorData(input.to_owned()) // Allocate a string for the error context message
        }
    }

    impl Debug for ErrorData {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            self.0.fmt(f)
        }
    }

    #[cfg(feature = "error-context")]
    impl core::fmt::Display for ErrorData {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            core::fmt::Display::fmt(&self.0, f)
        }
    }
}

/// A Device
#[derive(Clone, Debug, PartialEq)]
pub enum Device {
    A,
    B,
    C,
    D,
    E,
}

impl From<Device> for u8 {
    fn from(d: Device) -> u8 {
        match d {
            Device::A => 1,
            Device::B => 2,
            Device::C => 3,
            Device::D => 4,
            Device::E => 5,
        }
    }
}

impl str::FromStr for Device {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "0" | "a" | "A" | "10000" => Ok(Device::A),
            "1" | "b" | "B" | "01000" => Ok(Device::B),
            "2" | "c" | "C" | "00100" => Ok(Device::C),
            "3" | "d" | "D" | "00010" => Ok(Device::D),
            "4" | "e" | "E" | "00001" => Ok(Device::E),
            _ => Err(Error::InvalidDevice(s.into())),
        }
    }
}

/// State to switch a socket to
#[derive(Clone, Debug, PartialEq)]
pub enum State {
    On,
    Off,
}

impl str::FromStr for State {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "On" | "on" | "1" | "true" => Ok(State::On),
            "Off" | "off" | "0" | "false" => Ok(State::Off),
            _ => Err(Error::InvalidState(s.into())),
        }
    }
}

/// Value to set a GPIO to
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Low,
    High,
}

// Converts a bit string (eg. "1000") into the tri-state binary representation.
fn binary_string_to_tri_state<'a>(buf: &'a mut [u8], bits: impl Iterator<Item = char>) -> &'a [u8] {
    let mut n = 0;
    // write to buffer
    bits.enumerate().for_each(|(i, c)| {
        match c {
            '0' => buf[i] = b'F',
            '1' => buf[i] = b'0',
            _ => unreachable!(),
        }
        n = i + 1;
    });

    // take subslice of only the written bytes
    &buf[..n]
}

/// Converts the tri-state binary representation into bit string representation.
fn tri_state_to_binary_string<'a>(buf: &'a [u8]) -> impl Iterator<Item = char> + 'a {
    buf.iter().map(|b| match b {
        b'F' => '0',
        b'0' => '1',
        _ => unreachable!(),
    })
}

/// Converts the tri-state binary representation into a 64bit decimal code word.
pub fn tri_state_to_decimal_code(code_word: &[u8]) -> u64 {
    // Byte slice starts with MSB
    code_word.iter().fold(0u64, |mut code, c| {
        code <<= 2u64;
        match c {
            b'0' => code |= 0b00,
            b'F' => code |= 0b01,
            b'1' => code |= 0b11,
            _ => unreachable!(),
        }
        code
    })
}

fn decimal_code_to_tri_state<'a>(buf: &'a mut [u8], decimal_code: u64, length: usize) -> &'a [u8] {
    let length = if length % 2 != 0 { length + 1 } else { length };
    // Byte slice should start with MSB
    buf.iter_mut()
        .take(length / 2)
        .rfold(decimal_code, |mut code, b| {
            // LSB to MSB
            let twobits: u8 = (code & 0b11) as u8;
            *b = match twobits {
                0b00 => b'0',
                0b01 => b'F',
                0b11 => b'1',
                _ => unreachable!(),
            };
            code >>= 2u64;
            code
        });

    &buf[0..length / 2]
}

/// Encoding
pub trait Encoding {
    /// encode the group/device/state command to a tristate byte slice
    fn encode<'a>(
        buf: &'a mut [u8],
        group: &str,
        device: &Device,
        state: &State,
    ) -> Result<&'a [u8], Error>;
}

/// Encoding A - check [rc-switch](https://github.com/sui77/rc-switch/) for details
pub struct EncodingA;

impl Encoding for EncodingA {
    fn encode<'a>(
        buf: &'a mut [u8],
        group: &str,
        device: &Device,
        state: &State,
    ) -> Result<&'a [u8], Error> {
        if group.len() != 5 || group.chars().any(|c| c != '0' && c != '1') {
            return Err(Error::InvalidGroup(group.into()));
        }
        let chars = group.chars();

        let device = match device {
            Device::A => "10000",
            Device::B => "01000",
            Device::C => "00100",
            Device::D => "00010",
            Device::E => "00001",
        };

        let chars = chars.chain(device.chars());

        let chars = match *state {
            State::On => chars.chain("10".chars()),
            State::Off => chars.chain("01".chars()),
        };

        Ok(binary_string_to_tri_state(buf, chars))
    }
}

/// Encoding B - check [rc-switch](https://github.com/sui77/rc-switch/) for details
pub struct EncodingB;

impl Encoding for EncodingB {
    fn encode<'a>(
        buf: &'a mut [u8],
        group: &str,
        device: &Device,
        state: &State,
    ) -> Result<&'a [u8], Error> {
        // group, aka. addressCode int in rc-switch.
        // addressCode 1 == group "0" == binary string "1000" == tri-state string "0FFF"
        let group = match group {
            "A" | "a" | "0" => "1000",
            "B" | "b" | "1" => "0100",
            "C" | "c" | "2" => "0010",
            "D" | "d" | "3" => "0001",
            "1000" | "0100" | "0010" | "0001" => group,
            _ => return Err(Error::InvalidGroup(group.into())),
        };

        let chars = group.chars();

        let device = match device {
            Device::A => "1000",
            Device::B => "0100",
            Device::C => "0010",
            Device::D => "0001",
            Device::E => return Err(Error::InvalidDevice("E".into())),
        };

        let chars = chars.chain(device.chars());

        let chars = match *state {
            State::On => chars.chain("0000".chars()),
            State::Off => chars.chain("0001".chars()),
        };

        Ok(binary_string_to_tri_state(buf, chars))
    }
}

/// Encoding C - check [rc-switch](https://github.com/sui77/rc-switch/) for details
pub struct EncodingC;

impl Encoding for EncodingC {
    fn encode<'a>(
        _buf: &'a mut [u8],
        _group: &str,
        _device: &Device,
        _state: &State,
    ) -> Result<&'a [u8], Error> {
        unimplemented!()
    }
}

/// Interface for GPIO control
pub trait Pin {
    fn set(&mut self, value: &Value) -> Result<(), Error>;
}

/// Interface for delay to enable no_std
pub trait Delay {
    /// blocks the caller for `micros` microseconds
    fn delay_microseconds(&mut self, us: u32) -> ();
}

/// Handle to a Funksteckdose system
#[derive(Debug)]
pub struct Funksteckdose<T: Pin, D: Delay, E: Encoding, P: Protocol> {
    pin: T,
    delay: D,
    repeat_transmit: usize,
    protocol: PhantomData<P>,
    encoding: PhantomData<E>,
}

impl<T: Pin, D: Delay, E: Encoding, P: Protocol> Funksteckdose<T, D, E, P> {
    /// Create a new instance with a given pin and default protocol
    /// ```
    /// type Funksteckdose = funksteckdose::Funksteckdose<WiringPiPin, EncodingA, Protocol1>;
    /// let pin = WiringPiPin::new(0);
    /// let d: Funksteckdose = Funksteckdose::new(pin);
    /// ```
    #[cfg(feature = "std")]
    pub fn new(pin: T) -> Funksteckdose<T, impl Delay, E, P> {
        Funksteckdose {
            pin,
            delay: StdDelay {},
            repeat_transmit: 10,
            protocol: PhantomData,
            encoding: PhantomData,
        }
    }

    /// Create a new instance with a given pin and transmit count
    /// ```
    /// type Funksteckdose = funksteckdose::Funksteckdose<WiringPiPin, EncodingA, Protocol1>;
    /// let pin = WiringPiPin::new(0);
    /// let d: Funksteckdose = Funksteckdose::with_repeat_transmit(pin, 5);
    /// ```
    #[cfg(feature = "std")]
    pub fn with_repeat_transmit(
        pin: T,
        repeat_transmit: usize,
    ) -> Funksteckdose<T, impl Delay, E, P> {
        Funksteckdose {
            pin,
            delay: StdDelay {},
            repeat_transmit: repeat_transmit,
            protocol: PhantomData,
            encoding: PhantomData,
        }
    }

    /// Create a new instance with given pin, delay implementation and transmit count.
    /// Delay is implemented for [`embedded_hal::blocking::delay::DelayUs`]
    pub fn new_with_delay(pin: T, delay: D, repeat_transmit: usize) -> Funksteckdose<T, D, E, P> {
        Funksteckdose {
            pin,
            delay,
            repeat_transmit,
            protocol: PhantomData,
            encoding: PhantomData,
        }
    }

    /// Send a control sequence to give group and device.
    /// The group is coded like the dip switches in the devices e.g "10010"
    /// ```
    /// type Funksteckdose = funksteckdose::Funksteckdose<WiringPiPin, EncodingA, Protocol1>;
    /// let pin = WiringPiPin::new(0);
    /// let d: Funksteckdose = Funksteckdose::with_repeat_transmit(pin, 5);
    /// d.send("10001", &Device::A, &State::On).expect("Failed to send");
    /// ```
    pub fn send(&mut self, group: &str, device: &Device, state: &State) -> Result<(), Error> {
        // Get the code word for this group/device/state.
        // This is equivalent of getCodeWordA/B/C/D in rc-switch for implemented devices.
        let mut buf = [0; 64];
        let code_word = { E::encode(&mut buf, group, device, state)? };

        let code = tri_state_to_decimal_code(code_word);
        self.send_decimal(code, code_word.len() * 2)?;
        Ok(())
    }

    /// send_decimal  is equivalent to one of the rc-switch send() implementations.
    /// send_decimal sends rc-switch decimal code.
    /// ```
    /// type Funksteckdose = funksteckdose::Funksteckdose<WiringPiPin, EncodingA, Protocol1>;
    /// let pin = WiringPiPin::new(0);
    /// let d: Funksteckdose = Funksteckdose::with_repeat_transmit(pin, 5);
    /// d.send_decimal(5526612, 24).expect("Failed to send");
    /// ```
    pub fn send_decimal(&mut self, decimal_code: u64, length: usize) -> Result<(), Error> {
        // Transmit the first `length` bits of the `decimal_code`. The
        // bits are sent from MSB to LSB, i.e., first the bit at position length-1,
        // then the bit at position length-2, and so on, till finally the bit at position 0.
        let (first, second) = if P::values().inverted_signal {
            (Value::Low, Value::High)
        } else {
            (Value::High, Value::Low)
        };
        for _ in 0..self.repeat_transmit {
            let one = P::values().one;
            let zero = P::values().zero;
            for i in (0..length).rev() {
                let s = if decimal_code & (1 << i) != 0 {
                    &one
                } else {
                    &zero
                };
                self.transmit(s, &first, &second)?;
            }
            self.transmit(&P::values().sync_factor, &first, &second)?;
        }

        // Disable transmit after sending (i.e., for inverted protocols)
        self.pin.set(&Value::Low)?;
        Ok(())
    }

    fn transmit(&mut self, pulses: &HighLow, first: &Value, second: &Value) -> Result<(), Error> {
        self.pin.set(first)?;
        self.delay((P::values().pulse_length * pulses.high) as u32);
        self.pin.set(second)?;
        self.delay((P::values().pulse_length * pulses.low) as u32);
        Ok(())
    }

    fn delay(&mut self, micros: u32) {
        if micros > 0 {
            self.delay.delay_microseconds(micros);
        }
    }
}

#[cfg(feature = "std")]
struct StdDelay {}

#[cfg(feature = "std")]
impl Delay for StdDelay {
    fn delay_microseconds(&mut self, micros: u32) -> () {
        if micros > 0 {
            let now = std::time::Instant::now();
            let micros = u128::from(micros);
            while now.elapsed().as_micros() < micros {}
        }
    }
}

/// Number of pulses
#[derive(Clone, Debug)]
pub struct HighLow {
    pub high: u64,
    pub low: u64,
}

impl HighLow {
    fn new(high: u64, low: u64) -> HighLow {
        HighLow { high, low }
    }
}

/// Format for protocol definitions
#[derive(Clone, Debug)]
pub struct ProtocolValues {
    pulse_length: u64,
    sync_factor: HighLow,
    zero: HighLow,
    one: HighLow,
    inverted_signal: bool,
}

/// A protocol definition
pub trait Protocol {
    fn values() -> ProtocolValues;
}

/// Protocol 1
pub struct Protocol1;

impl Protocol for Protocol1 {
    fn values() -> ProtocolValues {
        ProtocolValues {
            pulse_length: 350,
            sync_factor: HighLow::new(1, 31),
            zero: HighLow::new(1, 3),
            one: HighLow::new(3, 1),
            inverted_signal: false,
        }
    }
}

/// Protocol 2
pub struct Protocol2;

impl Protocol for Protocol2 {
    fn values() -> ProtocolValues {
        ProtocolValues {
            pulse_length: 650,
            sync_factor: HighLow::new(1, 10),
            zero: HighLow::new(1, 2),
            one: HighLow::new(2, 1),
            inverted_signal: false,
        }
    }
}

/// Protocol 3
pub struct Protocol3;

impl Protocol for Protocol3 {
    fn values() -> ProtocolValues {
        ProtocolValues {
            pulse_length: 100,
            sync_factor: HighLow::new(30, 71),
            zero: HighLow::new(4, 11),
            one: HighLow::new(9, 6),
            inverted_signal: false,
        }
    }
}

/// Protocol 4
pub struct Protocol4;

impl Protocol for Protocol4 {
    fn values() -> ProtocolValues {
        ProtocolValues {
            pulse_length: 380,
            sync_factor: HighLow::new(1, 6),
            zero: HighLow::new(1, 3),
            one: HighLow::new(3, 1),
            inverted_signal: false,
        }
    }
}

/// Protocol 4
pub struct Protocol5;

impl Protocol for Protocol5 {
    fn values() -> ProtocolValues {
        ProtocolValues {
            pulse_length: 500,
            sync_factor: HighLow::new(6, 14),
            zero: HighLow::new(1, 2),
            one: HighLow::new(2, 1),
            inverted_signal: false,
        }
    }
}

/// Protocol HT6P20B
pub struct ProtocolHT6P20B;

impl Protocol for ProtocolHT6P20B {
    fn values() -> ProtocolValues {
        ProtocolValues {
            pulse_length: 450,
            sync_factor: HighLow::new(23, 1),
            zero: HighLow::new(1, 2),
            one: HighLow::new(2, 1),
            inverted_signal: true,
        }
    }
}

/// Protocol HS2303-PT, i. e. used in AUKEY Remote
pub struct ProtocolHS2303;

impl Protocol for ProtocolHS2303 {
    fn values() -> ProtocolValues {
        ProtocolValues {
            pulse_length: 150,
            sync_factor: HighLow::new(2, 62),
            zero: HighLow::new(1, 6),
            one: HighLow::new(6, 1),
            inverted_signal: false,
        }
    }
}

/// A implementation of Pin to be used with wiringpi on a Raspberry
///
///```
/// let pin = WiringPiPin::new(0);
/// let funksteckdose = Funksteckdose::new(pin, 1).unwrap();
/// funksteckdose.send("10011", "10000", State::On);
///```
#[cfg(feature = "wiringpi")]
pub mod wiringpi {
    use super::{Error, Pin, Value};

    pub struct WiringPiPin {
        pin: wiringpi::pin::OutputPin<wiringpi::pin::WiringPi>,
    }

    impl WiringPiPin {
        pub fn new(pin: u16) -> WiringPiPin {
            let pi = wiringpi::setup();
            WiringPiPin {
                pin: pi.output_pin(pin),
            }
        }
    }

    impl Pin for WiringPiPin {
        fn set(&mut self, value: &Value) -> Result<(), Error> {
            match value {
                Value::High => self.pin.digital_write(wiringpi::pin::Value::High),
                Value::Low => self.pin.digital_write(wiringpi::pin::Value::Low),
            }
            Ok(())
        }
    }
}

/// Trait implementations for embedded_hal traits.
///
/// This allows &mut [`embedded_hal::digital::v2::OutputPin`] to be used as [`Pin`]
/// and &mut [`embedded_hal::blocking::delay::DelayUs<u32>`] to be used as [`Delay`].
#[cfg(feature = "embedded-hal")]
pub mod embeddedhal {
    use super::{Delay, Error, Pin, Value};

    impl<T, E> Pin for &mut T
    where
        T: embedded_hal::digital::v2::OutputPin<Error = E>,
    {
        fn set(&mut self, value: &Value) -> Result<(), Error> {
            match value {
                Value::High => self.set_high().map_err(|_| Error::GpioError),
                Value::Low => self.set_low().map_err(|_| Error::GpioError),
            }
        }
    }

    impl<T> Delay for &mut T
    where
        T: embedded_hal::blocking::delay::DelayUs<u32>,
    {
        fn delay_microseconds(&mut self, us: u32) -> () {
            self.delay_us(us)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encoding_a() {
        let mut buf = [0u8; 32];

        let group = "10001";
        let device = &Device::D;
        let state = &State::Off;
        let e = EncodingA::encode(&mut buf, group, device, state).unwrap();
        let code_decimal = tri_state_to_decimal_code(e);
        assert_eq!(code_decimal, 1381652);

        let state = &State::On;
        let e = EncodingA::encode(&mut buf, group, device, state).unwrap();
        let code_decimal = tri_state_to_decimal_code(e);
        assert_eq!(code_decimal, 1381649);
    }

    #[test]
    fn test_encoding_b() {
        let mut buf = [0u8; 32];
        // Device string is 0 indexed so lets do the same for group.
        // Device "0" == Device "A" == Device 1u8
        // Group "0" == Group "A" == Group 1u8
        let group = "3"; // group 4
        let device = &Device::D; // device 4
        let state = &State::Off;
        let e = EncodingB::encode(&mut buf, group, device, state).unwrap();
        let code_decimal = tri_state_to_decimal_code(e);
        assert_eq!(code_decimal, 5526612);

        let state = &State::On;
        let e = EncodingB::encode(&mut buf, group, device, state).unwrap();
        let code_decimal = tri_state_to_decimal_code(e);
        assert_eq!(code_decimal, 5526613);
    }

    #[test]
    fn test_binary_string_tofrom_tri_state() {
        let input = "000100010000";
        let mut buf = [0u8; 32];

        let tristate = binary_string_to_tri_state(&mut buf, input.chars());
        assert_eq!(
            &[70u8, 70, 70, 48, 70, 70, 70, 48, 70, 70, 70, 70],
            tristate
        );
        let bits = tri_state_to_binary_string(tristate);

        assert_eq!(input, bits.collect::<String>());
    }

    #[test]
    fn test_tri_state_tofrom_decimal_code() {
        // Encoding A
        let input = &[48, 70, 70, 70, 48, 70, 70, 70, 48, 70, 70, 48];
        let decimal_code = tri_state_to_decimal_code(input);
        assert_eq!(1381652, decimal_code);
        let mut buf = [0u8; 32];
        let tristate = decimal_code_to_tri_state(&mut buf, decimal_code, 24);
        assert_eq!(input, tristate);

        let input = &[48u8, 70, 70, 70, 48, 70, 70, 70, 48, 70, 48, 70];
        let decimal_code = tri_state_to_decimal_code(input);
        assert_eq!(1381649, decimal_code);
        let mut buf = [0u8; 32];
        let tristate = decimal_code_to_tri_state(&mut buf, decimal_code, 24);
        assert_eq!(input, tristate);

        // Encoding B
        let input = &[70u8, 70, 70, 48, 70, 70, 70, 48, 70, 70, 70, 70];
        let decimal_code = tri_state_to_decimal_code(input);
        assert_eq!(5526613, decimal_code);
        let mut buf = [0u8; 32];
        let tristate = decimal_code_to_tri_state(&mut buf, decimal_code, 24);
        assert_eq!(input, tristate);

        let input = &[70u8, 70, 70, 48, 70, 70, 70, 48, 70, 70, 70, 48];
        let decimal_code = tri_state_to_decimal_code(input);
        assert_eq!(5526612, decimal_code);
        let mut buf = [0u8; 32];
        let tristate = decimal_code_to_tri_state(&mut buf, decimal_code, 24);
        assert_eq!(input, tristate);
    }
}
