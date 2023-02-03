#![warn(missing_docs)]

//! Multigrid is an open-source grid management library, with a focus on several grid types, ease of use and performance.
//!
//! > Primarily inspired by this [RedBlobGames article](https://www.redblobgames.com/grids/hexagons/).
//!
//! ## Warning
//! Multigrid is still in the _very_ early stages of development.
//! Features are missing and implemented features can and will change.
//! For now it is recommended to use alternatives or be prepared for breaking changes.
//!
//! ## Design Goals
//! - **Complete**: Support several grid types
//! - **Modular**: Disable functionality you don't need
//! - **Extendable**: Allow the addition of custom grid types
//! - **Consistent**: Use consistent interface for all types
//!
//! ## Libraries Used
//! - [glam-rs](https://github.com/bitshifter/glam-rs): a simple and fast math library for games and graphics
//!
//! ## License
//! Multigrid is free, open source and permissively licensed! All code in this repository is dual-licensed under either:
//! - MIT License ([LICENSE-MIT](LICENSE-MIT) or [http://opensource.org/licenses/MIT](http://opensource.org/licenses/MIT))
//! - Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or [http://www.apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0))
//!
//! ## Special thanks
//! - [Hexx](https://github.com/ManevilleF/hexx): For setting a standard
//! - [RedBlobGames](https://www.redblobgames.com/): For the amazing article

#[cfg(feature = "hexagonal")]
pub mod hexagonal;
