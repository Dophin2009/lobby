[![Build status](https://github.com/Dophin2009/lobby/workflows/ci/badge.svg)](https://github.com/Dophin2009/lobby/actions)
[![Crates.io](https://img.shields.io/crates/v/lobby.svg)](https://crates.io/crates/lobby)
[![Docs.rs](https://docs.rs/lobby/badge.svg)](https://docs.rs/lobby)

# Lobby

A const-size queue-like data structure.

## Usage

Add Lobby to your `Cargo.toml`:

```toml
[dependencies]
lobby = "0.1"
```

And use it:

```rust
use lobby::Lobby;

fn main() {
    let mut m = Lobby::new();

    m.push(0);
    m.push(1);
    m.push(2);
    assert_eq!(Some(&0), m.first());

    m.push(3);
    assert_eq!(Some(&1), m.first());
}
```
