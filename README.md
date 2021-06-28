[![Build status](https://github.com/Dophin2009/lobby-queue/workflows/ci/badge.svg)](https://github.com/Dophin2009/lobby/actions)
[![Crates.io](https://img.shields.io/crates/v/lobby-queue.svg)](https://crates.io/crates/lobby)
[![Docs.rs](https://docs.rs/lobby-queue/badge.svg)](https://docs.rs/lobby)

# lobby-queue

A const-size queue-like data structure.

## Usage

Add lobby-queue to your `Cargo.toml`:

```toml
[dependencies]
lobby-queue = "0.1"
```

And use it:

```rust
use lobby_queue::Lobby;

fn main() {
    let mut m = lobby_queue::new([None, None, None]);

    m.push(0);
    m.push(1);
    m.push(2);
    assert_eq!(Some(&0), m.first());

    m.push(3);
    assert_eq!(Some(&1), m.first());
}
```
