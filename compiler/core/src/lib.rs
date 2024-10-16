//! The core compiler implementation for Jabber.

pub mod span;

mod nodes {
    include!(concat!(env!("OUT_DIR"), "/nodes.rs"));
}
