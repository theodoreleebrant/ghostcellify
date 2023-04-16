# `Ghostcellify` 



Do you have a graph-like data-structure that suffers from `RefCell` hell? Enter: `Ghostcellify`, a tool to automatically rewrite 
your expensive, dynamically-checked `RefCell` data structures to more performant, statically-checked `GhostCell`-based data structures. No manual intervention required!

## Example: A Doubly-Linked List

Consider a doubly-linked list, akin to `benches/dlist/dlist.rs`. 

```rust
pub struct Node<T> {
    data: T,
    prev: Option<WeakNodePtr<T>>,
    next: Option<NodePtr<T>>,
}

impl<T> Node<T> { 
    fn new(value: T) -> Self {
        Rc::new(RefCell:new(Node { 
            data: value,
            prev: None,
            next: None
        }))
    }

    pub fn insert_next<'a>(
        node1: &NodePtr<T>,
        node2: &NodePtr<T>
    ) { ... }
}

fn main() { 
    let node1 = Node::new(1);
    let node2 = Node::new(2);
    Node::insert_next(&node1, node2.clone());
}
```

`RefCell` has two drawbacks: 
1. **Performance:** Runtime checks which lead to less-performant code
2. **Safety**: Can panic if Rust's permission rules (AXM = aliasing XOR mutability) are violated; see the commented test at the end of `dlist.rs` which describes a panic when creating two multiple mutable borrows of a `RefCell`:

```
#[test]
#[should_panic]
fn test_multi_mut_borrow() {
    let node1 : Rc<RefCell<Node<T>>> = Node::new(1);
    let cell : RefCell<Node<T>> = *node1; // typically, this is performed implicitly via the `Deref` trait
    let r1 = node1.borrow_mut();
    let r2 = node1.borrow_mut();
}
```

Note: The Rust AXM rules are typically referred to as "permissions" by the Rust community. 

The solution: `GhostCell` [1], a `Cell`-type that enforces permissions at the data structure level (instead of at each `RefCell`) at *compile-time*, i.e. without the need for runtime checks. A `GhostCell`-based version of `dlist` (see `benches/dlist/dlist.fixed.rs`) runs 3x faster than its `RefCell`-counterpart. 


```diff
pub struct Node<'id0, T> {
    data: T,
-   prev: Option<WeakNodePtr<T>>,
-   next: Option<NodePtr<'id0, T>>,
+   prev: Option<WeakNodePtr<'id0, T>>,
+    next: Option<NodePtr<'id0, T>>,
}

- impl<T> Node<T> { 
+ impl<'id0, T>  Node<'id0, T>
    fn new(value: T) -> Self {
-        Rc::new(RefCell::new(...))    
+        Rc::new(GhostCell:new(...))
    }

    pub fn insert_next<'a>(
        node1: &NodePtr<T>,
        node2: &NodePtr<T>
+       token: &mut GhostToken<'id0>
    ) { ... }
}

fn main() { 
+ GhostToken::new(|token| { 
    let node1 = Node::new(1);
    ...
-    Node::insert_next(&node1, node2.clone());
+    Node::insert_next(&node1, node2.clone(), token);
+});  
}
```

`GhostCellify` performs this rewrite automatically! Setup the repository per the instructions, and run `cargo run --release --bin v2 benches/dlist/dlist.rs` to haunt your `RefCell`s. 


## User Setup
- Clone this repository. 
- Run the following to enable Rust's compiler libraries (last working version: 31 Dec 2022):
    ```
    rustup default nightly-2022-12-31
    rustup component add --toolchain nightly-2022-12-31 rustfmt rust-src rustc-dev llvm-tools-preview rust-analyzer-preview rust-analysis
    rustup component add llvm-tools
    cargo build
    ```
- Run `cargo build`
- Run `cargo run -- release --bin v2 <path-to-file>`. `Ghostcellify` assumes the root folder as your local directory for execution.        
  - Example: `cargo run -- release -- bin v2 benches/dlist/dlist.rs`.  


##  Development Setup
In order to configure the project for development do the following:

```
rustup default nightly-2022-12-31
rustup component add --toolchain nightly-2022-12-31 rustfmt rust-src rustc-dev llvm-tools-preview rust-analyzer-preview rust-analysis
rustup component add llvm-tools
cargo build
```

## Pending Language Features
- Support for multiple generic parameters
- Mutually-recursive structs
- Transforming non-main driver code
- Add VSCode support

## References

[1] [Joshua Yanovski, Hoang-Hai Dang, Ralf Jung, and Derek Dreyer.
GhostCell: Separating Permissions from Data in Rust. Proc. ACM Program. Lang., 5(ICFP), Aug 2021.](https://plv.mpi-sws.org/rustbelt/ghostcell/paper.pdf)

