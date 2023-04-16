// Code adapted from ghost-cell repository

use ghost_cell::{GhostCell, GhostToken};
use std::cell::RefCell;
use std::rc::{Rc, Weak};

/// A doubly-linked list node.
#[rustfmt::ghostcellify]
pub struct Node<'id0, T> {
    data: T,
    prev: Option<WeakNodePtr<'id0, T>>,
    next: Option<NodePtr<'id0, T>>,
}

/// A `Weak` pointer to a node.
pub type WeakNodePtr<'id0, T> = Weak<GhostCell<'id0, Node<'id0, T>>>;
/// A strong `Arc` pointer to a node.
pub type NodePtr<'id0, T> = Rc<GhostCell<'id0, Node<'id0, T>>>;

impl<'id0, T> Node<'id0, T> {
    pub fn new(value: T) -> NodePtr<'id0, T> {
        Rc::new(GhostCell::new(
            Self {
                data: value,
                prev: None,
                next: None,
            }
        ))
    }

    pub fn prev_weak(&self) -> Option<&WeakNodePtr<'id0, T>> {
        self.prev.as_ref()
    }

    pub fn prev(&self) -> Option<NodePtr<'id0, T>> {
        self.prev_weak().and_then(|p| p.upgrade())
    }

    pub fn next(&self) -> Option<&NodePtr<'id0, T>> {
        self.next.as_ref()
    }

    /// Unlink the nodes adjacent to `node`. The node will have `next` and `prev` be `None` after this.
    
    pub fn remove<'a>(node: &NodePtr<'id0, T>, token: &mut GhostToken<'id0>) {
        // `take` both pointers from `node`, setting its fields to `None`.
        let mut node = node.borrow_mut(token);
        let old_prev: Option<NodePtr<'id0, T>> = node.prev.as_ref().and_then(|p| p.upgrade());
        let old_next: Option<NodePtr<'id0, T>> = node.next.take();
        // link `old_prev` and `old_next together
        if let Some(old_next) = &old_next {
            old_next.borrow_mut(token).prev = old_prev.as_ref().map(|p| Rc::downgrade(&p));
        }
        if let Some(old_prev) = &old_prev {
            old_prev.borrow_mut(token).next = old_next;
        }
    }

    /// Insert `node2` right after `node1` in the list.
    pub fn insert_next<'a>(
        node1: &NodePtr<'id0, T>,
        node2: NodePtr<'id0, T>, token: &mut GhostToken<'id0>
    ) {
        // Step 1: unlink the prev and next pointers of nodes that are
        // adjacent to node2.
        Self::remove(&node2, token);

        // Step 2: get out the old next pointer as node1_old_next.
        let node1_old_next: Option<NodePtr<'id0, T>> = node1.borrow_mut(token).next.take();
        if let Some(node1_old_next) = &node1_old_next {
            node1_old_next.borrow_mut(token).prev = Some(Rc::downgrade(&node2));
        }

        // Step 3: link node2 to node1 and node1_old_next.
        let mut node2_inner = node2.borrow_mut(token);
        node2_inner.prev = Some(Rc::downgrade(node1));
        node2_inner.next = node1_old_next;

        // Step 4: Link node1.next to node2.
        node1.borrow_mut(token).next = Some(node2.clone());
    }

    /// Mutable iteration only works as "interior iteration", since we cannot hand out mutable references
    /// to multiple nodes at the same time.
    pub fn iter_mut(
        node: &NodePtr<'id0, T>,
        mut f: impl FnMut(&mut T), token: &mut GhostToken<'id0>,
    ) {
        let mut cur = Some(node.clone());
        while let Some(node) = cur {
            let mut node = node.borrow_mut(token); // mutably borrow `node` with `token`
            f(&mut node.data);
            cur = node.next.clone();
        }
    }

    /// Immutable interior traversal.
    pub fn iterate(
        node: &NodePtr<'id0, T>,
        f: impl Fn(&T), token: &GhostToken<'id0>,
    ) {
        let mut cur = Some(node.clone());
        while let Some(node) = cur {
            let node= node.borrow(token); // immutably borrow `node` with `token`
            f(&node.data);
            cur = node.next.clone();
        }
    }
}

fn main() {
GhostToken::new(|mut token| {
let token = &mut token; 
    let node1 = Node::new(1);
    let node2 = Node::new(2);
    let node3 = Node::new(3);
    let node4 = Node::new(4);
    let node5 = Node::new(5);
    let node6 = Node::new(6);
    let node7 = Node::new(7);
    let node8 = Node::new(8);
    let node9 = Node::new(9);
    let node10 = Node::new(10);

    Node::insert_next(&node1, node2.clone(), token);
    Node::insert_next(&node2, node3.clone(), token);
    Node::insert_next(&node3, node4.clone(), token);
    Node::insert_next(&node4, node5.clone(), token);
    Node::insert_next(&node5, node6.clone(), token);
    Node::insert_next(&node6, node7.clone(), token);
    Node::insert_next(&node7, node8.clone(), token);
    Node::insert_next(&node8, node9.clone(), token);
    Node::insert_next(&node9, node10.clone(), token);

    Node::iterate(&node1, |x| println!("{}", x), token);
    println!("-------------------");
    Node::iter_mut(&node1, |x| *x += 1, token);
    Node::iterate(&node1, |x| println!("{}", x), token);
});
}

#[test]
#[should_panic]
fn test_multi_mut_borrow() {
    let node1 : Rc<RefCell<Node<T>>> = Node::new(1);
    let cell : RefCell<Node<T>> = *node1; // typically, this is performed implicitly via the `Deref` trait
    let r1 = node1.borrow_mut();
    let r2 = node1.borrow_mut();
}

