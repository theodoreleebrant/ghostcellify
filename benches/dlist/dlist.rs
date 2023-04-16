// Code adapted from ghost-cell repository

use std::cell::RefCell;
use std::rc::{Rc, Weak};

/// A doubly-linked list node.
#[rustfmt::ghostcellify]
pub struct Node<T> {
    data: T,
    prev: Option<WeakNodePtr<T>>,
    next: Option<NodePtr<T>>,
}

/// A `Weak` pointer to a node.
pub type WeakNodePtr<T> = Weak<RefCell<Node<T>>>;
/// A strong `Arc` pointer to a node.
pub type NodePtr<T> = Rc<RefCell<Node<T>>>;

impl<T> Node<T> {
    pub fn new(value: T) -> NodePtr<T> {
        Rc::new(RefCell::new(
            Self {
                data: value,
                prev: None,
                next: None,
            }
        ))
    }

    pub fn prev_weak(&self) -> Option<&WeakNodePtr<T>> {
        self.prev.as_ref()
    }

    pub fn prev(&self) -> Option<NodePtr<T>> {
        self.prev_weak().and_then(|p| p.upgrade())
    }

    pub fn next(&self) -> Option<&NodePtr<T>> {
        self.next.as_ref()
    }

    /// Unlink the nodes adjacent to `node`. The node will have `next` and `prev` be `None` after this.
    
    pub fn remove<'a>(node: &NodePtr<T>) {
        // `take` both pointers from `node`, setting its fields to `None`.
        let mut node = node.borrow_mut();
        let old_prev: Option<NodePtr<T>> = node.prev.as_ref().and_then(|p| p.upgrade());
        let old_next: Option<NodePtr<T>> = node.next.take();
        // link `old_prev` and `old_next together
        if let Some(old_next) = &old_next {
            old_next.borrow_mut().prev = old_prev.as_ref().map(|p| Rc::downgrade(&p));
        }
        if let Some(old_prev) = &old_prev {
            old_prev.borrow_mut().next = old_next;
        }
    }

    /// Insert `node2` right after `node1` in the list.
    pub fn insert_next<'a>(
        node1: &NodePtr<T>,
        node2: NodePtr<T>
    ) {
        // Step 1: unlink the prev and next pointers of nodes that are
        // adjacent to node2.
        Self::remove(&node2);

        // Step 2: get out the old next pointer as node1_old_next.
        let node1_old_next: Option<NodePtr<T>> = node1.borrow_mut().next.take();
        if let Some(node1_old_next) = &node1_old_next {
            node1_old_next.borrow_mut().prev = Some(Rc::downgrade(&node2));
        }

        // Step 3: link node2 to node1 and node1_old_next.
        let mut node2_inner = node2.borrow_mut();
        node2_inner.prev = Some(Rc::downgrade(node1));
        node2_inner.next = node1_old_next;

        // Step 4: Link node1.next to node2.
        node1.borrow_mut().next = Some(node2.clone());
    }

    /// Mutable iteration only works as "interior iteration", since we cannot hand out mutable references
    /// to multiple nodes at the same time.
    pub fn iter_mut(
        node: &NodePtr<T>,
        mut f: impl FnMut(&mut T),
    ) {
        let mut cur = Some(node.clone());
        while let Some(node) = cur {
            let mut node = node.borrow_mut(); // mutably borrow `node` with `token`
            f(&mut node.data);
            cur = node.next.clone();
        }
    }

    /// Immutable interior traversal.
    pub fn iterate(
        node: &NodePtr<T>,
        f: impl Fn(&T),
    ) {
        let mut cur = Some(node.clone());
        while let Some(node) = cur {
            let node= node.borrow(); // immutably borrow `node` with `token`
            f(&node.data);
            cur = node.next.clone();
        }
    }
}

fn main() { 
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

    Node::insert_next(&node1, node2.clone());
    Node::insert_next(&node2, node3.clone());
    Node::insert_next(&node3, node4.clone());
    Node::insert_next(&node4, node5.clone());
    Node::insert_next(&node5, node6.clone());
    Node::insert_next(&node6, node7.clone());
    Node::insert_next(&node7, node8.clone());
    Node::insert_next(&node8, node9.clone());
    Node::insert_next(&node9, node10.clone());

    Node::iterate(&node1, |x| println!("{}", x));
    println!("-------------------");
    Node::iter_mut(&node1, |x| *x += 1);
    Node::iterate(&node1, |x| println!("{}", x));
}

#[test]
#[should_panic]
fn test_multi_mut_borrow() {
    let node1 : Rc<RefCell<Node<T>>> = Node::new(1);
    let cell : RefCell<Node<T>> = *node1; // typically, this is performed implicitly via the `Deref` trait
    let r1 = node1.borrow_mut();
    let r2 = node1.borrow_mut();
}

