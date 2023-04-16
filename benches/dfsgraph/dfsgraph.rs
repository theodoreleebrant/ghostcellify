
// source: https://users.rust-lang.org/t/graph-structure-with-rc-and-refcell/54663/3

use std::cell::RefCell;
use std::fmt::Display;
use std::rc::Rc;
use std::vec::Vec;

type Wrapper<T> = Rc<RefCell<T>>;

fn wrap<T>(data: T) -> Wrapper<T> {
    Rc::new(RefCell::new(data))
}

#[derive(Debug)]
struct Node<T> {
    data: T,
    children: Vec<Wrapper<Node<T>>>
}

impl<T: Display> Node<T> {
    fn add_child(&mut self, child: Wrapper<Node<T>>) {
        self.children.push(child);
    }

    fn new(data: T) -> Node<T> {
        Node { data, children: Vec::new() }
    }

    fn depth_first(&self) {
        println!("node {}", self.data);
        for child in self.children.iter() {
            child.borrow().depth_first();
        }
    }
}

fn main() {
    let a = wrap(Node::new('A'));
    let b = wrap(Node::new('B'));
    let c = wrap(Node::new('C'));
    let d = wrap(Node::new('D'));

    a.borrow_mut().add_child(Rc::clone(&b));
    a.borrow_mut().add_child(Rc::clone(&c));
    b.borrow_mut().add_child(Rc::clone(&d));
    a.borrow_mut().depth_first();
}