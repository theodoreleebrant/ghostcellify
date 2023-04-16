use ghost_cell::{GhostCell, GhostToken};
use std::rc::Rc;
use std::cell::RefCell;

pub struct Circle<'id> {
    head: Rc<GhostCell<'id, Node<'id>>>,
}

struct Node<'id> {
    val: i32,
    next: Option<Rc<GhostCell<'id, Node<'id>>>>,
    last: Option<Rc<GhostCell<'id, Node<'id>>>>,
}

impl<'id> Circle<'id> { 

    pub fn remove(&mut self, token: &mut GhostToken<'id>)  {
        let mut next = match &self.head.borrow(token).next{
            Some(x) => x.clone(),
            None => panic!("can't remove last element"),
        };
        let last = self.head.borrow(token).last.as_ref().unwrap();

        // combine 
        last.borrow_mut(token).next = Some(next.clone());

        next.borrow_mut(token).last = Some(last.clone());

        self.head = next;
    }

    // pub fn new(val: i32) -> Circle<'id> {
    //     return Circle{head: Node::new(val)}
    // }

    pub fn value(&self, token: &GhostToken<'id>) -> i32 {
        return self.head.borrow(token).value();
    }

    pub fn next(&mut self, token: &mut GhostToken<'id>) -> i32{
        match &self.head.clone().borrow(token).next{
            Some(x) => self.head = x.clone(),
            None => (),
        }
        self.head.borrow(token).value()
    }

    pub fn last(&mut self, token: &mut GhostToken<'id>) -> i32{
        match &self.head.clone().borrow(token).last{
            Some(x) => self.head = x.clone(),
            None => (),
        }
        self.head.borrow(token).value()
    }

    pub fn insert_after(&mut self, val: i32, token: &mut GhostToken<'id>){
        let mut node = match &self.head.clone().borrow(token).next{
            Some(x) => x.clone(),
            None => self.head.clone(),
        };
        let mut new_node = Node::new(val);
        Node::combine(&mut self.head, &mut new_node, token);
        Node::combine(&mut new_node, &mut node, token);
    }

    // pub fn insert_after_step(&mut self, val: i32){
    //     self.insert_after(val);
    //     self.next();
    // }

    pub fn insert_before(&mut self, val: i32, token: &mut GhostToken<'id>){
        let mut node = match &self.head.clone().borrow(token).last{
            Some(x) => x.clone(),
            None => self.head.clone(),
        };
        let mut new_node = Node::new(val);
        Node::combine(&mut new_node, &mut self.head, token);
        Node::combine(&mut node, &mut new_node, token);
    }

    pub fn insert_before_step(&mut self, val: i32, token: &mut GhostToken<'id>){
        self.insert_before(val, token);
        self.next(token);
    }
}

impl<'id> Node<'id> {
    pub fn new(val: i32) -> Rc<GhostCell<'id, Node<'id>>> {
        return Rc::new(GhostCell::new(Node{val:val, next: None, last: None}));
    }

    pub fn combine<'a>(node1: &'a mut Rc<GhostCell<'id, Node<'id>>>, node2: &'a mut Rc<GhostCell<'id, Node<'id>>>, token: &mut GhostToken<'id>){
        node1.borrow_mut(token).next = Some(node2.clone());
        node2.borrow_mut(token).last = Some(node1.clone());
    }

    pub fn value(&self) -> i32 {
        return self.val;
    }
}