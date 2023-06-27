
use ghost_cell::{GhostCell, GhostToken};
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashSet, VecDeque};
use std::rc::Rc;

pub const NUM_TRIALS: usize = 1;
pub const SYMMETRIZE: bool = true; // false = undirected
pub const UNIFORM: bool = true;
pub const NEEDS_WEIGHTS: bool = true;
pub const FILE_NAME: &'static str = ""; // ""
pub const INVERT: bool = false;
pub const SCALE: usize = 8;
pub const DEGREE: usize = 10;

pub type NodeId<> = usize;
pub type Weight<> = usize;
pub type Edge<> = (NodeId, NodeId, Option<Weight>); // (from, to, weight)
pub type WEdge<> = (NodeId, NodeId, Weight);
pub type EdgeList<> = Vec<Edge>;
pub type WEdgeList<> = Vec<WEdge>;
type WrappedNode<T> = Rc<RefCell<Node<T>>>;


pub struct Node<T> {
    node_id: NodeId,
    value: Option<T>,
    in_edges: BTreeMap<NodeId, HalfEdge<T>>, // (other_id, {other_node, weight})
    out_edges: BTreeMap<NodeId, HalfEdge<T>>,
}

pub struct HalfEdge<T> {
    inner: WrappedNode<T>,
    weight: Option<usize>,
}

#[rustfmt::ghostcellify]
pub struct Graph<'id0, T> {
    vertices: RefCell<BTreeMap<usize, WrappedNode<T>>>,
    num_edges: Cell<usize>,
    directed: bool,
}

impl<'id0, T> Graph<'id0, T> {
    pub fn new(directed: bool) -> Self {
        Graph {
            vertices: RefCell::new(BTreeMap::new()),
            num_edges: Cell::new(0),
            directed,
        }
    }
}

