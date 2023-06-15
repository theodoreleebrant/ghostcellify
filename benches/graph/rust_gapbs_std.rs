
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

pub type NodeId = usize;
pub type Weight = usize;
pub type Edge = (NodeId, NodeId, Option<Weight>); // (from, to, weight)
pub type WEdge = (NodeId, NodeId, Weight);
pub type EdgeList = Vec<Edge>;
pub type WEdgeList = Vec<WEdge>;
type WrappedNode<T> = Rc<RefCell<Node<T>>>;

#[rustfmt::ghostcellify]
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
pub struct Graph<T> {
    vertices: RefCell<BTreeMap<usize, WrappedNode<T>>>,
    num_edges: Cell<usize>,
    directed: bool,
}

impl<T> Node<T> {
    pub fn new(node_id: NodeId, value: Option<T>) -> Self {
        Node {
            node_id,
            value,
            in_edges: BTreeMap::new(),
            out_edges: BTreeMap::new(),
        }
    }

    pub fn add_in_edge(
        curr_node: &Rc<RefCell<Node<T>>>,
        from_node: &Rc<RefCell<Node<T>>>,
        weight: &Option<Weight>,
    ) -> bool {
        let from_id = from_node.borrow().node_id;

        // Disable self-edges
        if curr_node.borrow().node_id == from_id {
            return false;
        }

        curr_node
            .borrow_mut()
            .in_edges
            .insert(from_id, HalfEdge::from_node(Rc::clone(from_node), weight))
            .is_none()
    }

    pub fn add_out_edge(
        curr_node: &Rc<RefCell<Node<T>>>,
        to_node: &Rc<RefCell<Node<T>>>,
        weight: &Option<Weight>,
    ) -> bool {
        let to_id = to_node.borrow().node_id;

        // Disable self-edges
        if curr_node.borrow().node_id == to_id {
            return false;
        }

        curr_node
            .borrow_mut()
            .out_edges
            .insert(to_id, HalfEdge::from_node(Rc::clone(to_node), weight))
            .is_none()
    }

    pub fn as_node(&self) -> NodeId {
        self.node_id
    }
}

impl<T> HalfEdge<T> {
    pub fn get_weight(&self) -> usize {
        self.weight.expect("Weights must be assigned before used")
    }

    pub fn set_weight(&mut self, weight: usize) {
        self.weight.replace(weight);
    }

    pub fn as_node(&self) -> NodeId {
        self.inner.borrow().node_id
    }

    pub fn from_node(node: Rc<RefCell<Node<T>>>, weight: &Option<usize>) -> Self {
        Self {
            inner: node,
            weight: weight.as_ref().map(|x| *x),
        }
    }
}

impl<T> std::ops::Deref for HalfEdge<T> {
    type Target = Rc<RefCell<Node<T>>>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: Clone> Graph<T> {
    pub fn build_directed(num_nodes: usize, edge_list: &EdgeList) -> Self {
        let mut graph = Graph::new(true);
        for v in 0..num_nodes {
            graph.add_vertex(v, None);
        }

        for (v, e, w) in edge_list {
            graph.add_edge(*v, *e, w, true);
            graph.num_edges.set(graph.num_edges.get() + 1);
            // graph.num_edges.replace(graph.num_edges.get() + 1);
        }

        graph
    }

    pub fn build_undirected(num_nodes: usize, edge_list: &EdgeList) -> Self {
        let mut graph = Graph::new(false);
        // println!("Building undirected, with {} nodes", num_nodes);
        for v in 0..num_nodes {
            graph.add_vertex(v, None);
        }
        for (v, e, w) in edge_list {
            graph.add_edge(*v, *e, w, false);
            // graph.num_edges.replace(graph.num_edges.get() + 1);
            graph.num_edges.set(graph.num_edges.get() + 1);
        }

        graph
    }

    pub fn directed(&self) -> bool {
        self.directed
    }

    pub fn num_nodes(&self) -> usize {
        self.vertices.borrow().len()
    }

    pub fn num_edges(&self) -> usize {
        self.num_edges.get()
    }

    pub fn num_edges_directed(&self) -> usize {
        if self.directed {
            self.num_edges.get()
        } else {
            self.num_edges.get() * 2
        }
    }

    pub fn out_degree(&self, v: NodeId) -> usize {
        if let Some(found) = self.vertices.borrow().get(&v) {
            found.borrow().out_edges.len()
        } else {
            0
        }
    }

    pub fn in_degree(&self, v: NodeId) -> usize {
        println!("Graph inversion is probably disabled... in in_degree()");
        if let Some(found) = self.vertices.borrow().get(&v) {
            found.borrow().in_edges.len()
        } else {
            panic!("Vertex not found");
        }
    }

    pub fn out_neigh(&self, v: NodeId) -> Box<std::vec::IntoIter<HalfEdge<T>>> {
        if let Some(vertex) = self.vertices.borrow().get(&v) {
            let mut edges = Vec::new();
            for edge in vertex.borrow().out_edges.values() {
                edges.push(HalfEdge {
                    inner: edge.inner.clone(),
                    weight: edge.weight.clone(),
                });
            }

            Box::new(edges.into_iter())
        } else {
            panic!("Vertex not found");
        }
    }

    pub fn in_neigh(&self, v: NodeId) -> Box<std::vec::IntoIter<HalfEdge<T>>> {
        if let Some(vertex) = self.vertices.borrow().get(&v) {
            let mut edges = Vec::new();
            for edge in vertex.borrow().in_edges.values() {
                edges.push(HalfEdge {
                    inner: edge.inner.clone(),
                    weight: edge.weight.clone(),
                });
            }

            Box::new(edges.into_iter())
        } else {
            panic!("Vertex not found");
        }
    }

    pub fn print_stats(&self) {
        println!("---------- GRAPH ----------");
        println!("  Num Nodes          - {:?}", self.num_nodes());
        println!("  Num Edges          - {:?}", self.num_edges_directed());
        println!("---------------------------");
    }

    pub fn vertices(&self) -> Box<std::vec::IntoIter<WrappedNode<T>>> {
        let mut edges = Vec::new();
        for wrappednode in self.vertices.borrow().values() {
            edges.push(wrappednode.clone());
        }

        Box::new(edges.into_iter())
    }

    pub fn replace_out_edges(&self, v: NodeId, edges: Vec<HalfEdge<T>>) {
        if let Some(vertex) = self.vertices.borrow().get(&v) {
            let mut new_edges = BTreeMap::new();
            for e in edges {
                new_edges.insert(e.as_node(), e);
            }
            vertex.borrow_mut().out_edges = new_edges;
        }
    }

    pub fn replace_in_edges(&self, v: NodeId, edges: Vec<HalfEdge<T>>) {
        if let Some(vertex) = self.vertices.borrow().get(&v) {
            let mut new_edges = BTreeMap::new();
            for e in edges {
                new_edges.insert(e.as_node(), e);
            }
            vertex.borrow_mut().in_edges = new_edges;
        }
    }

    pub fn old_bfs(&self, v: NodeId) {
        self.bfs(v, None);
    }

    pub fn op_add_vertex(&self, v: NodeId) {
        self.add_vertex(v, None);
    }

    pub fn op_add_edge(&mut self, v: NodeId, e: NodeId) {
        self.add_edge(v, e, &None, false);
    }

    pub fn op_delete_edge(&self, v: NodeId, e: NodeId) {
        self.vertices
            .borrow()
            .get(&v)
            .map(|vertex| vertex.borrow_mut().out_edges.remove(&e));
    }

    pub fn op_delete_vertex(&self, v: NodeId) {
        self.vertices.borrow_mut().remove(&v);
    }

    pub fn op_find_vertex(&self, v: NodeId) {
        self.find_vertex(v);
    }
}

impl<T> Graph<T> {
    pub fn new(directed: bool) -> Self {
        Graph {
            vertices: RefCell::new(BTreeMap::new()),
            num_edges: Cell::new(0),
            directed,
        }
    }

    pub fn find_vertex(&self, vertex: usize) -> Option<Rc<RefCell<Node<T>>>> {
        self.vertices.borrow().get(&vertex).map(|v| Rc::clone(v))
    }

    pub fn add_vertex(&self, node_id: usize, value: Option<T>) -> Rc<RefCell<Node<T>>> {
        let new_node = Rc::new(RefCell::new(Node::new(node_id, value)));
        self.vertices
            .borrow_mut()
            .entry(node_id)
            .or_insert(new_node.clone());
        new_node
    }

    pub fn add_edge(&mut self, vertex: usize, edge: usize, weight: &Option<usize>, directed: bool) {
        if let (Some(vertex_node), Some(edge_node)) = (
            self.vertices.borrow().get(&vertex),
            self.vertices.borrow().get(&edge),
        ) {
            if !directed {
                Node::add_out_edge(&edge_node, &vertex_node, weight);
            } else {
                Node::add_in_edge(&edge_node, &vertex_node, weight);
            }

            if Node::add_out_edge(&vertex_node, &edge_node, weight) {
                self.num_edges.set(self.num_edges.get() + 1);
                // self.num_edges.replace(self.num_edges.get() + 1);
            }
        } else {
            // panic!("Could not add edge, one or both of the nodes you are trying to connect does not exist");
        }
    }

    pub fn connect(
        &mut self,
        vertex_node: &Rc<RefCell<Node<T>>>,
        edge_node: &Rc<RefCell<Node<T>>>,
        weight: &Option<usize>,
        directed: bool,
    ) {
        if !directed {
            Node::add_out_edge(&edge_node, &vertex_node, weight);
        } else {
            Node::add_in_edge(&edge_node, &vertex_node, weight);
        }

        if Node::add_out_edge(&vertex_node, &edge_node, weight) {
            self.num_edges.set(self.num_edges.get() + 1);
        }
    }

    pub fn bfs(&self, start: usize, goal: Option<usize>) -> usize {
        let mut queue = VecDeque::new();
        let mut discovered = HashSet::new();

        let start = self.find_vertex(start).unwrap();
        discovered.insert(start.borrow().node_id);
        queue.push_back(Rc::clone(&start));

        while let Some(node) = queue.pop_front() {
            let locked_node = node.borrow();
            for edge in locked_node.out_edges.values() {
                let edge_node_id = edge.borrow().node_id;

                if goal == Some(edge_node_id) {
                    return discovered.len();
                }

                if !discovered.contains(&edge_node_id) {
                    discovered.insert(edge_node_id);
                    queue.push_back(Rc::clone(&edge));
                }
            }
        }

        discovered.len()
    }
}
