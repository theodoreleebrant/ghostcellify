
use ghost_cell::{GhostCell, GhostToken};
#[allow(unused_imports)]
use std::{
    cell::{Ref, RefCell},
    cmp::Ordering,
    collections::BTreeMap,
    fmt,
    marker::PhantomData,
    ops::Deref,
    rc::{Rc, Weak},
};

// #[derive(Clone)]
pub struct BinarySearchBree<'id0> {
    root: Option<RcRefCell<Hook<'id0>>>,
}

impl<'id0> BinarySearchBree<'id0> {
    pub fn new() -> Self {
        Self { root: None }
    }
    
    /// 挿入します。
    pub fn insert(&mut self, key: u32, token: &GhostToken<'id0>) {
        if let Some(root) = self.root.as_mut() {
            let mut x: RcRefCell<Hook<'id0>> = Rc::clone(root);
            let i = loop {
                let i = if key <= x.borrow(token).key { 0 } else { 1 };
                let y = x.borrow(token).children[i].as_ref().map(Rc::clone);
                if let Some(y) = y {
                    x = y;
                } else {
                    break i;
                }
            };
            let hook = rc_ref_cell(Hook<'id0>::new(key));
            Hook<'id0>::connect(&x, i, Some(hook));
        } else {
            self.root = Some(rc_ref_cell(Hook<'id0>::new(key)));
        }
    }

    /// キーで検索して、あればひとつ（もっとも上にあるもの）を消します
    pub fn delete(&mut self, key: u32, token: &GhostToken<'id0>) -> Option<u32> {
        if let Some(x) = self.search(key) {
            if let Some(right) = x.borrow(token).children[1].as_ref() {
                if x.borrow(token).children[0].is_none() {
                    self.transplant(&x, x.borrow(token).children[1].as_ref().map(Rc::clone));
                } else {
                    let y = Hook<'id0>::tree_extremum(Rc::clone(&right), 0);
                    if !Rc::ptr_eq(&right, &y) {
                        self.transplant(&y, y.borrow(token).children[1].as_ref().map(Rc::clone));
                        Hook<'id0>::connect(&y, 1, x.borrow(token).children[1].as_ref().map(Rc::clone));
                    }
                    self.transplant(&x, Some(Rc::clone(&y)));
                    Hook<'id0>::connect(&y, 0, x.borrow(token).children[0].as_ref().map(Rc::clone));
                }
            } else {
                self.transplant(&x, x.borrow(token).children[0].as_ref().map(Rc::clone));
            }
            self.validate();
            Some(x.borrow(token).key)
        } else {
            None
        }
    }
    pub fn get(&self, key: u32, token: &GhostToken<'id0>) -> Option<u32> {
        self.search(key).map(|hook| hook.borrow(token).key)
    }
    pub fn contains(&self, key: u32) -> bool {
        self.search(key).is_some()
    }
    pub fn first(&self, token: &GhostToken<'id0>) -> Option<u32> {
        self.root
            .as_ref()
            .map(|root| Hook<'id0>::tree_extremum(Rc::clone(root), 0).borrow(token).key)
    }
    pub fn last(&self, token: &GhostToken<'id0>) -> Option<u32> {
        self.root
            .as_ref()
            .map(|root| Hook<'id0>::tree_extremum(Rc::clone(root), 1).borrow(token).key)
    }
    fn search(&self, key: u32, token: &GhostToken<'id0>) -> Option<RcRefCell<Hook<'id0>>> {
        self.root.as_ref().and_then(|root| {
            let mut x: RcRefCell<Hook<'id0>> = Rc::clone(root);
            loop {
                let i = match key.cmp(&x.borrow(token).key) {
                    Ordering::Equal => return Some(Rc::clone(&x)),
                    Ordering::Less => 0,
                    Ordering::Greater => 1,
                };
                let y = x.borrow(token).children[i].as_ref().map(Rc::clone);
                if let Some(y) = y {
                    x = y;
                } else {
                    break None;
                }
            }
        })
    }
    pub fn collect_vec(&self, token: &GhostToken<'id0>) -> Vec<u32> {
        let mut res = Vec::new();
        if let Some(root) = self.root.as_ref() {
            root.borrow(token).collect_vec(&mut res);
        }
        res
    }
    fn print(&self, fmt: &mut fmt::Formatter, token: &GhostToken<'id0>) -> fmt::Result {
        if let Some(root) = self.root.as_ref().map(|root| root.borrow(token)) {
            fmt.debug_tuple("BinarySearchBree").field(&root).finish()
        } else {
            fmt.debug_tuple("BinarySearchBree").finish()
        }
    }
    /// `x` のいた場所に `y` を植えます。
    ///
    /// ### Details
    ///
    /// - （この場合で呼ばないで！） `y` が `x` の先祖のとき、`y` の部分木が消えます。
    /// - `x` が根のとき、`y` を根にして、さらに `y` が `None` でなければ `y` の親を `None` にします。
    /// - `x` が根でないとき、`x` の親 `p` の適切な子を `y` にして、`y` の親を `p` にします。
    ///
    /// いずれにしても、もともとの `x` の部分木のうち `y`
    /// の部分木に含まれない部分は、どこからもリンクされなくなります。
    ///
    fn transplant(&mut self, x: &RcRefCell<Hook<'id0>>, y: Option<RcRefCell<Hook<'id0>>>, token: &mut GhostToken<'id0>) {
        if let Some(p) = x.borrow(token).parent.as_ref().map(Weak::upgrade).flatten() {
            let i = (0..2)
                .find(|&i| {
                    p.borrow(token).children[i]
                        .as_ref()
                        .map_or(false, |child| Rc::ptr_eq(&child, x))
                })
                .unwrap();
            Hook<'id0>::connect(&p, i, y.as_ref().map(Rc::clone));
        } else {
            if let Some(y) = y.as_ref() {
                y.borrow_mut(token).parent = None;
            }
            self.root = y;
        }
    }
    /// 各ノードの親ポインタが正しく逆になっていなければ、パニックします。
    fn validate(&self, token: &GhostToken<'id0>) {
        if let Some(root) = self.root.as_ref() {
            assert!(root.borrow(token).parent.is_none(), "{:?}", VWrapper(self));
            fn dfs(me: &BinarySearchBree<'id0>, x: &RcRefCell<Hook<'id0>>, token: &GhostToken<'id0>) {
                if let Some(child) = x.borrow(token).children[0].as_ref() {
                    assert!(
                        Rc::ptr_eq(&child.borrow(token).parent().unwrap(), &x),
                        "x = {:?}, child = {:?}, {:?}",
                        x,
                        child.borrow(token).deref(),
                        VWrapper(me)
                    );
                    dfs(me, child);
                }
                if let Some(child) = x.borrow(token).children[1].as_ref() {
                    assert!(
                        Rc::ptr_eq(&child.borrow(token).parent().unwrap(), &x),
                        "x = {:?}, child = {:?}, {:?}",
                        x,
                        child.borrow(token).deref(),
                        VWrapper(me)
                    );
                    dfs(me, child);
                }
            };
            dfs(self, root);
        }
    }
}

impl<'id0> Verbose for BinarySearchBree<'id0> {
    fn verbose(&self, fmt: &mut fmt::Formatter, token: &GhostToken<'id0>) -> fmt::Result {
        self.root
            .iter()
            .map(|root| root.borrow(token).verbose(fmt))
            .collect()
    }
}

trait Verbose {
    fn verbose(&self, fmt: &mut fmt::Formatter) -> fmt::Result;
}

/// デバッグ
struct VWrapper<'a, T>(&'a T);
impl<'a, T> fmt::Debug for VWrapper<'a, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.0.verbose(fmt)
    }
}

/// デバッグ
impl<'id0> fmt::Debug for Hook<'id0> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.print(fmt)
    }
}
/// デバッグ
impl<'id0> fmt::Debug for BinarySearchBree<'id0> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.print(fmt)
    }
}

/// リンク付きノード
// #[derive(Clone)]
#[rustfmt::ghostcellify]
struct Hook<'id0> {
    children: [Option<RcRefCell<Hook<'id0>>>; 2],
    parent: Option<WeakRefCell<Hook<'id0>>>,
    key: u32,
}
impl<'id0> Hook<'id0> {
    fn new(key: u32) -> Self {
        Self {
            children: [None, None],
            parent: None,
            key,
        }
    }

    fn tree_extremum(mut root: RcRefCell<Self>, i: usize, token: &GhostToken<'id0>) -> RcRefCell<Self> {
        loop {
            let left = root.borrow(token).children[i].as_ref().map(Rc::clone);
            if let Some(left) = left {
                root = left;
                break;
            }
        };
        root
    }

    /// x の i 番目の子を y にして、y の親を i にします。
    fn connect(x: &RcRefCell<Self>, i: usize, y: Option<RcRefCell<Self>>, token: &mut GhostToken<'id0>) {
        x.borrow_mut(token).children[i] = y.as_ref().map(Rc::clone);
        if let Some(y) = y.as_ref() {
            y.borrow_mut(token).parent = Some(Rc::downgrade(x));
        }
    }
    /// None のとき None、Some(無効な Weak） のときパニックです。
    fn parent(&self) -> Option<RcRefCell<Hook<'id0>>> {
        self.parent
            .as_ref()
            .map(|parent| Weak::upgrade(parent).unwrap())
    }
    
    fn collect_vec(&self, vec: &mut Vec<u32>, token: &GhostToken<'id0>) {
        if let Some(child) = &self.children[0] {
            child.borrow(token).collect_vec(vec);
        }
        vec.push(self.key);
        if let Some(child) = &self.children[1] {
            child.borrow(token).collect_vec(vec);
        }
    }
    
    fn print(&self, fmt: &mut fmt::Formatter, token: &GhostToken<'id0>) -> fmt::Result {
            write!(fmt, "(")?;
            if let Some(child) = &self.children[0] {
                child.borrow(token).print(fmt)?;
            }
            write!(fmt, "{}", self.key)?;
            if let Some(child) = &self.children[1] {
                child.borrow(token).print(fmt)?;
            }
            write!(fmt, ")")
    }
}

impl<'id0> Verbose for Hook<'id0> {
    fn verbose(&self, fmt: &mut fmt::Formatter, token: &GhostToken<'id0>) -> fmt::Result {
        if let Some(child) = &self.children[0] {
            child.borrow(token).verbose(fmt)?;
        }
        writeln!(fmt)?;
        write!(fmt, "  - ")?;
        fmt.debug_struct("Node")
            .field("key", &self.key)
            .field("parent", &self.parent.as_ref().map(Weak::upgrade))
            .finish()?;
        if let Some(child) = &self.children[1] {
            child.borrow(token).verbose(fmt)?;
        }
        Ok(())
    }
}

/// サボるためのツール
type RcRefCell<T> = Rc<RefCell<T>>;
/// サボるためのツール
type WeakRefCell<T> = Weak<RefCell<T>>;
/// サボるためのツール
fn rc_ref_cell<T>(x: T) -> RcRefCell<T> {
    Rc::new(GhostCell::new(x))
}
#[cfg(test)]
mod tests {
    use super::span::Span;
    use super::BinarySearchBree;
    use rand::prelude::*;

    #[test]
    fn test_hand() {
        let mut rng = StdRng::seed_from_u64(42);
        let mut bst = BinarySearchBree::new();
        let mut vec = Vec::new();
        for _ in 0..20 {
            for _ in 0..2000 {
                let key = rng.gen_range(0, 30);
                match rng.gen_range(0, 7) {
                    0 => {
                        println!("insert {}", key);
                        bst.insert(key);
                        let lb = vec.lower_bound(&key);
                        vec.insert(lb, key);
                    }
                    1 => {
                        assert_eq!(bst.contains(key), vec.binary_search(&key).is_ok());
                    }
                    2 => {
                        assert_eq!(bst.get(key), vec.binary_search(&key).ok().map(|i| vec[i]));
                    }
                    3..=6 => {
                        println!("delete {}", key);
                        bst.delete(key);
                        let lb = vec.lower_bound(&key);
                        if vec.get(lb).map_or(false, |x| x == &key) {
                            vec.remove(lb);
                        }
                    }
                    _ => panic!(),
                }
                println!("bst = {:?}", &bst);
                println!("vec = {:?}", &vec);
                assert_eq!(&bst.collect_vec(), &vec);
                assert_eq!(bst.first(), vec.first().copied());
                assert_eq!(bst.last(), vec.last().copied());
                println!();
            }
        }
    }
}
// dbg {{{
#[allow(dead_code)]
mod dbg {
    #[macro_export]
    macro_rules! lg {
        () => {
            $crate::eprintln!("[{}:{}]", $crate::file!(), $crate::line!());
        };
        ($val:expr) => {
            match $val {
                tmp => {
                    eprintln!("[{}:{}] {} = {:?}",
                        file!(), line!(), stringify!($val), &tmp);
                    tmp
                }
            }
        };
        ($val:expr,) => { $crate::lg!($val) };
        ($($val:expr),+ $(,)?) => {
            ($($crate::lg!($val)),+,)
        };
    }

    #[macro_export]
    macro_rules! lg_nl {
        () => {
            eprintln!("[{}:{}]", $crate::file!(), $crate::line!());
        };
        ($val:expr) => {
            match $val {
                tmp => {
                    eprintln!("[{}:{}] {}:\n{:?}", file!(), line!(), stringify!($val), tmp);
                    tmp
                }
            };
        };
    }

    #[macro_export]
    macro_rules! msg {
        () => {
            compile_error!();
        };
        ($msg:expr) => {
            $crate::eprintln!("[{}:{}][{}]", $crate::file!(), $crate::line!(), $msg);
        };
        ($msg:expr, $val:expr) => {
            match $val {
                tmp => {
                    eprintln!("[{}:{}][{}] {} = {:?}",
                        file!(), line!(), $msg, stringify!($val), &tmp);
                    tmp
                }
            }
        };
        ($msg:expr, $val:expr,) => { msg!($msg, $val) };
        ($msg:expr, $($val:expr),+ $(,)?) => {
            ($(msg!($msg, $val)),+,)
        };
    }

    #[macro_export]
    macro_rules! tabular {
        ($val:expr) => {
            $crate::lg_nl!(crate::dbg::Tabular($val))
        };
    }

    #[macro_export]
    macro_rules! boolean_table {
        ($val:expr) => {
            $crate::lg_nl!(crate::dbg::BooleanTable($val));
        };
    }

    #[macro_export]
    macro_rules! boolean_slice {
        ($val:expr) => {
            $crate::lg!(crate::dbg::BooleanSlice($val));
        };
    }

    use std::fmt::{Debug, Formatter};

    #[derive(Clone)]
    pub struct Tabular<'a, T>(pub &'a [T]);
    impl<'a, T> Debug for Tabular<'a, T> {
        fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
            for i in 0..self.0.len() {
                writeln!(f, "{:2} | {:?}", i, &self.0[i])?;
            }
            Ok(())
        }
    }

    #[derive(Clone)]
    pub struct BooleanTable<'a>(pub &'a [Vec<bool>]);
    impl<'a> Debug for BooleanTable<'a> {
        fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
            for i in 0..self.0.len() {
                writeln!(f, "{:2} | {:?}", i, BooleanSlice(&self.0[i]))?;
            }
            Ok(())
        }
    }

    #[derive(Clone)]
    pub struct BooleanSlice<'a>(pub &'a [bool]);
    impl<'a> Debug for BooleanSlice<'a> {
        fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
            write!(
                f,
                "{}",
                self.0
                    .iter()
                    .map(|&b| if b { "1 " } else { "0 " })
                    .collect::<String>()
            )?;
            Ok(())
        }
    }
}
// }}}
// span {{{
#[allow(dead_code)]
mod span {
    use std::{cmp, ops};

    impl<T> Span<T> for [T] {
        fn __span_internal_len(&self) -> usize {
            self.len()
        }

        fn __span_internal_is_empty(&self) -> bool {
            self.is_empty()
        }

        fn __span_internal_sort(&mut self)
        where
            T: cmp::Ord,
        {
            self.sort()
        }

        fn __span_internal_sort_by<F>(&mut self, compare: F)
        where
            F: FnMut(&T, &T) -> cmp::Ordering,
        {
            self.sort_by(compare)
        }

        fn __span_internal_sort_by_key<K, F>(&mut self, f: F)
        where
            F: FnMut(&T) -> K,
            K: cmp::Ord,
        {
            self.sort_by_key(f)
        }
    }

    pub trait Span<T>: ops::Index<usize, Output = T> {
        fn __span_internal_len(&self) -> usize;

        fn __span_internal_is_empty(&self) -> bool {
            self.__span_internal_len() == 0
        }

        fn __span_internal_sort(&mut self)
        where
            T: cmp::Ord;

        fn __span_internal_sort_by<F>(&mut self, compare: F)
        where
            F: FnMut(&T, &T) -> cmp::Ordering;

        fn __span_internal_sort_by_key<K, F>(&mut self, f: F)
        where
            F: FnMut(&T) -> K,
            K: cmp::Ord;

        fn sort_reverse(&mut self)
        where
            T: cmp::Ord,
        {
            self.__span_internal_sort_by(|a, b| a.cmp(b).reverse())
        }

        fn sort_reverse_by<F>(&mut self, mut compare: F)
        where
            F: FnMut(&T, &T) -> cmp::Ordering,
        {
            self.__span_internal_sort_by(|a, b| compare(a, b).reverse())
        }

        fn sort_reverse_by_key<K, F>(&mut self, mut f: F)
        where
            F: FnMut(&T) -> K,
            K: cmp::Ord,
        {
            self.__span_internal_sort_by_key(|x| cmp::Reverse(f(x)))
        }

        fn lower_bound<'a>(&'a self, x: &Self::Output) -> usize
        where
            T: Ord,
        {
            self.lower_bound_by(|p| p.cmp(x))
        }

        fn lower_bound_by_key<B, F>(&self, b: &B, mut f: F) -> usize
        where
            F: FnMut(&T) -> B,
            B: Ord,
        {
            self.lower_bound_by(|x| f(x).cmp(b))
        }

        fn lower_bound_by<F>(&self, mut f: F) -> usize
        where
            F: FnMut(&T) -> cmp::Ordering,
        {
            self.partition_point(|x| f(x) == cmp::Ordering::Less)
        }

        fn upper_bound<'a>(&'a self, x: &Self::Output) -> usize
        where
            Self::Output: Ord,
        {
            self.upper_bound_by(|p| p.cmp(x))
        }

        fn upper_bound_by_key<B, F>(&self, b: &B, mut f: F) -> usize
        where
            F: FnMut(&T) -> B,
            B: Ord,
        {
            self.upper_bound_by(|x| f(x).cmp(b))
        }

        fn upper_bound_by<F>(&self, mut f: F) -> usize
        where
            F: FnMut(&T) -> cmp::Ordering,
        {
            self.partition_point(|x| f(x) != cmp::Ordering::Greater)
        }

        fn partition_point<F>(&self, mut pred: F) -> usize
        where
            F: FnMut(&T) -> bool,
        {
            let mut left = 0;
            let mut right = self.__span_internal_len();
            while left != right {
                let mid = left + (right - left) / 2;
                let value = &self[mid];
                if pred(value) {
                    left = mid + 1;
                } else {
                    right = mid;
                }
            }
            left
        }
    }
}