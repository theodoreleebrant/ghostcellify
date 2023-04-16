#[macro_export]

macro_rules! ghostcellify {
    ($item:item) => { #[allow(dead_code)] $item };
}
