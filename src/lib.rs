use std::cmp::{Ord, Ordering};
use std::ops::Not;

#[derive(PartialEq)]
pub enum Color {
    Red,
    Black,
}

impl Not for Color {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Color::Red => Color::Black,
            Color::Black => Color::Red,
        }
    }
}

struct Node<K, V>
where
    K: Ord,
{
    pub left: Option<Box<Node<K, V>>>,
    pub right: Option<Box<Node<K, V>>>,
    pub color: Color,

    pub key: K,
    pub value: V,
}

impl<K, V> Node<K, V>
where
    K: Ord,
{
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            color: Color::Red,
            left: None,
            right: None,
        }
    }

    fn is_left_red(self: &Box<Self>) -> bool {
        match self.left.as_ref() {
            Some(left) => left.color == Color::Red,
            None => false,
        }
    }

    fn is_left_of_left_red(self: &Box<Self>) -> bool {
        match self.left.as_ref() {
            Some(left) => match left.left.as_ref() {
                Some(left) => left.color == Color::Red,
                None => false,
            },
            None => false,
        }
    }

    fn is_right_red(self: &Box<Self>) -> bool {
        match self.right.as_ref() {
            Some(right) => right.color == Color::Red,
            None => false,
        }
    }

    fn rotate_left(mut self: Box<Self>) -> Box<Self> {
        match self.right {
            Some(mut root) => {
                self.right = root.left;

                root.color = self.color;
                self.color = Color::Red;

                root.left = Some(self);
                root
            }
            None => self,
        }
    }

    fn rotate_right(mut self: Box<Self>) -> Box<Self> {
        match self.left {
            Some(mut root) => {
                self.left = root.right;

                root.color = self.color;
                self.color = Color::Red;

                root.right = Some(self);
                root
            }
            None => self,
        }
    }

    fn flip_colors(mut self: Box<Self>) -> Box<Self> {
        self.color = !self.color;

        if let Some(mut left) = self.left {
            left.color = !left.color;
            self.left = Some(left);
        }

        if let Some(mut right) = self.right {
            right.color = !right.color;
            self.right = Some(right);
        }
        self
    }
}

pub struct Tree<K, V>
where
    K: Ord,
{
    root: Option<Box<Node<K, V>>>,
}

impl<K, V> Tree<K, V>
where
    K: Ord,
{
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn search(&self, key: K) -> Option<&V> {
        let mut current = self.root.as_ref();

        while let Some(n) = current {
            match key.cmp(&n.key) {
                Ordering::Equal => return Some(&n.value),
                Ordering::Less => current = n.left.as_ref(),
                Ordering::Greater => current = n.right.as_ref(),
            }
        }

        None
    }

    // TODO: Figure out if we want to assume ownership of input params.
    pub fn insert(&mut self, key: K, value: V) {
        let mut root = Self::insert_node(self.root.take(), key, value);

        if let Some(r) = root.as_mut() {
            r.color = Color::Black;
        }

        self.root = root;
    }

    fn insert_node(node: Option<Box<Node<K, V>>>, key: K, value: V) -> Option<Box<Node<K, V>>> {
        match node {
            None => Some(Box::new(Node::new(key, value))),
            Some(mut n) => {
                if n.is_left_red() && n.is_right_red() {
                    n = n.flip_colors();
                }

                match key.cmp(&n.key) {
                    Ordering::Equal => n.value = value,
                    Ordering::Less => n.left = Self::insert_node(n.left.take(), key, value),
                    Ordering::Greater => n.right = Self::insert_node(n.right.take(), key, value),
                }

                if n.is_right_red() && !n.is_left_red() {
                    n = n.rotate_left()
                }

                if n.is_left_red() && n.is_left_of_left_red() {
                    n = n.rotate_right()
                }

                Some(n)
            }
        }
    }

    pub fn delete(&mut self, key: K) {
        let mut root = Self::delete_node(self.root.take(), key);

        if let Some(r) = root.as_mut() {
            r.color = Color::Black;
        }

        self.root = root;
    }

    fn delete_node(node: Option<Box<Node<K, V>>>, key: K) -> Option<Box<Node<K, V>>> {
        node
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert() {
        let mut tree: Tree<i32, String> = Tree::new();
        tree.insert(1, "1".to_string());
    }
}
