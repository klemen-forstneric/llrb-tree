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
    K: Clone + Ord,
    V: Clone,
{
    pub left: Option<Box<Node<K, V>>>,
    pub right: Option<Box<Node<K, V>>>,
    pub color: Color,

    pub key: K,
    pub value: V,
}

impl<K, V> Node<K, V>
where
    K: Clone + Ord,
    V: Clone,
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

    fn is_right_red(self: &Box<Self>) -> bool {
        match self.right.as_ref() {
            Some(right) => right.color == Color::Red,
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

    fn is_left_of_right_red(self: &Box<Self>) -> bool {
        match self.right.as_ref() {
            Some(right) => match right.left.as_ref() {
                Some(left) => left.color == Color::Red,
                None => false,
            },
            None => false,
        }
    }

    fn move_red_left(mut self: Box<Self>) -> Box<Self> {
        self = self.flip_colors();

        if let Some(right) = self.right {
            if !right.is_left_red() {
                self.right = Some(right);
            } else {
                self.right = Some(right.rotate_right());
                self = self.rotate_left();
                self = self.flip_colors();
            }
        }

        self
    }

    fn move_red_right(mut self: Box<Self>) -> Box<Self> {
        self = self.flip_colors();

        if let Some(left) = self.left.as_ref() {
            if left.is_left_red() {
                self = self.rotate_right();
                self = self.flip_colors();
            }
        }

        self
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
    K: Clone + Ord,
    V: Clone,
{
    root: Option<Box<Node<K, V>>>,
}

impl<K, V> Tree<K, V>
where
    K: Clone + Ord,
    V: Clone,
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
                match key.cmp(&n.key) {
                    Ordering::Equal => n.value = value,
                    Ordering::Less => n.left = Self::insert_node(n.left.take(), key, value),
                    Ordering::Greater => n.right = Self::insert_node(n.right.take(), key, value),
                }

                Some(Self::balance(n))
            }
        }
    }

    fn balance(mut n: Box<Node<K, V>>) -> Box<Node<K, V>> {
        if n.is_right_red() && !n.is_left_red() {
            n = n.rotate_left()
        }

        if n.is_left_red() && n.is_left_of_left_red() {
            n = n.rotate_right()
        }

        if n.is_left_red() && n.is_right_red() {
            n = n.flip_colors();
        }

        n
    }

    pub fn delete(&mut self, key: K) {
        let mut root = Self::delete_node(self.root.take(), key);

        if let Some(r) = root.as_mut() {
            r.color = Color::Black;
        }

        self.root = root;
    }

    fn delete_node(node: Option<Box<Node<K, V>>>, key: K) -> Option<Box<Node<K, V>>> {
        node.and_then(|mut n| {
            match key.cmp(&n.key) {
                Ordering::Less => {
                    if !n.is_left_red() && !n.is_left_of_left_red() {
                        n = n.move_red_left();
                    }

                    n.left = Self::delete_node(n.left.take(), key);
                }
                Ordering::Greater => {
                    if n.is_left_red() {
                        n = n.rotate_right();
                    }
                    if !n.is_right_red() && !n.is_left_of_right_red() {
                        n = n.move_red_right();
                    }

                    n.right = Self::delete_node(n.right.take(), key);
                }
                Ordering::Equal => {
                    if n.is_left_red() {
                        n = n.rotate_right();
                    }

                    if n.right.is_none() {
                        return None;
                    }

                    if !n.is_right_red() && !n.is_left_of_right_red() {
                        n = n.move_red_right();
                    }

                    // Unwrap is safe to do, because we're checking above if right is None.
                    let min = Self::find_min_node(n.right.as_ref()).unwrap();

                    n.value = min.value.clone();
                    n.key = min.key.clone();
                    n.right = Self::delete_min_node(n.right);
                }
            }

            Some(Self::balance(n))
        })
    }

    fn find_min_node(node: Option<&Box<Node<K, V>>>) -> Option<&Box<Node<K, V>>> {
        node.and_then(|n| {
            let mut min = n;
            while let Some(l) = min.left.as_ref() {
                min = l;
            }

            Some(min)
        })
    }

    fn delete_min_node(node: Option<Box<Node<K, V>>>) -> Option<Box<Node<K, V>>> {
        node.and_then(|mut n| {
            // If n.left is None, we know n is the min node of this subtree. In order to
            // avoid deleting the right subtree, we attach n.right to where n was.
            if n.left.is_none() {
                return n.right;
            }

            if !n.is_left_red() && !n.is_left_of_left_red() {
                n = n.move_red_left()
            }

            n.left = Self::delete_min_node(n.left);

            Some(Self::balance(n))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert() {
        let mut tree: Tree<i32, &'static str> = Tree::new();
        tree.insert(1, "1");

        assert_eq!(Some(&"1"), tree.search(1));
    }
}
