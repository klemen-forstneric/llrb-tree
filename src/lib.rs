//! A Left-Leaning Red-Black (LLRB) tree implementation.
//!
//! This module implements an LLRB tree supporting insertion, deletion,
//! and search of key/value pairs. The implementation uses the standard
//! red-black tree rebalancing algorithm and maintains the invariant that
//! the tree's root is always black.

use std::cmp::{Ord, Ordering};
use std::ops::Not;

/// The color of a node in the LLRB tree.
#[derive(Debug, PartialEq)]
pub enum Color {
    /// A red node.
    Red,
    /// A black node.
    Black,
}

impl Not for Color {
    type Output = Self;

    /// Flips the color.
    ///
    /// # Examples
    ///
    /// ```
    /// use llrb_tree::Color;
    /// assert_eq!(!Color::Red, Color::Black);
    /// assert_eq!(!Color::Black, Color::Red);
    /// ```
    fn not(self) -> Self::Output {
        match self {
            Color::Red => Color::Black,
            Color::Black => Color::Red,
        }
    }
}

/// A node in the LLRB tree.
///
/// Each node stores a key/value pair, its children, and its color.
#[derive(Debug)]
struct Node<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    /// The left child.
    pub left: Option<Box<Node<K, V>>>,
    /// The right child.
    pub right: Option<Box<Node<K, V>>>,
    /// The color of this node.
    pub color: Color,
    /// The key of the node.
    pub key: K,
    /// The associated value with the key.
    pub value: V,
}

impl<K, V> Node<K, V>
where
    K: Clone + Ord,
    V: Clone,
{
    /// Creates a new `Node` with the given key and value.
    ///
    /// New nodes are red by default.
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            color: Color::Red,
            left: None,
            right: None,
        }
    }

    /// Returns `true` if the left child is red.
    fn is_left_red(&self) -> bool {
        match self.left.as_ref() {
            Some(left) => left.color == Color::Red,
            None => false,
        }
    }

    /// Returns `true` if the right child is red.
    fn is_right_red(&self) -> bool {
        match self.right.as_ref() {
            Some(right) => right.color == Color::Red,
            None => false,
        }
    }

    /// Returns `true` if the left child of the left child is red.
    fn is_left_of_left_red(&self) -> bool {
        match self.left.as_ref() {
            Some(left) => match left.left.as_ref() {
                Some(left) => left.color == Color::Red,
                None => false,
            },
            None => false,
        }
    }

    /// Returns `true` if the left child of the right child is red.
    fn is_left_of_right_red(&self) -> bool {
        match self.right.as_ref() {
            Some(right) => match right.left.as_ref() {
                Some(left) => left.color == Color::Red,
                None => false,
            },
            None => false,
        }
    }

    /// Moves a red node left.
    ///
    /// This method is used during deletion to ensure that the left child
    /// or one of its descendants is red.
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

    /// Moves a red node right.
    ///
    /// This method is used during deletion to ensure that the right child
    /// or one of its descendants is red.
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

    /// Rotates the tree to the left.
    ///
    /// Returns the new root of the subtree.
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

    /// Rotates the tree to the right.
    ///
    /// Returns the new root of the subtree.
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

    /// Flips the colors of this node and its immediate children.
    ///
    /// Returns `self` with flipped colors.
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

/// A Left-Leaning Red-Black (LLRB) tree.
///
/// This tree supports insertion, deletion, and search operations.
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
    /// Creates a new empty `Tree`.
    ///
    /// # Examples
    ///
    /// ```
    /// use llrb_tree::Tree;
    /// let tree: Tree<i32, &str> = Tree::new();
    /// ```
    pub fn new() -> Self {
        Self { root: None }
    }

    /// Searches for a value associated with the given key.
    ///
    /// Returns a reference to the value if found, or `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use llrb_tree::Tree;
    /// let mut tree = Tree::new();
    /// tree.insert(1, "one");
    /// assert_eq!(tree.search(1), Some(&"one"));
    /// ```
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

    /// Inserts a key-value pair into the tree.
    ///
    /// If the key already exists, its value is updated.
    ///
    /// # Examples
    ///
    /// ```
    /// use llrb_tree::Tree;
    /// let mut tree = Tree::new();
    /// tree.insert(1, "one");
    /// assert_eq!(tree.search(1), Some(&"one"));
    /// ```
    pub fn insert(&mut self, key: K, value: V) {
        let mut root = Self::insert_node(self.root.take(), key, value);

        if let Some(r) = root.as_mut() {
            r.color = Color::Black;
        }

        self.root = root;
    }

    /// Recursive helper for insertion.
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

    /// Balances the subtree by performing necessary rotations and color flips.
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

    /// Deletes a key and its associated value from the tree.
    ///
    /// If the key does not exist, the tree is left unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use llrb_tree::Tree;
    /// let mut tree = Tree::new();
    /// tree.insert(1, "one");
    /// tree.delete(1);
    /// assert_eq!(tree.search(1), None);
    /// ```
    pub fn delete(&mut self, key: K) {
        let mut root = Self::delete_node(self.root.take(), key);

        if let Some(r) = root.as_mut() {
            r.color = Color::Black;
        }

        self.root = root;
    }

    /// Recursive helper for deletion.
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

    /// Locates the node with the minimum key in the subtree.
    fn find_min_node(node: Option<&Box<Node<K, V>>>) -> Option<&Box<Node<K, V>>> {
        node.and_then(|n| {
            let mut min = n;
            while let Some(l) = min.left.as_ref() {
                min = l;
            }

            Some(min)
        })
    }

    /// Deletes the minimum node from the subtree.
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
