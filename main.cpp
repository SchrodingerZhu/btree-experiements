#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <functional>
#include <iostream>
#include <iterator>
#include <random>
#include <search.h>
#include <string>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <vector>

#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

//
//                 =========
//                 | 4 | 7 |
//       ----------=========----------
//       |             |             |
//       |             |             |
//   =========     =========     =========
//   | 1 | 3 |     | 5 |   |     | 8 | 9 |
//   =========     =========     =========
//
//   represents
//                  __ 4 __
//                 |       |
//                 |       |
//                 1_     _7_
//                   |   |   |
//                   3   5   8_
//                             |
//                             9

template <class T, class Comparator, size_t B> struct BTree {

  using LocationFlag = uint32_t;
  static constexpr LocationFlag FOUND = 1ull << 16ull;
  static constexpr LocationFlag FOUND_MASK = FOUND - 1;

  enum class NodeType { Internal, Leaf };

  struct Node;

  struct Cell {
    T data;
    Node *node;
  };

  using CellPtr = Cell *;

  struct NodeHeader {
    Cell *storage[2 * B - 1];
    Node *parent;
    uint16_t usage;
    uint16_t parent_index;
    NodeType type;
  };

  struct SplitResult {
    Node *left;
    Node *right;
    Cell *pivot;
  };

  struct Node {
    static constexpr size_t LEAF_SIZE = sizeof(NodeHeader);
    static constexpr size_t INTERNAL_SIZE =
        sizeof(NodeHeader) + sizeof(void *) * 2 * B;

    NodeHeader header;
    Node *children[0];

    static Node *new_node(NodeType type) {
      auto *mem = reinterpret_cast<Node *>(aligned_alloc(
          alignof(Node),
          (type == NodeType::Internal) ? INTERNAL_SIZE : LEAF_SIZE));
      if (mem) {
        mem->header.parent = nullptr;
        mem->header.usage = 0;
        mem->header.parent_index = 0;
        mem->header.type = type;
      }
      return mem;
    }

    static Node *allocate_node_chain(size_t count) {
      Node *node = nullptr;
      while (count--) {
        Node *allocated = new_node(NodeType::Internal);
        if (allocated == nullptr) {
          while (node != nullptr) {
            auto tmp = node->header.parent;
            free(node);
            node = tmp;
          }
          break;
        }

        allocated->header.parent = node;
        node = allocated;
      }
      return node;
    }

    Node *new_same_node() { return new_node(header.type); }

    const T &at(size_t i) const { return header.storage[i]->data; }

    T &at(size_t i) {
      return const_cast<T &>(const_cast<const Node *>(this)->at(i));
    }

    LocationFlag local_search(const T &key, const Comparator &comp) const {
      LocationFlag i = 0;
      while (i < header.usage && comp(at(i), key) < 0)
        i++;

      if (i < header.usage && comp(at(i), key) == 0)
        return FOUND | i;

      return i;
    }

    // Split a node when a node is full (usage == 2 * B - 1).
    SplitResult split(Node *r) {
      assert(header.usage == 2 * B - 1);
      Node *l = this;

      l->header.usage = B - 1;
      r->header.usage = B - 1;
      l->header.parent = header.parent;
      r->header.parent = header.parent;

      memcpy(&r->header.storage[0], &header.storage[B],
             sizeof(void *) * (B - 1));
      for (uint16_t i = 0; i < B - 1; ++i) {
        r->header.storage[i]->node = r;
      }

      if (this->header.type == NodeType::Internal) {
        memcpy(r->children, &children[B], sizeof(void *) * B);
        for (uint16_t i = 0; i < B; ++i) {
          r->children[i]->header.parent = r;
          r->children[i]->header.parent_index = i;
        }
      }

      return {l, r, header.storage[B - 1]};
    }

    // Adopt the child as a singleton node.
    void adopt_as_singleton(Node *l, Node *r, Cell *cell) {
      this->header.usage = 1;
      this->header.storage[0] = cell;
      cell->node = this;
      this->children[0] = l;
      l->header.parent_index = 0;
      l->header.parent = this;
      this->children[1] = r;
      r->header.parent_index = 1;
      r->header.parent = this;
    }

    // Free the memory of nodes recursively
    template <class Cleaner>
    static void destroy(Node *node, const Cleaner &cleaner = {}) {
      if (node == nullptr)
        return;
      if (node->header.type == NodeType::Internal) {
        if (node->header.usage != 0) {
          for (size_t i = 0; i <= node->header.usage; ++i) {
            destroy(node->children[i], cleaner);
          }
        }
      }
      for (uint16_t i = 0; i < node->header.usage; ++i) {
        cleaner(&node->header.storage[i]->data);
        free(node->header.storage[i]);
      }
      free(node);
    }

    // Adopt a child without overflow checking
    void adopt_no_overflow_internal(Node *l, Node *r, Cell *cell,
                                    uint16_t position) {
      adopt_no_overflow_leaf(cell, position);

      // also need to handle children pointers
      memmove(children + position + 1, children + position,
              (header.usage - position) * sizeof(void *));
      children[position] = l;
      l->header.parent = this;
      children[position + 1] = r;
      r->header.parent = this;
      for (size_t i = position; i < header.usage + 1; ++i) {
        children[i]->header.parent_index = i;
      }
      assert(children[header.usage] != nullptr);
    }

    void adopt_no_overflow_leaf(Cell *cell, uint16_t position) {
      memmove(&header.storage[position + 1], &header.storage[position],
              sizeof(void *) * (header.usage - position));
      header.storage[position] = cell;
      cell->node = this;
      header.usage++;
    }

    struct Slot {
      Node *node;
      size_t consecutive_full_nodes;
      size_t depth;
      LocationFlag location;
    };

    struct Coordinate {
      Node *node;
      LocationFlag index;
    };

    static Slot find_slot(const T &key, const Comparator &comp, Node *current) {
      size_t consecutive_full_nodes = 0;
      size_t depth = 0;
      while (true) {
        LocationFlag index = current->local_search(key, comp);
        if (index & FOUND)
          return {current, consecutive_full_nodes, depth, index};

        if (current->header.type == NodeType::Leaf)
          return {current, consecutive_full_nodes, depth, index};

        consecutive_full_nodes = (current->header.usage == 2 * B - 2)
                                     ? consecutive_full_nodes + 1
                                     : 0;

        current = current->children[index & FOUND_MASK];

        depth++;
      }
    }

    static Coordinate find(const T &key, const Comparator &comp,
                           Node *current) {
      if (current == nullptr) {
        return {nullptr, 0};
      }
      while (true) {
        LocationFlag index = current->local_search(key, comp);
        if (index & FOUND)
          return {current, index};

        if (current->header.type == NodeType::Leaf)
          return {current, index};
        current = current->children[index & FOUND_MASK];
      }
    }

    static Cell *insert_at(Slot slot, const T &data, Node *&root) {
      Node *current = slot.node;
      uint16_t index = slot.location;

      Cell *cell =
          static_cast<Cell *>(aligned_alloc(alignof(Cell), sizeof(Cell)));
      if (cell == nullptr) {
        return nullptr;
      }
      cell->data = data;

      // The leaf node does not split, simply insert it.
      if (likely(current->header.usage < 2 * B - 2)) {
        current->adopt_no_overflow_leaf(cell, index);
        return cell;
      }

      // memory for splitting current node
      Node *new_leaf = new_node(NodeType::Leaf);
      if (unlikely(new_leaf == nullptr)) {
        free(cell);
        return nullptr;
      }

      // memory for splitting root node
      Node *new_root = nullptr;
      if (unlikely(slot.depth == slot.consecutive_full_nodes)) {
        new_root = new_node(NodeType::Internal);
        if (new_root == nullptr) {
          free(cell);
          free(new_leaf);
          return nullptr;
        }
      }

      // memory for splitting consecutive internal nodes
      Node *new_internals = nullptr;
      if (unlikely(slot.consecutive_full_nodes > 0)) {
        new_internals = allocate_node_chain(slot.consecutive_full_nodes);
        if (new_internals == nullptr) {
          free(cell);
          free(new_root);
          free(new_leaf);
          return nullptr;
        }
      }

      // adopt the element at the leaf level
      current->adopt_no_overflow_leaf(cell, index);
      SplitResult split = current->split(new_leaf);

      while (new_internals != nullptr) {
        index = current->header.parent_index;
        current = current->header.parent;
        SplitResult previous = split;

        current->adopt_no_overflow_internal(split.left, split.right,
                                            split.pivot, index);
        Node *mem = new_internals;
        new_internals = mem->header.parent;
        split = current->split(mem);
      }

      if (likely(current->header.parent != nullptr)) {
        current->header.parent->adopt_no_overflow_internal(
            split.left, split.right, split.pivot, current->header.parent_index);
      } else {
        new_root->adopt_as_singleton(split.left, split.right, split.pivot);
        root = new_root;
      }

      return cell;
    }

    void borrow_left(Node *src) {
      // check(this, true);
      // check(src);
      memmove(&header.storage[1], &header.storage[0],
              header.usage * sizeof(void *));
      header.storage[0] =
          header.parent->header.storage[header.parent_index - 1];
      header.storage[0]->node = this;
      header.usage++;

      header.parent->header.storage[header.parent_index - 1] =
          src->header.storage[src->header.usage - 1];
      header.parent->header.storage[header.parent_index - 1]->node =
          header.parent;

      if (header.type == NodeType::Internal) {
        memmove(&children[1], &children[0], header.usage * sizeof(void *));
        children[0] = src->children[src->header.usage];
        children[0]->header.parent = this;
        for (uint16_t i = 0; i <= header.usage; ++i) {
          children[i]->header.parent_index = i;
        }
      }

      src->header.usage--;

      // check(this);
      // check(src);
    }

    void borrow_right(Node *src) {
      // check(this, true);
      // check(src);
      header.storage[header.usage] =
          header.parent->header.storage[header.parent_index];
      header.storage[header.usage]->node = this;
      header.usage++;

      if (header.type == NodeType::Internal) {
        children[header.usage] = src->children[0];
        children[header.usage]->header.parent = this;
        children[header.usage]->header.parent_index = header.usage;
      }

      header.parent->header.storage[header.parent_index] =
          src->header.storage[0];
      header.parent->header.storage[header.parent_index]->node = header.parent;

      memmove(&src->header.storage[0], &src->header.storage[1],
              (src->header.usage - 1) * sizeof(void *));

      if (header.type == NodeType::Internal) {
        memmove(&src->children[0], &src->children[1],
                src->header.usage * sizeof(void *));
        for (uint16_t i = 0; i < src->header.usage; ++i) {
          src->children[i]->header.parent_index = i;
        }
      }

      src->header.usage--;
      // check(this);
      // check(src);
    }

    static Node *merge(Node *left, Node *right, Node *&root) {
      assert(left->header.parent == right->header.parent);
      assert(left->header.parent_index == right->header.parent_index - 1);
      assert(left->header.usage + right->header.usage + 1 < 2 * B - 1);
      // check(left, true);
      // check(right, true);

      Node *parent = left->header.parent;

      // take the element from parent
      left->header.storage[left->header.usage] =
          parent->header.storage[left->header.parent_index];
      left->header.storage[left->header.usage]->node = left;
      left->header.usage++;

      // update parent
      memmove(&parent->header.storage[left->header.parent_index],
              &parent->header.storage[right->header.parent_index],
              (parent->header.usage - right->header.parent_index) *
                  sizeof(void *));
      memmove(&parent->children[right->header.parent_index],
              &parent->children[right->header.parent_index + 1],
              (parent->header.usage - right->header.parent_index) *
                  sizeof(void *));
      for (uint16_t i = left->header.parent_index; i < parent->header.usage;
           ++i) {
        parent->children[i]->header.parent_index = i;
      }
      parent->header.usage--;

      // copy data from right into left
      memcpy(&left->header.storage[left->header.usage],
             &right->header.storage[0], right->header.usage * sizeof(void *));
      for (uint16_t i = left->header.usage;
           i < left->header.usage + right->header.usage; ++i) {
        left->header.storage[i]->node = left;
      }
      if (left->header.type == NodeType::Internal) {
        memcpy(&left->children[left->header.usage], &right->children[0],
               (right->header.usage + 1) * sizeof(void *));
        for (uint16_t i = left->header.usage;
             i <= left->header.usage + right->header.usage; ++i) {
          left->children[i]->header.parent_index = i;
          left->children[i]->header.parent = left;
        }
      }
      left->header.usage += right->header.usage;

      // clean up right node
      free(right);

      if (unlikely(parent->header.usage == 0)) {
        free(parent);
        left->header.parent = nullptr;
        // check(left);
        root = left;
        return left;
      }

      // check(left);
      // check(parent, true);
      return parent;
    }

    static void fix_underflow(Node *node, Node *&root) {
      while (node->underflow()) {
        uint16_t parent_index = node->header.parent_index;
        Node *parent = node->header.parent;

        if (parent_index != 0) {
          Node *target = parent->children[parent_index - 1];
          if (target->header.usage > B - 1) {
            node->borrow_left(target);
            return;
          }
          node = merge(target, node, root);
        } else {
          Node *target = parent->children[parent_index + 1];
          if (target->header.usage > B - 1) {
            node->borrow_right(target);
            return;
          }
          node = merge(node, target, root);
        }
      };
    }

    bool underflow() const {
      return header.usage < B - 1 && header.parent != nullptr;
    }

    T erase(uint16_t index, Node *&root) {
      if (header.type == NodeType::Internal) {
        Coordinate pred = max(this);
        Cell *tmp = pred.node->header.storage[pred.index];
        pred.node->header.storage[pred.index] = header.storage[index];
        header.storage[index] = tmp;
        pred.node->header.storage[pred.index]->node = this;
        header.storage[index]->node = pred.node;
        return pred.node->erase(pred.index, root);
      }

      T result = at(index);
      free(header.storage[index]);
      header.usage--;
      memmove(&header.storage[index], &header.storage[index + 1],
              (header.usage - index) * sizeof(void *));

      fix_underflow(this, root);

      if (unlikely(root->header.usage == 0)) {
        free(root);
        root = nullptr;
      }

      return result;
    }

    static Coordinate max(Node *node) {
      while (node->header.type == NodeType::Internal) {
        node = node->children[node->header.usage];
      }
      return {node, static_cast<uint16_t>(node->header.usage - 1)};
    }

    static void check(Node *node, bool skip_underflow = false) {
      assert(skip_underflow || !node->underflow());
      assert(node->header.usage < 2 * B - 1);
      for (uint16_t i = 0; i < node->header.usage; ++i) {
        assert(node->header.storage[i]->node == node);
      }
      if (node->header.type == NodeType::Internal) {
        for (uint16_t i = 0; i <= node->header.usage; ++i) {
          assert(node->children[i]->header.parent_index == i);
        }
      }
    }
  };

  Node *root = nullptr;

  Cell *insert(const T &data, const Comparator &comp = {}) {
    if (unlikely(root == nullptr)) {
      Cell *cell =
          static_cast<Cell *>(aligned_alloc(alignof(Cell), sizeof(Cell)));
      cell->data = data;

      if (unlikely(cell == nullptr))
        return nullptr;

      root = Node::new_node(NodeType::Leaf);

      if (unlikely(root == nullptr)) {
        free(cell);
        return nullptr;
      }

      root->adopt_no_overflow_leaf(cell, 0);
      return cell;
    } else {
      auto slot = Node::find_slot(data, comp, root);
      if (slot.location & FOUND) {
        return slot.node->header.storage[slot.location & FOUND_MASK];
      }
      return Node::insert_at(slot, data, root);
    }
  }

  Cell *find(const T &data, const Comparator &comp = {}) {
    auto coord = Node::find(data, comp, root);
    if (coord.index & FOUND)
      return coord.node->header.storage[coord.index & FOUND_MASK];
    return nullptr;
  }

  T erase(const T &data, const Comparator &comp = {}) {
    auto coord = Node::find(data, comp, root);
    if (coord.index & FOUND) {
      T result = coord.node->erase(coord.index & FOUND_MASK, root);
      return result;
    }
    return {};
  }

  static uint16_t index_of(Cell *cell) {
    auto *node = cell->node;
    for (uint16_t i = 0; i < node->header.usage; ++i) {
      if (node->header.storage[i] == cell)
        return i;
    }
    return node->header.usage;
  }

  static void check_tree(Node *node) {
    if (node == nullptr)
      return;
    assert(!node->underflow());
    assert(node->header.usage < 2 * B - 1);
    for (uint16_t i = 0; i < node->header.usage; ++i) {
      assert(node->header.storage[i]->node == node);
    }
    if (node->header.type == NodeType::Internal) {
      for (uint16_t i = 0; i <= node->header.usage; ++i) {
        assert(node->children[i]->header.parent_index == i);
        check_tree(node->children[i]);
      }
    }
  }

  template <class Cleaner> void destroy(const Cleaner &cleaner) {
    Node::destroy(root, cleaner);
  }

  template <class Visitor> static void walk(Cell *cell, Visitor vistor) {
    Node *node = cell->node;
    uint16_t index = 0;
    while (node->header.storage[index] != cell) {
      index++;
    }
    walk(node, index, 0, vistor);
  }

  template <class Visitor>
  static void walk(Node *node, uint16_t index, int depth, Visitor visitor) {

    for (uint16_t i = index; i < node->header.usage; ++i) {
      int binary_depth = depth + (i - index);

      if (node->header.type == NodeType::Internal) {
        visitor(node->header.storage[i], preorder, binary_depth);
        walk(node->children[i], 0, binary_depth + 1, visitor);
        visitor(node->header.storage[i], postorder, binary_depth);
      } else if (i != node->header.usage - 1) {
        visitor(node->header.storage[i], preorder, binary_depth);
        visitor(node->header.storage[i], postorder, binary_depth);
      } else {
        visitor(node->header.storage[i], leaf, binary_depth);
      }
    }

    if (node->header.type == NodeType::Internal) {
      walk(node->children[node->header.usage], 0,
           depth + (node->header.usage - index), visitor);
    }

    for (int32_t i = node->header.usage - 1; i >= index; --i) {
      int binary_depth = depth + (i - index);
      if (node->header.type == NodeType::Internal ||
          i != node->header.usage - 1)
        visitor(node->header.storage[i], endorder, binary_depth);
    }
  }

  template <class Visitor> void walk(Visitor visitor) {
    walk(root, 0, 0, visitor);
  }
};
struct Comp {
  template <class A, class B> int operator()(const A &a, const B &b) const {
    return a - b;
  }
};

template <typename T> static inline void compiler_barrier(T &&var) {
  asm volatile("" : : "r,m"(var) : "memory");
}

void none(void *) {}
__attribute__((noinline)) void action(const void *a, VISIT b, int c) {
  compiler_barrier(a);
  compiler_barrier(b);
  compiler_barrier(c);
}
struct LibcTree {
  void *root;
  static int compare(const void *a, const void *b) {
    return reinterpret_cast<size_t>(a) - reinterpret_cast<size_t>(b);
  }
  void *insert(size_t i) {
    return tsearch(reinterpret_cast<void *>(i), &root, compare);
  }
  void *find(size_t i) {
    return tfind(reinterpret_cast<void *>(i), &root, compare);
  }
  void *erase(size_t i) {
    return tdelete(reinterpret_cast<void *>(i), &root, compare);
  }
  void walk(typeof(action) act) { twalk(root, act); }
  template <class Cleaner> void destroy(const Cleaner &cleaner) {
    tdestroy(root, cleaner);
  }
};

template <class Gen>
std::vector<size_t> gen_random_data(size_t count, Gen &gen) {
  std::vector<size_t> res(count);
  std::uniform_int_distribution<size_t> dist;
  for (auto &i : res) {
    i = dist(gen);
  }
  return res;
}

std::vector<size_t> gen_sequential_data(size_t count) {
  std::vector<size_t> res(count);
  size_t t = 0;
  for (auto &i : res) {
    i = t++;
  }
  return res;
}

std::vector<size_t> gen_reverse_data(size_t count) {
  std::vector<size_t> res(count);
  size_t t = count;
  for (auto &i : res) {
    i = t--;
  }
  return res;
}

template <class Func, class... Args> void measure(Func &&func, Args &&...args) {
  using namespace std::chrono;
  auto start = high_resolution_clock::now();
  func(std::forward<Args>(args)...);
  auto end = high_resolution_clock::now();
  rusage usage;
  getrusage(RUSAGE_SELF, &usage);
  std::cout << "{\n";
  std::cout << "\t\"time\" : "
            << duration_cast<nanoseconds>(end - start).count() << ",\n";
  std::cout << "\t\"rss\" : " << usage.ru_maxrss << "\n";
  std::cout << "}" << std::endl;
}

template <class Tree> void sequential_insert(size_t count) {
  auto data = gen_sequential_data(count);
  auto tree = Tree{};
  measure([data = std::move(data), &tree]() {
    for (auto i : data) {
      tree.insert(i);
    }
  });
  auto none = [](void *) {};
  tree.destroy(none);
}

template <class Tree> void walk_on_sequential(size_t count) {
  auto data = gen_sequential_data(count);
  auto tree = Tree{};
  for (auto i : data) {
    tree.insert(i);
  }
  measure([data = std::move(data), &tree]() { tree.walk(action); });
  auto none = [](void *) {};
  tree.destroy(none);
}

template <class Tree> void walk_on_random(size_t count, size_t seed) {
  std::default_random_engine eng(seed);
  auto data = gen_random_data(count, eng);
  auto tree = Tree{};
  for (auto i : data) {
    tree.insert(i);
  }
  measure([data = std::move(data), &tree]() { tree.walk(action); });
  auto none = [](void *) {};
  tree.destroy(none);
}

template <class Tree> void randomized_insert(size_t count, uint64_t seed) {
  std::default_random_engine eng(seed);
  auto data = gen_random_data(count, eng);
  auto tree = Tree{};
  measure([data = std::move(data), &tree]() {
    for (auto i : data) {
      tree.insert(i);
    }
  });
  auto none = [](void *) {};
  tree.destroy(none);
}

template <class Tree> void randomized_delete(size_t count, uint64_t seed) {
  std::default_random_engine eng(seed);
  auto data = gen_random_data(count, eng);
  auto tree = Tree{};
  for (auto i : data) {
    tree.insert(i);
  }
  std::shuffle(data.begin(), data.end(), eng);
  measure([data = std::move(data), &tree]() {
    for (auto i : data) {
      tree.erase(i);
    }
  });
  auto none = [](void *) {};
  tree.destroy(none);
}

template <class Tree> void sequential_delete(size_t count) {
  auto data = gen_sequential_data(count);
  auto tree = Tree{};
  for (auto i : data) {
    tree.insert(i);
  }
  measure([data = std::move(data), &tree]() {
    for (auto i : data) {
      tree.erase(i);
    }
  });
  auto none = [](void *) {};
  tree.destroy(none);
}

template <class Tree> void reverse_delete(size_t count) {
  auto data = gen_sequential_data(count);
  auto tree = Tree{};
  for (auto i : data) {
    tree.insert(i);
  }
  measure([data = std::move(data), &tree]() {
    for (auto i = data.rbegin(); i != data.rend(); ++i) {
      tree.erase(*i);
    }
  });
  auto none = [](void *) {};
  tree.destroy(none);
}

template <class Tree> void sequential_lookup(size_t count) {
  auto data = gen_sequential_data(count);
  auto tree = Tree{};
  for (auto i : data) {
    tree.insert(i);
  }
  measure([data = std::move(data), &tree]() {
    for (auto i : data) {
      compiler_barrier(tree.find(i));
    }
  });
  auto none = [](void *) {};
  tree.destroy(none);
}

template <class Tree> void randomized_lookup(size_t count, uint64_t seed) {
  std::default_random_engine eng(seed);
  auto data = gen_random_data(count, eng);
  auto tree = Tree{};
  for (auto i : data) {
    tree.insert(i);
  }
  std::shuffle(data.begin(), data.end(), eng);
  measure([data = std::move(data), &tree]() {
    for (auto i : data) {
      compiler_barrier(tree.find(i));
    }
  });
  auto none = [](void *) {};
  tree.destroy(none);
}

enum class TreeAction {
  Insert,
  Erase,
  Find,
};

using ActPair = std::pair<TreeAction, size_t>;

std::vector<ActPair> prepare_random(double insert, double erase, size_t count,
                                    size_t seed) {
  std::default_random_engine eng(seed);
  std::uniform_real_distribution<double> float_dist{0.0, 1.0};
  std::uniform_int_distribution<size_t> int_dist;
  std::vector<size_t> working_set;
  std::vector<ActPair> res;
  while (count--) {
    auto x = float_dist(eng);
    if (x < insert) {
      auto t = int_dist(eng);
      working_set.push_back(t);
      res.emplace_back(TreeAction::Insert, t);
    } else if (x < insert + erase) {
      size_t target;
      if (working_set.size() > 0 && eng() & 1) {
        auto iter = working_set.begin();
        std::advance(iter, int_dist(eng) % working_set.size());
        target = *iter;
        working_set.erase(iter);
      } else {
        target = int_dist(eng);
      }
      res.emplace_back(TreeAction::Erase, target);
    } else {
      size_t target;
      if (working_set.size() > 0 && eng() & 1) {
        auto iter = working_set.begin();
        std::advance(iter, int_dist(eng) % working_set.size());
        target = *iter;
      } else {
        target = int_dist(eng);
      }
      res.emplace_back(TreeAction::Find, target);
    }
  }
  return res;
}

template <class Tree>
void random_workload(double insert, double erase, size_t count, size_t seed) {
  auto data = prepare_random(insert, erase, count, seed);
  auto tree = Tree{};
  measure([data = std::move(data), &tree]() {
    for (auto [act, x] : data) {
      switch (act) {
      case TreeAction::Insert:
        tree.insert(x);
        break;
      case TreeAction::Erase:
        tree.erase(x);
        break;
      case TreeAction::Find:
        compiler_barrier(tree.find(x));
        break;
      }
    }
  });
  tree.destroy([](void *) {});
}

#define DESPATCH(F, ...)                                                       \
  {                                                                            \
    if (tree_type == "libc")                                                   \
      F<LibcTree>(__VA_ARGS__);                                                \
    else                                                                       \
      F<Tree>(__VA_ARGS__);                                                    \
  }

// ./btree test tree count seed insert_portion erase_portion
int main(int argc, char **argv) {
  using Tree = BTree<size_t, Comp, 6>;
  std::string_view test_type = argv[1];
  std::string_view tree_type = argv[2];
  size_t count = std::stoull(argv[3]);

  if (test_type == "seqins") {
    DESPATCH(sequential_insert, count);
    return 0;
  }

  if (test_type == "seqlookup") {
    DESPATCH(sequential_lookup, count);
    return 0;
  }

  if (test_type == "seqdel") {
    DESPATCH(sequential_delete, count);
    return 0;
  }

  if (test_type == "revdel") {
    DESPATCH(reverse_delete, count);
    return 0;
  }

  if (test_type == "randins") {
    uint64_t seed = std::stoull(argv[4]);
    DESPATCH(randomized_insert, count, seed);
    return 0;
  }

  if (test_type == "randlookup") {
    uint64_t seed = std::stoull(argv[4]);
    DESPATCH(randomized_lookup, count, seed);
    return 0;
  }

  if (test_type == "randdel") {
    uint64_t seed = std::stoull(argv[4]);
    DESPATCH(randomized_delete, count, seed);
    return 0;
  }

  if (test_type == "randwork") {
    uint64_t seed = std::stoull(argv[4]);
    double insert = std::stod(argv[5]);
    double erase = std::stod(argv[6]);
    DESPATCH(random_workload, insert, erase, count, seed);
    return 0;
  }

  if (test_type == "walkseq") {
    DESPATCH(walk_on_sequential, count);
    return 0;
  }

  if (test_type == "walkrand") {
    uint64_t seed = std::stoull(argv[4]);
    DESPATCH(walk_on_random, count, seed);
    return 0;
  }
}
