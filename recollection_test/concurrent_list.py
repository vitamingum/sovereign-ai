#!/usr/bin/env python3
"""
Thread-Safe Concurrent Linked List

A linked list optimized for concurrent access with:
- Lock-free reads for iteration
- Hand-over-hand locking for writes
- Minimal contention between readers and writers

Design Philosophy:
- Readers should never block (snapshot semantics)
- Writers only lock the nodes they're modifying
- Supports concurrent iteration during modification

Components:
- Node: Data container with per-node lock
- ConcurrentLinkedList: Main list with hand-over-hand protocol
- ConcurrentQueue: FIFO built on the list
- ConcurrentStack: LIFO built on the list
"""

from __future__ import annotations
import threading
from dataclasses import dataclass, field
from typing import TypeVar, Generic, Optional, Iterator, Callable, List
from contextlib import contextmanager
import time

T = TypeVar('T')


class AtomicCounter:
    """Thread-safe counter for version tracking."""
    
    def __init__(self, initial: int = 0):
        self._value = initial
        self._lock = threading.Lock()
    
    def increment(self) -> int:
        with self._lock:
            self._value += 1
            return self._value
    
    def get(self) -> int:
        return self._value


class ConcurrentModificationError(Exception):
    """Raised when list is modified during iteration."""
    pass


@dataclass
class Node(Generic[T]):
    """
    List node with per-node locking.
    
    The 'marked' flag indicates logical deletion - the node
    is no longer part of the list but may still be referenced
    by iterators.
    """
    data: T
    next: Optional[Node[T]] = None
    marked: bool = False
    lock: threading.Lock = field(default_factory=threading.Lock)
    _id: int = 0  # For debugging
    
    def __repr__(self):
        return f"Node({self.data}, id={self._id}, marked={self.marked})"


class ConcurrentLinkedList(Generic[T]):
    """
    Thread-safe linked list with hand-over-hand locking.
    
    Locking Protocol:
    -----------------
    For traversal with modification (insert/remove):
    1. Lock the predecessor node
    2. Lock the current node  
    3. Validate: pred.next == curr (no concurrent modification)
    4. Perform operation
    5. Release locks in reverse order
    
    For read-only traversal:
    - No locks needed - follow next pointers
    - Check 'marked' flag to skip deleted nodes
    - Version counter detects concurrent modifications
    
    Usage:
        lst = ConcurrentLinkedList[int]()
        lst.append(1)
        lst.append(2)
        lst.prepend(0)
        
        # Thread-safe iteration
        for item in lst:
            print(item)
        
        # Conditional removal
        lst.remove_if(lambda x: x % 2 == 0)
    """
    
    def __init__(self):
        # Sentinel head node - never removed, simplifies edge cases
        self._head: Node[T] = Node(data=None, _id=-1)  # type: ignore
        self._size = AtomicCounter(0)
        self._version = AtomicCounter(0)
        self._node_counter = AtomicCounter(0)
    
    def _next_node_id(self) -> int:
        return self._node_counter.increment()
    
    def _increment_size(self):
        self._size.increment()
    
    def _decrement_size(self):
        with self._size._lock:
            self._size._value -= 1
    
    def __len__(self) -> int:
        return max(0, self._size.get())
    
    def __iter__(self) -> Iterator[T]:
        """
        Iterate over list elements.
        
        Creates a snapshot view - modifications during iteration
        will raise ConcurrentModificationError.
        """
        return ListIterator(self)
    
    def __contains__(self, value: T) -> bool:
        """Check if value exists in list."""
        return self.find(lambda x: x == value) is not None
    
    # ========== Read Operations (Lock-Free) ==========
    
    def head(self) -> Optional[T]:
        """Get first element without removing."""
        curr = self._head.next
        while curr is not None:
            if not curr.marked:
                return curr.data
            curr = curr.next
        return None
    
    def tail(self) -> Optional[T]:
        """Get last element without removing."""
        result = None
        curr = self._head.next
        while curr is not None:
            if not curr.marked:
                result = curr.data
            curr = curr.next
        return result
    
    def find(self, predicate: Callable[[T], bool]) -> Optional[T]:
        """Find first element matching predicate."""
        curr = self._head.next
        while curr is not None:
            if not curr.marked and predicate(curr.data):
                return curr.data
            curr = curr.next
        return None
    
    def find_all(self, predicate: Callable[[T], bool]) -> List[T]:
        """Find all elements matching predicate."""
        results = []
        curr = self._head.next
        while curr is not None:
            if not curr.marked and predicate(curr.data):
                results.append(curr.data)
            curr = curr.next
        return results
    
    def to_list(self) -> List[T]:
        """Convert to regular Python list (snapshot)."""
        return [item for item in self]
    
    # ========== Write Operations (Hand-over-Hand Locking) ==========
    
    def append(self, value: T) -> None:
        """
        Add value to end of list.
        
        Traverses to find tail, then inserts.
        """
        new_node = Node(
            data=value,
            _id=self._next_node_id()
        )
        
        # Find the tail with hand-over-hand
        pred = self._head
        pred.lock.acquire()
        
        try:
            while pred.next is not None:
                curr = pred.next
                curr.lock.acquire()
                pred.lock.release()
                pred = curr
            
            # pred is now the last node, and we hold its lock
            pred.next = new_node
            self._increment_size()
            self._version.increment()
        finally:
            pred.lock.release()
    
    def prepend(self, value: T) -> None:
        """
        Add value to beginning of list.
        
        Only needs to lock the head sentinel.
        """
        new_node = Node(
            data=value,
            _id=self._next_node_id()
        )
        
        self._head.lock.acquire()
        try:
            new_node.next = self._head.next
            self._head.next = new_node
            self._increment_size()
            self._version.increment()
        finally:
            self._head.lock.release()
    
    def insert_after(self, target: T, value: T) -> bool:
        """
        Insert value after first occurrence of target.
        
        Returns True if target was found and value inserted.
        """
        new_node = Node(
            data=value,
            _id=self._next_node_id()
        )
        
        pred = self._head
        pred.lock.acquire()
        
        try:
            curr = pred.next
            
            while curr is not None:
                curr.lock.acquire()
                
                if not curr.marked and curr.data == target:
                    # Found target, insert after it
                    new_node.next = curr.next
                    curr.next = new_node
                    self._increment_size()
                    self._version.increment()
                    pred.lock.release()
                    curr.lock.release()
                    return True
                
                # Move forward
                pred.lock.release()
                pred = curr
                curr = curr.next
            
            return False
        finally:
            # Release any held lock
            if pred.lock.locked():
                pred.lock.release()
    
    def remove(self, value: T) -> bool:
        """
        Remove first occurrence of value.
        
        Uses hand-over-hand locking:
        1. Lock predecessor
        2. Lock current (the node to remove)
        3. Validate pred.next == curr
        4. Mark curr as deleted
        5. Update pred.next to skip curr
        6. Release locks
        
        Returns True if value was found and removed.
        """
        pred = self._head
        pred.lock.acquire()
        
        try:
            curr = pred.next
            
            while curr is not None:
                curr.lock.acquire()
                
                # Validate the link is still intact
                if pred.next != curr:
                    # Another thread modified pred.next, retry
                    curr.lock.release()
                    pred.lock.release()
                    return self.remove(value)
                
                if not curr.marked and curr.data == value:
                    # Found it - mark and unlink
                    curr.marked = True
                    pred.next = curr.next
                    
                    self._decrement_size()
                    self._version.increment()
                    
                    # Release locks
                    pred.lock.release()
                    curr.lock.release()
                    return True
                
                # Move forward: release pred, keep curr as new pred
                pred.lock.release()
                pred = curr
                curr = curr.next
            
            return False
        finally:
            # Ensure pred lock released if we exit loop without finding
            if pred.lock.locked():
                pred.lock.release()
    
    def remove_if(self, predicate: Callable[[T], bool]) -> int:
        """
        Remove all elements matching predicate.
        
        Returns count of removed elements.
        """
        removed_count = 0
        
        pred = self._head
        pred.lock.acquire()
        
        try:
            curr = pred.next
            
            while curr is not None:
                curr.lock.acquire()
                
                # Validate link
                if pred.next != curr:
                    curr.lock.release()
                    # Lost our position, restart
                    pred.lock.release()
                    return removed_count + self.remove_if(predicate)
                
                if not curr.marked and predicate(curr.data):
                    # Remove this node
                    curr.marked = True
                    next_node = curr.next
                    pred.next = next_node
                    
                    self._decrement_size()
                    self._version.increment()
                    removed_count += 1
                    
                    # Move to next without changing pred
                    curr.lock.release()
                    curr = next_node
                else:
                    # Move forward
                    pred.lock.release()
                    pred = curr
                    curr = curr.next
            
            return removed_count
        finally:
            if pred.lock.locked():
                pred.lock.release()
    
    def clear(self) -> None:
        """Remove all elements."""
        self._head.lock.acquire()
        try:
            # Mark all nodes as deleted
            curr = self._head.next
            while curr is not None:
                curr.marked = True
                curr = curr.next
            
            self._head.next = None
            self._size._value = 0
            self._version.increment()
        finally:
            self._head.lock.release()
    
    def insert_sorted(self, value: T, key: Callable[[T], any] = None) -> None:
        """
        Insert value in sorted position.
        
        Assumes list is already sorted by key function.
        """
        if key is None:
            key = lambda x: x
        
        new_node = Node(
            data=value,
            _id=self._next_node_id()
        )
        new_key = key(value)
        
        pred = self._head
        pred.lock.acquire()
        
        try:
            curr = pred.next
            
            while curr is not None:
                curr.lock.acquire()
                
                # Validate
                if pred.next != curr:
                    curr.lock.release()
                    pred.lock.release()
                    return self.insert_sorted(value, key)
                
                if not curr.marked and key(curr.data) > new_key:
                    # Insert before curr (after pred)
                    new_node.next = curr
                    pred.next = new_node
                    self._increment_size()
                    self._version.increment()
                    curr.lock.release()
                    pred.lock.release()
                    return
                
                pred.lock.release()
                pred = curr
                curr = curr.next
            
            # Append at end
            pred.next = new_node
            self._increment_size()
            self._version.increment()
        finally:
            if pred.lock.locked():
                pred.lock.release()


class ListIterator(Generic[T]):
    """
    Snapshot iterator for ConcurrentLinkedList.
    
    Records version at creation time and detects
    modifications during iteration.
    """
    
    def __init__(self, lst: ConcurrentLinkedList[T]):
        self._list = lst
        self._version_at_start = lst._version.get()
        self._current = lst._head.next
    
    def __iter__(self) -> Iterator[T]:
        return self
    
    def __next__(self) -> T:
        # Check for concurrent modification
        if self._list._version.get() != self._version_at_start:
            raise ConcurrentModificationError(
                "List was modified during iteration"
            )
        
        # Skip marked (deleted) nodes
        while self._current is not None:
            if not self._current.marked:
                data = self._current.data
                self._current = self._current.next
                return data
            self._current = self._current.next
        
        raise StopIteration


class ConcurrentQueue(Generic[T]):
    """
    Thread-safe FIFO queue built on ConcurrentLinkedList.
    
    Optimized for producer-consumer patterns.
    """
    
    def __init__(self):
        self._list = ConcurrentLinkedList[T]()
        self._head_lock = threading.Lock()
    
    def enqueue(self, value: T) -> None:
        """Add item to back of queue."""
        self._list.append(value)
    
    def dequeue(self) -> Optional[T]:
        """
        Remove and return item from front of queue.
        
        Returns None if queue is empty.
        """
        with self._head_lock:
            head_val = self._list.head()
            if head_val is not None:
                self._list.remove(head_val)
                return head_val
            return None
    
    def peek(self) -> Optional[T]:
        """View front item without removing."""
        return self._list.head()
    
    def __len__(self) -> int:
        return len(self._list)
    
    def is_empty(self) -> bool:
        return len(self._list) == 0


class ConcurrentStack(Generic[T]):
    """
    Thread-safe LIFO stack built on ConcurrentLinkedList.
    """
    
    def __init__(self):
        self._list = ConcurrentLinkedList[T]()
    
    def push(self, value: T) -> None:
        """Push item onto stack."""
        self._list.prepend(value)
    
    def pop(self) -> Optional[T]:
        """
        Pop and return top item.
        
        Returns None if stack is empty.
        """
        head_val = self._list.head()
        if head_val is not None:
            self._list.remove(head_val)
            return head_val
        return None
    
    def peek(self) -> Optional[T]:
        """View top item without removing."""
        return self._list.head()
    
    def __len__(self) -> int:
        return len(self._list)
    
    def is_empty(self) -> bool:
        return len(self._list) == 0


if __name__ == "__main__":
    # Quick demo
    print("ConcurrentLinkedList Demo")
    print("=" * 40)
    
    lst = ConcurrentLinkedList[int]()
    
    # Basic operations
    for i in range(5):
        lst.append(i)
    print(f"After appending 0-4: {lst.to_list()}")
    
    lst.prepend(-1)
    print(f"After prepending -1: {lst.to_list()}")
    
    lst.remove(2)
    print(f"After removing 2: {lst.to_list()}")
    
    lst.insert_after(3, 2.5)
    print(f"After inserting 2.5 after 3: {lst.to_list()}")
    
    print(f"\nFind even numbers: {lst.find_all(lambda x: isinstance(x, int) and x % 2 == 0)}")
    
    # Queue demo
    print("\nConcurrentQueue Demo")
    print("=" * 40)
    q = ConcurrentQueue[str]()
    q.enqueue("first")
    q.enqueue("second")
    q.enqueue("third")
    print(f"Dequeue: {q.dequeue()}")
    print(f"Dequeue: {q.dequeue()}")
    print(f"Peek: {q.peek()}")
