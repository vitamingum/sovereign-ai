#!/usr/bin/env python3
"""
Tests for ConcurrentLinkedList

Tests cover:
1. Basic single-threaded operations
2. Concurrent read/write correctness
3. Edge cases
"""

import unittest
import threading
import time
import random
from concurrent_list import (
    ConcurrentLinkedList, 
    ConcurrentQueue, 
    ConcurrentStack,
    ConcurrentModificationError
)


class TestBasicOperations(unittest.TestCase):
    """Single-threaded correctness tests."""
    
    def test_empty_list(self):
        """Fresh list should be empty."""
        lst = ConcurrentLinkedList()
        self.assertEqual(len(lst), 0)
        self.assertEqual(lst.to_list(), [])
        self.assertIsNone(lst.head())
    
    def test_append(self):
        """Append adds to end."""
        lst = ConcurrentLinkedList[int]()
        lst.append(1)
        lst.append(2)
        lst.append(3)
        self.assertEqual(lst.to_list(), [1, 2, 3])
        self.assertEqual(len(lst), 3)
    
    def test_prepend(self):
        """Prepend adds to beginning."""
        lst = ConcurrentLinkedList[int]()
        lst.prepend(1)
        lst.prepend(2)
        lst.prepend(3)
        self.assertEqual(lst.to_list(), [3, 2, 1])
    
    def test_remove_existing(self):
        """Remove existing element."""
        lst = ConcurrentLinkedList[int]()
        lst.append(1)
        lst.append(2)
        lst.append(3)
        
        result = lst.remove(2)
        self.assertTrue(result)
        self.assertEqual(lst.to_list(), [1, 3])
    
    def test_remove_nonexistent(self):
        """Remove returns False for missing element."""
        lst = ConcurrentLinkedList[int]()
        lst.append(1)
        lst.append(2)
        
        result = lst.remove(999)
        self.assertFalse(result)
        self.assertEqual(lst.to_list(), [1, 2])
    
    def test_remove_head(self):
        """Remove first element."""
        lst = ConcurrentLinkedList[int]()
        lst.append(1)
        lst.append(2)
        lst.append(3)
        
        lst.remove(1)
        self.assertEqual(lst.to_list(), [2, 3])
    
    def test_remove_tail(self):
        """Remove last element."""
        lst = ConcurrentLinkedList[int]()
        lst.append(1)
        lst.append(2)
        lst.append(3)
        
        lst.remove(3)
        self.assertEqual(lst.to_list(), [1, 2])
    
    def test_find(self):
        """Find returns matching element."""
        lst = ConcurrentLinkedList[int]()
        for i in range(10):
            lst.append(i)
        
        result = lst.find(lambda x: x > 5)
        self.assertEqual(result, 6)
    
    def test_find_all(self):
        """Find all matching elements."""
        lst = ConcurrentLinkedList[int]()
        for i in range(10):
            lst.append(i)
        
        evens = lst.find_all(lambda x: x % 2 == 0)
        self.assertEqual(evens, [0, 2, 4, 6, 8])
    
    def test_find_all_consecutive(self):
        """Find all should work with consecutive matches."""
        lst = ConcurrentLinkedList[int]()
        for i in range(10):
            lst.append(i)
        
        # All items >= 5 should be found (consecutive matches)
        result = lst.find_all(lambda x: x >= 5)
        self.assertEqual(result, [5, 6, 7, 8, 9])
    
    def test_contains(self):
        """In operator works."""
        lst = ConcurrentLinkedList[int]()
        lst.append(1)
        lst.append(2)
        
        self.assertTrue(1 in lst)
        self.assertFalse(999 in lst)
    
    def test_insert_after(self):
        """Insert after specific element."""
        lst = ConcurrentLinkedList[int]()
        lst.append(1)
        lst.append(3)
        
        lst.insert_after(1, 2)
        self.assertEqual(lst.to_list(), [1, 2, 3])
    
    def test_remove_if(self):
        """Remove elements by predicate."""
        lst = ConcurrentLinkedList[int]()
        for i in range(10):
            lst.append(i)
        
        removed = lst.remove_if(lambda x: x % 2 == 0)
        self.assertEqual(removed, 5)
        self.assertEqual(lst.to_list(), [1, 3, 5, 7, 9])
    
    def test_clear(self):
        """Clear removes all elements."""
        lst = ConcurrentLinkedList[int]()
        for i in range(5):
            lst.append(i)
        
        lst.clear()
        self.assertEqual(len(lst), 0)
        self.assertEqual(lst.to_list(), [])
    
    def test_insert_sorted(self):
        """Insert maintains sort order."""
        lst = ConcurrentLinkedList[int]()
        lst.insert_sorted(5)
        lst.insert_sorted(3)
        lst.insert_sorted(7)
        lst.insert_sorted(1)
        lst.insert_sorted(9)
        
        self.assertEqual(lst.to_list(), [1, 3, 5, 7, 9])


class TestIteration(unittest.TestCase):
    """Iterator behavior tests."""
    
    def test_basic_iteration(self):
        """Can iterate over elements."""
        lst = ConcurrentLinkedList[int]()
        for i in range(5):
            lst.append(i)
        
        items = list(lst)
        self.assertEqual(items, [0, 1, 2, 3, 4])
    
    def test_iteration_skips_marked(self):
        """Iterator skips logically deleted nodes."""
        lst = ConcurrentLinkedList[int]()
        for i in range(5):
            lst.append(i)
        
        lst.remove(2)
        items = list(lst)
        self.assertEqual(items, [0, 1, 3, 4])


class TestQueue(unittest.TestCase):
    """ConcurrentQueue tests."""
    
    def test_fifo_order(self):
        """Queue maintains FIFO order."""
        q = ConcurrentQueue[int]()
        q.enqueue(1)
        q.enqueue(2)
        q.enqueue(3)
        
        self.assertEqual(q.dequeue(), 1)
        self.assertEqual(q.dequeue(), 2)
        self.assertEqual(q.dequeue(), 3)
        self.assertIsNone(q.dequeue())
    
    def test_peek(self):
        """Peek doesn't remove."""
        q = ConcurrentQueue[int]()
        q.enqueue(1)
        
        self.assertEqual(q.peek(), 1)
        self.assertEqual(q.peek(), 1)
        self.assertEqual(len(q), 1)


class TestStack(unittest.TestCase):
    """ConcurrentStack tests."""
    
    def test_lifo_order(self):
        """Stack maintains LIFO order."""
        s = ConcurrentStack[int]()
        s.push(1)
        s.push(2)
        s.push(3)
        
        self.assertEqual(s.pop(), 3)
        self.assertEqual(s.pop(), 2)
        self.assertEqual(s.pop(), 1)
        self.assertIsNone(s.pop())


class TestConcurrentOperations(unittest.TestCase):
    """Multi-threaded correctness tests."""
    
    def test_rapid_remove_same_region(self):
        """Rapid removes in same list region should be consistent."""
        # This test targets hand-over-hand locking correctness
        for _ in range(10):  # Run multiple times to catch races
            lst = ConcurrentLinkedList[int]()
            for i in range(100):
                lst.append(i)
            
            errors = []
            removed_by = {}  # track who removed what
            lock = threading.Lock()
            
            def remover(tid, targets):
                for val in targets:
                    try:
                        if lst.remove(val):
                            with lock:
                                if val in removed_by:
                                    errors.append(f"Double remove: {val} by {tid} and {removed_by[val]}")
                                removed_by[val] = tid
                    except Exception as e:
                        errors.append(f"Thread {tid} error: {e}")
            
            # Multiple threads targeting overlapping ranges
            t1 = threading.Thread(target=remover, args=(1, range(0, 50)))
            t2 = threading.Thread(target=remover, args=(2, range(25, 75)))
            t3 = threading.Thread(target=remover, args=(3, range(50, 100)))
            
            t1.start(); t2.start(); t3.start()
            t1.join(); t2.join(); t3.join()
            
            if errors:
                self.fail(f"Errors: {errors}")
            
            # Every item 0-99 should be removed exactly once
            remaining = set(lst.to_list())
            removed = set(removed_by.keys())
            all_items = set(range(100))
            
            self.assertEqual(remaining | removed, all_items, 
                f"Missing items: {all_items - (remaining | removed)}")
            self.assertEqual(remaining & removed, set(),
                f"Items both in list and removed: {remaining & removed}")
    
    def test_concurrent_appends(self):
        """Multiple threads appending shouldn't lose data."""
        lst = ConcurrentLinkedList[int]()
        num_threads = 4
        items_per_thread = 50
        
        def append_items(thread_id):
            for i in range(items_per_thread):
                lst.append(thread_id * 1000 + i)
        
        threads = [
            threading.Thread(target=append_items, args=(t,))
            for t in range(num_threads)
        ]
        
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        
        self.assertEqual(len(lst), num_threads * items_per_thread)
    
    def test_concurrent_removes(self):
        """Concurrent removes don't corrupt list."""
        lst = ConcurrentLinkedList[int]()
        for i in range(100):
            lst.append(i)
        
        removed = []
        lock = threading.Lock()
        
        def remove_items(start, step):
            for i in range(start, 100, step):
                if lst.remove(i):
                    with lock:
                        removed.append(i)
        
        threads = [
            threading.Thread(target=remove_items, args=(t, 4))
            for t in range(4)
        ]
        
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        
        # All items should be removed exactly once
        remaining = lst.to_list()
        self.assertEqual(len(removed) + len(remaining), 100)
        self.assertEqual(len(set(removed)), len(removed))  # No duplicates
    
    def test_concurrent_append_and_remove(self):
        """Appends and removes running concurrently."""
        lst = ConcurrentLinkedList[int]()
        for i in range(50):
            lst.append(i)
        
        errors = []
        
        def appender():
            try:
                for i in range(50, 100):
                    lst.append(i)
                    time.sleep(0.001)
            except Exception as e:
                errors.append(str(e))
        
        def remover():
            try:
                for i in range(25):
                    lst.remove(i)
                    time.sleep(0.001)
            except Exception as e:
                errors.append(str(e))
        
        t1 = threading.Thread(target=appender)
        t2 = threading.Thread(target=remover)
        
        t1.start()
        t2.start()
        t1.join(timeout=5)
        t2.join(timeout=5)
        
        self.assertEqual(errors, [], f"Errors during concurrent ops: {errors}")
        
        # List should be consistent
        items = lst.to_list()
        self.assertEqual(len(items), len(set(items)))  # No duplicates
    
    def test_producer_consumer_queue(self):
        """Queue handles producer-consumer pattern."""
        q = ConcurrentQueue[int]()
        produced = []
        consumed = []
        prod_lock = threading.Lock()
        cons_lock = threading.Lock()
        done = threading.Event()
        
        def producer(pid):
            for i in range(25):
                val = pid * 100 + i
                q.enqueue(val)
                with prod_lock:
                    produced.append(val)
                time.sleep(0.001)
        
        def consumer():
            while not done.is_set() or len(q) > 0:
                val = q.dequeue()
                if val is not None:
                    with cons_lock:
                        consumed.append(val)
                else:
                    time.sleep(0.005)
        
        producers = [threading.Thread(target=producer, args=(i,)) for i in range(4)]
        consumers = [threading.Thread(target=consumer) for _ in range(2)]
        
        for t in producers + consumers:
            t.start()
        
        for t in producers:
            t.join()
        
        # Signal consumers to finish
        time.sleep(0.1)
        done.set()
        
        for t in consumers:
            t.join(timeout=2)
        
        # Drain any remaining
        while True:
            v = q.dequeue()
            if v is None:
                break
            consumed.append(v)
        
        self.assertEqual(len(produced), 100)
        self.assertEqual(sorted(produced), sorted(consumed))


if __name__ == "__main__":
    unittest.main(verbosity=2)
