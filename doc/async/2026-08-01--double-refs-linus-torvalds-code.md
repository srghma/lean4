1. http://felipec.github.io/good-taste/parts/1.html
2. http://felipec.github.io/good-taste/parts/2.html
3. http://felipec.github.io/good-taste/parts/3.html

<details>
  <summary>bench.cpp</summary>
  
```cpp
#include <benchmark/benchmark.h>
#include <vector>
#include <forward_list>
#include <list>
#include <cstddef>

// ======================================================
// Compiler detection (quick-bench lets you pick GCC or
// Clang from the dropdown — this labels each run so you
// can tell which stdlib/compiler produced which numbers)
// ======================================================
#if defined(__clang__)
    #define COMPILER_NAME "Clang"
#elif defined(__GNUC__)
    #define COMPILER_NAME "GCC"
#else
    #define COMPILER_NAME "Unknown"
#endif

// ======================================================
// Struct 1 (Part 1): used by initial-slow and initial-fast
// ======================================================
struct node {
    int value;
    node *next;
};

void remove_list_entry_slow(node **head, node *entry)
{
    node *prev = nullptr, *walk;
    walk = *head;
    while (walk != entry) {
        prev = walk;
        walk = walk->next;
    }
    if (!prev)
        *head = entry->next;
    else
        prev->next = entry->next;
}

void remove_list_entry_fast(node **head, node *entry)
{
    node **p = head;
    while (*p != entry)
        p = &(*p)->next;
    *p = entry->next;
}

// ======================================================
// Struct 2 (Part 2): GLib-style GSList
// ======================================================
struct node_data {
    int value;
};

struct GSList {
    void *data;
    GSList *next;
};

GSList *g_slist_remove_link(GSList *list, GSList *link)
{
    GSList **p;
    for (p = &list; *p; p = &(*p)->next) {
        if (*p != link) continue;
        *p = (*p)->next;
        break;
    }
    return list;
}

// ======================================================
// Struct 3 (Part 3): Linux-style embedded llist_node
// ======================================================
struct llist_node {
    llist_node *next;
};

struct llist_head {
    llist_node *first;
};

struct lnode {
    llist_node node;
    int value;
};

#define llist_for_each(pos, n) for ((pos) = (n); pos; (pos) = (pos)->next)

void llist_del(llist_head *list, llist_node *entry)
{
    llist_node *p;
    llist_for_each(p, (llist_node *)list) {
        if (p->next != entry) continue;
        p->next = entry->next;
        return;
    }
}

// ======================================================
// Benchmarks: build an N-node list, remove the middle
// node, rebuild every iteration (setup excluded via
// PauseTiming/ResumeTiming so we only measure removal).
// ======================================================
static const int N = 1000;

static void BM_InitialSlow(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::vector<node> nodes(N);
        for (int i = 0; i < N; i++) {
            nodes[i].value = i;
            nodes[i].next = (i + 1 < N) ? &nodes[i + 1] : nullptr;
        }
        node *head = &nodes[0];
        node *target = &nodes[N / 2];
        state.ResumeTiming();

        remove_list_entry_slow(&head, target);
        benchmark::DoNotOptimize(head);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_InitialSlow);

static void BM_InitialFast(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::vector<node> nodes(N);
        for (int i = 0; i < N; i++) {
            nodes[i].value = i;
            nodes[i].next = (i + 1 < N) ? &nodes[i + 1] : nullptr;
        }
        node *head = &nodes[0];
        node *target = &nodes[N / 2];
        state.ResumeTiming();

        remove_list_entry_fast(&head, target);
        benchmark::DoNotOptimize(head);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_InitialFast);

static void BM_GLib(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::vector<node_data> data(N);
        std::vector<GSList> links(N);
        for (int i = 0; i < N; i++) {
            data[i].value = i;
            links[i].data = &data[i];
            links[i].next = (i + 1 < N) ? &links[i + 1] : nullptr;
        }
        GSList *list = &links[0];
        GSList *target = &links[N / 2];
        state.ResumeTiming();

        list = g_slist_remove_link(list, target);
        benchmark::DoNotOptimize(list);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_GLib);

static void BM_Linux(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::vector<lnode> nodes(N);
        for (int i = 0; i < N; i++) {
            nodes[i].value = i;
            nodes[i].node.next = (i + 1 < N) ? &nodes[i + 1].node : nullptr;
        }
        llist_head list_head = { &nodes[0].node };
        llist_node *target = &nodes[N / 2].node;
        state.ResumeTiming();

        llist_del(&list_head, target);
        benchmark::DoNotOptimize(list_head.first);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_Linux);

// ======================================================
// std::forward_list (singly linked, C++11 stdlib)
// No O(1) erase-by-iterator exists for forward_list, so
// like the custom singly-linked versions above, we must
// traverse and track the predecessor ourselves.
// ======================================================
static void BM_StdForwardList(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::forward_list<int> flist;
        {
            auto it = flist.before_begin();
            for (int i = 0; i < N; i++)
                it = flist.insert_after(it, i);
        }
        int target_value = N / 2;
        state.ResumeTiming();

        auto prev = flist.before_begin();
        for (auto it = flist.begin(); it != flist.end(); ++it) {
            if (*it == target_value) {
                flist.erase_after(prev);
                break;
            }
            prev = it;
        }
        benchmark::DoNotOptimize(flist);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_StdForwardList);

// ======================================================
// std::list (doubly linked)
// Given an iterator to the target (as if you already held
// a pointer to the node, like the custom versions' `entry`
// argument), erase is O(1) — no predecessor traversal
// needed. This is the whole point of a prev pointer.
// ======================================================
static void BM_StdList(benchmark::State& state) {
    for (auto _ : state) {
        state.PauseTiming();
        std::list<int> dlist;
        for (int i = 0; i < N; i++)
            dlist.push_back(i);
        auto target_it = dlist.begin();
        std::advance(target_it, N / 2);
        state.ResumeTiming();

        dlist.erase(target_it);
        benchmark::DoNotOptimize(dlist);
    }
    state.SetLabel(COMPILER_NAME);
}
BENCHMARK(BM_StdList);
```

</details>

- BM_initialSlow 6,328.464
- BM_initialFast 6,419.343
- BM_GLib 6,114.761
- BM_Linux 6,019.624

<details>
  <summary>test2.cpp</summary>

```cpp
#include <iostream>
#include <string_view>

struct node {
  int value{0};        // Fix S836: Default initialization prevents garbage values
  node *next{nullptr};  // Fix S836: Default initialization prevents garbage values
};

// --- CONFIGURATION SWITCH ---
// Fix S5028: Replaced #define with constexpr
constexpr bool USE_FAST = true;

// Implementation 1: Slow
void remove_list_entry_slow(node **head, node *entry) {
  node *prev = nullptr; // Fix S1659: Dedicated statement for each identifier
  node *walk = *head;   // Fix S1659: Dedicated statement for each identifier

  while (walk != entry) {
    prev = walk;
    walk = walk->next;
  }
  if (!prev)
    *head = entry->next;
  else
    prev->next = entry->next;
}

// Implementation 2: Fast
void remove_list_entry_fast(node **head, node *entry) {
  node **p = head;
  while (*p != entry)
    p = &(*p)->next;
  *p = entry->next;
}

// Fix S5028: Replaced macro selection with constexpr string and if constexpr
constexpr std::string_view MODE_STRING = USE_FAST ? "FAST (Indirect Pointer)" : "SLOW (Prev Pointer)";

inline void remove_list_entry(node **head, node *entry) {
  if constexpr (USE_FAST) {
    remove_list_entry_fast(head, entry);
  } else {
    remove_list_entry_slow(head, entry);
  }
}

// Helper: Print the list
void print_list(const node *head) {
  for (const node *curr = head; curr != nullptr; curr = curr->next) {
    std::cout << curr->value << " -> ";
  }
  std::cout << "nullptr\n";
}

// Helper: Append to list in O(1) time (Zero loops, Zero 'if' statements)
void append(node **&tail, int val) {
  auto *new_node = new node{val, nullptr}; // NOSONAR (cpp:S5025) - Intentional raw heap allocation
  *tail = new_node;       // Link new node into the list
  tail = &new_node->next; // Move tail pointer to point to the new node's 'next' field
}

int main() {
  std::cout << "=== Running with: " << MODE_STRING << " ===\n\n";

  node *head = nullptr;
  node **tail = &head; // 'tail' points to where the next node should be inserted

  // All appends are now O(1) instantaneous calls!
  append(tail, 10);
  append(tail, 20);
  append(tail, 30);
  append(tail, 40);
  append(tail, 50);

  std::cout << "Original list:\n";
  print_list(head);

  // 1. Remove FRONT
  node *front = head;
  remove_list_entry(&head, front);
  delete front; // NOSONAR (cpp:S5025) - Intentional manual memory management

  std::cout << "\nAfter removing FRONT (10):\n";
  print_list(head);

  // 2. Remove END
  node *end = head;
  while (end->next != nullptr) {
    end = end->next;
  }
  remove_list_entry(&head, end);
  delete end; // NOSONAR (cpp:S5025) - Intentional manual memory management

  std::cout << "\nAfter removing END (50):\n";
  print_list(head);

  // Clean remaining list memory
  while (head != nullptr) {
    node *temp = head;
    head = head->next;
    delete temp; // NOSONAR (cpp:S5025) - Intentional cleanup
  }

  return 0;
}
```
</details>

SP (Stack Pointer, highest word), LV (Local Variable pointer), ~~and TOS (Top of Stack)~~, PC program counter
CPP constant pool pointer

https://drive.google.com/drive/folders/1YHLjEdp6AomSQEPJ8z4iXI8VkKz3v3RB

%rbp - register base pointer (start) LV pointer, lowest word of function foo local variables, local variable
$rsp - register stack pointer (end), SP

<details>

  <summary>react app debugger</summary>


```tsx
import React, { useMemo, useState } from "react";

/* ============================================================================
   SIMULATION ENGINE
   ----------------------------------------------------------------------------
   Nothing here is a hand-authored "step 3 of 4 scenarios" table. Instead we
   maintain a tiny byte-addressable memory object (mem: addr -> value) and
   literally execute the two C functions against it, logging a snapshot after
   every statement. Because it's a real (tiny) interpreter, switching the
   delete target from "head" to "end" changes the loop trip-count on its own
   -- nothing about the trace is special-cased per scenario.

   Word size is 4 (matches the IJVM convention: LV/SP/CPP index by words).
   Each node occupies 2 words: [value][next].
   ========================================================================== */

const WORD = 4;
const HEAP_BASE = 0x1000;
const NODE_STRIDE = 0x10; // spaced out for readable addresses, not packed
const STACK_HEAD_VAR = 0x7ff8; // main()'s local `head`, highest (newest-main) address

const fmt = (n) => "0x" + (n >>> 0).toString(16).toUpperCase().padStart(4, "0");

function makeNodes() {
  return [
    { id: "A", addr: HEAP_BASE + 0 * NODE_STRIDE, value: 10 },
    { id: "B", addr: HEAP_BASE + 1 * NODE_STRIDE, value: 20 },
    { id: "C", addr: HEAP_BASE + 2 * NODE_STRIDE, value: 30 },
  ];
}

const SLOW_CODE = [
  "void remove_list_entry_slow(node **head, node *entry) {",
  "    node *prev = nullptr, *walk = *head;",
  "    while (walk != entry) {",
  "        prev = walk;",
  "        walk = walk->next;",
  "    }",
  "    if (!prev)",
  "        *head = entry->next;",
  "    else",
  "        prev->next = entry->next;",
  "}",
];

const FAST_CODE = [
  "void remove_list_entry_fast(node **head, node *entry) {",
  "    node **p = head;",
  "    while (*p != entry)",
  "        p = &(*p)->next;",
  "    *p = entry->next;",
  "}",
];

function buildTrace(mode, target) {
  const nodes = makeNodes();
  const HEAD = STACK_HEAD_VAR;
  const HEAD_PTR = HEAD - WORD;
  const ENTRY = HEAD - 2 * WORD;
  const LOCAL1 = HEAD - 3 * WORD; // prev (slow) / p (fast)
  const LOCAL2 = HEAD - 4 * WORD; // walk (slow only)

  const targetAddr = target === "head" ? nodes[0].addr : nodes[nodes.length - 1].addr;

  const nameOf = (addr) => {
    if (addr === 0) return "NULL";
    if (addr === HEAD) return "main.head";
    const n = nodes.find((x) => x.addr === addr);
    return n ? `Node ${n.id}` : fmt(addr);
  };

  let mem = {};
  mem[HEAD] = nodes[0].addr;
  nodes.forEach((n, i) => {
    mem[n.addr] = n.value; // value field, never mutated
    mem[n.addr + WORD] = i + 1 < nodes.length ? nodes[i + 1].addr : 0; // next field
  });

  const steps = [];
  let pc = 0;
  const push = (opts) => {
    steps.push({ pc: fmt(pc), mem: { ...mem }, ...opts });
    pc += WORD;
  };

  // ---- call ----
  mem[HEAD_PTR] = HEAD;
  mem[ENTRY] = targetAddr;
  mem[LOCAL1] = 0;
  if (mode === "slow") mem[LOCAL2] = 0;

  push({
    cLine: 0,
    instr: mode === "slow" ? "INVOKEVIRTUAL remove_slow" : "INVOKEVIRTUAL remove_fast",
    framePushed: true,
    sp: mode === "slow" ? LOCAL2 : LOCAL1,
    lv: HEAD_PTR,
    note: `Call remove_${mode}(&head, ${nameOf(targetAddr)}). Parameters land on the stack: head_ptr = &head (${fmt(
      HEAD
    )}), entry = ${fmt(targetAddr)}.`,
    branch: false,
    activeAddr: null,
    mar: null,
    mdr: null,
  });

  if (mode === "slow") {
    // walk = *head
    mem[LOCAL2] = mem[mem[HEAD_PTR]];
    push({
      cLine: 1,
      instr: "ILOAD head_ptr; ILOAD_IND; ISTORE walk",
      framePushed: true,
      sp: LOCAL2,
      lv: HEAD_PTR,
      note: `Dereference head (\u2192 ${fmt(HEAD)}) and copy its value into walk: walk = ${fmt(
        mem[LOCAL2]
      )} (${nameOf(mem[LOCAL2])}).`,
      branch: false,
      activeAddr: HEAD,
      mar: HEAD,
      mdr: mem[LOCAL2],
    });

    while (mem[LOCAL2] !== mem[ENTRY]) {
      push({
        cLine: 2,
        instr: "ILOAD walk; ILOAD entry; IF_ICMPEQ",
        framePushed: true,
        sp: LOCAL2,
        lv: HEAD_PTR,
        note: `while (walk != entry): walk=${fmt(mem[LOCAL2])} (${nameOf(
          mem[LOCAL2]
        )}), entry=${fmt(mem[ENTRY])} (${nameOf(mem[ENTRY])}) \u2192 NOT equal, loop body runs.`,
        branch: false,
        cmp: false,
        activeAddr: null,
        mar: null,
        mdr: null,
      });

      mem[LOCAL1] = mem[LOCAL2]; // prev = walk
      push({
        cLine: 3,
        instr: "ILOAD walk; ISTORE prev",
        framePushed: true,
        sp: LOCAL2,
        lv: HEAD_PTR,
        note: `prev = walk \u2192 prev now points to ${nameOf(mem[LOCAL1])}.`,
        branch: false,
        activeAddr: LOCAL1,
        mar: null,
        mdr: null,
      });

      const walkNextAddr = mem[LOCAL2] + WORD;
      const newWalk = mem[walkNextAddr];
      mem[LOCAL2] = newWalk;
      push({
        cLine: 4,
        instr: "ILOAD walk; ILOAD_FIELD next; ISTORE walk",
        framePushed: true,
        sp: LOCAL2,
        lv: HEAD_PTR,
        note: `Dereference walk->next: heap read at ${fmt(walkNextAddr)} \u2192 ${fmt(
          newWalk
        )}. walk now points to ${nameOf(newWalk)}.`,
        branch: false,
        activeAddr: walkNextAddr,
        mar: walkNextAddr,
        mdr: newWalk,
      });
    }

    push({
      cLine: 2,
      instr: "ILOAD walk; ILOAD entry; IF_ICMPEQ",
      framePushed: true,
      sp: LOCAL2,
      lv: HEAD_PTR,
      note: `while (walk != entry): walk == entry (${nameOf(mem[LOCAL2])}) \u2192 equal, loop terminates.`,
      branch: false,
      cmp: true,
      activeAddr: null,
      mar: null,
      mdr: null,
    });

    const isNull = mem[LOCAL1] === 0;
    push({
      cLine: 6,
      instr: "ILOAD prev; IFEQ",
      framePushed: true,
      sp: LOCAL2,
      lv: HEAD_PTR,
      note: isNull
        ? `prev is NULL (0x0000) \u2014 we're removing the FIRST node. \u26a1 Branch taken to the head-update path.`
        : `prev is not NULL \u2014 branch NOT taken, falls through to the prev->next update.`,
      branch: true,
      cmp: isNull,
      activeAddr: LOCAL1,
      mar: null,
      mdr: null,
    });

    const entryNextAddr = mem[ENTRY] + WORD;
    const entryNextVal = mem[entryNextAddr];
    if (isNull) {
      mem[HEAD] = entryNextVal;
      push({
        cLine: 7,
        instr: "ILOAD entry; ILOAD_FIELD next; ISTORE_IND head_ptr",
        framePushed: true,
        sp: LOCAL2,
        lv: HEAD_PTR,
        note: `*head = entry->next: read ${fmt(entryNextAddr)} \u2192 ${fmt(
          entryNextVal
        )}, write it into main.head (${fmt(HEAD)}).`,
        branch: false,
        activeAddr: HEAD,
        mar: HEAD,
        mdr: entryNextVal,
      });
    } else {
      const prevNextAddr = mem[LOCAL1] + WORD;
      mem[prevNextAddr] = entryNextVal;
      push({
        cLine: 9,
        instr: "ILOAD entry; ILOAD_FIELD next; ISTORE_IND prev.next",
        framePushed: true,
        sp: LOCAL2,
        lv: HEAD_PTR,
        note: `prev->next = entry->next: read ${fmt(entryNextAddr)} \u2192 ${fmt(
          entryNextVal
        )}, write it into ${nameOf(mem[LOCAL1])}'s next field (${fmt(prevNextAddr)}).`,
        branch: false,
        activeAddr: prevNextAddr,
        mar: prevNextAddr,
        mdr: entryNextVal,
      });
    }

    push({
      cLine: 10,
      instr: "IRETURN",
      framePushed: false,
      sp: HEAD,
      lv: HEAD,
      note: `Return. Frame popped \u2014 remove_slow used ${
        mode === "slow" ? "an extra branch" : ""
      } plus a dedicated prev pointer to handle the head case.`,
      branch: false,
      activeAddr: null,
      mar: null,
      mdr: null,
    });
  } else {
    // fast: p = head
    mem[LOCAL1] = mem[HEAD_PTR];
    push({
      cLine: 1,
      instr: "ILOAD head_ptr; ISTORE p",
      framePushed: true,
      sp: LOCAL1,
      lv: HEAD_PTR,
      note: `p = head \u2014 p is set to the address stored in head_ptr itself: ${fmt(
        mem[LOCAL1]
      )} (the address of main.head). No 'walk' variable needed.`,
      branch: false,
      activeAddr: HEAD_PTR,
      mar: HEAD_PTR,
      mdr: mem[LOCAL1],
    });

    while (mem[mem[LOCAL1]] !== mem[ENTRY]) {
      const derefAddr = mem[LOCAL1];
      const derefVal = mem[derefAddr];
      push({
        cLine: 2,
        instr: "ILOAD p; ILOAD_IND; ILOAD entry; IF_ICMPEQ",
        framePushed: true,
        sp: LOCAL1,
        lv: HEAD_PTR,
        note: `while (*p != entry): dereference p (${fmt(derefAddr)}) \u2192 ${fmt(
          derefVal
        )} (${nameOf(derefVal)}); compare with entry (${fmt(mem[ENTRY])}, ${nameOf(
          mem[ENTRY]
        )}) \u2192 NOT equal, loop continues.`,
        branch: false,
        cmp: false,
        activeAddr: derefAddr,
        mar: derefAddr,
        mdr: derefVal,
      });

      const newP = derefVal + WORD;
      mem[LOCAL1] = newP;
      push({
        cLine: 3,
        instr: "ILOAD p; ILOAD_IND; COMPUTE &next; ISTORE p",
        framePushed: true,
        sp: LOCAL1,
        lv: HEAD_PTR,
        note: `p = &(*p)->next \u2014 pure address arithmetic (${fmt(derefVal)} + ${WORD}), no extra heap read. p now points at ${nameOf(
          derefVal
        )}'s next field: ${fmt(newP)}.`,
        branch: false,
        activeAddr: newP,
        mar: null,
        mdr: null,
      });
    }

    const derefAddr = mem[LOCAL1];
    const derefVal = mem[derefAddr];
    push({
      cLine: 2,
      instr: "ILOAD p; ILOAD_IND; ILOAD entry; IF_ICMPEQ",
      framePushed: true,
      sp: LOCAL1,
      lv: HEAD_PTR,
      note: `while (*p != entry): *p == entry (${nameOf(
        derefVal
      )}) \u2192 equal, loop terminates. p already points at whichever slot needs to change \u2014 ${fmt(
        derefAddr
      )} \u2014 decided implicitly by the loop, not by a branch.`,
      branch: false,
      cmp: true,
      activeAddr: derefAddr,
      mar: derefAddr,
      mdr: derefVal,
    });

    const entryNextAddr = mem[ENTRY] + WORD;
    const entryNextVal = mem[entryNextAddr];
    const pAddr = mem[LOCAL1];
    mem[pAddr] = entryNextVal;
    push({
      cLine: 4,
      instr: "ILOAD entry; ILOAD_FIELD next; ISTORE_IND p",
      framePushed: true,
      sp: LOCAL1,
      lv: HEAD_PTR,
      note: `*p = entry->next: read ${fmt(entryNextAddr)} \u2192 ${fmt(
        entryNextVal
      )}, write it to the address p holds (${fmt(
        pAddr
      )}). No IFEQ / branch instruction anywhere in this function \u2014 the same code path handles head, middle, and tail.`,
      branch: false,
      activeAddr: pAddr,
      mar: pAddr,
      mdr: entryNextVal,
    });

    push({
      cLine: 5,
      instr: "IRETURN",
      framePushed: false,
      sp: HEAD,
      lv: HEAD,
      note: `Return. Frame popped \u2014 remove_fast never needed a prev variable or a conditional branch.`,
      branch: false,
      activeAddr: null,
      mar: null,
      mdr: null,
    });
  }

  return { steps, nodes, addrs: { HEAD, HEAD_PTR, ENTRY, LOCAL1, LOCAL2 }, targetAddr, nameOf };
}

function stackLayout(mode, addrs) {
  const { HEAD, HEAD_PTR, ENTRY, LOCAL1, LOCAL2 } = addrs;
  const base = [{ addr: HEAD, label: "head", frame: "main" }];
  const call =
    mode === "slow"
      ? [
          { addr: HEAD_PTR, label: "head_ptr", frame: "call" },
          { addr: ENTRY, label: "entry", frame: "call" },
          { addr: LOCAL1, label: "prev", frame: "call" },
          { addr: LOCAL2, label: "walk", frame: "call" },
        ]
      : [
          { addr: HEAD_PTR, label: "head_ptr", frame: "call" },
          { addr: ENTRY, label: "entry", frame: "call" },
          { addr: LOCAL1, label: "p", frame: "call" },
        ];
  return { base, call };
}

/* ============================================================================
   REACT COMPONENT
   ========================================================================== */

export default function IJVMDebugger() {
  const [mode, setMode] = useState("fast");
  const [target, setTarget] = useState("end");
  const [stepIdx, setStepIdx] = useState(0);

  const trace = useMemo(() => buildTrace(mode, target), [mode, target]);
  const { steps, nodes, addrs, nameOf } = trace;
  const step = steps[Math.min(stepIdx, steps.length - 1)];
  const code = mode === "slow" ? SLOW_CODE : FAST_CODE;
  const layout = stackLayout(mode, addrs);

  const changeMode = (m) => {
    setMode(m);
    setStepIdx(0);
  };
  const changeTarget = (t) => {
    setTarget(t);
    setStepIdx(0);
  };
  const next = () => setStepIdx((i) => Math.min(i + 1, steps.length - 1));
  const prev = () => setStepIdx((i) => Math.max(i - 1, 0));

  // reachability + head, derived purely from current memory snapshot
  const reachable = new Set();
  {
    let cur = step.mem[addrs.HEAD];
    let guard = 0;
    while (cur && guard < 10) {
      reachable.add(cur);
      cur = step.mem[cur + WORD];
      guard++;
    }
  }
  const headTarget = step.mem[addrs.HEAD];

  const stackRows = step.framePushed ? [...layout.base, ...layout.call] : layout.base;
  // render address-descending (highest/oldest at top == visually "down the stack")
  stackRows.sort((a, b) => b.addr - a.addr);

  // heap rows: address-descending too, so higher (later-allocated / "up") sits
  // closer to the gap between stack and heap, and the base sits at the very
  // bottom -- this is what makes "heap grows up" visually correct.
  const heapRows = [...nodes].sort((a, b) => b.addr - a.addr);

  return (
    <div style={styles.app}>
      <style>{css}</style>

      <header style={styles.header}>
        <div>
          <h1 style={styles.title}>
            <span style={styles.titleAccent}>&#9611;</span> Pointer Surgery
          </h1>
          <p style={styles.subtitle}>
            IJVM-style walkthrough &middot; stack grows <b style={{ color: T.rose }}>down</b> from
            high memory, heap grows <b style={{ color: T.green }}>up</b> from low memory
          </p>
        </div>

        <div style={styles.controls}>
          <div style={styles.toggleGroup}>
            <span style={styles.toggleLabel}>program</span>
            <button
              onClick={() => changeMode("slow")}
              style={{ ...styles.toggleBtn, ...(mode === "slow" ? styles.toggleBtnActiveRose : {}) }}
            >
              slow
            </button>
            <button
              onClick={() => changeMode("fast")}
              style={{ ...styles.toggleBtn, ...(mode === "fast" ? styles.toggleBtnActiveCyan : {}) }}
            >
              fast
            </button>
          </div>

          <div style={styles.toggleGroup}>
            <span style={styles.toggleLabel}>delete</span>
            <button
              onClick={() => changeTarget("head")}
              style={{ ...styles.toggleBtn, ...(target === "head" ? styles.toggleBtnActiveAmber : {}) }}
            >
              head
            </button>
            <button
              onClick={() => changeTarget("end")}
              style={{ ...styles.toggleBtn, ...(target === "end" ? styles.toggleBtnActiveAmber : {}) }}
            >
              end
            </button>
          </div>

          <div style={styles.stepGroup}>
            <button onClick={prev} disabled={stepIdx === 0} style={styles.stepBtn}>
              &larr; prev
            </button>
            <span style={styles.stepCount}>
              {stepIdx + 1} / {steps.length}
            </span>
            <button onClick={next} disabled={stepIdx === steps.length - 1} style={styles.stepBtnPrimary}>
              next &rarr;
            </button>
          </div>
        </div>
      </header>

      <div style={styles.noteBar}>
        <span style={styles.pcChip}>{step.pc}</span>
        <span style={styles.instrChip}>{step.instr}</span>
        {step.branch && <span style={styles.branchChip}>&#9889; branch</span>}
        <span style={styles.noteText}>{step.note}</span>
      </div>

      <div style={styles.grid}>
        {/* LEFT: registers + code */}
        <div style={styles.leftCol}>
          <section style={styles.panel}>
            <h2 style={styles.panelTitle}>registers</h2>
            <div style={styles.regGrid}>
              <RegChip label="PC" value={step.pc} color={T.amber} />
              <RegChip label="SP" value={fmt(step.sp)} color={T.rose} />
              <RegChip label="LV" value={fmt(step.lv)} color={T.cyan} />
              <RegChip label="MAR" value={step.mar != null ? fmt(step.mar) : "\u2014"} color={T.ink} />
              <RegChip label="MDR" value={step.mdr != null ? fmt(step.mdr) : "\u2014"} color={T.ink} />
            </div>
          </section>

          <section style={{ ...styles.panel, flex: 1 }}>
            <h2 style={styles.panelTitle}>
              source &middot; remove_{mode}
            </h2>
            <div style={styles.codeBlock}>
              {code.map((line, i) => (
                <div
                  key={i}
                  style={{
                    ...styles.codeLine,
                    ...(i === step.cLine ? styles.codeLineActive : {}),
                  }}
                >
                  <span style={styles.codeLineNo}>{i + 1}</span>
                  {line}
                </div>
              ))}
            </div>
            <div style={styles.legend}>
              <LegendDot color={T.cyan} label="pointer / control frame" />
              <LegendDot color={T.amber} label="active memory access" />
              <LegendDot color={T.rose} label="branch / unreachable" />
              <LegendDot color={T.green} label="current head" />
            </div>
          </section>
        </div>

        {/* RIGHT: unified address space */}
        <section style={styles.memPanel}>
          <div style={styles.memHeader}>
            <h2 style={styles.panelTitle}>address space</h2>
            <span style={styles.memHint}>word = {WORD} bytes</span>
          </div>

          <div style={styles.memCol}>
            <div style={styles.memEdgeLabel}>high memory &middot; 0x7FFF</div>

            <div style={styles.growArrowDown}>
              <div style={styles.growLine} />
              <span>stack grows down</span>
            </div>

            {stackRows.map((row) => {
              const isSP = row.addr === step.sp;
              const isLV = row.addr === step.lv;
              const isActive = row.addr === step.activeAddr;
              const val = step.mem[row.addr];
              const isPointerLike = row.label !== "prev" || val !== 0;
              return (
                <div
                  key={row.addr}
                  style={{
                    ...styles.stackRow,
                    ...(row.frame === "call" ? styles.stackRowCall : {}),
                    ...(isActive ? styles.rowPulse : {}),
                  }}
                >
                  <div style={styles.rowMarkers}>
                    {isSP && <span style={styles.markerSP}>SP</span>}
                    {isLV && <span style={styles.markerLV}>LV</span>}
                  </div>
                  <span style={styles.rowAddr}>{fmt(row.addr)}</span>
                  <span style={styles.rowLabel}>{row.label}</span>
                  <span style={styles.rowValue}>{fmt(val)}</span>
                  <span style={styles.rowPointsTo}>
                    {val !== 0 && (row.label !== "walk" && row.label !== "p" ? true : true)
                      ? `\u2192 ${nameOf(val)}`
                      : ""}
                  </span>
                </div>
              );
            })}

            <div style={styles.gapRegion}>
              <div style={styles.gapLine} />
              <span style={styles.gapLabel}>&middot; &middot; &middot; unmapped &middot; &middot; &middot;</span>
              <div style={styles.gapLine} />
            </div>

            {heapRows.map((n) => {
              const nextAddr = n.addr + WORD;
              const nextVal = step.mem[nextAddr];
              const isReachable = reachable.has(n.addr);
              const isHead = n.addr === headTarget;
              const isTarget = n.addr === trace.targetAddr;
              const activeHere = step.activeAddr === n.addr || step.activeAddr === nextAddr;
              return (
                <div
                  key={n.addr}
                  style={{
                    ...styles.heapCard,
                    ...(isReachable ? {} : styles.heapCardOrphan),
                    ...(activeHere ? styles.rowPulse : {}),
                  }}
                >
                  <div style={styles.heapCardHeader}>
                    <span style={styles.heapCardTitle}>
                      Node {n.id}
                      {isHead && <span style={styles.headTag}>HEAD</span>}
                      {isTarget && <span style={styles.targetTag}>TARGET</span>}
                      {!isReachable && <span style={styles.orphanTag}>unreachable</span>}
                    </span>
                    <span style={styles.rowAddr}>{fmt(n.addr)}</span>
                  </div>
                  <div style={styles.heapFields}>
                    <div style={styles.heapField}>
                      <span style={styles.heapFieldLabel}>value @ {fmt(n.addr)}</span>
                      <span style={styles.heapFieldValue}>{n.value}</span>
                    </div>
                    <div style={styles.heapField}>
                      <span style={styles.heapFieldLabel}>next @ {fmt(nextAddr)}</span>
                      <span style={styles.heapFieldValue}>
                        {fmt(nextVal)}{" "}
                        <span style={styles.heapFieldPointsTo}>({nameOf(nextVal)})</span>
                      </span>
                    </div>
                  </div>
                </div>
              );
            })}

            <div style={styles.growArrowUp}>
              <span>heap grows up</span>
              <div style={styles.growLine} />
            </div>

            <div style={styles.memEdgeLabel}>low memory &middot; 0x1000</div>
          </div>
        </section>
      </div>
    </div>
  );
}

function RegChip({ label, value, color }) {
  return (
    <div style={styles.regChip}>
      <span style={styles.regLabel}>{label}</span>
      <span style={{ ...styles.regValue, color }}>{value}</span>
    </div>
  );
}

function LegendDot({ color, label }) {
  return (
    <div style={styles.legendItem}>
      <span style={{ ...styles.legendDot, background: color }} />
      <span>{label}</span>
    </div>
  );
}

/* ============================================================================
   DESIGN TOKENS
   ========================================================================== */

const T = {
  bg: "#0a0e14",
  panel: "#0e1620",
  panelAlt: "#111b26",
  rule: "#1c2a38",
  ink: "#c9d6e3",
  inkDim: "#6b7f92",
  amber: "#e8a33d",
  cyan: "#4fc3e8",
  rose: "#e8615f",
  green: "#7fd99a",
};

const css = `
  @import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500;600;700&family=IBM+Plex+Sans+Condensed:wght@500;600;700&display=swap');
  * { box-sizing: border-box; }
  button { font-family: inherit; cursor: pointer; }
  button:disabled { cursor: not-allowed; opacity: 0.35; }
  ::selection { background: ${T.amber}44; }
`;

const styles = {
  app: {
    minHeight: "100vh",
    background: `radial-gradient(ellipse at top, ${T.panelAlt} 0%, ${T.bg} 55%)`,
    color: T.ink,
    fontFamily: "'IBM Plex Mono', ui-monospace, monospace",
    padding: "20px",
  },
  header: {
    display: "flex",
    flexWrap: "wrap",
    justifyContent: "space-between",
    alignItems: "flex-end",
    gap: "16px",
    borderBottom: `1px solid ${T.rule}`,
    paddingBottom: "16px",
    marginBottom: "14px",
  },
  title: {
    fontFamily: "'IBM Plex Sans Condensed', sans-serif",
    fontWeight: 700,
    fontSize: "22px",
    letterSpacing: "0.02em",
    margin: 0,
    display: "flex",
    alignItems: "center",
    gap: "8px",
  },
  titleAccent: { color: T.amber },
  subtitle: {
    fontSize: "12px",
    color: T.inkDim,
    marginTop: "4px",
  },
  controls: { display: "flex", flexWrap: "wrap", gap: "18px", alignItems: "center" },
  toggleGroup: {
    display: "flex",
    alignItems: "center",
    gap: "6px",
    background: T.panel,
    border: `1px solid ${T.rule}`,
    borderRadius: "6px",
    padding: "4px 6px",
  },
  toggleLabel: {
    fontFamily: "'IBM Plex Sans Condensed', sans-serif",
    fontSize: "10px",
    letterSpacing: "0.08em",
    textTransform: "uppercase",
    color: T.inkDim,
    padding: "0 4px",
  },
  toggleBtn: {
    background: "transparent",
    border: "none",
    color: T.inkDim,
    fontSize: "12px",
    fontWeight: 600,
    padding: "5px 10px",
    borderRadius: "4px",
    fontFamily: "'IBM Plex Sans Condensed', sans-serif",
    textTransform: "uppercase",
    letterSpacing: "0.04em",
  },
  toggleBtnActiveRose: { background: T.rose + "26", color: T.rose },
  toggleBtnActiveCyan: { background: T.cyan + "26", color: T.cyan },
  toggleBtnActiveAmber: { background: T.amber + "26", color: T.amber },
  stepGroup: { display: "flex", alignItems: "center", gap: "10px" },
  stepBtn: {
    background: T.panel,
    border: `1px solid ${T.rule}`,
    color: T.ink,
    fontSize: "12px",
    fontWeight: 600,
    padding: "8px 12px",
    borderRadius: "6px",
    fontFamily: "'IBM Plex Sans Condensed', sans-serif",
  },
  stepBtnPrimary: {
    background: T.amber,
    border: `1px solid ${T.amber}`,
    color: "#1a1204",
    fontSize: "12px",
    fontWeight: 700,
    padding: "8px 14px",
    borderRadius: "6px",
    fontFamily: "'IBM Plex Sans Condensed', sans-serif",
  },
  stepCount: { fontSize: "11px", color: T.inkDim, minWidth: "48px", textAlign: "center" },
  noteBar: {
    display: "flex",
    alignItems: "center",
    flexWrap: "wrap",
    gap: "10px",
    background: T.panel,
    border: `1px solid ${T.rule}`,
    borderLeft: `3px solid ${T.amber}`,
    borderRadius: "6px",
    padding: "10px 14px",
    marginBottom: "16px",
    fontSize: "12.5px",
  },
  pcChip: {
    background: T.bg,
    border: `1px solid ${T.rule}`,
    color: T.amber,
    fontWeight: 700,
    fontSize: "11px",
    padding: "3px 8px",
    borderRadius: "4px",
  },
  instrChip: {
    color: T.cyan,
    fontSize: "11px",
    fontWeight: 600,
  },
  branchChip: {
    background: T.rose + "22",
    color: T.rose,
    fontSize: "10px",
    fontWeight: 700,
    padding: "3px 8px",
    borderRadius: "4px",
    letterSpacing: "0.04em",
  },
  noteText: { color: T.ink, lineHeight: 1.5, flex: 1, minWidth: "260px" },
  grid: {
    display: "grid",
    gridTemplateColumns: "340px 1fr",
    gap: "16px",
    alignItems: "start",
  },
  leftCol: { display: "flex", flexDirection: "column", gap: "16px" },
  panel: {
    background: T.panel,
    border: `1px solid ${T.rule}`,
    borderRadius: "8px",
    padding: "14px",
  },
  panelTitle: {
    fontFamily: "'IBM Plex Sans Condensed', sans-serif",
    fontSize: "11px",
    textTransform: "uppercase",
    letterSpacing: "0.1em",
    color: T.inkDim,
    margin: "0 0 10px 0",
  },
  regGrid: { display: "grid", gridTemplateColumns: "1fr 1fr", gap: "8px" },
  regChip: {
    background: T.bg,
    border: `1px solid ${T.rule}`,
    borderRadius: "6px",
    padding: "8px 10px",
  },
  regLabel: { display: "block", fontSize: "10px", color: T.inkDim, marginBottom: "2px" },
  regValue: { fontSize: "13px", fontWeight: 700 },
  codeBlock: {
    background: T.bg,
    border: `1px solid ${T.rule}`,
    borderRadius: "6px",
    padding: "10px",
    fontSize: "12px",
    overflowX: "auto",
  },
  codeLine: {
    display: "flex",
    gap: "10px",
    padding: "3px 6px",
    borderRadius: "4px",
    color: T.inkDim,
    whiteSpace: "pre",
  },
  codeLineActive: {
    background: T.amber + "1c",
    color: T.amber,
    fontWeight: 600,
    borderLeft: `2px solid ${T.amber}`,
  },
  codeLineNo: { color: T.rule, userSelect: "none", minWidth: "14px" },
  legend: {
    display: "flex",
    flexWrap: "wrap",
    gap: "10px",
    marginTop: "12px",
    fontSize: "10.5px",
    color: T.inkDim,
  },
  legendItem: { display: "flex", alignItems: "center", gap: "5px" },
  legendDot: { width: "7px", height: "7px", borderRadius: "50%", display: "inline-block" },
  memPanel: {
    background: T.panel,
    border: `1px solid ${T.rule}`,
    borderRadius: "8px",
    padding: "14px",
  },
  memHeader: { display: "flex", justifyContent: "space-between", alignItems: "baseline" },
  memHint: { fontSize: "10.5px", color: T.inkDim },
  memCol: { display: "flex", flexDirection: "column", gap: "6px", marginTop: "6px" },
  memEdgeLabel: {
    textAlign: "center",
    fontSize: "10px",
    color: T.inkDim,
    padding: "2px 0",
  },
  growArrowDown: {
    display: "flex",
    alignItems: "center",
    gap: "8px",
    fontSize: "10px",
    color: T.rose,
    padding: "2px 4px",
  },
  growArrowUp: {
    display: "flex",
    alignItems: "center",
    gap: "8px",
    fontSize: "10px",
    color: T.green,
    padding: "2px 4px",
  },
  growLine: { flex: 1, height: "1px", background: "currentColor", opacity: 0.35 },
  stackRow: {
    position: "relative",
    display: "grid",
    gridTemplateColumns: "44px 82px 100px 82px 1fr",
    alignItems: "center",
    gap: "8px",
    background: T.bg,
    border: `1px solid ${T.rule}`,
    borderRadius: "6px",
    padding: "8px 10px",
    fontSize: "12px",
  },
  stackRowCall: { background: T.cyan + "10", borderColor: T.cyan + "40" },
  rowMarkers: { display: "flex", gap: "4px" },
  markerSP: {
    fontSize: "9px",
    fontWeight: 700,
    color: "#1a0a08",
    background: T.rose,
    borderRadius: "3px",
    padding: "1px 4px",
  },
  markerLV: {
    fontSize: "9px",
    fontWeight: 700,
    color: "#04181c",
    background: T.cyan,
    borderRadius: "3px",
    padding: "1px 4px",
  },
  rowAddr: { color: T.inkDim, fontSize: "11px" },
  rowLabel: { color: T.ink, fontWeight: 600 },
  rowValue: { color: T.amber, fontWeight: 600 },
  rowPointsTo: { color: T.inkDim, fontSize: "11px", textAlign: "right" },
  rowPulse: {
    borderColor: T.amber,
    boxShadow: `0 0 0 1px ${T.amber}, 0 0 14px 0 ${T.amber}55`,
  },
  gapRegion: {
    display: "flex",
    alignItems: "center",
    gap: "10px",
    padding: "6px 4px",
    color: T.inkDim,
    fontSize: "10px",
  },
  gapLine: { flex: 1, height: "1px", borderTop: `1px dashed ${T.rule}` },
  gapLabel: { whiteSpace: "nowrap" },
  heapCard: {
    background: T.bg,
    border: `1px solid ${T.rule}`,
    borderLeft: `3px solid ${T.green}`,
    borderRadius: "6px",
    padding: "8px 10px",
  },
  heapCardOrphan: {
    borderLeftColor: T.rose,
    opacity: 0.55,
  },
  heapCardHeader: {
    display: "flex",
    justifyContent: "space-between",
    alignItems: "center",
    marginBottom: "6px",
  },
  heapCardTitle: { display: "flex", alignItems: "center", gap: "6px", fontWeight: 700, fontSize: "12px" },
  headTag: {
    fontSize: "9px",
    fontWeight: 700,
    color: "#04180c",
    background: T.green,
    borderRadius: "3px",
    padding: "1px 5px",
  },
  targetTag: {
    fontSize: "9px",
    fontWeight: 700,
    color: "#1a1204",
    background: T.amber,
    borderRadius: "3px",
    padding: "1px 5px",
  },
  orphanTag: {
    fontSize: "9px",
    fontWeight: 700,
    color: "#200606",
    background: T.rose,
    borderRadius: "3px",
    padding: "1px 5px",
  },
  heapFields: { display: "flex", gap: "10px" },
  heapField: {
    flex: 1,
    background: T.panelAlt,
    borderRadius: "4px",
    padding: "5px 8px",
  },
  heapFieldLabel: { display: "block", fontSize: "9.5px", color: T.inkDim },
  heapFieldValue: { fontSize: "12px", color: T.ink, fontWeight: 600 },
  heapFieldPointsTo: { color: T.inkDim, fontWeight: 400, fontSize: "10.5px" },
};
```

  
</details>
