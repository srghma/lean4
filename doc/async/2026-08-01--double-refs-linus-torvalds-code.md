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


| **Inner \ Outer** | **Outer Pointer is Non-Nullable (`*...`)** | **Outer Pointer is Nullable (`?*...`)** |
| :--- | :--- | :--- |
| **Inner Pointer is Non-Nullable (`*Node`)** | IF non-optional node THEN **`**Node`** <br> ELSE **`**?Node`** | IF non-optional node THEN **`?**Node`** <br> ELSE **`?**?Node`** |
| **Inner Pointer is Nullable (`?*Node`)** | IF non-optional node THEN **`*?*Node`** (Linus) <br> ELSE **`*?*?Node`** | IF non-optional node THEN **`?*?*Node`** <br> ELSE **`?*?*?Node`** |


<details>
  <summary>zig ?* ?* ?</summary>



```zig
import React, { useMemo, useState } from "react";

/* ============================================================================
   TYPE-SPACE DATA
   ----------------------------------------------------------------------------
   Every learnable Zig type in this app is keyed by its literal spelling
   ("Node", "*Node", "?*Node", ...). Vector / matrix / cube all just render
   pointers into this one map, so clicking the same type from two different
   sections (e.g. "*Node" in both the matrix and the cube) shows identical
   content -- there's exactly one source of truth per type.
   ========================================================================== */

const EXAMPLES = {
  Node: {
    formula: "Node",
    title: "Plain value",
    blurb: "The struct itself. Copying it copies every field.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

pub fn main() void {
    // \`Node\` is a plain value: it lives wherever you put it
    // (stack, another struct, ...) and copying it copies the
    // whole struct.
    var n: Node = .{ .value = 10 };
    n.value += 5;
    std.debug.print("n.value = {d}\\n", .{n.value});
}`,
  },
  "?Node": {
    formula: "?Node",
    title: "Optional value",
    blurb: "The whole struct, plus one extra bit for \u201cpresent or not\u201d. Still not a pointer.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

pub fn main() void {
    // \`?Node\` is an *optional value*, not a pointer: it's the
    // whole struct plus one bit saying "present or not".
    var maybe: ?Node = Node{ .value = 3 };

    if (maybe) |n| {
        std.debug.print("present: {d}\\n", .{n.value});
    }

    maybe = null;
    std.debug.print("is null now: {}\\n", .{maybe == null});
}`,
  },
  "*Node": {
    formula: "*Node",
    title: "Non-null pointer",
    blurb: "Must point at a real Node. No unwrapping, ever.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn bump(n: *Node) void {
    // \`n\` is guaranteed non-null: no unwrapping required.
    n.value += 1;
}

pub fn main() void {
    var n = Node{ .value = 1 };
    bump(&n);
    std.debug.print("n.value = {d}\\n", .{n.value});
}`,
  },
  "*?Node": {
    formula: "*?Node",
    title: "Non-null pointer to an optional value",
    blurb: "The pointer can't be null \u2014 but the value it points at can be empty.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn clearSlot(slot: *?Node) void {
    // \`slot\` itself can never be null, but the *value it
    // points at* can be empty.
    slot.* = null;
}

pub fn main() void {
    var slot: ?Node = Node{ .value = 7 };
    clearSlot(&slot);
    std.debug.print("slot is null: {}\\n", .{slot == null});
}`,
  },
  "?*Node": {
    formula: "?*Node",
    title: "Nullable pointer",
    blurb: "The classic linked-list \u201cnext\u201d field: either a real Node or nothing.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
    next: ?*Node = null,
};

pub fn main() void {
    var b = Node{ .value = 2 };
    var a = Node{ .value = 1, .next = &b };

    var walk: ?*Node = &a;
    while (walk) |n| : (walk = n.next) {
        std.debug.print("{d}\\n", .{n.value});
    }
}`,
  },
  "?*?Node": {
    formula: "?*?Node",
    title: "Nullable pointer to an optional value",
    blurb: "Two independent maybes stacked: the pointer might be absent, and so might the value.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn maybeClear(slot: ?*?Node) void {
    if (slot) |s| {
        s.* = null;
    }
}

pub fn main() void {
    var value: ?Node = Node{ .value = 9 };
    maybeClear(&value);
    std.debug.print("value is null: {}\\n", .{value == null});
}`,
  },
  "**Node": {
    formula: "**Node",
    title: "Non-null pointer to a non-null pointer",
    blurb: "Both levels are guaranteed non-null. Not the good-taste.md trick \u2014 see the callout below.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn bumpIndirect(pp: **Node) void {
    // both levels are guaranteed non-null
    pp.*.*.value += 100;
}

pub fn main() void {
    var n = Node{ .value = 1 };
    var p: *Node = &n;
    bumpIndirect(&p);
    std.debug.print("n.value = {d}\\n", .{n.value});
}`,
  },
  "**?Node": {
    formula: "**?Node",
    title: "Non-null pointer to a non-null pointer to an optional value",
    blurb: "Two guaranteed pointer hops, landing on a slot that may or may not hold a Node.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
};

fn clearIndirect(pp: **?Node) void {
    pp.*.* = null;
}

pub fn main() void {
    var slot: ?Node = Node{ .value = 4 };
    var p: *?Node = &slot;
    clearIndirect(&p);
    std.debug.print("slot is null: {}\\n", .{slot == null});
}`,
  },
  linus: {
    formula: "*?*Node",
    title: "The good-taste.md trick",
    blurb:
      "A non-null pointer to a nullable pointer. This \u2014 not **Node \u2014 is the real Zig translation of Linus's indirect-pointer remove(): the outer pointer (p) can never be null, but the slot it points at (head, or some node's .next) legitimately can be.",
    code: `const std = @import("std");

const Node = struct {
    value: i32,
    next: ?*Node = null,
};

// Zig translation of remove_list_entry_fast() from good-taste.md.
// p's type is *?*Node: p itself is never null, but *p (a head
// pointer or a .next field) legitimately can be.
fn removeEntry(head: *?*Node, entry: *Node) void {
    var p: *?*Node = head;
    while (p.* != entry) : (p = &p.*.?.next) {}
    p.* = entry.next;
}

pub fn main() void {
    var c = Node{ .value = 3 };
    var b = Node{ .value = 2, .next = &c };
    var a = Node{ .value = 1, .next = &b };
    var head: ?*Node = &a;

    removeEntry(&head, &b); // unlink the middle node

    var walk = head;
    while (walk) |n| : (walk = n.next) {
        std.debug.print("{d}\\n", .{n.value});
    }
}`,
  },
};

const ZIG_PLAY_URL = "https://zig-play.dev/";

/* ============================================================================
   VECTOR + MATRIX DATA
   ========================================================================== */

const VECTOR_ITEMS = ["Node", "?Node"];

const MATRIX_ROWS = [
  { key: "ptr", label: "Ptr (*)" },
  { key: "optptr", label: "Opt-Ptr (?*)" },
];
const MATRIX_COLS = [
  { key: "val", label: "Value (Node)" },
  { key: "optval", label: "Opt-Value (?Node)" },
];
const MATRIX_CELLS = {
  "ptr:val": "*Node",
  "ptr:optval": "*?Node",
  "optptr:val": "?*Node",
  "optptr:optval": "?*?Node",
};

/* ============================================================================
   CUBE GEOMETRY
   ----------------------------------------------------------------------------
   Static isometric projection (no rotation, no CSS 3D). Axes:
     a (x, screen-right-down)  -> pointer present?
     b (y, screen-left-down)   -> pointer-to-pointer present?
     c (z, screen-up)          -> Optional-of-Node?
   a=0,b=1 is geometrically drawn but logically invalid: you can't have a
   second pointer level without a first.
   ========================================================================== */

const COS30 = Math.cos(Math.PI / 6);
const SIN30 = Math.sin(Math.PI / 6);
const S = 100; // ground (a,b) unit scale
const SZ = 78; // vertical (c) unit scale -- deliberately != S so opposite
// corners (0,0,0) and (1,1,1) never land on the same pixel.

function project(a, b, c) {
  return {
    x: (a - b) * S * COS30,
    y: (a + b) * S * SIN30 - c * SZ,
  };
}

function cubeType(a, b, c) {
  if (a === 0 && b === 1) return { invalid: true };
  const depth = a === 0 ? 0 : b === 0 ? 1 : 2;
  const type = "*".repeat(depth) + (c === 1 ? "?Node" : "Node");
  return { invalid: false, type };
}

const CUBE_VERTICES = [];
for (const a of [0, 1]) {
  for (const b of [0, 1]) {
    for (const c of [0, 1]) {
      CUBE_VERTICES.push({ a, b, c, ...project(a, b, c), ...cubeType(a, b, c) });
    }
  }
}

const CUBE_EDGES = [];
for (let i = 0; i < CUBE_VERTICES.length; i++) {
  for (let j = i + 1; j < CUBE_VERTICES.length; j++) {
    const v1 = CUBE_VERTICES[i];
    const v2 = CUBE_VERTICES[j];
    const diff =
      Math.abs(v1.a - v2.a) + Math.abs(v1.b - v2.b) + Math.abs(v1.c - v2.c);
    if (diff === 1) CUBE_EDGES.push([v1, v2]);
  }
}

/* ============================================================================
   COMPONENT
   ========================================================================== */

export default function ZigTypeSpace() {
  const [selected, setSelected] = useState("linus");
  const example = EXAMPLES[selected];

  const [copied, setCopied] = useState(false);
  const copy = () => {
    navigator.clipboard?.writeText(example.code).then(() => {
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    });
  };

  return (
    <div style={styles.app}>
      <style>{css}</style>

      <header style={styles.header}>
        <h1 style={styles.h1}>
          <span style={styles.h1Accent}>zig</span> type space
        </h1>
        <p style={styles.sub}>
          value &rarr; pointer &rarr; pointer-to-pointer, crossed with Optional. Click any type to load a
          runnable example.
        </p>
      </header>

      <div style={styles.layout}>
        <main style={styles.main}>
          {/* 1. VECTOR */}
          <Section
            index="01"
            title="the vector"
            hint="Node vs. ?Node \u2014 value, or optional value. No pointer yet."
          >
            <div style={styles.vectorRow}>
              {VECTOR_ITEMS.map((k) => (
                <TypeChip key={k} typeKey={k} selected={selected} onSelect={setSelected} size="lg" />
              ))}
            </div>
          </Section>

          {/* 2. MATRIX */}
          <Section
            index="02"
            title="the matrix"
            hint="One pointer level, crossed with pointer-nullability and value-optionality."
          >
            <table style={styles.table}>
              <thead>
                <tr>
                  <th style={styles.thCorner} />
                  {MATRIX_COLS.map((col) => (
                    <th key={col.key} style={styles.th}>
                      {col.label}
                    </th>
                  ))}
                </tr>
              </thead>
              <tbody>
                {MATRIX_ROWS.map((row) => (
                  <tr key={row.key}>
                    <td style={styles.thRow}>{row.label}</td>
                    {MATRIX_COLS.map((col) => {
                      const type = MATRIX_CELLS[`${row.key}:${col.key}`];
                      return (
                        <td key={col.key} style={styles.td}>
                          <TypeChip typeKey={type} selected={selected} onSelect={setSelected} size="md" />
                        </td>
                      );
                    })}
                  </tr>
                ))}
              </tbody>
            </table>
          </Section>

          {/* 3. CUBE */}
          <Section
            index="03"
            title="the cube"
            hint="x = pointer \u00b7 y = pointer-to-pointer \u00b7 z (up) = Optional. Static \u2014 nothing spins."
          >
            <div style={styles.cubeWrap}>
              <svg viewBox="-140 -130 280 270" style={styles.cubeSvg}>
                {CUBE_EDGES.map(([v1, v2], i) => {
                  const dashed = v1.invalid || v2.invalid;
                  return (
                    <line
                      key={i}
                      x1={v1.x}
                      y1={v1.y}
                      x2={v2.x}
                      y2={v2.y}
                      stroke={dashed ? T.rule : T.edge}
                      strokeWidth={1.5}
                      strokeDasharray={dashed ? "3 4" : undefined}
                    />
                  );
                })}

                {/* axis indicators from the origin (0,0,0) = plain Node */}
                <AxisLabel x={120} y={72} color={T.cyan} label="x \u00b7 pointer" />
                <AxisLabel x={-124} y={72} color={T.violet} anchor="end" label="y \u00b7 ptr-to-ptr" />
                <AxisLabel x={0} y={-104} color={T.green} anchor="middle" label="z \u00b7 Optional" />

                {CUBE_VERTICES.map((v, i) => (
                  <CubeVertex key={i} v={v} selected={selected} onSelect={setSelected} />
                ))}
              </svg>
            </div>
            <p style={styles.cubeFoot}>
              Dashed vertices (x=0, y=1) are geometrically present but not legal types: you can't have a
              second pointer indirection without a first.
            </p>
          </Section>

          {/* CALLOUT */}
          <Section index="04" title="the actual good-taste.md type" hint="Where the cube's **Node quietly diverges from the real trick.">
            <button
              style={{
                ...styles.linusCard,
                ...(selected === "linus" ? styles.linusCardActive : {}),
              }}
              onClick={() => setSelected("linus")}
            >
              <code style={styles.linusFormula}>*?*Node</code>
              <span style={styles.linusText}>
                Non-null pointer to a nullable pointer &mdash; not <code>**Node</code>. The outer pointer
                (p) can never be null; the slot it points at (head, or a node's .next) legitimately can be.
              </span>
            </button>
          </Section>
        </main>

        {/* SIDEBAR */}
        <aside style={styles.sidebar}>
          <div style={styles.sidebarInner}>
            <span style={styles.sidebarEyebrow}>selected type</span>
            <code style={styles.sidebarFormula}>{example.formula}</code>
            <h3 style={styles.sidebarTitle}>{example.title}</h3>
            <p style={styles.sidebarBlurb}>{example.blurb}</p>

            <pre style={styles.codeBlock}>
              <code>{example.code}</code>
            </pre>

            <div style={styles.sidebarActions}>
              <button style={styles.copyBtn} onClick={copy}>
                {copied ? "copied \u2713" : "copy code"}
              </button>
              <a href={ZIG_PLAY_URL} target="_blank" rel="noreferrer" style={styles.playLink}>
                open zig-play.dev &rarr;
              </a>
            </div>
            <p style={styles.sidebarNote}>Paste the copied snippet into zig-play.dev's editor and run it.</p>
          </div>
        </aside>
      </div>
    </div>
  );
}

function Section({ index, title, hint, children }) {
  return (
    <section style={styles.section}>
      <div style={styles.sectionHead}>
        <span style={styles.sectionIndex}>{index}</span>
        <div>
          <h2 style={styles.sectionTitle}>{title}</h2>
          <p style={styles.sectionHint}>{hint}</p>
        </div>
      </div>
      {children}
    </section>
  );
}

function TypeChip({ typeKey, selected, onSelect, size }) {
  const isSel = selected === typeKey;
  return (
    <button
      onClick={() => onSelect(typeKey)}
      style={{
        ...styles.chip,
        ...(size === "lg" ? styles.chipLg : styles.chipMd),
        ...(isSel ? styles.chipActive : {}),
      }}
    >
      {typeKey}
    </button>
  );
}

function AxisLabel({ x, y, color, label, anchor = "start" }) {
  return (
    <text x={x} y={y} fill={color} fontSize="11" fontWeight="600" textAnchor={anchor} style={{ fontFamily: "'IBM Plex Mono', monospace" }}>
      {label}
    </text>
  );
}

function CubeVertex({ v, selected, onSelect }) {
  const key = v.invalid ? null : v.type;
  const isSel = key && selected === key;
  const color = v.invalid ? T.rule : v.c === 1 ? T.green : T.cyan;
  const labelDx = v.a === 0 && v.b === 0 ? -6 : 6;
  const anchor = v.a === 0 && v.b === 0 ? "end" : "start";

  return (
    <g
      onClick={() => key && onSelect(key)}
      style={{ cursor: key ? "pointer" : "default" }}
    >
      <circle
        cx={v.x}
        cy={v.y}
        r={isSel ? 8 : 6}
        fill={v.invalid ? T.bg : isSel ? color : T.panel}
        stroke={color}
        strokeWidth={isSel ? 2.5 : 1.5}
        strokeDasharray={v.invalid ? "2 2" : undefined}
      />
      <text
        x={v.x + labelDx}
        y={v.y - 10}
        fontSize={v.invalid ? 9 : 11}
        fontWeight={isSel ? 700 : 600}
        fill={v.invalid ? T.inkDim : isSel ? color : T.ink}
        textAnchor={anchor}
        style={{ fontFamily: "'IBM Plex Mono', monospace" }}
      >
        {v.invalid ? "n/a" : v.type}
      </text>
    </g>
  );
}

/* ============================================================================
   DESIGN TOKENS
   ========================================================================== */

const T = {
  bg: "#0b0d10",
  panel: "#14171c",
  panelAlt: "#181c22",
  rule: "#262c34",
  edge: "#3a4552",
  ink: "#d7dee6",
  inkDim: "#717d8a",
  amber: "#f2a93c", // zig's brand tone, used sparingly
  cyan: "#5ec4d6",
  violet: "#9d8cf0",
  green: "#7fd99a",
};

const css = `
  @import url('https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500;600;700&family=IBM+Plex+Sans:wght@500;600;700&display=swap');
  * { box-sizing: border-box; }
  button { font-family: inherit; cursor: pointer; }
  ::selection { background: ${T.amber}44; }
`;

const styles = {
  app: {
    minHeight: "100vh",
    background: T.bg,
    color: T.ink,
    fontFamily: "'IBM Plex Sans', sans-serif",
    padding: "28px 28px 60px",
  },
  header: { marginBottom: "24px" },
  h1: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "24px",
    fontWeight: 700,
    margin: 0,
    letterSpacing: "-0.01em",
  },
  h1Accent: { color: T.amber },
  sub: { color: T.inkDim, fontSize: "13px", marginTop: "6px", maxWidth: "560px", lineHeight: 1.5 },
  layout: { display: "grid", gridTemplateColumns: "1fr 320px", gap: "24px", alignItems: "start" },
  main: { display: "flex", flexDirection: "column", gap: "8px" },
  section: {
    borderTop: `1px solid ${T.rule}`,
    padding: "24px 0",
  },
  sectionHead: { display: "flex", gap: "14px", marginBottom: "16px" },
  sectionIndex: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "12px",
    color: T.amber,
    fontWeight: 700,
    paddingTop: "3px",
  },
  sectionTitle: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "16px",
    fontWeight: 700,
    margin: 0,
    textTransform: "lowercase",
  },
  sectionHint: { color: T.inkDim, fontSize: "12.5px", marginTop: "3px", maxWidth: "520px" },
  vectorRow: { display: "flex", gap: "12px" },
  chip: {
    fontFamily: "'IBM Plex Mono', monospace",
    background: T.panel,
    border: `1px solid ${T.rule}`,
    color: T.ink,
    borderRadius: "7px",
    fontWeight: 600,
  },
  chipLg: { padding: "16px 22px", fontSize: "17px" },
  chipMd: { padding: "10px 14px", fontSize: "13px", width: "100%" },
  chipActive: { borderColor: T.amber, color: T.amber, background: T.amber + "14" },
  table: { borderCollapse: "collapse", width: "100%", maxWidth: "520px" },
  thCorner: { border: `1px solid ${T.rule}`, background: T.panelAlt },
  th: {
    border: `1px solid ${T.rule}`,
    background: T.panelAlt,
    padding: "10px",
    fontSize: "11.5px",
    color: T.inkDim,
    fontWeight: 600,
    textTransform: "uppercase",
    letterSpacing: "0.04em",
  },
  thRow: {
    border: `1px solid ${T.rule}`,
    background: T.panelAlt,
    padding: "10px",
    fontSize: "11.5px",
    color: T.inkDim,
    fontWeight: 600,
    whiteSpace: "nowrap",
  },
  td: { border: `1px solid ${T.rule}`, padding: "10px" },
  cubeWrap: { display: "flex", justifyContent: "center" },
  cubeSvg: { width: "100%", maxWidth: "460px", height: "auto" },
  cubeFoot: { color: T.inkDim, fontSize: "11.5px", textAlign: "center", marginTop: "6px", maxWidth: "480px", marginLeft: "auto", marginRight: "auto" },
  linusCard: {
    display: "flex",
    flexDirection: "column",
    gap: "8px",
    alignItems: "flex-start",
    textAlign: "left",
    width: "100%",
    background: T.panel,
    border: `1px solid ${T.rule}`,
    borderLeft: `3px solid ${T.amber}`,
    borderRadius: "8px",
    padding: "16px 18px",
  },
  linusCardActive: { background: T.amber + "12", borderColor: T.amber },
  linusFormula: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "20px",
    fontWeight: 700,
    color: T.amber,
  },
  linusText: { color: T.ink, fontSize: "13px", lineHeight: 1.6 },
  sidebar: { position: "sticky", top: "24px" },
  sidebarInner: {
    background: T.panel,
    border: `1px solid ${T.rule}`,
    borderRadius: "10px",
    padding: "18px",
    display: "flex",
    flexDirection: "column",
    gap: "8px",
  },
  sidebarEyebrow: {
    fontSize: "10px",
    textTransform: "uppercase",
    letterSpacing: "0.1em",
    color: T.inkDim,
    fontWeight: 600,
  },
  sidebarFormula: {
    fontFamily: "'IBM Plex Mono', monospace",
    fontSize: "26px",
    fontWeight: 700,
    color: T.amber,
  },
  sidebarTitle: { fontSize: "14px", margin: "2px 0 0", fontWeight: 700 },
  sidebarBlurb: { fontSize: "12.5px", color: T.inkDim, lineHeight: 1.55, margin: 0 },
  codeBlock: {
    background: T.bg,
    border: `1px solid ${T.rule}`,
    borderRadius: "7px",
    padding: "12px",
    fontSize: "11px",
    lineHeight: 1.6,
    overflowX: "auto",
    color: T.ink,
    fontFamily: "'IBM Plex Mono', monospace",
    margin: "6px 0",
    maxHeight: "440px",
  },
  sidebarActions: { display: "flex", gap: "8px", alignItems: "center" },
  copyBtn: {
    background: T.panelAlt,
    border: `1px solid ${T.rule}`,
    color: T.ink,
    borderRadius: "6px",
    padding: "8px 12px",
    fontSize: "11.5px",
    fontWeight: 600,
    fontFamily: "'IBM Plex Mono', monospace",
  },
  playLink: {
    color: T.cyan,
    fontSize: "11.5px",
    fontWeight: 600,
    fontFamily: "'IBM Plex Mono', monospace",
    textDecoration: "none",
  },
  sidebarNote: { fontSize: "10.5px", color: T.inkDim, marginTop: "2px" },
};
```

</details>

<details>
  <summary>zig ?int vs int memory size</summary>

```zig
const std = @import("std");

pub fn main() void {
    std.debug.print("--- Value Optionality (Uses a Tag) ---\n", .{});
    std.debug.print("size of i32:     {} bytes\n", .{@sizeOf(i32)});
    std.debug.print("size of ?i32:    {} bytes (Larger!)\n", .{@sizeOf(?i32)});

    std.debug.print("\n--- Pointer Optionality (Optimized) ---\n", .{});
    std.debug.print("size of *i32:    {} bytes\n", .{@sizeOf(*i32)});
    std.debug.print("size of ?*i32:   {} bytes (Same size!)\n", .{@sizeOf(?*i32)});

    // Demonstrate distinguishing 0 from null
    var maybe_int: ?i32 = 0;
    if (maybe_int) |val| {
        std.debug.print("\nmaybe_int is present and its value is: {}\n", .{val});
    }

    maybe_int = null;
    if (maybe_int == null) {
        std.debug.print("maybe_int is now null, which is different from 0.\n", .{});
    }
}
```

</details>

<details>
  <summary>zig ?*?*?int -> print path</summary>

```zig
const std = @import("std");

inline fn deepPrint(outer: ?*?*?i32, base_addr: usize) void {
    // Helper to print formatting logic once
    const printAddr = struct {
        fn run(label: []const u8, ptr: anytype, base: usize) void {
            const addr = @intFromPtr(ptr);
            const offset = @as(i128, @intCast(addr)) - @as(i128, @intCast(base));
            // Manually add '+' for positive offsets since Zig doesn't support {:+}
            const sign = if (offset >= 0) "+" else "";
            std.debug.print("{s} [0x{x} (base{s}{d})] -> ", .{ label, addr, sign, offset });
        }
    }.run;

    // Level 1: Outer Pointer
    if (outer) |inner_ptr_ref| {
        printAddr("outer ptr", inner_ptr_ref, base_addr);

        // Level 2: Inner Pointer
        if (inner_ptr_ref.*) |int_ref| {
            printAddr("inner ptr", int_ref, base_addr);

            // Level 3: The actual Integer Value
            if (int_ref.*) |val| {
                std.debug.print("int was {}\n", .{val});
            } else {
                std.debug.print("int was null -> STOP\n", .{});
            }
        } else {
            std.debug.print("inner ptr [null] -> STOP\n", .{});
        }
    } else {
        std.debug.print("outer ptr [null] -> STOP\n", .{});
    }
}

pub fn main() void {
    // Capture base address
    var origin: i32 = 0;
    const base_addr = @intFromPtr(&origin);

    std.debug.print("--- Triple-Nullability Cube (Base: 0x{x}) ---\n\n", .{base_addr});

    // Setup variables on the stack
    var middle_null: ?*?i32 = null;

    var val_null: ?i32 = null;
    var middle_to_val_null: ?*?i32 = &val_null;

    var val_one: ?i32 = 1;
    var middle_to_val_one: ?*?i32 = &val_one;

    // V1: Root is null
    std.debug.print("V1: ", .{});
    deepPrint(null, base_addr);

    // V2: Root exists, points to a null pointer
    std.debug.print("V2: ", .{});
    deepPrint(&middle_null, base_addr);

    // V3: Root and Inner exist, but value is null
    std.debug.print("V3: ", .{});
    deepPrint(&middle_to_val_null, base_addr);

    // V4: All layers exist
    std.debug.print("V4: ", .{});
    deepPrint(&middle_to_val_one, base_addr);
}
```

</details>

```
--- Triple-Nullability Cube (Base: 0x7ffe9e4604b0) ---

V1: outer ptr [null] -> STOP
V2: outer ptr [0x7ffe9e460498 (base-24)] -> inner ptr [null] -> STOP
V3: outer ptr [0x7ffe9e4604a0 (base-16)] -> inner ptr [0x7ffe9e4604b4 (base+4)] -> int was null -> STOP
V4: outer ptr [0x7ffe9e4604a8 (base-8)] -> inner ptr [0x7ffe9e4604bc (base+12)] -> int was 1
```

<details>
  <summary>zig</summary>

```zig
const std = @import("std");

const Node = struct {
    value: i32 = 0,
    next: ?*Node = null,
};

// --- CONFIGURATION ---
const use_fast = true;
const mode_string = if (use_fast) "FAST (Indirect Pointer)" else "SLOW (Prev Pointer)";

/// Implementation 1: Slow (Tracking previous node)
fn removeEntrySlow(head: *?*Node, entry: *Node) void { // non-null pointer to nullable pointer to non-optional Node. Why to nullable? Bc we will make the stack cell 00000 if only one node
    var prev: ?*Node = null;
    var walk = head.*;

    while (walk != entry) {
        prev = walk;
        // .? asserts walk is not null because we assume the entry exists in the list
        walk = walk.?.next;
    }

    if (prev == null) {
        head.* = entry.next;
    } else {
        prev.?.next = entry.next;
    }
}

/// Implementation 2: Fast (Using indirect pointers)
/// This is the Zig version of the "Linus Torvalds" pointer approach
fn removeEntryFast(head: *?*Node, entry: *Node) void {
    // p is a pointer to a pointer (indirect pointer)
    var p: *?*Node = head;

    // While the pointer we are looking at doesn't point to the target entry
    while (p.* != entry) {
        // Move 'p' to point to the address of the 'next' field of the current node
        p = &p.*.?.next;
    }

    // Direct assignment: update the 'next' field of the previous node
    // (or the head itself) to skip the entry.
    p.* = entry.next;
}

inline fn removeEntry(head: *?*Node, entry: *Node) void {
    if (comptime use_fast) {
        removeEntryFast(head, entry);
    } else {
        removeEntrySlow(head, entry);
    }
}

/// Helper: Print the list
fn printList(head: ?*Node) void {
    var curr = head;
    while (curr) |n| {
        std.debug.print("{} -> ", .{n.value});
        curr = n.next;
    }
    std.debug.print("null\n", .{});
}

/// Helper: O(1) Append using indirect tail pointer
/// Returns the address of the 'next' field of the new node
fn append(tail: *?*Node, allocator: std.mem.Allocator, val: i32) !*?*Node {
    const new_node = try allocator.create(Node);
    new_node.* = .{ .value = val, .next = null };

    tail.* = new_node;
    return &new_node.next;
}

pub fn main() !void {
    // page_allocator is the most stable allocator across different Zig versions
    const allocator = std.heap.page_allocator;

    std.debug.print("=== Running with: {s} ===\n\n", .{mode_string});

    var head: ?*Node = null;
    var tail_ptr: *?*Node = &head;

    // O(1) Appends (Zero loops, Zero 'if' statements)
    tail_ptr = try append(tail_ptr, allocator, 10);
    tail_ptr = try append(tail_ptr, allocator, 20);
    tail_ptr = try append(tail_ptr, allocator, 30);
    tail_ptr = try append(tail_ptr, allocator, 40);
    tail_ptr = try append(tail_ptr, allocator, 50);

    std.debug.print("Original list:\n", .{});
    printList(head);

    // 1. Remove FRONT (10)
    if (head) |front| {
        removeEntry(&head, front);
        allocator.destroy(front);
        std.debug.print("\nAfter removing FRONT (10):\n", .{});
        printList(head);
    }

    // 2. Remove END (50)
    var end_search = head;
    while (end_search) |n| {
        if (n.next == null) break;
        end_search = n.next;
    }

    if (end_search) |end| {
        removeEntry(&head, end);
        allocator.destroy(end);
        std.debug.print("\nAfter removing END (50):\n", .{});
        printList(head);
    }

    // Cleanup remaining list memory
    var curr = head;
    while (curr) |n| {
        const next = n.next;
        allocator.destroy(n);
        curr = next;
    }
}
```

</details>

<details>
  <summary>c3 (doenst work)</summary>

```c3
module main;

import std::io;

struct Node {
    int value;
    Node* next;
}

const bool USE_FAST = true;

/**
 * Implementation 1: Slow
 */
fn void remove_entry_slow(Node** head, Node* entry) {
    Node* prev = null;
    Node* walk = *head;

    while (walk != entry) {
        prev = walk;
        walk = walk.next;
    }

    if (prev == null) {
        *head = entry.next;
    } else {
        prev.next = entry.next;
    }
}

/**
 * Implementation 2: Fast (Indirect Pointer)
 */
fn void remove_entry_fast(Node** head, Node* entry) {
    Node** p = head;

    while (*p != entry) {
        // p points to the previous node's 'next' field (or 'head')
        // we take the address of the current node's 'next' field
        p = &((*p).next);
    }

    // This updates the actual memory slot 'p' points to
    *p = entry.next;
}

fn void remove_entry(Node** head, Node* entry) {
    if (USE_FAST) {
        remove_entry_fast(head, entry);
    } else {
        remove_entry_slow(head, entry);
    }
}

/**
 * O(1) Append
 * Note: mem::new(Node) is the standard C3 allocation syntax
 */
fn Node** append(Node** tail, int val) {
    Node* new_node = mem::new(Node);
    new_node.value = val;
    new_node.next = null;

    *tail = new_node;
    return &new_node.next;
}

fn void print_list(Node* head) {
    Node* curr = head;
    while (curr != null) {
        io::printf("%d -> ", curr.value);
        curr = curr.next;
    }
    io::printn("null");
}

fn int main() {
    io::printf("=== Running with: %s ===\n", USE_FAST ? "FAST" : "SLOW");

    Node* head = null;
    Node** tail_ptr = &head;

    // O(1) Appends
    tail_ptr = append(tail_ptr, 10);
    tail_ptr = append(tail_ptr, 20);
    tail_ptr = append(tail_ptr, 30);
    tail_ptr = append(tail_ptr, 40);
    tail_ptr = append(tail_ptr, 50);

    io::printn("Original list:");
    print_list(head);

    // 1. Remove FRONT (10)
    if (head != null) {
        Node* front = head;
        remove_entry(&head, front);
        mem::free(front);
        io::printn("\nAfter removing FRONT (10):");
        print_list(head);
    }

    // 2. Remove END (50)
    Node* end_search = head;
    while (end_search != null && end_search.next != null) {
        end_search = end_search.next;
    }

    if (end_search != null) {
        remove_entry(&head, end_search);
        mem::free(end_search);
        io::printn("\nAfter removing END (50):");
        print_list(head);
    }

    // Cleanup remaining memory
    Node* curr = head;
    while (curr != null) {
        Node* next = curr.next;
        mem::free(curr);
        curr = next;
    }

    return 0;
}
```

</details>





<details>
  <summary>go (no not-null pointers like in zig. so shit)</summary>

```go
package main

import "fmt"

type Node struct {
	Value int
	Next  *Node
}

// Implementation 1: Slow (Traditional prev pointer)
func removeEntrySlow(head **Node, entry *Node) {
	var prev *Node = nil
	walk := *head

	for walk != entry && walk != nil {
		prev = walk
		walk = walk.Next
	}

	if prev == nil {
		// Entry was the head
		*head = entry.Next
	} else {
		// Entry was in the middle or end
		prev.Next = entry.Next
	}
}

// Implementation 2: Fast (Indirect Pointer approach)
// This is the Go version of the Linus Torvalds approach.
func removeEntryFast(head **Node, entry *Node) {
	// p is a pointer to a pointer (**Node)
	p := head

	// Iterate until the pointer we are looking at points to the entry
	for *p != entry {
		// Advance p to point to the address of the 'Next' field
		// of the current node.
		p = &((*p).Next)
	}

	// Update the pointer (either the head or a Next field)
	// to skip the entry.
	*p = entry.Next
}

// Helper: O(1) Append using indirect tail pointer
func appendNode(tail **Node, val int) **Node {
	newNode := &Node{Value: val, Next: nil}
	*tail = newNode
	// Return the address of the Next field of the new node
	return &newNode.Next
}

func printList(head *Node) {
	for curr := head; curr != nil; curr = curr.Next {
		fmt.Printf("%d -> ", curr.Value)
	}
	fmt.Println("nil")
}

func main() {
	var head *Node = nil
	// tailPtr points to the pointer that needs to be updated
	tailPtr := &head

	// O(1) Appends
	tailPtr = appendNode(tailPtr, 10)
	tailPtr = appendNode(tailPtr, 20)
	tailPtr = appendNode(tailPtr, 30)
	tailPtr = appendNode(tailPtr, 40)
	tailPtr = appendNode(tailPtr, 50)

	fmt.Println("Original list:")
	printList(head)

	// 1. Remove FRONT (10)
	if head != nil {
		front := head
		removeEntryFast(&head, front)
		fmt.Println("\nAfter removing FRONT (10):")
		printList(head)
	}

	// 2. Remove END (50)
	var end *Node = head
	for end.Next != nil {
		end = end.Next
	}
	removeEntryFast(&head, end)
	fmt.Println("\nAfter removing END (50):")
	printList(head)
}
```

</details>

<details>
  <summary>rust (but unsafe if needed and double pointers but outer is nullable and inner is not nullable)</summary>

```rust
use std::ptr::{NonNull};

struct Node {
    value: i32,
    // The "inner" pointer. Using Option<NonNull> is the Rust way to
    // have a "nullable pointer" that is non-nullable when active.
    next: Option<NonNull<Node>>,
}

// HERE IS A PROBLEM : I WANT TO REQUIRE THAT head ON INPUT is NOT NULL, but on output MAY BE NULL, and the memory location should be same
unsafe fn remove_entry_fast(head: &mut Option<NonNull<Node>>, entry: NonNull<Node>) {
    // 1. Handle "outer is nullable" check
    // THIS IS NEEDED WHEN USING
    // head: *mut Option<NonNull<Node>>
    // instead of
    // head: &mut Option<NonNull<Node>>
    // NOT NEEDED NOT bc & guarantees NonNull pointers
    //if head.is_null() { return; }

    // 'p' is our indirect pointer (pointer to a pointer)
    let mut p: *mut Option<NonNull<Node>> = head;

    // While the pointer at 'p' does not point to our entry
    // We compare the addresses of the NonNull pointers
    unsafe {
    while (*p).is_some_and(|node_ptr| node_ptr != entry) {
        // Move 'p' to point to the address of the 'next' field of the current node
        // We unwrap the optional because the while loop condition guaranteed it exists
        p = &mut (*(*p).unwrap().as_ptr()).next;
    }

    // Direct assignment: The pointer at 'p' (either 'head' or a 'next' field)
    // is updated to point to whatever the entry was pointing to.
    *p = (*entry.as_ptr()).next;
    }
}

// TODO: maybe this will reuse

/// The "Linus" signature:
/// - head_addr: A Non-nullable pointer to a nullable pointer slot.
/// - entry: The non-nullable node to remove.
/// - Returns: A reference to the same memory slot after modification.
// unsafe fn remove_entry_fast<'a>(
//     head_addr: NonNull<Option<NonNull<Node>>>,
//     entry: NonNull<Node>
// ) -> &'a Option<NonNull<Node>> {
//
//     // p is our indirect pointer (starts at the address of 'head')
//     let mut p: *mut Option<NonNull<Node>> = head_addr.as_ptr();
//
//     unsafe {
//         // While the pointer inside slot 'p' does not point to 'entry'
//         while (*p).map_or(false, |node_ptr| node_ptr != entry) {
//             // p = address of the 'next' field of the current node
//             p = &mut (*(*p).unwrap().as_ptr()).next;
//         }
//
//         // The "Magic" update: Write the successor's address into the slot 'p' points to.
//         // This slot is either the 'head' variable or a 'next' field.
//         *p = (*entry.as_ptr()).next;
//
//         // Return a reference to the updated memory location
//         &*p
//     }
// }


/// Helper: O(1) Append using indirect tail pointer
unsafe fn append(tail: *mut Option<NonNull<Node>>, val: i32) -> *mut Option<NonNull<Node>> {
    // Allocate a new node on the heap (Box::into_raw keeps it alive)
    let new_node = Box::into_raw(Box::new(Node {
        value: val,
        next: None,
    }));

    unsafe {
    let non_null_node = NonNull::new_unchecked(new_node);

    // Link the new node into the slot pointed to by tail
    *tail = Some(non_null_node);

    // Return the address of the new node's next field
    &mut (*new_node).next
    }
}

fn print_list(head: Option<NonNull<Node>>) {
    let mut curr = head;
    while let Some(node_ptr) = curr {
        unsafe {
            print!("{} -> ", (*node_ptr.as_ptr()).value);
            curr = (*node_ptr.as_ptr()).next;
        }
    }
    println!("null");
}

#[inline(never)]
pub fn main() {
    let mut head: Option<NonNull<Node>> = None;
    let mut tail_ptr: *mut Option<NonNull<Node>> = &mut head;

    unsafe {
        // O(1) Appends
        tail_ptr = append(tail_ptr, 10);
        tail_ptr = append(tail_ptr, 20);
        tail_ptr = append(tail_ptr, 30);
        tail_ptr = append(tail_ptr, 40);
        _ = append(tail_ptr, 50); // Use _ to avoid unused assignment warning

        println!("Original list:");
        print_list(head);

        // 1. Remove FRONT (10)
        if let Some(front) = head {
            remove_entry_fast(&mut head, front);
            // Re-constitute Box to free memory
            let _ = Box::from_raw(front.as_ptr());
            println!("\nAfter removing FRONT (10):");
            print_list(head);
        }

        // 2. Remove END (50)
        let mut end = head.unwrap();
        while let Some(next_node) = (*end.as_ptr()).next {
            end = next_node;
        }
        remove_entry_fast(&mut head, end);
        let _ = Box::from_raw(end.as_ptr());
        println!("\nAfter removing END (50):");
        print_list(head);

        // Cleanup remaining
        let mut curr = head;
        while let Some(node_ptr) = curr {
            let next = (*node_ptr.as_ptr()).next;
            let _ = Box::from_raw(node_ptr.as_ptr());
            curr = next;
        }
    }
}
```

</details>



<details>
  <summary>odin (no not-null pointers support)</summary>

```odin
package main

import "core:fmt"

Node :: struct {
	value: i32,
	next:  ^Node,
}

// --- CONFIGURATION ---
USE_FAST :: true
MODE_STRING := USE_FAST ? "FAST (Indirect Pointer)" : "SLOW (Prev Pointer)"

/**
 * Implementation 1: Slow (Tracking previous node)
 */
remove_entry_slow :: proc(head: ^^Node, entry: ^Node) {
	// Assertions enforce our "Must not be null" contract
	assert(head != nil, "head handle must not be nil")
	assert(entry != nil, "entry node must not be nil")

	prev: ^Node = nil
	walk := head^

	for walk != entry && walk != nil {
		prev = walk
		walk = walk.next
	}

	if prev == nil {
		head^ = entry.next
	} else {
		prev.next = entry.next
	}
}

/**
 * Implementation 2: Fast (Indirect Pointer approach)
 * This is the Odin version of the Linus Torvalds approach.
 */
remove_entry_fast :: proc(head: ^^Node, entry: ^Node) {
	// Assertions enforce our "Must not be null" contract
	assert(head != nil, "head handle must not be nil")
	assert(entry != nil, "entry node must not be nil")

	p := head

	// Traverse until the pointer in slot 'p' points to entry
	for p^ != entry {
		// p points to the previous node's 'next' field (or the head)
		// We move p to point to the current node's 'next' field
		p = &p^.next
	}

	// Update the memory slot (head or a next field) to skip the entry
	p^ = entry.next
}

/**
 * Dispatcher
 * 'when' is Odin's version of 'if constexpr'
 */
remove_entry :: proc(head: ^^Node, entry: ^Node) {
	when USE_FAST {
		remove_entry_fast(head, entry)
	} else {
		remove_entry_slow(head, entry)
	}
}

/**
 * Helper: O(1) Append using indirect tail pointer
 */
append :: proc(tail: ^^Node, val: i32) -> ^^Node {
	assert(tail != nil)

	new_node := new(Node)
	new_node.value = val
	new_node.next = nil

	tail^ = new_node
	return &new_node.next
}

print_list :: proc(head: ^Node) {
	for curr := head; curr != nil; curr = curr.next {
		fmt.printf("%d -> ", curr.value)
	}
	fmt.println("nil")
}

main :: proc() {
	fmt.printf("=== Running with: %s ===\n\n", MODE_STRING)

	head: ^Node = nil
	tail_ptr := &head

	// O(1) Appends
	tail_ptr = append(tail_ptr, 10)
	tail_ptr = append(tail_ptr, 20)
	tail_ptr = append(tail_ptr, 30)
	tail_ptr = append(tail_ptr, 40)
	tail_ptr = append(tail_ptr, 50)

	fmt.println("Original list:")
	print_list(head)

	// 1. Remove FRONT (10)
	if head != nil {
		front := head
		remove_entry(&head, front)
		free(front)
		fmt.println("\nAfter removing FRONT (10):")
		print_list(head)
	}

	// 2. Remove END (50)
	// First, find the end node
	end_search := head
	for end_search != nil && end_search.next != nil {
		end_search = end_search.next
	}

	if end_search != nil {
		remove_entry(&head, end_search)
		free(end_search)
		fmt.println("\nAfter removing END (50):")
		print_list(head)
	}

	// Cleanup remaining memory
	curr := head
	for curr != nil {
		next := curr.next
		free(curr)
		curr = next
	}
}
```

</details>




<details>
  <summary>nim (has not null and strict null checking, but its checker is stupid/has-amnesia bc I assign the not null value to nullable pointer and it forgets)</summary>



| Requirement | Nim Syntax | Explanation |
| :--- | :--- | :--- |
| **Outer Non-Null, Inner Nullable** | `ptr (ptr NodeObj) not nil` | A valid address of a variable that holds a nullable pointer. |
| **Outer Non-Null, Inner Non-Null** | `ptr (ptr NodeObj not nil) not nil` | A valid address of a variable that **must** hold a valid address. |
| **Triple Optionality (`?*?*?int`)** | `ptr ptr Option[int]` | Everything is nullable by default. |

```nim
{.experimental: "strictNotNil".}

type
  NodeObj = object
    value: int
    next: ptr NodeObj
  Node = ptr NodeObj

# --- CONFIGURATION ---
const useFast = true
const modeString = if useFast: 
  "FAST (Indirect Pointer)" else: "SLOW (Prev Pointer)"

## Implementation 1: Slow
proc removeEntrySlow(head: ptr Node not nil, entry: Node not nil) =
  var prev: Node = nil
  var walk = head[]

  while walk != nil and walk != entry:
    prev = walk
    walk = walk.next

  if prev == nil:
    head[] = entry.next
  else:
    prev.next = entry.next

## Implementation 2: Fast (Indirect Pointer approach)
## head is a 'ptr Node' (pointer to a pointer)
proc removeEntryFast(head: ptr Node, entry: Node not nil) =
  # 'p' is our indirect pointer
  var p: ptr Node = head

  # While the pointer stored at address 'p' does not point to 'entry'
  while p[] != entry:
    # addr() takes the address of the field
    # p[] dereferences to get the current node
    p = addr(p[].next)

  # Update the slot (head or a next field) to skip entry
  p[] = entry.next

proc removeEntry(head: ptr Node, entry: Node not nil) =
  when useFast:
    removeEntryFast(head, entry)
  else:
    removeEntrySlow(head, entry)

## Helper: O(1) Append
proc append(tail: ptr Node, val: int): ptr Node =
  # create() is Nim's version of malloc
  let newNode = create(NodeObj)
  newNode.value = val
  newNode.next = nil

  tail[] = newNode
  return addr(newNode.next)

proc printList(head: Node) =
  var curr = head
  while curr != nil:
    stdout.write($curr.value & " -> ")
    curr = curr.next
  echo "nil"

proc main() =
  echo "=== Running with: ", modeString, " ===\n"

  var head: Node = nil
  var tailPtr: ptr Node = addr(head)

  # O(1) Appends
  tailPtr = append(tailPtr, 10)
  tailPtr = append(tailPtr, 20)
  tailPtr = append(tailPtr, 30)
  tailPtr = append(tailPtr, 40)
  tailPtr = append(tailPtr, 50)

  echo "Original list:"
  printList(head)

  # 1. Remove FRONT (10)
  if head != nil:
    let front = head
    removeEntry(addr(head), front)
    dealloc(front) # dealloc() is Nim's free
    echo "\nAfter removing FRONT (10):"
    printList(head)

  # 2. Remove END (50)
  var endNode = head
  while endNode != nil and endNode.next != nil:
    endNode = endNode.next
  
  if endNode != nil:
    removeEntry(addr(head), endNode)
    dealloc(endNode)
    echo "\nAfter removing END (50):"
    printList(head)

  # Cleanup
  var curr = head
  while curr != nil:
    let next = curr.next
    dealloc(curr)
    curr = next

main()
```

</details>

<!--
<details>
  <summary>go</summary>

```go
```

</details>
-->

- the safe version was fastest https://github.com/srghma/aeneas-test
