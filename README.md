This is Napalm programming language.

It is a new scripting programming language inspired by JavaScript, TypeScript and Wren.

My intention is this language not to be a toy programming language, but something you could use to build real apps when it's released. I am far from this, however.

My main goal is Napalm to be fast. To achieve this I use:
- Cranelift for the JIT, with a rich and optimized runtime, and a fast calling convention based on registers that do not allocate on the 'heap'.
- Several optimizations in the IR pre-JIT. Some of them are very impactful like natively memoizing hot, pure classes.
- Hidden classes/shapes with monomorphic and polymorphic inline caches. This is the same mechanism that modern top-tier JavaScript engines use (V8, SpiderMonkey, JSC).
- A StickyImmix garbage collector, made with MMTk. StickyImmix is a generational garbage collector, despite it doesn't use a nursery space.
- String interning, to save a lot of memory, and to make string comparisons trivial (no longer byte to byte comparison, just compare the pointer).
- Small object optimizations, inlining and allocating on the 'stack' as much as possible. Usage of TinyVec, CompactStr, SmallBox, and my own CompactMap: are structures that allocate on the 'stack' while the content is small.
- There are planned a lot of extra optimizations, like for example Escape Analisys, Loop Fusion, Deforestation, and Function Inlining.

Language features (Done/Planned):
- Variables and assignations. [x]
- Control flow and loops. [x]
- Arrays and arrays methods. [x]
- Strings and strings methods. [x]
- Functions, lambda functions, and closures. [x]
- Objects and object methods. [x]
- Classes, inheritance, getters/setters, static methods. [x]
- Event loop, timers, micro-tasks, macro-tasks. [x]
- Promises, Deferreds, and async/await. [x]
- Map and Set, and all their methods. [x]
- Modules, imports and exports. [x]
- Object destructuring, object rest, and object spread. [x]
- Array functional methods. [x]
- Operator conditional/nullish, optional chaining, pipeline operator. [x]
- A small, concise, powerful eDSL for creating server services. [x]
- Enums. [ ]
- Try/Catch/Finally. [ ]
- Defer/Errdefer. [ ]
- Dates and dates methods. [ ]
- Proxies a là JavaScript. [ ]
- Generators. [ ]
- Fibers a là Wren. [ ]
- Ranges a là Wren. [ ]
- Decorators a là TypeScript. [ ]
- Operator overloading for classes. [ ]
- An optional type system a là TypeScript, with optional static typing, interfaces and generics. [ ]
- TODO (add more, functional programming, reactive programming, UI bindings, standard library, etc). [ ]

Known bugs:
- When a function is natively memoized, it can cause use-after-free errors if memoized values are not primitives (like an object), since complex values allocate on the GC that can free them in any moment while the native memoization thinks they are still there.

Limitations:
Napalm, by design, does not have an interpreter, but just a JIT. I opted for a single JIT without re-compilations instead of a complex architecture with an interpreter and a multi-tier JIT, because I am a single developer working on this and I would have not enough time. I opted for simplicity instead of complexity. Also, I find a waste of time and resources, to develop them, since they are only going to run for a fraction of a second until the top-tier JIT kicks-in. This sadly mean that:
- Cold start time might be somewhat slower than very fast engines like Wren or LuaJIT (but still faster than CPython or Node).
- I can't do a lot of speculative optimizations nor PGO, so it's unlikely Napalm gets as fast as top-tier JavaScript engines and LuaJIT (though still competitive, in some benchmarks we are even faster than Node).
- Napalm won't work on platforms where JIT compilation isn't allowed (like iOS, consoles, or running in WebAssembly)
I have, however, a proto-interpreter (direct threaded, register based, compact bytecode) in very very early stages in a different project, I might consider developing it further and adapting it to Napalm once I finish everything else.
