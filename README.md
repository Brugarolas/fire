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
- Enums. [x]
- Try/Catch/Finally. [x]
- Defer/Errdefer. [x]
- Dates and dates methods. [ ]
- Proxies a là JavaScript. [ ]
- Generators. [ ]
- Fibers a là Wren. [ ]
- Ranges a là Wren. [ ]
- Decorators a là TypeScript. [ ]
- Operator overloading for classes. [ ]
- An optional type system a là TypeScript, with optional static typing, interfaces and generics. [x]
- TODO (add more, functional programming, reactive programming, UI bindings, standard library, etc). [ ]

Enums:
```text
enum Color { Red, Green, Blue }             // 0, 1, 2
enum Status { Pending = 10, Running, Done = 20 }
enum Direction { Up = "up", Down = "down" }
enum Alias { First = 4, Same = First, Next = Alias.First + 1 }

print(Color.Green);                         // 1
print(Color[Color.Green]);                  // "Green"
print(Direction.Up);                        // "up"
```
- Declarations accept an optional trailing comma and an optional semicolon after `}`. Empty enums are supported.
- Numeric members start at zero and increment from the previous numeric member. Explicit negative and fractional values are supported. A member after a string value must have an explicit initializer.
- Initializers are compile-time constants: numeric/string literals, previous members of the same enum (`First`, `Alias.First`, or `Alias["First"]`), parentheses, unary `+`/`-`, numeric `+`, `-`, `*`, `/`, `%`, and string concatenation with `+`. Forward references, function calls, non-finite results, and auto-increments that exceed numeric precision are rejected.
- Numeric members get reverse mappings; the last member with a duplicated numeric value wins. String members do not get reverse mappings. Duplicate member names and numeric member names are rejected.
- Enums work at module level and in local declaration scopes, including async functions, class methods, and captured closures. Module enums are shared objects accessible to functions in that module, not recreated on each access.
- Use `export enum Color { ... }` or `export { Color };`, then named imports (including aliases) or namespace imports. Private enums are not exposed in module namespaces.
- Enum values are ordinary numbers or strings, and enum namespaces use ordinary Napalm object semantics. This is not a nominal type system or a read-only property checker. Payload variants, declaration merging, `const enum` erasure, and arbitrary runtime initializers are not supported.
- Constants are resolved by the frontend; object construction and member access use the existing Cranelift/JIT paths. No enum-specific unsafe C runtime helpers are needed. Numeric indexing on ordinary objects also reads string-keyed properties, enabling reverse lookup. An object's own `size` property takes precedence over the builtin size operation.

Run the example with `cargo run -- scripts/enums.napalm` and the language/module regressions with `cargo test --test enums -- --test-threads=1`.
Use `--no-default-features` for the same tests without GC if MMTk cannot reserve its heap address range on Windows.
Compilation errors now exit with a nonzero status rather than reporting success.

Exception handling:
- `throw` accepts any value; `catch (error)` receives that same value. `catch { ... }` is also supported.
- `finally` runs on normal completion, return, and exception propagation. A return or throw in `finally` replaces the pending result.
- Handlers, finalizers, saved locals, and completion dispatch are compiled directly with Cranelift. A small thread-local state accessor carries exceptions across the existing single-result calling convention; no runtime unwinder or function re-entry is used.
- Async functions settle their promises only after finalizers finish. Rejected `await` expressions can be caught.
- Uncaught top-level exceptions print a diagnostic and exit with a nonzero status.
- WIR optimization passes currently bypass functions containing try regions because those passes do not yet model exceptional CFG edges. Cranelift still compiles these functions normally.

Run the exception example with `cargo run -- scripts/trycatch.napalm` and the regression suite with `cargo test --test trycatch`.
If MMTk cannot reserve its heap address range on Windows, the same suite can be run without GC using `cargo test --no-default-features --test trycatch`.

Deferred cleanup (Zig-style):
```text
fn work(fail) {
    var value = 1;
    defer print(["last cleanup", value]);
    errdefer |error| print(["failed", error]);
    defer { print("first cleanup"); value = value + 1; }
    value = 7;
    if (fail) { throw "failure"; }
    return value; // result is 7; the last cleanup sees 8
}
```
- `defer expression;` and `defer { statements }` run at the end of the enclosing lexical scope, in reverse registration order. Expressions are evaluated at exit, using the latest values of locals visible at registration. Block bodies accept an optional trailing semicolon.
- `errdefer expression;` and `errdefer { statements }` run only when an exception escapes that scope. Napalm uses thrown exceptions, not Zig error-union return values: normal returns (including null/false) do not trigger `errdefer`, and exceptions caught inside the scope do not trigger it.
- `errdefer |error| expression;` or `errdefer |error| { statements }` binds the original thrown value inside the cleanup. Reassigning that binding does not change the propagated exception.
- Registrations only take effect when reached. Function bodies, branches, loop iterations, and try/catch/finally bodies each have their own cleanup scope. A loop body finishes its cleanup before the next iteration or `for` step.
- A return expression is evaluated before cleanup starts. Deferred mutations affect subsequent cleanups and enclosing scopes but do not replace the already-computed return value (ordinary object-reference semantics still apply).
- `return` cannot escape a cleanup body; returns inside nested function literals are allowed. A cleanup that throws replaces the pending return/exception, while remaining outer cleanups still run. This follows Napalm's `finally` semantics rather than Zig's restriction on fallible cleanup.
- Cleanup works in closures, instance/static methods, module initializers, and async functions. Async cleanup, including `await`, finishes before the promise settles. Module-level cleanup runs when that module's initializer exits, not at process shutdown.
- Cleanup control flow is compiled with Cranelift using lexical handler/finalizer regions. No runtime defer scheduler, cleanup closures, or new unsafe C helpers are required. As with explicit try regions, WIR optimization passes currently bypass these functions; Cranelift still compiles them.

Run `cargo run -- scripts/defer.napalm` for the example and `cargo test --test defer -- --test-threads=1` for cleanup regressions. Add `--no-default-features` to test without GC when MMTk cannot reserve its Windows heap range.

Optional static typing:
```text
interface Named { name: string; }
interface Animal extends Named { legs: number; speak(): string; }
type Id = number | string;
type Maybe<T> = T | null;

class Dog implements Animal {
    name: string;
    legs: number = 4;
    constructor(name: string) { this.name = name; }
    fn speak(): string { return this.name + " says woof"; }
}

fn intro(a: Animal): string { return a.speak() + " on " + a.legs + " legs"; }
fn longest<T extends { length: number }>(a: T, b: T): T { return a.length >= b.length ? a : b; }
fn orZero(v: Maybe<number>): number { if (v == null) { return 0; } return v; }
fn tag(name: string, suffix?: string): string { return suffix == null ? name : name + suffix; }

var words: string[] = ["a", "b"];
var scores: Map<string, number> = new Map();
var n = untypedValue() as number;          // checked at runtime
```
- Types are optional and gradual. Unannotated values are `any`, and untyped code (including `Array`, `Map`, objects, and classes) behaves exactly as before; `var x = 1; x = "s";` still works.
- Types: `number` (a single numeric type), `string`, `boolean`, `null`/`undefined`, `void`, `any` (`unknown` is currently an alias of `any`), `never`, unions (`A | B`), arrays (`T[]`/`Array<T>`), `Map<K, V>`, `Set<T>`, `Promise<T>`, function types (`(x: T, y?: U) => R`), object types (`{ x: number; label?: string; m(): string }`), classes, enums, interfaces, and type aliases.
- Interfaces are structural and may `extend` other interfaces. `class C implements I` is verified at compile time. Object literals, class instances, and interface values satisfy an interface when they have compatible members. Strings and arrays satisfy `{ length: number }`.
- Generics work on functions, classes, class methods, interfaces, and aliases, with optional `extends` constraints. Type arguments can be explicit (`identity<number>(4)`, `new Box<string>(s)`) or inferred from arguments.
- Classes accept TypeScript-style field declarations (`name: string;`, `legs: number = 4;`); initializers run at the start of the constructor.
- Parameters may be optional (`p?: T`, meaning `T | null` when omitted); required parameters cannot follow optional ones. `value as T` is a checked cast.
- The checker runs before lowering and reports every type error with its function and source location: incompatible assignments, arguments, and returns; wrong arity; unknown members of known types; missing interface members; incorrect `implements`; and unknown types. The program does not run when type errors are found.
- Null checks narrow types: `x == null`, `x != null`, and truthiness in `if` branches; after an `if` whose branch returns or throws; and on the right of `&&`/`||`. Narrowing is dropped after assignments, around loops that assign the variable, and for variables assigned inside closures or `defer` blocks.
- In functions with annotations, an unannotated `var` takes its initializer's type. Untyped functions and top-level code keep `any` locals.
- When an `any` value flows into a typed parameter, variable, return value, or `as` cast, a compiled guard checks its runtime representation, including the members required by interface and object types. A mismatch throws a catchable string such as ``"TypeError: parameter `n` of `double` expects number"``. It runs `finally`/`errdefer`, rejects the promise of an async function, and exits with a nonzero status if uncaught.
- Known types let the lowerer emit specialized IR: typed string `+` and `==` become direct concatenation and comparison, `string + non-string` uses string concatenation, and typed array/string length and indexing call the JIT intrinsics directly instead of dynamic dispatch. Guards are inline Cranelift predicates (tag tests, string/array/object checks, and property lookups), not new unsafe C runtime helpers.
- `export interface`, `export type`, and annotated exports are checked across modules: named imports (including aliases such as `import { Point as P }`) and namespace imports (`import * as geo` with qualified types such as `geo.Point` or `geo.Box<number>`) carry their static types into the importing module. Imported functions are guarded only once, by the exporting module. Classes and enums are typed through namespaces too (`new geo.Box(1)`, `geo.Color.Red`). Interfaces and type aliases without `export` stay private: importing them is a compile-time error.
- Re-exports (`export { x, y as z } from "./m.napalm"` and `export * from "./m.napalm"`) forward the provider's live bindings, values and types alike; re-exporting a missing member is a compile-time error.
- Limitations: containers are not deep-checked at runtime (a `number[]` guard only checks for an array); `Map.get` returns the declared value type without a presence check; accessors are not part of interface shape checks; lambdas need explicit parameter annotations (no contextual typing); there are no literal, tuple, mapped, or conditional types, declaration merging, or generic method signatures inside interfaces/object types.

Run `cargo run -- scripts/types.napalm` for the example and `cargo test --test types -- --test-threads=1` for the regressions. The checker unit tests run with `cargo test --no-default-features --bin Napalm typeck`. Add `--no-default-features` to test without GC when MMTk cannot reserve its Windows heap range.

JIT core intrinsics:
- 26 runtime helpers now have shared Cranelift fast paths, used by native calls and the corresponding WIR array instructions.
- Type checks: string, map, set, proxy, and nullish.
- Arrays: length, indexed get/set, push/pop, shift/unshift, setLength, and fill. Reads, removals, primitive stores, and capacity-preserving resizes execute directly in generated code. Allocation, capacity growth, and GC pointer-store barriers use existing runtime helpers.
- `array.fill(value)` is now exposed as a method; it fills existing elements and returns null, matching the existing runtime helper.
- Strings: byte length, startsWith/endsWith, slice/substring, indexOf/lastIndexOf, trim/trimStart/trimEnd, and toUpperCase/toLowerCase. Existing byte-index and sentinel semantics are preserved. String results use the existing interner; prefix/suffix comparisons use the existing `memcmp` import.
- Short searches (up to 64 remaining bytes) run a generated search loop; larger searches retain Rust's optimized runtime search. ASCII trimming is compiled directly; non-ASCII boundaries use the Unicode-aware runtime. Case conversion handles ASCII strings up to 64 bytes in generated code and falls back for Unicode or longer inputs.
- Array layout offsets are discovered from the host compiler's actual `Vec<i64>` representation rather than assuming a Rust field order.

Run the language regression with `cargo run -- scripts/runtime_intrinsics.napalm`.
Run differential tests plus language/exception regressions with `cargo test --no-default-features --bin Napalm --test runtime_intrinsics --test trycatch -- --test-threads=1`.
Use `cargo test --test runtime_intrinsics` to exercise the GC-enabled pointer-store fallbacks.
The focused benchmark is `cargo run --no-default-features -- perf/runtime.napalm`; compare the program-execution timer rather than total build/JIT startup time.

Runtime semantics:
- Integer literals beyond `i32` use the existing `f64` representation instead of panicking. Binary64 precision and range apply to these literals.
- Binary `|` uses the existing bitwise numeric operations, with precedence between equality and logical `&&`. Bitwise operators (`|`, `<<`, `>>`, `>>>`) follow JavaScript ToInt32 semantics: operands wrap modulo 2^32, shift counts are taken modulo 32, and `>>>` yields an unsigned 32-bit result. Pipe lambdas and `|>` pipelines remain supported.
- Top-level variables are module-scoped live bindings: functions, methods, and closures see later assignments and can update them. Local declarations and parameters shadow these bindings; private variables stay private to their module. Namespace members (`ns.x`) read the same live bindings. `var` is block-scoped: using a variable outside the block that declares it is a compile-time error pointing at the use.
- Arrays support `includes(value[, fromIndex])` and `indexOf(value[, fromIndex])`, including negative starting indices. Both compare numeric values and string contents; objects compare by identity. `includes` finds `NaN`, while `indexOf` does not.
- Calling a missing or non-callable array method raises a catchable `TypeError` instead of crashing, including bracket notation.
- Numbers follow JavaScript: integers stay small integers while results are exact, and `/` produces a float when it is not exact (`7 / 2` is `3.5`, `6 / 2` is `3`). Integer overflow promotes to float, and `0 / 0` and `1 / 0` give `NaN` and `inf`. Float literals, mixed int/float arithmetic, and comparisons work everywhere, including in constant folding.
- `+` with a string operand coerces the other operand, even when the types are unknown (`"d " + 4` is `"d 4"`).
- Method calls on objects and class instances dispatch dynamically. User methods named like builtins (`push`, `map`, `replace`, `get`, `set`, `add`, `has`, `delete`, `keys`, ...) are called instead of the builtin. Arrays, strings, Maps, and Sets still use the builtins. Class methods may be named `get`, `set`, `delete`, `catch`, or `finally`.
- `length` and `size` are ordinary readable and assignable properties on objects (`this.size = 3`). On arrays, assigning `length` resizes the array.
- `key in obj` evaluates `key` when it is a variable or an expression; otherwise the bare identifier is used as the property name.

Run `cargo test --test runtime_bugs -- --test-threads=1` for these regressions.

Known bugs:
- When a function is natively memoized, it can cause use-after-free errors if memoized values are not primitives (like an object), since complex values allocate on the GC that can free them in any moment while the native memoization thinks they are still there.

Limitations:
Napalm, by design, does not have an interpreter, but just a JIT. I opted for a single JIT without re-compilations instead of a complex architecture with an interpreter and a multi-tier JIT, because I am a single developer working on this and I would have not enough time. I opted for simplicity instead of complexity. Also, I find a waste of time and resources, to develop them, since they are only going to run for a fraction of a second until the top-tier JIT kicks-in. This sadly mean that:
- Cold start time might be somewhat slower than very fast engines like Wren or LuaJIT (but still faster than CPython or Node).
- I can't do a lot of speculative optimizations nor PGO, so it's unlikely Napalm gets as fast as top-tier JavaScript engines and LuaJIT (though still competitive, in some benchmarks we are even faster than Node).
- Napalm won't work on platforms where JIT compilation isn't allowed (like iOS, consoles, or running in WebAssembly)
I have, however, a proto-interpreter (direct threaded, register based, compact bytecode) in very very early stages in a different project, I might consider developing it further and adapting it to Napalm once I finish everything else.
