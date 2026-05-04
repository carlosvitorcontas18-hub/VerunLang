use verun::codegen::c::CTarget;
use verun::codegen::cairo::CairoTarget;
use verun::codegen::go::GoTarget;
use verun::codegen::java::JavaTarget;
use verun::codegen::move_lang::MoveTarget;
use verun::codegen::rust::RustTarget;
use verun::codegen::solidity::SolidityTarget;
use verun::codegen::target::CodeTarget;
use verun::codegen::typescript::TypeScriptTarget;
use verun::codegen::vyper::VyperTarget;
use verun::parser::parse_source;

#[test]
fn codegen_rust_counter() {
    let source = include_str!("../examples/counter.verun");
    let program = parse_source(source).unwrap();

    let target = RustTarget;
    let output = target.generate(&program);

    assert!(output.contains("pub struct Counter"));
    assert!(output.contains("pub fn new()"));
    assert!(output.contains("pub fn increment"));
    assert!(output.contains("pub fn decrement"));
    assert!(output.contains("pub fn reset"));
    // Invariant assertions
    assert!(output.contains("debug_assert!"));
    assert!(output.contains("invariant 'non_negative' violated"));
    assert!(output.contains("invariant 'bounded' violated"));
}

#[test]
fn codegen_typescript_counter() {
    let source = include_str!("../examples/counter.verun");
    let program = parse_source(source).unwrap();

    let target = TypeScriptTarget;
    let output = target.generate(&program);

    assert!(output.contains("export class Counter"));
    assert!(output.contains("constructor()"));
    assert!(output.contains("public increment"));
    assert!(output.contains("public decrement"));
    assert!(output.contains("public reset"));
    // Invariant assertions
    assert!(output.contains("invariant 'non_negative' violated"));
    assert!(output.contains("invariant 'bounded' violated"));
}

#[test]
fn codegen_rust_token() {
    let source = include_str!("../examples/token.verun");
    let program = parse_source(source).unwrap();

    let target = RustTarget;
    let output = target.generate(&program);

    assert!(output.contains("pub struct Token"));
    assert!(output.contains("pub fn transfer_a_to_b"));
    assert!(output.contains("pub fn mint"));
    // Postcondition assertions
    assert!(output.contains("postcondition violated"));
    assert!(output.contains("_old_balance_a"));
    assert!(output.contains("debug_assert!"));
}

#[test]
fn codegen_typescript_token() {
    let source = include_str!("../examples/token.verun");
    let program = parse_source(source).unwrap();

    let target = TypeScriptTarget;
    let output = target.generate(&program);

    assert!(output.contains("export class Token"));
    assert!(output.contains("public transfer_a_to_b"));
    assert!(output.contains("public mint"));
    // Postcondition assertions
    assert!(output.contains("postcondition violated"));
    assert!(output.contains("_old_balance_a"));
}

#[test]
fn codegen_rust_old_in_postcondition() {
    let source = r#"
        state Counter {
            value: int

            invariant non_negative {
                value >= 0
            }

            init {
                value = 0
            }

            transition add(n: int) {
                where { n > 0 }
                value += n
                ensure {
                    value == old(value) + n
                }
            }
        }
    "#;
    let program = parse_source(source).unwrap();
    let target = RustTarget;
    let output = target.generate(&program);

    // old(value) should become _old_value
    assert!(output.contains("_old_value"));
    assert!(output.contains("let _old_value = self.value.clone()"));
    // postcondition: value == old(value) + n
    assert!(output.contains("debug_assert!((self.value == (_old_value + n))"));
    // invariant
    assert!(output.contains("debug_assert!((self.value >= 0)"));
}

#[test]
fn codegen_typescript_old_in_postcondition() {
    let source = r#"
        state Counter {
            value: int

            invariant non_negative {
                value >= 0
            }

            init {
                value = 0
            }

            transition add(n: int) {
                where { n > 0 }
                value += n
                ensure {
                    value == old(value) + n
                }
            }
        }
    "#;
    let program = parse_source(source).unwrap();
    let target = TypeScriptTarget;
    let output = target.generate(&program);

    assert!(output.contains("_old_value"));
    assert!(output.contains("const _old_value = this.value"));
    assert!(output.contains("(this.value === (_old_value + n))"));
}

#[test]
fn codegen_rust_auction_enum() {
    let source = include_str!("../examples/auction.verun");
    let program = parse_source(source).unwrap();

    let target = RustTarget;
    let output = target.generate(&program);

    // Enum generation
    assert!(output.contains("#[derive(Debug, Clone, Copy, PartialEq, Eq)]"));
    assert!(output.contains("pub enum AuctionPhase"));
    assert!(output.contains("Open,"));
    assert!(output.contains("Closed,"));
    assert!(output.contains("Finalized"));
    // State struct
    assert!(output.contains("pub struct Auction"));
    assert!(output.contains("pub phase: AuctionPhase"));
    // Init with enum variant
    assert!(output.contains("AuctionPhase::Open"));
    // Transition with enum comparison
    assert!(output.contains("pub fn place_bid"));
    assert!(output.contains("pub fn close_auction"));
    assert!(output.contains("pub fn finalize"));
    // Postcondition + invariant assertions
    assert!(output.contains("debug_assert!"));
    assert!(output.contains("postcondition violated"));
    assert!(output.contains("_old_bid_count"));
}

#[test]
fn codegen_typescript_auction_enum() {
    let source = include_str!("../examples/auction.verun");
    let program = parse_source(source).unwrap();

    let target = TypeScriptTarget;
    let output = target.generate(&program);

    // Enum generation
    assert!(output.contains("export enum AuctionPhase"));
    assert!(output.contains("Open = \"Open\""));
    assert!(output.contains("Closed = \"Closed\""));
    // State class
    assert!(output.contains("export class Auction"));
    assert!(output.contains("public phase: AuctionPhase"));
    // Transitions
    assert!(output.contains("public place_bid"));
    assert!(output.contains("public close_auction"));
    assert!(output.contains("public finalize"));
    // Postcondition + invariant assertions
    assert!(output.contains("postcondition violated"));
    assert!(output.contains("_old_bid_count"));
}

#[test]
fn codegen_rust_if_else() {
    let source = r#"
        state Clamped {
            x: int

            invariant bounded { x >= 0 && x <= 100 }

            init { x = 50 }

            transition adjust(delta: int) {
                where { delta >= -50 && delta <= 50 }
                if x + delta > 100 {
                    x = 100
                } else {
                    if x + delta < 0 {
                        x = 0
                    } else {
                        x = x + delta
                    }
                }
            }
        }
    "#;
    let program = parse_source(source).unwrap();
    let target = RustTarget;
    let output = target.generate(&program);

    assert!(output.contains("if ("));
    assert!(output.contains("} else {"));
    assert!(output.contains("self.x = 100"));
    assert!(output.contains("self.x = 0"));
    assert!(output.contains("self.x = (self.x + delta)"));
    assert!(output.contains("debug_assert!"));
}

#[test]
fn codegen_solidity_counter() {
    let source = include_str!("../examples/counter.verun");
    let program = parse_source(source).unwrap();

    let target = SolidityTarget;
    let output = target.generate(&program);

    assert!(output.contains("pragma solidity ^0.8.20;"));
    assert!(output.contains("contract Counter {"));
    assert!(output.contains("int256 public value;"));
    assert!(output.contains("constructor()"));
    assert!(output.contains("modifier checkInvariants()"));
    assert!(output.contains("require((value >= 0), \"invariant 'non_negative' violated\")"));
    assert!(output.contains("function increment(int256 amount) external checkInvariants"));
    assert!(output.contains("function decrement(int256 amount) external checkInvariants"));
    assert!(output.contains("function reset() external checkInvariants"));
    assert!(output.contains("require((amount > 0), \"precondition failed\")"));
    assert!(output.contains("value += amount;"));
}

#[test]
fn codegen_solidity_token() {
    let source = include_str!("../examples/token.verun");
    let program = parse_source(source).unwrap();

    let target = SolidityTarget;
    let output = target.generate(&program);

    assert!(output.contains("contract Token {"));
    assert!(output.contains("event Transfer("));
    assert!(output.contains("event Mint("));
    assert!(output.contains("balance_a -= amount;"));
    assert!(output.contains("balance_b += amount;"));
    assert!(output.contains("emit Transfer(amount);"));
    assert!(output.contains("require((balance_a == (_old_balance_a - amount))"));
    assert!(output.contains("int256 _old_balance_a = balance_a;"));
}

#[test]
fn codegen_solidity_auction_enum() {
    let source = include_str!("../examples/auction.verun");
    let program = parse_source(source).unwrap();

    let target = SolidityTarget;
    let output = target.generate(&program);

    assert!(output.contains("enum AuctionPhase {"));
    assert!(output.contains("Open,"));
    assert!(output.contains("Closed,"));
    assert!(output.contains("contract Auction {"));
    assert!(output.contains("AuctionPhase public phase;"));
    assert!(output.contains("phase = AuctionPhase.Open;"));
    assert!(output.contains("require((phase == AuctionPhase.Open)"));
    assert!(output.contains("function place_bid(int256 amount)"));
    assert!(output.contains("emit BidPlaced(amount);"));
    // Named type (enum) should NOT use memory
    assert!(output.contains("AuctionPhase _old_phase = phase;"));
}

#[test]
fn codegen_solidity_buffer_array() {
    let source = include_str!("../examples/buffer.verun");
    let program = parse_source(source).unwrap();

    let target = SolidityTarget;
    let output = target.generate(&program);

    assert!(output.contains("int256[8] public values;"));
    assert!(output.contains("int256 public length;"));
    assert!(output.contains("values[length] = val;"));
    assert!(output.contains("function push(int256 val)"));
    assert!(output.contains("function pop()"));
    assert!(output.contains("require((length < 8)"));
}

#[test]
fn codegen_solidity_map() {
    let source = r#"
        state Registry {
            balances: map[int, int]
            count: int

            invariant positive_count { count >= 0 }

            init {
                count = 0
            }

            transition set_balance(key: int, val: int) {
                where { val >= 0 }
                count += 1
            }
        }
    "#;
    let program = parse_source(source).unwrap();

    let target = SolidityTarget;
    let output = target.generate(&program);

    assert!(output.contains("mapping(int256 => int256)"));
    assert!(output.contains("contract Registry {"));
    assert!(output.contains("function set_balance(int256 key, int256 val)"));
}

#[test]
fn codegen_match_and_let_across_targets() {
    let source = r#"
        enum Mode { Idle, Busy }

        state Machine {
            mode: Mode
            value: int

            init {
                mode = Mode::Idle
                value = 0
            }

            transition step(next: Mode, amount: int) {
                let safe: int = amount
                match next {
                    Mode::Idle => {
                        value = 0
                    },
                    Mode::Busy => {
                        value = safe
                    }
                }
            }
        }
    "#;
    let program = parse_source(source).unwrap();

    let rust = RustTarget.generate(&program);
    assert!(rust.contains("let safe: i64 = amount"));
    assert!(rust.contains("match next"));
    assert!(rust.contains("Mode::Idle"));
    assert!(rust.contains("Mode::Busy"));

    let ts = TypeScriptTarget.generate(&program);
    assert!(ts.contains("const safe = amount"));
    assert!(ts.contains("if (next === Mode.Idle)"));
    assert!(ts.contains("else if (next === Mode.Busy)"));

    let sol = SolidityTarget.generate(&program);
    assert!(sol.contains("int256 safe = amount;"));
    assert!(sol.contains("if (next == Mode.Idle)"));
    assert!(sol.contains("else if (next == Mode.Busy)"));
}

#[test]
fn codegen_new_targets_smoke() {
    let source = include_str!("../examples/match_workflow.verun");
    let program = parse_source(source).unwrap();

    let go = GoTarget.generate(&program);
    assert!(go.contains("package generated"));
    assert!(go.contains("type Workflow struct"));
    assert!(go.contains("func (s *Workflow) Submit"));

    let java = JavaTarget.generate(&program);
    assert!(java.contains("class Workflow"));
    assert!(java.contains("public void submit"));

    let c = CTarget.generate(&program);
    assert!(c.contains("typedef struct Workflow"));
    assert!(c.contains("void workflow_submit("));

    let mv = MoveTarget.generate(&program);
    assert!(mv.contains("module verun::generated"));
    assert!(mv.contains("public fun submit"));

    let cairo = CairoTarget.generate(&program);
    assert!(cairo.contains("struct Workflow"));
    assert!(cairo.contains("fn submit("));

    let vyper = VyperTarget.generate(&program);
    assert!(vyper.contains("@external"));
    assert!(vyper.contains("def submit("));
}

#[test]
fn codegen_quantifiers_no_placeholders() {
    let source = r#"
        state Quant {
            values: int[8]
            n: int

            invariant bounded {
                n >= 0 && n <= 8
            }

            invariant all_positive {
                forall i in 0..n: values[i] >= 0
            }

            init {
                n = 0
            }

            transition can_add(v: int) {
                where {
                    exists i in 0..8: i >= 0
                    v >= 0
                }
                if n < 8 {
                    values[n] = v
                    n += 1
                }
            }
        }
    "#;

    let program = parse_source(source).unwrap();

    let rust = RustTarget.generate(&program);
    assert!(!rust.contains("todo!()"));
    assert!(!rust.contains("unsupported"));

    let ts = TypeScriptTarget.generate(&program);
    assert!(!ts.contains("unsupported"));
    assert!(!ts.contains("undefined /* unsupported */"));

    let go = GoTarget.generate(&program);
    assert!(!go.contains("/* unsupported */"));

    let java = JavaTarget.generate(&program);
    assert!(!java.contains("/* unsupported */"));

    let c = CTarget.generate(&program);
    assert!(!c.contains("0 /* unsupported */"));

    let sol = SolidityTarget.generate(&program);
    assert!(!sol.contains("/* unsupported */"));

    let mv = MoveTarget.generate(&program);
    assert!(!mv.contains("forall i in"));
    assert!(!mv.contains("exists i in"));

    let cairo = CairoTarget.generate(&program);
    assert!(!cairo.contains("forall i in"));
    assert!(!cairo.contains("exists i in"));

    let vyper = VyperTarget.generate(&program);
    assert!(!vyper.contains("forall i in"));
    assert!(!vyper.contains("exists i in"));
}
