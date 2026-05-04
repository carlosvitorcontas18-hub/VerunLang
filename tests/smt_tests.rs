use verun::ast::nodes::Item;
use verun::parser::parse_source;
use verun::smt::solver::Solver;
use verun::smt::verifier::Verifier;

fn verify_source(source: &str) -> (usize, usize) {
    let program = parse_source(source).unwrap();
    let solver = Solver::new();
    let ctx = solver.create_context();
    let mut verifier = Verifier::new(&ctx);

    for item in &program.items {
        match &item.node {
            Item::EnumDef(e) => verifier.register_enum(e),
            Item::Function(f) => verifier.register_function(f),
            Item::TypeDef(t) => verifier.register_type_def(t),
            Item::ConstDef(c) => verifier.register_const(c),
            _ => {}
        }
    }

    let mut total = 0;
    let mut passed = 0;

    for item in &program.items {
        if let Item::State(state) = &item.node {
            let result = verifier.verify_state(state);
            for check in &result.checks {
                total += 1;
                if check.passed {
                    passed += 1;
                }
            }
        }
    }

    (passed, total)
}

#[test]
fn verify_counter_all_pass() {
    let source = include_str!("../examples/counter.verun");
    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "All checks should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_token_all_pass() {
    let source = include_str!("../examples/token.verun");
    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "All checks should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_voting_all_pass() {
    let source = include_str!("../examples/voting.verun");
    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "All checks should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_broken_invariant_fails() {
    let source = r#"
        state Broken {
            x: int

            invariant positive {
                x > 0
            }

            init {
                x = 0
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert!(passed < total, "Init violates invariant, should fail");
}

#[test]
fn verify_transition_violates_invariant() {
    let source = r#"
        state Bad {
            x: int

            invariant bounded {
                x <= 100
            }

            init {
                x = 0
            }

            transition set_too_high() {
                x = 200
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(passed < total, "Transition violates invariant, should fail");
}

#[test]
fn verify_auction_all_pass() {
    let source = include_str!("../examples/auction.verun");
    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "All checks should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_sequential_ssa_encoding() {
    let source = r#"
        state Seq {
            x: int
            y: int

            invariant y_follows_x {
                y == x + 1
            }

            init {
                x = 0
                y = 1
            }

            transition step() {
                x = x + 1
                y = x + 1
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert_eq!(
        passed, total,
        "Sequential SSA: y=x+1 should use new x ({}/{})",
        passed, total
    );
}

#[test]
fn verify_sequential_ssa_detects_violation() {
    let source = r#"
        state SeqBad {
            x: int
            y: int

            invariant y_is_x_plus_one {
                y == x + 1
            }

            init {
                x = 0
                y = 1
            }

            transition bad_step() {
                x = x + 1
                y = x
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(passed < total, "y=x (new x) violates y==x+1, should fail");
}

#[test]
fn verify_if_else_encoding() {
    let source = r#"
        state Clamped {
            x: int

            invariant bounded {
                x >= 0 && x <= 100
            }

            init {
                x = 50
            }

            transition adjust(delta: int) {
                where {
                    delta >= -50 && delta <= 50
                }
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
    let (passed, total) = verify_source(source);
    assert_eq!(
        passed, total,
        "Clamped if/else should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_enum_phase_transition() {
    let source = r#"
        enum Phase { A, B }
        state Machine {
            p: Phase

            invariant must_be_a {
                p == Phase::A
            }

            init {
                p = Phase::A
            }

            transition go_b() {
                p = Phase::B
                ensure { p == Phase::B }
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(passed < total, "go_b violates must_be_a, should fail");
}

#[test]
fn verify_clamped_detects_violation() {
    let source = include_str!("../examples/clamped.verun");
    let (passed, total) = verify_source(source);
    // 'adjust' should pass all checks, 'set' should fail (no bounds check)
    assert!(total > 0, "Should have checks");
    assert!(
        passed < total,
        "set transition should violate in_bounds invariant ({}/{})",
        passed,
        total
    );
}

#[test]
fn verify_order_all_pass() {
    let source = include_str!("../examples/order.verun");
    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "All checks should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_buffer_array_invariant() {
    let source = include_str!("../examples/buffer.verun");
    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "Buffer with store should pass all checks ({}/{})",
        passed, total
    );
}

#[test]
fn verify_ledger_all_pass() {
    let source = include_str!("../examples/ledger.verun");
    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "All checks should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_array_index_in_invariant() {
    let source = r#"
        state ArrCheck {
            data: int[4]
            head: int

            invariant head_bounded {
                head >= 0 && head < 4
            }

            invariant head_positive {
                data[head] >= 0
            }

            init {
                head = 0
            }

            transition next() {
                where { head < 3 }
                head += 1
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    // head_positive fails because data is symbolic — data[head] could be negative
    assert!(
        passed < total,
        "data[head] >= 0 should fail with symbolic array ({}/{})",
        passed,
        total
    );
}

#[test]
fn verify_map_access_in_invariant() {
    let source = r#"
        state MapCheck {
            scores: map[int, int]
            player_count: int

            invariant has_players {
                player_count >= 0
            }

            init {
                player_count = 0
            }

            transition add_player() {
                player_count += 1
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "Map state should verify ({}/{})",
        passed, total
    );
}

#[test]
fn verify_uninterpreted_function() {
    let source = r#"
        fn compute(x: int) -> int

        state FnTest {
            val: int

            invariant non_negative {
                val >= 0
            }

            init {
                val = 0
            }

            transition step(n: int) {
                where { n > 0 }
                val += n
                ensure { val == old(val) + n }
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "Uninterpreted fn with simple state should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_match_encoding_preserves_invariant() {
    let source = r#"
            enum Mode { Idle, Busy }

            state M {
                mode: Mode
                value: int

                invariant non_negative {
                    value >= 0
                }

                init {
                    mode = Mode::Idle
                    value = 0
                }

                transition step(next: Mode, amount: int) {
                    where {
                        amount >= 0
                    }
                    let safe: int = amount
                    match next {
                        Mode::Idle => {
                            value = 0
                        },
                        Mode::Busy => {
                            value = safe
                        }
                    }
                    mode = next
                }
            }
        "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "match transition should preserve invariant ({}/{})",
        passed, total
    );
}

#[test]
fn verify_stack_all_pass() {
    let source = include_str!("../examples/stack.verun");
    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "Stack with assert should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_array_store_preserves_invariant() {
    let source = r#"
        state ArrStore {
            vals: int[4]
            count: int

            invariant count_bounded {
                count >= 0 && count <= 4
            }

            invariant all_positive {
                forall i in 0..count: vals[i] > 0
            }

            init {
                count = 0
            }

            transition add(v: int) {
                where {
                    v > 0
                    count < 4
                }
                vals[count] = v
                count += 1
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "Array store with quantified invariant should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_assert_constrains_state() {
    let source = r#"
        state AssertTest {
            x: int

            invariant bounded {
                x >= 0 && x <= 100
            }

            init {
                x = 0
            }

            transition set(val: int) {
                assert val >= 0
                assert val <= 100
                x = val
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "Assert should constrain SMT state ({}/{})",
        passed, total
    );
}

#[test]
fn verify_implies_operator() {
    let source = r#"
        state ImpliesTest {
            x: int
            active: bool

            invariant implies_check {
                active ==> x > 0
            }

            init {
                x = 1
                active = false
            }

            transition activate() {
                where { x > 0 }
                active = true
            }

            transition set_value(val: int) {
                where { val > 0 }
                x = val
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "Implies invariant should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_implies_violation() {
    let source = r#"
        state ImpliesViolation {
            x: int
            active: bool

            invariant implies_check {
                active ==> x > 0
            }

            init {
                x = 0
                active = true
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert!(passed < total, "Init violates implies invariant");
}

#[test]
fn verify_builtin_abs() {
    let source = r#"
        state AbsTest {
            x: int
            y: int

            invariant abs_positive {
                y >= 0
            }

            init {
                x = -5
                y = abs(x)
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "abs() should produce non-negative ({}/{})",
        passed, total
    );
}

#[test]
fn verify_builtin_min_max() {
    let source = r#"
        state MinMaxTest {
            a: int
            b: int
            lo: int
            hi: int

            invariant min_leq {
                lo <= a && lo <= b
            }

            invariant max_geq {
                hi >= a && hi >= b
            }

            init {
                a = 10
                b = 20
                lo = min(a, b)
                hi = max(a, b)
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "min/max invariants should pass ({}/{})",
        passed, total
    );
}

#[test]
fn verify_refinement_type_basic() {
    let source = r#"
        type PositiveInt = int where value > 0

        state RefinementTest {
            amount: PositiveInt

            invariant positive {
                amount > 0
            }

            init {
                amount = 10
            }

            transition increase(delta: PositiveInt) {
                amount = amount + delta
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    assert_eq!(
        passed, total,
        "Refinement type should help verify ({}/{})",
        passed, total
    );
}

#[test]
fn verify_refinement_type_violation() {
    let source = r#"
        type NonNegative = int where value >= 0

        state RefinementViolation {
            balance: NonNegative

            invariant non_neg {
                balance >= 0
            }

            init {
                balance = 100
            }

            transition withdraw(amount: int) {
                where { amount > 0 }
                balance = balance - amount
            }
        }
    "#;
    let (passed, total) = verify_source(source);
    assert!(total > 0);
    // Without refinement on param, withdraw can make balance negative
    assert!(passed < total, "Should detect possible negative balance");
}

#[test]
fn verify_transition_body_uses_registered_constants() {
    let source = r#"
        const STEP: int = 1

        state ConstBody {
            x: int

            invariant non_negative {
                x >= 0
            }

            init {
                x = 0
            }

            transition advance(n: int) {
                where {
                    n >= 0
                }
                let delta: int = n + STEP
                x = x + delta
                ensure {
                    x == old(x) + n + STEP
                }
            }
        }
    "#;

    let (passed, total) = verify_source(source);
    assert!(total > 0, "Should have checks");
    assert_eq!(
        passed, total,
        "Constants in transition body must be available in SSA context ({}/{})",
        passed, total
    );
}
