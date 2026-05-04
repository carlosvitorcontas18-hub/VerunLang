use verun::ast::nodes::{Item, Statement};
use verun::parser::parse_source;

#[test]
fn parse_counter_example() {
    let source = include_str!("../examples/counter.verun");
    let result = parse_source(source);
    assert!(
        result.is_ok(),
        "Failed to parse counter.verun: {:?}",
        result.err()
    );
    let program = result.unwrap();
    assert!(!program.items.is_empty());
}

#[test]
fn parse_token_example() {
    let source = include_str!("../examples/token.verun");
    let result = parse_source(source);
    assert!(
        result.is_ok(),
        "Failed to parse token.verun: {:?}",
        result.err()
    );
}

#[test]
fn parse_voting_example() {
    let source = include_str!("../examples/voting.verun");
    let result = parse_source(source);
    assert!(
        result.is_ok(),
        "Failed to parse voting.verun: {:?}",
        result.err()
    );
}

#[test]
fn parse_minimal_state() {
    let source = r#"
        state Minimal {
            x: int

            init {
                x = 0
            }
        }
    "#;
    let result = parse_source(source);
    assert!(result.is_ok(), "Failed: {:?}", result.err());
}

#[test]
fn parse_with_invariant() {
    let source = r#"
        state Bounded {
            value: int

            invariant positive {
                value >= 0
            }

            init {
                value = 0
            }

            transition inc() {
                where {
                    value < 100
                }
                value += 1
            }
        }
    "#;
    let result = parse_source(source);
    assert!(result.is_ok(), "Failed: {:?}", result.err());
}

#[test]
fn parse_with_enum() {
    let source = r#"
        enum Status {
            Active,
            Inactive,
            Pending
        }

        state Machine {
            status: Status

            init {
                status = Status::Active
            }
        }
    "#;
    let result = parse_source(source);
    assert!(result.is_ok(), "Failed: {:?}", result.err());
}

#[test]
fn parse_with_types() {
    let source = r#"
        state WithTypes {
            count: int
            rate: real
            active: bool
            name: string

            init {
                count = 0
                rate = 1.5
                active = true
                name = "test"
            }
        }
    "#;
    let result = parse_source(source);
    assert!(result.is_ok(), "Failed: {:?}", result.err());
}

#[test]
fn parse_error_invalid_syntax() {
    let source = "state { }";
    let result = parse_source(source);
    assert!(result.is_err());
}

#[test]
fn parse_error_unclosed_brace() {
    let source = r#"
        state Broken {
            x: int
            init { x = 0
    "#;
    let result = parse_source(source);
    assert!(result.is_err());
}

#[test]
fn parse_error_missing_type() {
    let source = r#"
        state Bad {
            x:
            init { x = 0 }
        }
    "#;
    let result = parse_source(source);
    assert!(result.is_err());
}

#[test]
fn parse_error_invalid_operator() {
    let source = r#"
        state Bad {
            x: int
            init { x = 0 }
            transition go() {
                x = 1 ?? 2
            }
        }
    "#;
    let result = parse_source(source);
    assert!(result.is_err());
}

#[test]
fn parse_error_empty_enum() {
    let source = "enum Empty { }";
    let result = parse_source(source);
    assert!(result.is_err());
}

#[test]
fn parse_auction_example() {
    let source = include_str!("../examples/auction.verun");
    let result = parse_source(source);
    assert!(
        result.is_ok(),
        "Failed to parse auction.verun: {:?}",
        result.err()
    );
}

#[test]
fn parse_if_else_nested() {
    let source = r#"
        state S {
            x: int
            init { x = 0 }
            transition go(n: int) {
                if n > 0 {
                    if n > 10 {
                        x = 10
                    } else {
                        x = n
                    }
                } else {
                    x = 0
                }
            }
        }
    "#;
    let result = parse_source(source);
    assert!(
        result.is_ok(),
        "Failed to parse nested if/else: {:?}",
        result.err()
    );
}

#[test]
fn parse_transition_with_params() {
    let source = r#"
        state Account {
            balance: int

            invariant non_negative {
                balance >= 0
            }

            init {
                balance = 0
            }

            transition deposit(amount: int) {
                where {
                    amount > 0
                }
                balance += amount
                ensure {
                    balance == old(balance) + amount
                }
            }
        }
    "#;
    let result = parse_source(source);
    assert!(result.is_ok(), "Failed: {:?}", result.err());
}

#[test]
fn parse_with_const_let_match() {
    let source = r#"
        enum Mode { Idle, Busy }

        const LIMIT: int = 10

        state Machine {
            mode: Mode
            count: int

            init {
                mode = Mode::Idle
                count = 0
            }

            transition tick(next: Mode) {
                let local_limit: int = LIMIT
                match next {
                    Mode::Idle => {
                        count = 0
                    },
                    Mode::Busy => {
                        count = local_limit
                    }
                }
                mode = next
            }
        }
    "#;
    let result = parse_source(source);
    assert!(
        result.is_ok(),
        "Failed to parse const/let/match: {:?}",
        result.err()
    );
}

#[test]
fn parse_else_if_chain() {
    let source = r#"
        state S {
            x: int
            init { x = 0 }
            transition go(v: int) {
                if v < 0 {
                    x = -1
                } else if v == 0 {
                    x = 0
                } else {
                    x = 1
                }
            }
        }
    "#;
    let result = parse_source(source);
    assert!(
        result.is_ok(),
        "Failed to parse else-if chain: {:?}",
        result.err()
    );
}

#[test]
fn parse_match_workflow_example() {
    let source = include_str!("../examples/match_workflow.verun");
    let result = parse_source(source);
    assert!(
        result.is_ok(),
        "Failed to parse match_workflow.verun: {:?}",
        result.err()
    );
}

#[test]
fn parse_preserves_assert_statement_order() {
    let source = r#"
        state S {
            x: int

            init {
                x = 0
            }

            transition step(v: int) {
                x = v
                assert x >= 0
                x = x + 1
            }
        }
    "#;

    let program = parse_source(source).expect("source should parse");
    let state = program
        .items
        .iter()
        .find_map(|item| match &item.node {
            Item::State(state) => Some(state),
            _ => None,
        })
        .expect("state should exist");
    let transition = state
        .transitions
        .iter()
        .find(|t| t.name.node == "step")
        .expect("transition should exist");

    assert_eq!(transition.body.len(), 3, "expected 3 statements in body");
    assert!(
        matches!(transition.body[0].node, Statement::Assign(_)),
        "first statement should be assignment"
    );
    assert!(
        matches!(transition.body[1].node, Statement::Assert { .. }),
        "second statement should be assert"
    );
    assert!(
        matches!(
            transition.body[2].node,
            Statement::Assign(_) | Statement::CompoundAssign { .. }
        ),
        "third statement should be assignment/compound assignment"
    );
}
