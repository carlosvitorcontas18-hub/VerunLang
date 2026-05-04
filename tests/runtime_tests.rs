use std::collections::HashMap;

use verun::ast::nodes::Item;
use verun::parser::parse_source;
use verun::runtime::engine::Engine;
use verun::runtime::value::Value;

fn run_with_consts(source: &str) -> Vec<(String, Engine)> {
    let program = parse_source(source).unwrap();

    let top_level_consts: Vec<_> = program
        .items
        .iter()
        .filter_map(|i| {
            if let Item::ConstDef(c) = &i.node {
                Some(c.clone())
            } else {
                None
            }
        })
        .collect();

    let mut results = Vec::new();

    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);

            for c in &top_level_consts {
                engine.load_const(c).unwrap();
            }
            for c in &state.constants {
                engine.load_const(c).unwrap();
            }
            engine.initialize_state(state).unwrap();

            results.push((state.name.node.clone(), engine));
        }
    }

    results
}

#[test]
fn runtime_counter_init() {
    let source = include_str!("../examples/counter.verun");
    let program = parse_source(source).unwrap();

    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);
            engine.initialize_state(state).unwrap();

            assert_eq!(engine.get_field("value"), Some(&Value::Int(0)));
            assert_eq!(engine.get_field("max_value"), Some(&Value::Int(100)));
        }
    }
}

#[test]
fn runtime_counter_increment() {
    let source = include_str!("../examples/counter.verun");
    let program = parse_source(source).unwrap();

    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);
            engine.initialize_state(state).unwrap();

            let transition = state
                .transitions
                .iter()
                .find(|t| t.name.node == "increment")
                .unwrap();

            let mut args = HashMap::new();
            args.insert("amount".to_string(), Value::Int(10));

            let _events = engine
                .execute_transition(transition, args, &state.invariants)
                .unwrap();

            assert_eq!(engine.get_field("value"), Some(&Value::Int(10)));
        }
    }
}

#[test]
fn runtime_counter_precondition_fail() {
    let source = include_str!("../examples/counter.verun");
    let program = parse_source(source).unwrap();

    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);
            engine.initialize_state(state).unwrap();

            let transition = state
                .transitions
                .iter()
                .find(|t| t.name.node == "decrement")
                .unwrap();

            let mut args = HashMap::new();
            args.insert("amount".to_string(), Value::Int(10));

            let result = engine.execute_transition(transition, args, &state.invariants);
            assert!(
                result.is_err(),
                "Should fail precondition (value=0, decrement 10)"
            );
        }
    }
}

#[test]
fn runtime_token_transfer() {
    let source = include_str!("../examples/token.verun");
    let program = parse_source(source).unwrap();

    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);
            engine.initialize_state(state).unwrap();

            let transition = state
                .transitions
                .iter()
                .find(|t| t.name.node == "transfer_a_to_b")
                .unwrap();

            let mut args = HashMap::new();
            args.insert("amount".to_string(), Value::Int(100));

            engine
                .execute_transition(transition, args, &state.invariants)
                .unwrap();

            assert_eq!(engine.get_field("balance_a"), Some(&Value::Int(900)));
            assert_eq!(engine.get_field("balance_b"), Some(&Value::Int(100)));
            assert_eq!(engine.get_field("total_supply"), Some(&Value::Int(1000)));
        }
    }
}

#[test]
fn runtime_let_and_match() {
    let source = r#"
        enum Mode { Idle, Busy }

        state Machine {
            mode: Mode
            value: int

            init {
                mode = Mode::Idle
                value = 0
            }

            transition apply(next: Mode, amount: int) {
                let base: int = amount + 1
                match next {
                    Mode::Idle => {
                        value = 0
                    },
                    Mode::Busy => {
                        value = base
                    }
                }
                mode = next
            }
        }
    "#;
    let program = parse_source(source).unwrap();

    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);
            engine.initialize_state(state).unwrap();

            let transition = state
                .transitions
                .iter()
                .find(|t| t.name.node == "apply")
                .unwrap();

            let mut args = HashMap::new();
            args.insert(
                "next".to_string(),
                Value::Enum {
                    enum_name: "Mode".to_string(),
                    variant: "Busy".to_string(),
                },
            );
            args.insert("amount".to_string(), Value::Int(9));

            engine
                .execute_transition(transition, args, &state.invariants)
                .unwrap();

            assert_eq!(engine.get_field("value"), Some(&Value::Int(10)));
            assert_eq!(
                engine.get_field("mode"),
                Some(&Value::Enum {
                    enum_name: "Mode".to_string(),
                    variant: "Busy".to_string(),
                })
            );
        }
    }
}

#[test]
fn runtime_state_const_visible_in_transition() {
    let source = r#"
        state Bank {
            const LIMIT: int = 1000
            balance: int

            init { balance = 0 }

            transition deposit(amount: int) {
                where { balance + amount <= LIMIT }
                balance += amount
            }
        }
    "#;

    let mut engines = run_with_consts(source);
    let (_, ref mut engine) = engines[0];

    let program = parse_source(source).unwrap();
    for item in &program.items {
        if let Item::State(state) = &item.node {
            let trans = state
                .transitions
                .iter()
                .find(|t| t.name.node == "deposit")
                .unwrap();

            let mut args = HashMap::new();
            args.insert("amount".to_string(), Value::Int(500));
            engine
                .execute_transition(trans, args, &state.invariants)
                .unwrap();

            assert_eq!(engine.get_field("balance"), Some(&Value::Int(500)));

            let mut args_overflow = HashMap::new();
            args_overflow.insert("amount".to_string(), Value::Int(600));
            let result = engine.execute_transition(trans, args_overflow, &state.invariants);
            assert!(
                result.is_err(),
                "deposit above LIMIT should fail the precondition"
            );
        }
    }
}

#[test]
fn runtime_top_level_const_visible_in_transition() {
    let source = r#"
        const MAX: int = 50

        state Counter {
            value: int

            init { value = 0 }

            transition set(n: int) {
                where { n <= MAX }
                value = n
            }
        }
    "#;

    let mut engines = run_with_consts(source);
    let (_, ref mut engine) = engines[0];

    let program = parse_source(source).unwrap();
    for item in &program.items {
        if let Item::State(state) = &item.node {
            let trans = state
                .transitions
                .iter()
                .find(|t| t.name.node == "set")
                .unwrap();

            let mut args = HashMap::new();
            args.insert("n".to_string(), Value::Int(50));
            engine
                .execute_transition(trans, args, &state.invariants)
                .unwrap();
            assert_eq!(engine.get_field("value"), Some(&Value::Int(50)));

            let mut args_over = HashMap::new();
            args_over.insert("n".to_string(), Value::Int(51));
            let result = engine.execute_transition(trans, args_over, &state.invariants);
            assert!(
                result.is_err(),
                "setting value above MAX should fail the precondition"
            );
        }
    }
}

#[test]
fn runtime_initializes_collections_not_set_in_init() {
    let source = r#"
        state Collections {
            arr: int[4]
            balances: map[int, int]
            count: int

            init {
                count = 0
            }

            transition put(v: int) {
                where {
                    v > 0
                }
                arr[count] = v
                balances[count] += v
                count += 1
            }
        }
    "#;

    let program = parse_source(source).unwrap();
    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);
            engine.initialize_state(state).unwrap();

            let transition = state
                .transitions
                .iter()
                .find(|t| t.name.node == "put")
                .unwrap();
            let mut args = HashMap::new();
            args.insert("v".to_string(), Value::Int(7));

            engine
                .execute_transition(transition, args, &state.invariants)
                .unwrap();

            assert_eq!(engine.get_field("count"), Some(&Value::Int(1)));
            match engine.get_field("arr") {
                Some(Value::Array(items)) => {
                    assert_eq!(items.first(), Some(&Value::Int(7)));
                }
                other => panic!("expected array field, got {:?}", other),
            }
            match engine.get_field("balances") {
                Some(Value::Map(entries)) => {
                    assert_eq!(entries.get("0"), Some(&Value::Int(7)));
                }
                other => panic!("expected map field, got {:?}", other),
            }
        }
    }
}

#[test]
fn runtime_match_accepts_enum_string_argument() {
    let source = r#"
        enum Side { Buy, Sell }

        state M {
            side: Side

            init {
                side = Side::Buy
            }

            transition set(next: Side) {
                match next {
                    Side::Buy => {
                        side = Side::Buy
                    },
                    Side::Sell => {
                        side = Side::Sell
                    }
                }
            }
        }
    "#;

    let program = parse_source(source).unwrap();
    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);
            engine.initialize_state(state).unwrap();

            let transition = state
                .transitions
                .iter()
                .find(|t| t.name.node == "set")
                .unwrap();
            let mut args = HashMap::new();
            args.insert("next".to_string(), Value::String("Side::Sell".to_string()));

            engine
                .execute_transition(transition, args, &state.invariants)
                .unwrap();

            assert_eq!(
                engine.get_field("side"),
                Some(&Value::Enum {
                    enum_name: "Side".to_string(),
                    variant: "Sell".to_string(),
                })
            );
        }
    }
}
