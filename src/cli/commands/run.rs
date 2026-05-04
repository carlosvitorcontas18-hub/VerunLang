use std::collections::HashMap;
use std::process;

use anyhow::Result;

use crate::ast::nodes::Item;
use crate::errors::diagnostic::VerunError;
use crate::errors::report::{render_error, render_errors};
use crate::parser::parse_file_with_imports;
use crate::runtime::engine::Engine;
use crate::runtime::value::Value;
use crate::types::checker::TypeChecker;

pub fn execute(file: &str, transition: Option<&str>, show_state: bool) -> Result<()> {
    let loaded = match parse_file_with_imports(file) {
        Ok(p) => p,
        Err(e) => {
            let file_source = std::fs::read_to_string(file).unwrap_or_default();
            if let Some(parse_err) = e.downcast_ref::<VerunError>() {
                eprint!("{}", render_error(parse_err, &file_source, file));
            } else {
                eprintln!("Error: {}", e);
            }
            process::exit(1);
        }
    };
    let program = loaded.program;
    let source = loaded.root_source;

    let mut checker = TypeChecker::new();
    let type_errors = checker.check(&program);

    if !type_errors.is_empty() {
        let report = render_errors(&type_errors, &source, file);
        eprint!("{}", report);
        process::exit(1);
    }

    let mut top_level_consts: Vec<&crate::ast::nodes::ConstDef> = Vec::new();
    for item in &program.items {
        if let Item::ConstDef(c) = &item.node {
            top_level_consts.push(c);
        }
    }

    for item in &program.items {
        if let Item::State(state) = &item.node {
            let mut engine = Engine::new(&state.name.node);

            for c in &top_level_consts {
                engine.load_const(c)?;
            }

            for c in &state.constants {
                engine.load_const(c)?;
            }

            engine.initialize_state(state)?;

            if show_state {
                println!("State '{}' after init:", state.name.node);
                print_state(&engine);
            }

            if let Some(trans_spec) = transition {
                let (trans_name, args) = parse_transition_spec(trans_spec)?;

                let trans = state
                    .transitions
                    .iter()
                    .find(|t| t.name.node == trans_name)
                    .ok_or_else(|| anyhow::anyhow!("transition '{}' not found", trans_name))?;

                let mut param_map = HashMap::new();
                for (i, param) in trans.params.iter().enumerate() {
                    if let Some(arg_str) = args.get(i) {
                        let value = parse_value(arg_str);
                        param_map.insert(param.name.node.clone(), value);
                    }
                }

                let events = engine.execute_transition(trans, param_map, &state.invariants)?;

                if !events.is_empty() {
                    println!("Events emitted:");
                    for event in &events {
                        let args_str: Vec<String> =
                            event.args.iter().map(|a| a.to_string()).collect();
                        println!("  {}({})", event.name, args_str.join(", "));
                    }
                }

                if show_state {
                    println!("\nState after '{}':", trans_name);
                    print_state(&engine);
                }
            }
        }
    }

    Ok(())
}

fn print_state(engine: &Engine) {
    let state = engine.get_state();
    for (name, value) in &state.fields {
        println!("  {} = {}", name, value);
    }
}

fn parse_transition_spec(spec: &str) -> Result<(String, Vec<String>)> {
    if let Some(paren_pos) = spec.find('(') {
        let name = spec[..paren_pos].to_string();
        let args_str = &spec[paren_pos + 1..spec.len() - 1];
        let args: Vec<String> = if args_str.is_empty() {
            Vec::new()
        } else {
            args_str.split(',').map(|s| s.trim().to_string()).collect()
        };
        Ok((name, args))
    } else {
        Ok((spec.to_string(), Vec::new()))
    }
}

fn parse_value(s: &str) -> Value {
    if let Some((enum_name, variant)) = s.split_once("::")
        && !enum_name.is_empty()
        && !variant.is_empty()
    {
        return Value::Enum {
            enum_name: enum_name.to_string(),
            variant: variant.to_string(),
        };
    }
    if let Ok(v) = s.parse::<i64>() {
        return Value::Int(v);
    }
    if let Ok(v) = s.parse::<f64>() {
        return Value::Real(v);
    }
    if s == "true" {
        return Value::Bool(true);
    }
    if s == "false" {
        return Value::Bool(false);
    }
    Value::String(s.to_string())
}
