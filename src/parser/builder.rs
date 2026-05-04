use anyhow::{Result, bail};
use pest::iterators::Pair;

use super::grammar::Rule;
use crate::ast::nodes::*;
use crate::ast::span::{Span, Spanned};
use crate::ast::types::{EnumDef, Field, Type, TypeDef};

pub fn build_program(pairs: pest::iterators::Pairs<'_, Rule>, source: &str) -> Result<Program> {
    let mut items = Vec::new();

    for pair in pairs {
        match pair.as_rule() {
            Rule::import_decl => items.push(build_import(pair)?),
            Rule::enum_def => items.push(build_enum(pair)?),
            Rule::type_def => items.push(build_type_def(pair)?),
            Rule::const_decl => items.push(build_const_decl(pair)?),
            Rule::state_def => items.push(build_state(pair)?),
            Rule::fn_def => items.push(build_fn_def(pair)?),
            Rule::EOI => {}
            _ => {}
        }
    }

    Ok(Program {
        items,
        source: source.to_string(),
    })
}

fn span_from(pair: &Pair<'_, Rule>) -> Span {
    let pest_span = pair.as_span();
    Span::new(pest_span.start(), pest_span.end())
}

fn spanned<T>(node: T, pair: &Pair<'_, Rule>) -> Spanned<T> {
    Spanned::new(node, span_from(pair))
}

fn build_import(pair: Pair<'_, Rule>) -> Result<Spanned<Item>> {
    let span = span_from(&pair);
    let mut inner = pair.into_inner();

    let path_pair = inner.next().unwrap();
    let raw = path_pair.as_str();
    let path_str = raw.trim_matches('"').to_string();
    let path = spanned(path_str, &path_pair);

    let alias = inner.next().map(|p| spanned(p.as_str().to_string(), &p));

    Ok(Spanned::new(Item::Import(Import { path, alias }), span))
}

fn build_enum(pair: Pair<'_, Rule>) -> Result<Spanned<Item>> {
    let span = span_from(&pair);
    let mut inner = pair.into_inner();

    let name_pair = inner.next().unwrap();
    let name = spanned(name_pair.as_str().to_string(), &name_pair);

    let variants_pair = inner.next().unwrap();
    let variants = variants_pair
        .into_inner()
        .map(|p| spanned(p.as_str().to_string(), &p))
        .collect();

    Ok(Spanned::new(
        Item::EnumDef(EnumDef { name, variants }),
        span,
    ))
}

fn build_fn_def(pair: Pair<'_, Rule>) -> Result<Spanned<Item>> {
    let span = span_from(&pair);
    let mut inner = pair.into_inner();

    let mut is_extern = false;
    let first = inner.next().unwrap();
    let name_pair = if first.as_rule() == Rule::extern_modifier {
        is_extern = true;
        inner.next().unwrap()
    } else {
        first
    };
    let name = spanned(name_pair.as_str().to_string(), &name_pair);

    let mut params = Vec::new();
    let mut return_type = None;
    let mut body = None;

    for part in inner {
        match part.as_rule() {
            Rule::param_list => {
                params = build_params(part)?;
            }
            Rule::type_expr => {
                return_type = Some(build_type_expr(part)?);
            }
            Rule::fn_body => {
                let stmt_list = part.into_inner().next().unwrap();
                let stmts: Result<Vec<_>> =
                    stmt_list.into_inner().map(|s| build_statement(s)).collect();
                body = Some(stmts?);
            }
            _ => {}
        }
    }

    Ok(Spanned::new(
        Item::Function(FnDef {
            name,
            params,
            return_type: return_type.unwrap(),
            body,
            is_extern,
            span,
        }),
        span,
    ))
}

fn build_type_def(pair: Pair<'_, Rule>) -> Result<Spanned<Item>> {
    let span = span_from(&pair);
    let mut inner = pair.into_inner();

    let name_pair = inner.next().unwrap();
    let name = spanned(name_pair.as_str().to_string(), &name_pair);

    let next = inner.next().unwrap();

    if next.as_rule() == Rule::field_list {
        let fields = build_fields(next)?;
        Ok(Spanned::new(
            Item::TypeDef(TypeDef {
                name,
                fields,
                alias: None,
                refinement: None,
            }),
            span,
        ))
    } else {
        let alias_type = build_type_expr(next)?;
        let refinement = inner
            .next()
            .map(|expr_pair| build_expr(expr_pair))
            .transpose()?;
        Ok(Spanned::new(
            Item::TypeDef(TypeDef {
                name,
                fields: Vec::new(),
                alias: Some(alias_type),
                refinement,
            }),
            span,
        ))
    }
}

fn build_const_decl(pair: Pair<'_, Rule>) -> Result<Spanned<Item>> {
    let span = span_from(&pair);
    let mut inner = pair.into_inner();

    let name_pair = inner.next().unwrap();
    let name = spanned(name_pair.as_str().to_string(), &name_pair);

    let ty = build_type_expr(inner.next().unwrap())?;
    let value = build_expr(inner.next().unwrap())?;

    Ok(Spanned::new(
        Item::ConstDef(ConstDef {
            name,
            ty,
            value,
            span,
        }),
        span,
    ))
}

fn build_const_def_inner(pair: Pair<'_, Rule>) -> Result<ConstDef> {
    let span = span_from(&pair);
    let mut inner = pair.into_inner();

    let name_pair = inner.next().unwrap();
    let name = spanned(name_pair.as_str().to_string(), &name_pair);

    let ty = build_type_expr(inner.next().unwrap())?;
    let value = build_expr(inner.next().unwrap())?;

    Ok(ConstDef {
        name,
        ty,
        value,
        span,
    })
}

fn build_fields(pair: Pair<'_, Rule>) -> Result<Vec<Field>> {
    let mut fields = Vec::new();
    for field_pair in pair.into_inner() {
        if field_pair.as_rule() == Rule::field {
            let mut inner = field_pair.into_inner();
            let name_pair = inner.next().unwrap();
            let ty_pair = inner.next().unwrap();
            fields.push(Field {
                name: spanned(name_pair.as_str().to_string(), &name_pair),
                ty: build_type_expr(ty_pair)?,
            });
        }
    }
    Ok(fields)
}

fn build_type_expr(pair: Pair<'_, Rule>) -> Result<Spanned<Type>> {
    let span = span_from(&pair);
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::base_type => {
            let ty = match inner.as_str() {
                "int" => Type::Int,
                "real" => Type::Real,
                "bool" => Type::Bool,
                "string" => Type::String,
                name => Type::Named(name.to_string()),
            };
            Ok(Spanned::new(ty, span))
        }
        Rule::array_type => {
            let mut parts = inner.into_inner();
            let base = parts.next().unwrap();
            let size_pair = parts.next().unwrap();
            let size: usize = size_pair.as_str().parse()?;
            let element = match base.as_str() {
                "int" => Type::Int,
                "real" => Type::Real,
                "bool" => Type::Bool,
                "string" => Type::String,
                name => Type::Named(name.to_string()),
            };
            Ok(Spanned::new(
                Type::Array {
                    element: Box::new(element),
                    size,
                },
                span,
            ))
        }
        Rule::map_type => {
            let mut parts = inner.into_inner();
            let key_pair = parts.next().unwrap();
            let value_pair = parts.next().unwrap();
            let key = build_type_expr(key_pair)?;
            let value = build_type_expr(value_pair)?;
            Ok(Spanned::new(
                Type::Map {
                    key: Box::new(key.node),
                    value: Box::new(value.node),
                },
                span,
            ))
        }
        _ => bail!("unexpected type expression: {:?}", inner.as_rule()),
    }
}

fn build_state(pair: Pair<'_, Rule>) -> Result<Spanned<Item>> {
    let span = span_from(&pair);
    let mut inner = pair.into_inner();

    let name_pair = inner.next().unwrap();
    let name = spanned(name_pair.as_str().to_string(), &name_pair);

    let body_pair = inner.next().unwrap();
    let mut fields = Vec::new();
    let mut constants = Vec::new();
    let mut invariants = Vec::new();
    let mut init = None;
    let mut transitions = Vec::new();

    for member in body_pair.into_inner() {
        match member.as_rule() {
            Rule::const_decl => {
                constants.push(build_const_def_inner(member)?);
            }
            Rule::field_decl => {
                let mut parts = member.into_inner();
                let fname = parts.next().unwrap();
                let ftype = parts.next().unwrap();
                fields.push(Field {
                    name: spanned(fname.as_str().to_string(), &fname),
                    ty: build_type_expr(ftype)?,
                });
            }
            Rule::invariant_decl => {
                let inv_span = span_from(&member);
                let mut parts = member.into_inner();
                let first = parts.next().unwrap();

                let (inv_name, condition) = if first.as_rule() == Rule::ident {
                    let name = Some(spanned(first.as_str().to_string(), &first));
                    let expr_pair = parts.next().unwrap();
                    (name, build_expr(expr_pair)?)
                } else {
                    (None, build_expr(first)?)
                };

                invariants.push(Invariant {
                    name: inv_name,
                    condition,
                    span: inv_span,
                });
            }
            Rule::init_block => {
                let init_span = span_from(&member);
                let assign_list = member.into_inner().next().unwrap();
                let assignments = build_assignments(assign_list)?;
                init = Some(InitBlock {
                    assignments,
                    span: init_span,
                });
            }
            Rule::transition_decl => {
                transitions.push(build_transition(member)?);
            }
            _ => {}
        }
    }

    Ok(Spanned::new(
        Item::State(StateDef {
            name,
            fields,
            constants,
            invariants,
            init,
            transitions,
        }),
        span,
    ))
}

fn build_assignments(pair: Pair<'_, Rule>) -> Result<Vec<Assignment>> {
    let mut assigns = Vec::new();
    for assign_pair in pair.into_inner() {
        if assign_pair.as_rule() == Rule::assignment {
            let mut parts = assign_pair.into_inner();
            let target_pair = parts.next().unwrap();
            let value_pair = parts.next().unwrap();
            assigns.push(Assignment {
                target: spanned(target_pair.as_str().to_string(), &target_pair),
                value: build_expr(value_pair)?,
            });
        }
    }
    Ok(assigns)
}

fn build_transition(pair: Pair<'_, Rule>) -> Result<Transition> {
    let trans_span = span_from(&pair);
    let mut inner = pair.into_inner();

    let name_pair = inner.next().unwrap();
    let name = spanned(name_pair.as_str().to_string(), &name_pair);

    let mut params = Vec::new();
    let mut preconditions = Vec::new();
    let mut body = Vec::new();
    let mut postconditions = Vec::new();
    let mut emits = Vec::new();

    for part in inner {
        match part.as_rule() {
            Rule::param_list => {
                params = build_params(part)?;
            }
            Rule::transition_body => {
                for clause in part.into_inner() {
                    match clause.as_rule() {
                        Rule::where_clause => {
                            let expr_list = clause.into_inner().next().unwrap();
                            for expr_pair in expr_list.into_inner() {
                                preconditions.push(build_expr(expr_pair)?);
                            }
                        }
                        Rule::ensure_clause => {
                            let expr_list = clause.into_inner().next().unwrap();
                            for expr_pair in expr_list.into_inner() {
                                postconditions.push(build_expr(expr_pair)?);
                            }
                        }
                        Rule::emit_clause => {
                            emits.push(build_emit(clause)?);
                        }
                        Rule::assert_stmt => {
                            let assert_span = span_from(&clause);
                            let expr_pair = clause.into_inner().next().unwrap();
                            let condition = build_expr(expr_pair)?;
                            body.push(Spanned::new(Statement::Assert { condition }, assert_span));
                        }
                        Rule::statement => {
                            body.push(build_statement(clause)?);
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    Ok(Transition {
        name,
        params,
        preconditions,
        body,
        postconditions,
        emits,
        span: trans_span,
    })
}

fn build_params(pair: Pair<'_, Rule>) -> Result<Vec<Param>> {
    let mut params = Vec::new();
    for param_pair in pair.into_inner() {
        if param_pair.as_rule() == Rule::param {
            let mut parts = param_pair.into_inner();
            let name_pair = parts.next().unwrap();
            let ty_pair = parts.next().unwrap();
            params.push(Param {
                name: spanned(name_pair.as_str().to_string(), &name_pair),
                ty: build_type_expr(ty_pair)?,
            });
        }
    }
    Ok(params)
}

fn build_emit(pair: Pair<'_, Rule>) -> Result<Spanned<Emit>> {
    let span = span_from(&pair);
    let mut inner = pair.into_inner();

    let name_pair = inner.next().unwrap();
    let event_name = spanned(name_pair.as_str().to_string(), &name_pair);

    let mut args = Vec::new();
    if let Some(arg_list) = inner.next() {
        for arg_pair in arg_list.into_inner() {
            args.push(build_expr(arg_pair)?);
        }
    }

    Ok(Spanned::new(Emit { event_name, args }, span))
}

fn build_statement(pair: Pair<'_, Rule>) -> Result<Spanned<Statement>> {
    let span = span_from(&pair);
    let inner = pair.into_inner().next().unwrap();

    match inner.as_rule() {
        Rule::simple_assign => {
            let mut parts = inner.into_inner();
            let target_pair = parts.next().unwrap();
            let value_pair = parts.next().unwrap();
            Ok(Spanned::new(
                Statement::Assign(Assignment {
                    target: spanned(target_pair.as_str().to_string(), &target_pair),
                    value: build_expr(value_pair)?,
                }),
                span,
            ))
        }
        Rule::compound_assign => {
            let mut parts = inner.into_inner();
            let target_pair = parts.next().unwrap();
            let op_pair = parts.next().unwrap();
            let value_pair = parts.next().unwrap();

            let op = match op_pair.as_str() {
                "+=" => CompoundOp::Add,
                "-=" => CompoundOp::Sub,
                "*=" => CompoundOp::Mul,
                "/=" => CompoundOp::Div,
                _ => bail!("unknown compound operator: {}", op_pair.as_str()),
            };

            Ok(Spanned::new(
                Statement::CompoundAssign {
                    target: spanned(target_pair.as_str().to_string(), &target_pair),
                    op,
                    value: build_expr(value_pair)?,
                },
                span,
            ))
        }
        Rule::if_stmt => {
            let mut parts = inner.into_inner();
            let condition = build_expr(parts.next().unwrap())?;
            let then_list = parts.next().unwrap();
            let then_body: Result<Vec<_>> =
                then_list.into_inner().map(|s| build_statement(s)).collect();

            let else_body = if let Some(else_clause) = parts.next() {
                let inner_clause = else_clause.into_inner().next().unwrap();
                match inner_clause.as_rule() {
                    Rule::if_stmt => {
                        let nested_if = build_statement_inner(inner_clause)?;
                        Some(vec![nested_if])
                    }
                    Rule::statement_list => {
                        let stmts: Result<Vec<_>> = inner_clause
                            .into_inner()
                            .map(|s| build_statement(s))
                            .collect();
                        Some(stmts?)
                    }
                    _ => None,
                }
            } else {
                None
            };

            Ok(Spanned::new(
                Statement::If {
                    condition,
                    then_body: then_body?,
                    else_body,
                },
                span,
            ))
        }
        Rule::indexed_assign => {
            let mut parts = inner.into_inner();
            let target_pair = parts.next().unwrap();
            let index_pair = parts.next().unwrap();
            let value_pair = parts.next().unwrap();
            Ok(Spanned::new(
                Statement::IndexedAssign {
                    target: spanned(target_pair.as_str().to_string(), &target_pair),
                    index: build_expr(index_pair)?,
                    value: build_expr(value_pair)?,
                },
                span,
            ))
        }
        Rule::indexed_compound_assign => {
            let mut parts = inner.into_inner();
            let target_pair = parts.next().unwrap();
            let index_pair = parts.next().unwrap();
            let op_pair = parts.next().unwrap();
            let value_pair = parts.next().unwrap();

            let op = match op_pair.as_str() {
                "+=" => CompoundOp::Add,
                "-=" => CompoundOp::Sub,
                "*=" => CompoundOp::Mul,
                "/=" => CompoundOp::Div,
                _ => bail!("unknown compound operator: {}", op_pair.as_str()),
            };

            Ok(Spanned::new(
                Statement::IndexedCompoundAssign {
                    target: spanned(target_pair.as_str().to_string(), &target_pair),
                    index: build_expr(index_pair)?,
                    op,
                    value: build_expr(value_pair)?,
                },
                span,
            ))
        }
        Rule::let_stmt => {
            let mut parts = inner.into_inner();
            let name_pair = parts.next().unwrap();
            let name = spanned(name_pair.as_str().to_string(), &name_pair);

            let next = parts.next().unwrap();
            let (ty, value) = if next.as_rule() == Rule::type_expr {
                let ty = Some(build_type_expr(next)?);
                let val = build_expr(parts.next().unwrap())?;
                (ty, val)
            } else {
                (None, build_expr(next)?)
            };

            Ok(Spanned::new(Statement::Let { name, ty, value }, span))
        }
        Rule::match_stmt => {
            let mut parts = inner.into_inner();
            let match_expr = build_expr(parts.next().unwrap())?;
            let mut arms = Vec::new();

            for arm_pair in parts {
                if arm_pair.as_rule() == Rule::match_arm {
                    let mut arm_inner = arm_pair.into_inner();
                    let pattern_pair = arm_inner.next().unwrap();
                    let pattern = build_match_pattern(pattern_pair)?;
                    let stmt_list = arm_inner.next().unwrap();
                    let body: Result<Vec<_>> =
                        stmt_list.into_inner().map(|s| build_statement(s)).collect();
                    arms.push(MatchArm {
                        pattern,
                        body: body?,
                    });
                }
            }

            Ok(Spanned::new(
                Statement::Match {
                    expr: match_expr,
                    arms,
                },
                span,
            ))
        }
        _ => bail!("unexpected statement: {:?}", inner.as_rule()),
    }
}

fn build_match_pattern(pair: Pair<'_, Rule>) -> Result<Spanned<MatchPattern>> {
    let span = span_from(&pair);
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::enum_variant => {
            let parts: Vec<String> = inner.into_inner().map(|p| p.as_str().to_string()).collect();
            if parts.len() < 2 {
                bail!("invalid enum variant pattern");
            }
            let variant = parts.last().unwrap().clone();
            let enum_name = parts[..parts.len() - 1].join("::");
            Ok(Spanned::new(
                MatchPattern::EnumVariant { enum_name, variant },
                span,
            ))
        }
        Rule::integer_lit => {
            let val: i64 = inner.as_str().parse()?;
            Ok(Spanned::new(MatchPattern::IntLit(val), span))
        }
        Rule::bool_lit => {
            let val = inner.as_str() == "true";
            Ok(Spanned::new(MatchPattern::BoolLit(val), span))
        }
        Rule::string_lit => {
            let raw = inner.as_str();
            let val = raw[1..raw.len() - 1].to_string();
            Ok(Spanned::new(MatchPattern::StringLit(val), span))
        }
        Rule::ident => {
            if inner.as_str() == "_" {
                Ok(Spanned::new(MatchPattern::Wildcard, span))
            } else {
                bail!("unexpected match pattern: {}", inner.as_str())
            }
        }
        _ => bail!("unexpected match pattern: {:?}", inner.as_rule()),
    }
}

fn build_statement_inner(pair: Pair<'_, Rule>) -> Result<Spanned<Statement>> {
    let span = span_from(&pair);
    match pair.as_rule() {
        Rule::if_stmt => {
            let mut parts = pair.into_inner();
            let condition = build_expr(parts.next().unwrap())?;
            let then_list = parts.next().unwrap();
            let then_body: Result<Vec<_>> =
                then_list.into_inner().map(|s| build_statement(s)).collect();

            let else_body = if let Some(else_clause) = parts.next() {
                let inner_clause = else_clause.into_inner().next().unwrap();
                match inner_clause.as_rule() {
                    Rule::if_stmt => {
                        let nested_if = build_statement_inner(inner_clause)?;
                        Some(vec![nested_if])
                    }
                    Rule::statement_list => {
                        let stmts: Result<Vec<_>> = inner_clause
                            .into_inner()
                            .map(|s| build_statement(s))
                            .collect();
                        Some(stmts?)
                    }
                    _ => None,
                }
            } else {
                None
            };

            Ok(Spanned::new(
                Statement::If {
                    condition,
                    then_body: then_body?,
                    else_body,
                },
                span,
            ))
        }
        _ => bail!("unexpected inner statement: {:?}", pair.as_rule()),
    }
}

pub fn build_expr(pair: Pair<'_, Rule>) -> Result<Spanned<Expr>> {
    let span = span_from(&pair);
    let tokens: Vec<Pair<'_, Rule>> = pair.into_inner().collect();
    let mut pos = 0;
    let result = pratt_parse(&tokens, &mut pos, 0)?;

    if pos < tokens.len() {
        bail!("unexpected tokens remaining in expression");
    }

    if result.span == Span::dummy() {
        Ok(Spanned::new(result.node, span))
    } else {
        Ok(result)
    }
}

fn op_precedence(rule: &Rule) -> u8 {
    match rule {
        Rule::op_range => 1,
        Rule::op_implies => 2,
        Rule::op_or => 3,
        Rule::op_and => 4,
        Rule::op_eq | Rule::op_neq => 5,
        Rule::op_lt | Rule::op_gt | Rule::op_lte | Rule::op_gte => 6,
        Rule::op_add | Rule::op_sub => 7,
        Rule::op_mul | Rule::op_div | Rule::op_mod => 8,
        _ => 0,
    }
}

fn is_binary_op(rule: &Rule) -> bool {
    matches!(
        rule,
        Rule::op_add
            | Rule::op_sub
            | Rule::op_mul
            | Rule::op_div
            | Rule::op_mod
            | Rule::op_eq
            | Rule::op_neq
            | Rule::op_lt
            | Rule::op_gt
            | Rule::op_lte
            | Rule::op_gte
            | Rule::op_and
            | Rule::op_or
            | Rule::op_implies
            | Rule::op_range
    )
}

fn rule_to_binop(rule: &Rule) -> BinaryOp {
    match rule {
        Rule::op_add => BinaryOp::Add,
        Rule::op_sub => BinaryOp::Sub,
        Rule::op_mul => BinaryOp::Mul,
        Rule::op_div => BinaryOp::Div,
        Rule::op_mod => BinaryOp::Mod,
        Rule::op_eq => BinaryOp::Eq,
        Rule::op_neq => BinaryOp::Neq,
        Rule::op_lt => BinaryOp::Lt,
        Rule::op_gt => BinaryOp::Gt,
        Rule::op_lte => BinaryOp::Lte,
        Rule::op_gte => BinaryOp::Gte,
        Rule::op_and => BinaryOp::And,
        Rule::op_or => BinaryOp::Or,
        Rule::op_implies => BinaryOp::Implies,
        _ => unreachable!(),
    }
}

fn pratt_parse(tokens: &[Pair<'_, Rule>], pos: &mut usize, min_prec: u8) -> Result<Spanned<Expr>> {
    let mut left = parse_unary_expr(tokens, pos)?;

    while *pos < tokens.len() {
        let op_rule = tokens[*pos].as_rule();
        if !is_binary_op(&op_rule) {
            break;
        }
        let prec = op_precedence(&op_rule);
        if prec < min_prec {
            break;
        }

        *pos += 1;

        if op_rule == Rule::op_range {
            let right = parse_unary_expr(tokens, pos)?;
            let new_span = left.span.merge(right.span);
            left = Spanned::new(
                Expr::Range {
                    start: Box::new(left),
                    end: Box::new(right),
                },
                new_span,
            );
        } else {
            let right = pratt_parse(tokens, pos, prec + 1)?;
            let new_span = left.span.merge(right.span);
            left = Spanned::new(
                Expr::BinaryOp {
                    left: Box::new(left),
                    op: rule_to_binop(&op_rule),
                    right: Box::new(right),
                },
                new_span,
            );
        }
    }

    Ok(left)
}

fn parse_unary_expr(tokens: &[Pair<'_, Rule>], pos: &mut usize) -> Result<Spanned<Expr>> {
    if *pos < tokens.len() && matches!(tokens[*pos].as_rule(), Rule::op_neg | Rule::op_not) {
        let op_pair = &tokens[*pos];
        let op = match op_pair.as_rule() {
            Rule::op_neg => UnaryOp::Neg,
            Rule::op_not => UnaryOp::Not,
            _ => unreachable!(),
        };
        let op_span = span_from(op_pair);
        *pos += 1;
        let operand = parse_unary_expr(tokens, pos)?;
        let new_span = op_span.merge(operand.span);
        Ok(Spanned::new(
            Expr::UnaryOp {
                op,
                operand: Box::new(operand),
            },
            new_span,
        ))
    } else {
        let primary = build_primary(tokens[*pos].clone())?;
        *pos += 1;
        Ok(primary)
    }
}

fn build_primary(pair: Pair<'_, Rule>) -> Result<Spanned<Expr>> {
    let span = span_from(&pair);

    match pair.as_rule() {
        Rule::integer_lit => {
            let val: i64 = pair.as_str().parse()?;
            Ok(Spanned::new(Expr::IntLit(val), span))
        }
        Rule::real_lit => {
            let val: f64 = pair.as_str().parse()?;
            Ok(Spanned::new(Expr::RealLit(val), span))
        }
        Rule::bool_lit => {
            let val = pair.as_str() == "true";
            Ok(Spanned::new(Expr::BoolLit(val), span))
        }
        Rule::string_lit => {
            let raw = pair.as_str();
            let val = raw[1..raw.len() - 1].to_string();
            Ok(Spanned::new(Expr::StringLit(val), span))
        }
        Rule::ident_access => {
            let mut inner = pair.into_inner();
            let ident_pair = inner.next().unwrap();
            let mut expr = Spanned::new(
                Expr::Ident(ident_pair.as_str().to_string()),
                span_from(&ident_pair),
            );

            for accessor in inner {
                match accessor.as_rule() {
                    Rule::field_access => {
                        let field_pair = accessor.into_inner().next().unwrap();
                        let new_span = expr.span.merge(span_from(&field_pair));
                        expr = Spanned::new(
                            Expr::FieldAccess {
                                object: Box::new(expr),
                                field: spanned(field_pair.as_str().to_string(), &field_pair),
                            },
                            new_span,
                        );
                    }
                    Rule::index_access | Rule::map_access_op => {
                        let idx_expr = accessor.into_inner().next().unwrap();
                        let idx = build_expr(idx_expr)?;
                        let new_span = expr.span.merge(idx.span);
                        expr = Spanned::new(
                            Expr::IndexAccess {
                                object: Box::new(expr),
                                index: Box::new(idx),
                            },
                            new_span,
                        );
                    }
                    _ => {}
                }
            }

            Ok(expr)
        }
        Rule::fn_call => {
            let mut inner = pair.into_inner();
            let name_pair = inner.next().unwrap();
            let name = spanned(name_pair.as_str().to_string(), &name_pair);

            let mut args = Vec::new();
            if let Some(arg_list) = inner.next() {
                for arg_pair in arg_list.into_inner() {
                    args.push(build_expr(arg_pair)?);
                }
            }

            Ok(Spanned::new(Expr::FnCall { name, args }, span))
        }
        Rule::old_expr => {
            let inner_expr = pair.into_inner().next().unwrap();
            let expr = build_expr(inner_expr)?;
            Ok(Spanned::new(Expr::Old(Box::new(expr)), span))
        }
        Rule::forall_expr => {
            let mut inner = pair.into_inner();
            let var_pair = inner.next().unwrap();
            let domain_pair = inner.next().unwrap();
            let body_pair = inner.next().unwrap();

            Ok(Spanned::new(
                Expr::Forall {
                    var: spanned(var_pair.as_str().to_string(), &var_pair),
                    domain: Box::new(build_expr(domain_pair)?),
                    body: Box::new(build_expr(body_pair)?),
                },
                span,
            ))
        }
        Rule::exists_expr => {
            let mut inner = pair.into_inner();
            let var_pair = inner.next().unwrap();
            let domain_pair = inner.next().unwrap();
            let body_pair = inner.next().unwrap();

            Ok(Spanned::new(
                Expr::Exists {
                    var: spanned(var_pair.as_str().to_string(), &var_pair),
                    domain: Box::new(build_expr(domain_pair)?),
                    body: Box::new(build_expr(body_pair)?),
                },
                span,
            ))
        }
        Rule::enum_variant => {
            let parts: Vec<String> = pair.into_inner().map(|p| p.as_str().to_string()).collect();
            if parts.len() < 2 {
                bail!("invalid enum variant expression");
            }
            let variant = parts.last().unwrap().clone();
            let enum_name = parts[..parts.len() - 1].join("::");
            Ok(Spanned::new(Expr::EnumVariant { enum_name, variant }, span))
        }
        Rule::expr => build_expr(pair),
        _ => bail!("unexpected primary expression: {:?}", pair.as_rule()),
    }
}
