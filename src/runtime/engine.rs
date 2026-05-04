use std::collections::HashMap;

use anyhow::{Result, bail};

use crate::ast::nodes::*;
use crate::ast::span::Spanned;

use super::state::{RuntimeEvent, RuntimeState};
use super::value::Value;

pub struct Engine {
    state: RuntimeState,
}

impl Engine {
    pub fn new(state_name: &str) -> Self {
        Self {
            state: RuntimeState::new(state_name.to_string()),
        }
    }

    pub fn load_const(&mut self, c: &ConstDef) -> Result<()> {
        let value = self.eval_expr(&c.value)?;
        self.state.set(&c.name.node, value);
        Ok(())
    }

    pub fn initialize(&mut self, init: &InitBlock) -> Result<()> {
        for assign in &init.assignments {
            let value = self.eval_expr(&assign.value)?;
            self.state.set(&assign.target.node, value);
        }
        Ok(())
    }

    pub fn initialize_state(&mut self, state: &StateDef) -> Result<()> {
        for field in &state.fields {
            let default = Self::default_for_type(&field.ty.node);
            self.state.set(&field.name.node, default);
        }

        if let Some(init) = &state.init {
            self.initialize(init)?;
        }

        Ok(())
    }

    pub fn execute_transition(
        &mut self,
        transition: &Transition,
        args: HashMap<String, Value>,
        invariants: &[Invariant],
    ) -> Result<Vec<RuntimeEvent>> {
        let pre_state = self.state.snapshot();
        let mut locals = args;

        for pre in &transition.preconditions {
            let result = self.eval_expr_with_params(pre, &locals)?;
            if !result.is_truthy() {
                bail!(
                    "precondition failed for transition '{}'",
                    transition.name.node
                );
            }
        }

        let mut events = Vec::new();

        for stmt in &transition.body {
            self.exec_statement(stmt, &mut locals)?;
        }

        for emit in &transition.emits {
            let mut emit_args = Vec::new();
            for arg in &emit.node.args {
                emit_args.push(self.eval_expr_with_params(arg, &locals)?);
            }
            events.push(RuntimeEvent {
                name: emit.node.event_name.node.clone(),
                args: emit_args,
            });
        }

        for post in &transition.postconditions {
            let result = self.eval_postcondition(post, &pre_state, &locals)?;
            if !result.is_truthy() {
                bail!(
                    "postcondition failed for transition '{}'",
                    transition.name.node
                );
            }
        }

        for (i, inv) in invariants.iter().enumerate() {
            let result = self.eval_expr(&inv.condition)?;
            if !result.is_truthy() {
                let inv_name = inv
                    .name
                    .as_ref()
                    .map(|n| n.node.clone())
                    .unwrap_or_else(|| format!("invariant_{}", i));
                bail!(
                    "invariant '{}' violated after transition '{}'",
                    inv_name,
                    transition.name.node
                );
            }
        }

        self.state
            .record_transition(&transition.name.node, pre_state, events.clone());

        Ok(events)
    }

    pub fn get_state(&self) -> &RuntimeState {
        &self.state
    }

    pub fn get_field(&self, name: &str) -> Option<&Value> {
        self.state.get(name)
    }

    fn exec_statement(
        &mut self,
        stmt: &Spanned<Statement>,
        params: &mut HashMap<String, Value>,
    ) -> Result<()> {
        match &stmt.node {
            Statement::Assign(assign) => {
                let value = self.eval_expr_with_params(&assign.value, params)?;
                self.state.set(&assign.target.node, value);
            }
            Statement::CompoundAssign { target, op, value } => {
                let current = self
                    .state
                    .get(&target.node)
                    .cloned()
                    .unwrap_or(Value::Int(0));
                let rhs = self.eval_expr_with_params(value, params)?;
                let result = self.apply_compound_op(&current, op, &rhs)?;
                self.state.set(&target.node, result);
            }
            Statement::If {
                condition,
                then_body,
                else_body,
            } => {
                let cond = self.eval_expr_with_params(condition, params)?;
                if cond.is_truthy() {
                    for s in then_body {
                        self.exec_statement(s, params)?;
                    }
                } else if let Some(else_stmts) = else_body {
                    for s in else_stmts {
                        self.exec_statement(s, params)?;
                    }
                }
            }
            Statement::IndexedAssign {
                target,
                index,
                value,
            } => {
                let idx = self.eval_expr_with_params(index, params)?;
                let val = self.eval_expr_with_params(value, params)?;
                if let Some(arr) = self.state.get(&target.node).cloned() {
                    match arr {
                        Value::Array(mut elems) => {
                            if let Value::Int(i) = idx {
                                let i = i as usize;
                                if i < elems.len() {
                                    elems[i] = val;
                                    self.state.set(&target.node, Value::Array(elems));
                                } else {
                                    bail!("array index {} out of bounds (len {})", i, elems.len());
                                }
                            }
                        }
                        Value::Map(mut map) => {
                            let key = format!("{}", idx);
                            map.insert(key, val);
                            self.state.set(&target.node, Value::Map(map));
                        }
                        _ => bail!("cannot index into {:?}", arr),
                    }
                }
            }
            Statement::IndexedCompoundAssign {
                target,
                index,
                op,
                value,
            } => {
                let idx = self.eval_expr_with_params(index, params)?;
                let rhs = self.eval_expr_with_params(value, params)?;
                if let Some(arr) = self.state.get(&target.node).cloned() {
                    match arr {
                        Value::Array(mut elems) => {
                            if let Value::Int(i) = idx {
                                let i = i as usize;
                                if i < elems.len() {
                                    let result = self.apply_compound_op(&elems[i], op, &rhs)?;
                                    elems[i] = result;
                                    self.state.set(&target.node, Value::Array(elems));
                                } else {
                                    bail!("array index {} out of bounds (len {})", i, elems.len());
                                }
                            }
                        }
                        Value::Map(mut map) => {
                            let key = format!("{}", idx);
                            let current = map.get(&key).cloned().unwrap_or(Value::Int(0));
                            let result = self.apply_compound_op(&current, op, &rhs)?;
                            map.insert(key, result);
                            self.state.set(&target.node, Value::Map(map));
                        }
                        _ => bail!("cannot index into {:?}", arr),
                    }
                }
            }
            Statement::Assert { condition } => {
                let val = self.eval_expr_with_params(condition, params)?;
                if !val.is_truthy() {
                    bail!("assertion failed");
                }
            }
            Statement::Let { name, value, .. } => {
                let val = self.eval_expr_with_params(value, params)?;
                params.insert(name.node.clone(), val);
            }
            Statement::Match { expr, arms } => {
                let subject = self.eval_expr_with_params(expr, params)?;
                let mut matched = false;
                for arm in arms {
                    if self.match_pattern_runtime(&subject, &arm.pattern.node) {
                        for s in &arm.body {
                            self.exec_statement(s, params)?;
                        }
                        matched = true;
                        break;
                    }
                }
                if !matched {
                    bail!("non-exhaustive match at runtime");
                }
            }
        }
        Ok(())
    }

    fn match_pattern_runtime(&self, value: &Value, pattern: &MatchPattern) -> bool {
        match pattern {
            MatchPattern::Wildcard => true,
            MatchPattern::IntLit(v) => matches!(value, Value::Int(i) if i == v),
            MatchPattern::BoolLit(v) => matches!(value, Value::Bool(b) if b == v),
            MatchPattern::StringLit(v) => matches!(value, Value::String(s) if s == v),
            MatchPattern::EnumVariant { enum_name, variant } => {
                matches!(
                    value,
                    Value::Enum {
                        enum_name: en,
                        variant: vr
                    } if en == enum_name && vr == variant
                ) || matches!(
                    value,
                    Value::String(s) if s == &format!("{}::{}", enum_name, variant) || s == variant
                )
            }
        }
    }

    fn default_for_type(ty: &crate::ast::types::Type) -> Value {
        use crate::ast::types::Type;

        match ty {
            Type::Int => Value::Int(0),
            Type::Real => Value::Real(0.0),
            Type::Bool => Value::Bool(false),
            Type::String => Value::String(String::new()),
            Type::Array { element, size } => {
                Value::Array(vec![Self::default_for_type(element); *size])
            }
            Type::Map { .. } => Value::Map(HashMap::new()),
            Type::Enum(_) | Type::Named(_) => Value::Null,
        }
    }

    fn apply_compound_op(&self, current: &Value, op: &CompoundOp, rhs: &Value) -> Result<Value> {
        match (current, rhs) {
            (Value::Int(a), Value::Int(b)) => {
                let result = match op {
                    CompoundOp::Add => a + b,
                    CompoundOp::Sub => a - b,
                    CompoundOp::Mul => a * b,
                    CompoundOp::Div => {
                        if *b == 0 {
                            bail!("division by zero");
                        }
                        a / b
                    }
                };
                Ok(Value::Int(result))
            }
            (Value::Real(a), Value::Real(b)) => {
                let result = match op {
                    CompoundOp::Add => a + b,
                    CompoundOp::Sub => a - b,
                    CompoundOp::Mul => a * b,
                    CompoundOp::Div => {
                        if *b == 0.0 {
                            bail!("division by zero");
                        }
                        a / b
                    }
                };
                Ok(Value::Real(result))
            }
            _ => bail!("incompatible types for compound operation"),
        }
    }

    pub fn eval_expr(&self, expr: &Spanned<Expr>) -> Result<Value> {
        self.eval_expr_with_params(expr, &HashMap::new())
    }

    fn eval_expr_with_params(
        &self,
        expr: &Spanned<Expr>,
        params: &HashMap<String, Value>,
    ) -> Result<Value> {
        match &expr.node {
            Expr::IntLit(v) => Ok(Value::Int(*v)),
            Expr::RealLit(v) => Ok(Value::Real(*v)),
            Expr::BoolLit(v) => Ok(Value::Bool(*v)),
            Expr::StringLit(v) => Ok(Value::String(v.clone())),
            Expr::Ident(name) => {
                if let Some(val) = params.get(name) {
                    Ok(val.clone())
                } else if let Some(val) = self.state.get(name) {
                    Ok(val.clone())
                } else {
                    bail!("undefined variable: {}", name)
                }
            }
            Expr::UnaryOp { op, operand } => {
                let val = self.eval_expr_with_params(operand, params)?;
                match op {
                    UnaryOp::Neg => match val {
                        Value::Int(v) => Ok(Value::Int(-v)),
                        Value::Real(v) => Ok(Value::Real(-v)),
                        _ => bail!("cannot negate non-numeric value"),
                    },
                    UnaryOp::Not => match val {
                        Value::Bool(v) => Ok(Value::Bool(!v)),
                        _ => bail!("cannot negate non-boolean value"),
                    },
                }
            }
            Expr::BinaryOp { left, op, right } => {
                let l = self.eval_expr_with_params(left, params)?;
                let r = self.eval_expr_with_params(right, params)?;
                self.eval_binary_op(&l, op, &r)
            }
            Expr::Old(_) => bail!("old() can only be used in postconditions"),
            Expr::EnumVariant { enum_name, variant } => Ok(Value::Enum {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
            }),
            Expr::FieldAccess { object, field } => {
                let obj = self.eval_expr_with_params(object, params)?;
                match obj {
                    Value::Record(fields) => fields
                        .get(&field.node)
                        .cloned()
                        .ok_or_else(|| anyhow::anyhow!("field '{}' not found", field.node)),
                    _ => bail!("cannot access field on non-record value"),
                }
            }
            Expr::IndexAccess { object, index } => {
                let obj = self.eval_expr_with_params(object, params)?;
                let idx = self.eval_expr_with_params(index, params)?;
                match (&obj, &idx) {
                    (Value::Array(items), Value::Int(i)) => {
                        let i = *i as usize;
                        items
                            .get(i)
                            .cloned()
                            .ok_or_else(|| anyhow::anyhow!("index {} out of bounds", i))
                    }
                    (Value::Map(entries), Value::String(key)) => entries
                        .get(key)
                        .cloned()
                        .ok_or_else(|| anyhow::anyhow!("key '{}' not found", key)),
                    _ => bail!("invalid index access"),
                }
            }
            Expr::Forall { var, domain, body } => {
                if let Expr::Range { start, end } = &domain.node {
                    let s = self.eval_expr_with_params(start, params)?.as_int().unwrap();
                    let e = self.eval_expr_with_params(end, params)?.as_int().unwrap();
                    for i in s..e {
                        let mut inner_params = params.clone();
                        inner_params.insert(var.node.clone(), Value::Int(i));
                        let result = self.eval_expr_with_params(body, &inner_params)?;
                        if !result.is_truthy() {
                            return Ok(Value::Bool(false));
                        }
                    }
                    Ok(Value::Bool(true))
                } else {
                    bail!("forall requires a range domain in runtime")
                }
            }
            Expr::Exists { var, domain, body } => {
                if let Expr::Range { start, end } = &domain.node {
                    let s = self.eval_expr_with_params(start, params)?.as_int().unwrap();
                    let e = self.eval_expr_with_params(end, params)?.as_int().unwrap();
                    for i in s..e {
                        let mut inner_params = params.clone();
                        inner_params.insert(var.node.clone(), Value::Int(i));
                        let result = self.eval_expr_with_params(body, &inner_params)?;
                        if result.is_truthy() {
                            return Ok(Value::Bool(true));
                        }
                    }
                    Ok(Value::Bool(false))
                } else {
                    bail!("exists requires a range domain in runtime")
                }
            }
            Expr::FnCall { name, args } => self.eval_builtin_call(&name.node, args, params),
            _ => bail!("unsupported expression in runtime"),
        }
    }

    fn eval_postcondition(
        &self,
        expr: &Spanned<Expr>,
        pre_state: &HashMap<String, Value>,
        params: &HashMap<String, Value>,
    ) -> Result<Value> {
        match &expr.node {
            Expr::Old(inner) => {
                let mut old_params = params.clone();
                for (k, v) in pre_state {
                    old_params.insert(k.clone(), v.clone());
                }
                self.eval_expr_with_params(inner, &old_params)
            }
            Expr::BinaryOp { left, op, right } => {
                let l = self.eval_postcondition(left, pre_state, params)?;
                let r = self.eval_postcondition(right, pre_state, params)?;
                self.eval_binary_op(&l, op, &r)
            }
            _ => self.eval_expr_with_params(expr, params),
        }
    }

    fn eval_binary_op(&self, left: &Value, op: &BinaryOp, right: &Value) -> Result<Value> {
        match (left, right) {
            (Value::Int(a), Value::Int(b)) => match op {
                BinaryOp::Add => Ok(Value::Int(a + b)),
                BinaryOp::Sub => Ok(Value::Int(a - b)),
                BinaryOp::Mul => Ok(Value::Int(a * b)),
                BinaryOp::Div => {
                    if *b == 0 {
                        bail!("division by zero");
                    }
                    Ok(Value::Int(a / b))
                }
                BinaryOp::Mod => {
                    if *b == 0 {
                        bail!("division by zero");
                    }
                    Ok(Value::Int(a % b))
                }
                BinaryOp::Eq => Ok(Value::Bool(a == b)),
                BinaryOp::Neq => Ok(Value::Bool(a != b)),
                BinaryOp::Lt => Ok(Value::Bool(a < b)),
                BinaryOp::Gt => Ok(Value::Bool(a > b)),
                BinaryOp::Lte => Ok(Value::Bool(a <= b)),
                BinaryOp::Gte => Ok(Value::Bool(a >= b)),
                _ => bail!("invalid operator for integers"),
            },
            (Value::Real(a), Value::Real(b)) => match op {
                BinaryOp::Add => Ok(Value::Real(a + b)),
                BinaryOp::Sub => Ok(Value::Real(a - b)),
                BinaryOp::Mul => Ok(Value::Real(a * b)),
                BinaryOp::Div => {
                    if *b == 0.0 {
                        bail!("division by zero");
                    }
                    Ok(Value::Real(a / b))
                }
                BinaryOp::Eq => Ok(Value::Bool(a == b)),
                BinaryOp::Neq => Ok(Value::Bool(a != b)),
                BinaryOp::Lt => Ok(Value::Bool(a < b)),
                BinaryOp::Gt => Ok(Value::Bool(a > b)),
                BinaryOp::Lte => Ok(Value::Bool(a <= b)),
                BinaryOp::Gte => Ok(Value::Bool(a >= b)),
                _ => bail!("invalid operator for reals"),
            },
            (Value::Bool(a), Value::Bool(b)) => match op {
                BinaryOp::And => Ok(Value::Bool(*a && *b)),
                BinaryOp::Or => Ok(Value::Bool(*a || *b)),
                BinaryOp::Implies => Ok(Value::Bool(!*a || *b)),
                BinaryOp::Eq => Ok(Value::Bool(a == b)),
                BinaryOp::Neq => Ok(Value::Bool(a != b)),
                _ => bail!("invalid operator for booleans"),
            },
            (Value::String(a), Value::String(b)) => match op {
                BinaryOp::Eq => Ok(Value::Bool(a == b)),
                BinaryOp::Neq => Ok(Value::Bool(a != b)),
                _ => bail!("invalid operator for strings"),
            },
            (
                Value::Enum {
                    enum_name: e1,
                    variant: v1,
                },
                Value::Enum {
                    enum_name: e2,
                    variant: v2,
                },
            ) => match op {
                BinaryOp::Eq => Ok(Value::Bool(e1 == e2 && v1 == v2)),
                BinaryOp::Neq => Ok(Value::Bool(e1 != e2 || v1 != v2)),
                _ => bail!("invalid operator for enums"),
            },
            _ => bail!("incompatible types for binary operation"),
        }
    }

    fn eval_builtin_call(
        &self,
        name: &str,
        args: &[Spanned<Expr>],
        params: &HashMap<String, Value>,
    ) -> Result<Value> {
        match name {
            "abs" if args.len() == 1 => {
                let val = self.eval_expr_with_params(&args[0], params)?;
                match val {
                    Value::Int(v) => Ok(Value::Int(v.abs())),
                    Value::Real(v) => Ok(Value::Real(v.abs())),
                    _ => bail!("abs() requires a numeric argument"),
                }
            }
            "min" if args.len() == 2 => {
                let a = self.eval_expr_with_params(&args[0], params)?;
                let b = self.eval_expr_with_params(&args[1], params)?;
                match (&a, &b) {
                    (Value::Int(x), Value::Int(y)) => Ok(Value::Int(*x.min(y))),
                    (Value::Real(x), Value::Real(y)) => Ok(Value::Real(x.min(*y))),
                    _ => bail!("min() requires two numeric arguments of the same type"),
                }
            }
            "max" if args.len() == 2 => {
                let a = self.eval_expr_with_params(&args[0], params)?;
                let b = self.eval_expr_with_params(&args[1], params)?;
                match (&a, &b) {
                    (Value::Int(x), Value::Int(y)) => Ok(Value::Int(*x.max(y))),
                    (Value::Real(x), Value::Real(y)) => Ok(Value::Real(x.max(*y))),
                    _ => bail!("max() requires two numeric arguments of the same type"),
                }
            }
            _ => bail!("unknown function: {}", name),
        }
    }
}
