use std::collections::HashMap;

use z3::Context;
use z3::ast::{Ast, Bool, Dynamic};

use crate::ast::nodes::*;
use crate::ast::span::Spanned;
use crate::ast::types::EnumDef;

use super::counterexample::Counterexample;
use super::encoder::Encoder;
use super::solver::{CheckResult, SolverSession};

use crate::codegen::formatter;

#[derive(Debug, Clone)]
pub struct VerificationResult {
    pub state_name: String,
    pub checks: Vec<CheckReport>,
}

#[derive(Debug, Clone)]
pub struct CheckReport {
    pub kind: CheckKind,
    pub passed: bool,
    pub counterexample: Option<Counterexample>,
}

#[derive(Debug, Clone)]
pub enum CheckKind {
    InitSatisfiesInvariant {
        invariant_name: String,
    },
    TransitionPreservesInvariant {
        transition_name: String,
        invariant_name: String,
    },
    PostconditionHolds {
        transition_name: String,
    },
    DeadTransition {
        transition_name: String,
    },
}

impl std::fmt::Display for CheckKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckKind::InitSatisfiesInvariant { invariant_name } => {
                write!(f, "init satisfies invariant '{}'", invariant_name)
            }
            CheckKind::TransitionPreservesInvariant {
                transition_name,
                invariant_name,
            } => {
                write!(
                    f,
                    "transition '{}' preserves invariant '{}'",
                    transition_name, invariant_name
                )
            }
            CheckKind::PostconditionHolds { transition_name } => {
                write!(f, "postcondition of '{}' holds", transition_name)
            }
            CheckKind::DeadTransition { transition_name } => {
                write!(
                    f,
                    "transition '{}' is reachable (not dead)",
                    transition_name
                )
            }
        }
    }
}

pub struct Verifier<'ctx> {
    ctx: &'ctx Context,
    encoder: Encoder<'ctx>,
    refinements: HashMap<String, (crate::ast::types::Type, Spanned<Expr>)>,
    constants: HashMap<String, Dynamic<'ctx>>,
}

impl<'ctx> Verifier<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            encoder: Encoder::new(ctx),
            refinements: HashMap::new(),
            constants: HashMap::new(),
        }
    }

    pub fn register_enum(&mut self, def: &EnumDef) {
        self.encoder.register_enum(def);
    }

    pub fn register_function(&mut self, func: &crate::ast::nodes::FnDef) {
        self.encoder.register_function(func);
    }

    pub fn register_type_def(&mut self, typedef: &crate::ast::types::TypeDef) {
        if let (Some(alias), Some(refinement)) = (&typedef.alias, &typedef.refinement) {
            self.refinements.insert(
                typedef.name.node.clone(),
                (alias.node.clone(), refinement.clone()),
            );
        }
    }

    pub fn register_const(&mut self, constant: &ConstDef) {
        let vars = self.constants.clone();
        if let Some(encoded) = self.encoder.encode_expr(&constant.value, &vars) {
            self.constants.insert(constant.name.node.clone(), encoded);
        }
    }

    pub fn verify_state(&self, state: &StateDef) -> VerificationResult {
        let mut checks = Vec::new();
        let constants = self.collect_constants(state);

        checks.extend(self.check_init(state, &constants));

        for transition in &state.transitions {
            checks
                .extend(self.check_transition_preserves_invariants(state, transition, &constants));
            checks.extend(self.check_postconditions(state, transition, &constants));
            checks.push(self.check_dead_transition(state, transition, &constants));
        }

        VerificationResult {
            state_name: state.name.node.clone(),
            checks,
        }
    }

    fn collect_constants(&self, state: &StateDef) -> HashMap<String, Dynamic<'ctx>> {
        let mut vars = self.constants.clone();
        for constant in &state.constants {
            if let Some(encoded) = self.encoder.encode_expr(&constant.value, &vars) {
                vars.insert(constant.name.node.clone(), encoded);
            }
        }
        vars
    }

    fn make_state_vars(
        &self,
        fields: &[crate::ast::types::Field],
        prefix: &str,
    ) -> HashMap<String, Dynamic<'ctx>> {
        let mut vars = HashMap::new();
        for field in fields {
            let resolved_ty = self.resolve_type_for_field(&field.ty.node);
            let var = self
                .encoder
                .encode_state_var(&field.name.node, &resolved_ty, prefix);
            vars.insert(format!("{}_{}", prefix, &field.name.node), var.clone());
            if prefix == "pre" || prefix == "init" {
                vars.insert(field.name.node.clone(), var);
            }
        }
        vars
    }

    fn resolve_type_for_field(&self, ty: &crate::ast::types::Type) -> crate::ast::types::Type {
        if let crate::ast::types::Type::Named(name) = ty
            && let Some((base_ty, _)) = self.refinements.get(name)
        {
            return base_ty.clone();
        }
        ty.clone()
    }

    fn assert_refinements_for_fields(
        &self,
        fields: &[crate::ast::types::Field],
        vars: &HashMap<String, Dynamic<'ctx>>,
        session: &SolverSession<'ctx>,
    ) {
        for field in fields {
            if let crate::ast::types::Type::Named(type_name) = &field.ty.node
                && let Some((_base_ty, refinement)) = self.refinements.get(type_name)
            {
                let mut ref_vars = vars.clone();
                if let Some(val) = vars.get(&field.name.node) {
                    ref_vars.insert("value".to_string(), val.clone());
                }
                if let Some(encoded) = self.encoder.encode_expr(refinement, &ref_vars)
                    && let Some(bool_expr) = encoded.as_bool()
                {
                    session.assert(&bool_expr);
                }
            }
        }
    }

    fn assert_param_refinements(
        &self,
        params: &[Param],
        vars: &HashMap<String, Dynamic<'ctx>>,
        session: &SolverSession<'ctx>,
    ) {
        for param in params {
            if let crate::ast::types::Type::Named(type_name) = &param.ty.node
                && let Some((_base_ty, refinement)) = self.refinements.get(type_name)
            {
                let mut ref_vars = vars.clone();
                if let Some(val) = vars.get(&param.name.node) {
                    ref_vars.insert("value".to_string(), val.clone());
                }
                if let Some(encoded) = self.encoder.encode_expr(refinement, &ref_vars)
                    && let Some(bool_expr) = encoded.as_bool()
                {
                    session.assert(&bool_expr);
                }
            }
        }
    }

    fn check_init(
        &self,
        state: &StateDef,
        constants: &HashMap<String, Dynamic<'ctx>>,
    ) -> Vec<CheckReport> {
        let mut reports = Vec::new();
        let init = match &state.init {
            Some(init) => init,
            None => return reports,
        };

        let session = SolverSession::new(self.ctx);
        let mut vars = self.make_state_vars(&state.fields, "init");
        vars.extend(constants.clone());

        for assign in &init.assignments {
            let var_name = &assign.target.node;
            if let Some(var) = vars.get(var_name)
                && let Some(val) = self.encoder.encode_expr(&assign.value, &vars)
            {
                if let (Some(v), Some(e)) = (var.as_int(), val.as_int()) {
                    session.assert(&v._eq(&e));
                } else if let (Some(v), Some(e)) = (var.as_bool(), val.as_bool()) {
                    session.assert(&v._eq(&e));
                } else if let (Some(v), Some(e)) = (var.as_real(), val.as_real()) {
                    session.assert(&v._eq(&e));
                }
            }
        }

        for (i, inv) in state.invariants.iter().enumerate() {
            let inv_name = inv
                .name
                .as_ref()
                .map(|n| n.node.clone())
                .unwrap_or_else(|| format!("invariant_{}", i));

            session.push();

            let encoded = self.encoder.encode_expr(&inv.condition, &vars);
            let warnings = self.encoder.take_warnings();

            match encoded.and_then(|e| e.as_bool()) {
                Some(bool_expr) => {
                    session.assert(&bool_expr.not());

                    let var_list: Vec<(String, Dynamic)> =
                        vars.iter().map(|(k, v)| (k.clone(), v.clone())).collect();

                    match session.check() {
                        CheckResult::Verified => {
                            reports.push(CheckReport {
                                kind: CheckKind::InitSatisfiesInvariant {
                                    invariant_name: inv_name,
                                },
                                passed: true,
                                counterexample: None,
                            });
                        }
                        CheckResult::Failed { .. } => {
                            let ce_values = session.extract_counterexample(&var_list);
                            reports.push(CheckReport {
                                kind: CheckKind::InitSatisfiesInvariant {
                                    invariant_name: inv_name.clone(),
                                },
                                passed: false,
                                counterexample: Some(
                                    Counterexample::new(
                                        format!("init violates invariant '{}'", inv_name),
                                        ce_values,
                                        Some(inv.span),
                                    )
                                    .with_expression(formatter::format_expr(&inv.condition.node)),
                                ),
                            });
                        }
                        CheckResult::Unknown { reason } => {
                            reports.push(CheckReport {
                                kind: CheckKind::InitSatisfiesInvariant {
                                    invariant_name: inv_name,
                                },
                                passed: false,
                                counterexample: Some(Counterexample::new(
                                    format!("solver returned unknown: {}", reason),
                                    vec![],
                                    Some(inv.span),
                                )),
                            });
                        }
                    }
                }
                None => {
                    let msg = if warnings.is_empty() {
                        "could not encode invariant expression".to_string()
                    } else {
                        format!("could not encode invariant: {}", warnings.join("; "))
                    };
                    reports.push(CheckReport {
                        kind: CheckKind::InitSatisfiesInvariant {
                            invariant_name: inv_name,
                        },
                        passed: false,
                        counterexample: Some(Counterexample::new(msg, vec![], Some(inv.span))),
                    });
                }
            }

            session.pop();
        }

        reports
    }

    fn check_transition_preserves_invariants(
        &self,
        state: &StateDef,
        transition: &Transition,
        constants: &HashMap<String, Dynamic<'ctx>>,
    ) -> Vec<CheckReport> {
        let mut reports = Vec::new();
        let session = SolverSession::new(self.ctx);

        let mut pre_vars = self.make_state_vars(&state.fields, "pre");
        let mut post_vars = self.make_state_vars(&state.fields, "post");
        pre_vars.extend(constants.clone());
        post_vars.extend(constants.clone());

        let mut all_vars = pre_vars.clone();
        all_vars.extend(post_vars.clone());

        for param in &transition.params {
            let resolved_ty = self.resolve_type_for_field(&param.ty.node);
            let var = self
                .encoder
                .encode_state_var(&param.name.node, &resolved_ty, "param");
            all_vars.insert(param.name.node.clone(), var);
        }

        for inv in &state.invariants {
            if let Some(encoded) = self.encoder.encode_expr(&inv.condition, &pre_vars)
                && let Some(bool_expr) = encoded.as_bool()
            {
                session.assert(&bool_expr);
            }
        }

        self.assert_refinements_for_fields(&state.fields, &pre_vars, &session);

        for pre in &transition.preconditions {
            if let Some(encoded) = self.encoder.encode_expr(pre, &all_vars)
                && let Some(bool_expr) = encoded.as_bool()
            {
                session.assert(&bool_expr);
            }
        }

        self.assert_param_refinements(&transition.params, &all_vars, &session);

        self.encode_transition_body(
            state,
            transition,
            &pre_vars,
            &post_vars,
            &session,
            &all_vars,
            constants,
        );

        let mut post_eval_vars = post_vars.clone();
        for (name, var) in &pre_vars {
            if !name.starts_with("pre_") && !post_eval_vars.contains_key(name) {
                post_eval_vars.insert(name.clone(), var.clone());
            }
        }
        for field in &state.fields {
            post_eval_vars.insert(
                field.name.node.clone(),
                post_vars
                    .get(&format!("post_{}", field.name.node))
                    .unwrap()
                    .clone(),
            );
        }

        for (i, inv) in state.invariants.iter().enumerate() {
            let inv_name = inv
                .name
                .as_ref()
                .map(|n| n.node.clone())
                .unwrap_or_else(|| format!("invariant_{}", i));

            session.push();

            let encoded = self.encoder.encode_expr(&inv.condition, &post_eval_vars);
            let warnings = self.encoder.take_warnings();

            match encoded.and_then(|e| e.as_bool()) {
                Some(bool_expr) => {
                    session.assert(&bool_expr.not());

                    let var_list: Vec<(String, Dynamic)> = all_vars
                        .iter()
                        .chain(post_vars.iter())
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();

                    match session.check() {
                        CheckResult::Verified => {
                            reports.push(CheckReport {
                                kind: CheckKind::TransitionPreservesInvariant {
                                    transition_name: transition.name.node.clone(),
                                    invariant_name: inv_name,
                                },
                                passed: true,
                                counterexample: None,
                            });
                        }
                        CheckResult::Failed { .. } => {
                            let ce_values = session.extract_counterexample(&var_list);
                            reports.push(CheckReport {
                                kind: CheckKind::TransitionPreservesInvariant {
                                    transition_name: transition.name.node.clone(),
                                    invariant_name: inv_name.clone(),
                                },
                                passed: false,
                                counterexample: Some(
                                    Counterexample::new(
                                        format!(
                                            "transition '{}' can violate invariant '{}'",
                                            transition.name.node, inv_name
                                        ),
                                        ce_values,
                                        Some(transition.span),
                                    )
                                    .with_expression(formatter::format_expr(&inv.condition.node)),
                                ),
                            });
                        }
                        CheckResult::Unknown { reason } => {
                            reports.push(CheckReport {
                                kind: CheckKind::TransitionPreservesInvariant {
                                    transition_name: transition.name.node.clone(),
                                    invariant_name: inv_name,
                                },
                                passed: false,
                                counterexample: Some(Counterexample::new(
                                    format!("solver returned unknown: {}", reason),
                                    vec![],
                                    Some(transition.span),
                                )),
                            });
                        }
                    }
                }
                None => {
                    let msg = if warnings.is_empty() {
                        format!(
                            "could not encode invariant '{}' for transition '{}'",
                            inv_name, transition.name.node
                        )
                    } else {
                        format!(
                            "could not encode invariant '{}': {}",
                            inv_name,
                            warnings.join("; ")
                        )
                    };
                    reports.push(CheckReport {
                        kind: CheckKind::TransitionPreservesInvariant {
                            transition_name: transition.name.node.clone(),
                            invariant_name: inv_name,
                        },
                        passed: false,
                        counterexample: Some(Counterexample::new(msg, vec![], Some(inv.span))),
                    });
                }
            }

            session.pop();
        }

        reports
    }

    fn check_postconditions(
        &self,
        state: &StateDef,
        transition: &Transition,
        constants: &HashMap<String, Dynamic<'ctx>>,
    ) -> Vec<CheckReport> {
        if transition.postconditions.is_empty() {
            return Vec::new();
        }

        let mut reports = Vec::new();
        let session = SolverSession::new(self.ctx);

        let mut pre_vars = self.make_state_vars(&state.fields, "pre");
        let mut post_vars = self.make_state_vars(&state.fields, "post");
        pre_vars.extend(constants.clone());
        post_vars.extend(constants.clone());

        let mut all_vars = pre_vars.clone();
        all_vars.extend(post_vars.clone());

        for param in &transition.params {
            let resolved_ty = self.resolve_type_for_field(&param.ty.node);
            let var = self
                .encoder
                .encode_state_var(&param.name.node, &resolved_ty, "param");
            all_vars.insert(param.name.node.clone(), var);
        }

        for inv in &state.invariants {
            if let Some(encoded) = self.encoder.encode_expr(&inv.condition, &pre_vars)
                && let Some(bool_expr) = encoded.as_bool()
            {
                session.assert(&bool_expr);
            }
        }

        self.assert_refinements_for_fields(&state.fields, &pre_vars, &session);

        for pre in &transition.preconditions {
            if let Some(encoded) = self.encoder.encode_expr(pre, &all_vars)
                && let Some(bool_expr) = encoded.as_bool()
            {
                session.assert(&bool_expr);
            }
        }

        self.assert_param_refinements(&transition.params, &all_vars, &session);

        self.encode_transition_body(
            state,
            transition,
            &pre_vars,
            &post_vars,
            &session,
            &all_vars,
            constants,
        );

        let mut post_eval_vars = all_vars.clone();
        for field in &state.fields {
            post_eval_vars.insert(
                field.name.node.clone(),
                post_vars
                    .get(&format!("post_{}", field.name.node))
                    .unwrap()
                    .clone(),
            );
        }

        let mut postcond_exprs = Vec::new();
        let mut encode_failed = false;
        for post in &transition.postconditions {
            let encoded = self.encoder.encode_expr(post, &post_eval_vars);
            let _warnings = self.encoder.take_warnings();
            match encoded.and_then(|e| e.as_bool()) {
                Some(bool_expr) => postcond_exprs.push(bool_expr),
                None => {
                    encode_failed = true;
                }
            }
        }

        if encode_failed {
            reports.push(CheckReport {
                kind: CheckKind::PostconditionHolds {
                    transition_name: transition.name.node.clone(),
                },
                passed: false,
                counterexample: Some(Counterexample::new(
                    format!(
                        "could not encode postcondition of '{}'",
                        transition.name.node
                    ),
                    vec![],
                    Some(transition.span),
                )),
            });
        } else if !postcond_exprs.is_empty() {
            let refs: Vec<&Bool> = postcond_exprs.iter().collect();
            let all_posts = Bool::and(self.ctx, &refs);
            session.assert(&all_posts.not());

            let var_list: Vec<(String, Dynamic)> = all_vars
                .iter()
                .chain(post_vars.iter())
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();

            match session.check() {
                CheckResult::Verified => {
                    reports.push(CheckReport {
                        kind: CheckKind::PostconditionHolds {
                            transition_name: transition.name.node.clone(),
                        },
                        passed: true,
                        counterexample: None,
                    });
                }
                CheckResult::Failed { .. } => {
                    let ce_values = session.extract_counterexample(&var_list);
                    let postcond_text = transition
                        .postconditions
                        .iter()
                        .map(|p| formatter::format_expr(&p.node))
                        .collect::<Vec<_>>()
                        .join(" && ");
                    reports.push(CheckReport {
                        kind: CheckKind::PostconditionHolds {
                            transition_name: transition.name.node.clone(),
                        },
                        passed: false,
                        counterexample: Some(
                            Counterexample::new(
                                format!(
                                    "postcondition of '{}' can be violated",
                                    transition.name.node
                                ),
                                ce_values,
                                Some(transition.span),
                            )
                            .with_expression(postcond_text),
                        ),
                    });
                }
                CheckResult::Unknown { reason } => {
                    reports.push(CheckReport {
                        kind: CheckKind::PostconditionHolds {
                            transition_name: transition.name.node.clone(),
                        },
                        passed: false,
                        counterexample: Some(Counterexample::new(
                            format!("solver returned unknown: {}", reason),
                            vec![],
                            Some(transition.span),
                        )),
                    });
                }
            }
        }

        reports
    }

    fn check_dead_transition(
        &self,
        state: &StateDef,
        transition: &Transition,
        constants: &HashMap<String, Dynamic<'ctx>>,
    ) -> CheckReport {
        let session = SolverSession::new(self.ctx);

        let mut vars = self.make_state_vars(&state.fields, "pre");
        vars.extend(constants.clone());
        let mut all_vars = vars.clone();

        for param in &transition.params {
            let resolved_ty = self.resolve_type_for_field(&param.ty.node);
            let var = self
                .encoder
                .encode_state_var(&param.name.node, &resolved_ty, "param");
            all_vars.insert(param.name.node.clone(), var);
        }

        for inv in &state.invariants {
            if let Some(encoded) = self.encoder.encode_expr(&inv.condition, &vars)
                && let Some(bool_expr) = encoded.as_bool()
            {
                session.assert(&bool_expr);
            }
        }

        self.assert_refinements_for_fields(&state.fields, &vars, &session);

        for pre in &transition.preconditions {
            if let Some(encoded) = self.encoder.encode_expr(pre, &all_vars)
                && let Some(bool_expr) = encoded.as_bool()
            {
                session.assert(&bool_expr);
            }
        }

        match session.check() {
            CheckResult::Verified => CheckReport {
                kind: CheckKind::DeadTransition {
                    transition_name: transition.name.node.clone(),
                },
                passed: false,
                counterexample: Some(Counterexample::new(
                    format!(
                        "transition '{}' precondition is unsatisfiable (dead transition)",
                        transition.name.node
                    ),
                    vec![],
                    Some(transition.span),
                )),
            },
            _ => CheckReport {
                kind: CheckKind::DeadTransition {
                    transition_name: transition.name.node.clone(),
                },
                passed: true,
                counterexample: None,
            },
        }
    }

    fn encode_transition_body(
        &self,
        state: &StateDef,
        transition: &Transition,
        pre_vars: &HashMap<String, Dynamic<'ctx>>,
        post_vars: &HashMap<String, Dynamic<'ctx>>,
        session: &SolverSession<'ctx>,
        all_vars: &HashMap<String, Dynamic<'ctx>>,
        constants: &HashMap<String, Dynamic<'ctx>>,
    ) {
        let mut modified_fields: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut ssa_counter: HashMap<String, usize> = HashMap::new();

        let mut current_values: HashMap<String, Dynamic<'ctx>> = HashMap::new();
        for field in &state.fields {
            let pre_key = format!("pre_{}", field.name.node);
            if let Some(v) = pre_vars
                .get(&pre_key)
                .or_else(|| pre_vars.get(&field.name.node))
            {
                current_values.insert(field.name.node.clone(), v.clone());
            }
        }
        for param in &transition.params {
            if let Some(v) = all_vars.get(&param.name.node) {
                current_values.insert(param.name.node.clone(), v.clone());
            }
        }
        for (name, value) in constants {
            current_values.insert(name.clone(), value.clone());
        }

        for stmt in &transition.body {
            self.encode_statement_ssa(
                stmt,
                &mut current_values,
                post_vars,
                session,
                &mut modified_fields,
                &mut ssa_counter,
                state,
            );
        }

        for field in &state.fields {
            let post_key = format!("post_{}", field.name.node);
            if let Some(post_var) = post_vars.get(&post_key) {
                if modified_fields.contains(&field.name.node) {
                    if let Some(current) = current_values.get(&field.name.node) {
                        self.assert_eq_dynamic(session, post_var, current);
                    }
                } else {
                    let pre_key = format!("pre_{}", field.name.node);
                    if let Some(pre) = pre_vars.get(&pre_key) {
                        self.assert_eq_dynamic(session, post_var, pre);
                    }
                }
            }
        }
    }

    fn assert_eq_dynamic(
        &self,
        session: &SolverSession<'ctx>,
        a: &Dynamic<'ctx>,
        b: &Dynamic<'ctx>,
    ) {
        if let (Some(av), Some(bv)) = (a.as_int(), b.as_int()) {
            session.assert(&av._eq(&bv));
        } else if let (Some(av), Some(bv)) = (a.as_bool(), b.as_bool()) {
            session.assert(&av._eq(&bv));
        } else if let (Some(av), Some(bv)) = (a.as_real(), b.as_real()) {
            session.assert(&av._eq(&bv));
        } else if let (Some(av), Some(bv)) = (a.as_array(), b.as_array()) {
            session.assert(&av._eq(&bv));
        }
    }

    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::only_used_in_recursion)]
    fn encode_statement_ssa(
        &self,
        stmt: &Spanned<Statement>,
        current_values: &mut HashMap<String, Dynamic<'ctx>>,
        post_vars: &HashMap<String, Dynamic<'ctx>>,
        session: &SolverSession<'ctx>,
        modified: &mut std::collections::HashSet<String>,
        ssa_counter: &mut HashMap<String, usize>,
        state: &StateDef,
    ) {
        match &stmt.node {
            Statement::Assign(assign) => {
                if let Some(val) = self.encoder.encode_expr(&assign.value, current_values) {
                    current_values.insert(assign.target.node.clone(), val);
                }
                modified.insert(assign.target.node.clone());
            }
            Statement::CompoundAssign { target, op, value } => {
                let current = current_values.get(&target.node).cloned();
                if let (Some(cur), Some(val)) =
                    (current, self.encoder.encode_expr(value, current_values))
                {
                    if let (Some(cv), Some(ev)) = (cur.as_int(), val.as_int()) {
                        let result = match op {
                            CompoundOp::Add => Dynamic::from_ast(&(&cv + &ev)),
                            CompoundOp::Sub => Dynamic::from_ast(&(&cv - &ev)),
                            CompoundOp::Mul => Dynamic::from_ast(&(&cv * &ev)),
                            CompoundOp::Div => Dynamic::from_ast(&(&cv / &ev)),
                        };
                        current_values.insert(target.node.clone(), result);
                    } else if let (Some(cv), Some(ev)) = (cur.as_real(), val.as_real()) {
                        let result = match op {
                            CompoundOp::Add => Dynamic::from_ast(&(&cv + &ev)),
                            CompoundOp::Sub => Dynamic::from_ast(&(&cv - &ev)),
                            CompoundOp::Mul => Dynamic::from_ast(&(&cv * &ev)),
                            CompoundOp::Div => Dynamic::from_ast(&(&cv / &ev)),
                        };
                        current_values.insert(target.node.clone(), result);
                    }
                }
                modified.insert(target.node.clone());
            }
            Statement::IndexedAssign {
                target,
                index,
                value,
            } => {
                let arr = current_values.get(&target.node).cloned();
                let idx = self.encoder.encode_expr(index, current_values);
                let val = self.encoder.encode_expr(value, current_values);
                if let (Some(a), Some(i), Some(v)) = (arr, idx, val)
                    && let Some(arr_z3) = a.as_array()
                {
                    let stored = Dynamic::from_ast(&arr_z3.store(&i, &v));
                    current_values.insert(target.node.clone(), stored);
                }
                modified.insert(target.node.clone());
            }
            Statement::IndexedCompoundAssign {
                target,
                index,
                op,
                value,
            } => {
                let arr = current_values.get(&target.node).cloned();
                let idx = self.encoder.encode_expr(index, current_values);
                let val = self.encoder.encode_expr(value, current_values);
                if let (Some(a), Some(i), Some(v)) = (arr, idx, val)
                    && let Some(arr_z3) = a.as_array()
                {
                    let current_elem = arr_z3.select(&i);
                    if let (Some(ce), Some(ev)) = (current_elem.as_int(), v.as_int()) {
                        let result = match op {
                            CompoundOp::Add => Dynamic::from_ast(&(&ce + &ev)),
                            CompoundOp::Sub => Dynamic::from_ast(&(&ce - &ev)),
                            CompoundOp::Mul => Dynamic::from_ast(&(&ce * &ev)),
                            CompoundOp::Div => Dynamic::from_ast(&(&ce / &ev)),
                        };
                        let stored = Dynamic::from_ast(&arr_z3.store(&i, &result));
                        current_values.insert(target.node.clone(), stored);
                    } else if let (Some(ce), Some(ev)) = (current_elem.as_real(), v.as_real()) {
                        let result = match op {
                            CompoundOp::Add => Dynamic::from_ast(&(&ce + &ev)),
                            CompoundOp::Sub => Dynamic::from_ast(&(&ce - &ev)),
                            CompoundOp::Mul => Dynamic::from_ast(&(&ce * &ev)),
                            CompoundOp::Div => Dynamic::from_ast(&(&ce / &ev)),
                        };
                        let stored = Dynamic::from_ast(&arr_z3.store(&i, &result));
                        current_values.insert(target.node.clone(), stored);
                    }
                }
                modified.insert(target.node.clone());
            }
            Statement::Assert { condition } => {
                if let Some(encoded) = self.encoder.encode_expr(condition, current_values)
                    && let Some(bool_expr) = encoded.as_bool()
                {
                    session.assert(&bool_expr);
                }
            }
            Statement::If {
                condition,
                then_body,
                else_body,
            } => {
                if let Some(cond_encoded) = self.encoder.encode_expr(condition, current_values)
                    && let Some(cond_bool) = cond_encoded.as_bool()
                {
                    let mut then_values = current_values.clone();
                    let mut then_modified = std::collections::HashSet::new();
                    for s in then_body {
                        self.encode_statement_ssa(
                            s,
                            &mut then_values,
                            post_vars,
                            session,
                            &mut then_modified,
                            ssa_counter,
                            state,
                        );
                    }

                    let mut else_values = current_values.clone();
                    let mut else_modified = std::collections::HashSet::new();
                    if let Some(else_stmts) = else_body {
                        for s in else_stmts {
                            self.encode_statement_ssa(
                                s,
                                &mut else_values,
                                post_vars,
                                session,
                                &mut else_modified,
                                ssa_counter,
                                state,
                            );
                        }
                    }

                    let all_branch_modified: std::collections::HashSet<String> =
                        then_modified.union(&else_modified).cloned().collect();

                    for field_name in &all_branch_modified {
                        let then_val = then_values.get(field_name);
                        let else_val = else_values.get(field_name);

                        if let (Some(tv), Some(ev)) = (then_val, else_val) {
                            if let (Some(ti), Some(ei)) = (tv.as_int(), ev.as_int()) {
                                let ite_result = Dynamic::from_ast(&cond_bool.ite(&ti, &ei));
                                current_values.insert(field_name.clone(), ite_result);
                            } else if let (Some(tb), Some(eb)) = (tv.as_bool(), ev.as_bool()) {
                                let ite_result = Dynamic::from_ast(&cond_bool.ite(&tb, &eb));
                                current_values.insert(field_name.clone(), ite_result);
                            } else if let (Some(tr), Some(er)) = (tv.as_real(), ev.as_real()) {
                                let ite_result = Dynamic::from_ast(&cond_bool.ite(&tr, &er));
                                current_values.insert(field_name.clone(), ite_result);
                            } else if let (Some(ta), Some(ea)) = (tv.as_array(), ev.as_array()) {
                                let ite_result = Dynamic::from_ast(&cond_bool.ite(&ta, &ea));
                                current_values.insert(field_name.clone(), ite_result);
                            }
                        }
                    }

                    modified.extend(all_branch_modified);
                }
            }
            Statement::Let { name, value, .. } => {
                if let Some(val) = self.encoder.encode_expr(value, current_values) {
                    current_values.insert(name.node.clone(), val);
                }
            }
            Statement::Match { expr, arms } => {
                let Some(subject) = self.encoder.encode_expr(expr, current_values) else {
                    return;
                };

                let mut arm_values: Vec<HashMap<String, Dynamic<'ctx>>> = Vec::new();
                let mut arm_modified: Vec<std::collections::HashSet<String>> = Vec::new();

                for arm in arms {
                    let mut values = current_values.clone();
                    let mut modified_in_arm = std::collections::HashSet::new();
                    for s in &arm.body {
                        self.encode_statement_ssa(
                            s,
                            &mut values,
                            post_vars,
                            session,
                            &mut modified_in_arm,
                            ssa_counter,
                            state,
                        );
                    }
                    arm_values.push(values);
                    arm_modified.push(modified_in_arm);
                }

                let mut all_modified = std::collections::HashSet::new();
                for m in &arm_modified {
                    all_modified.extend(m.iter().cloned());
                }

                for var in &all_modified {
                    let mut selected = current_values.get(var).cloned();

                    for idx in (0..arms.len()).rev() {
                        let cond =
                            self.encode_match_arm_condition(&subject, &arms[idx].pattern.node);
                        let arm_val = arm_values[idx]
                            .get(var)
                            .cloned()
                            .or_else(|| current_values.get(var).cloned());

                        if let (Some(c), Some(arm_v), Some(sel)) = (cond, arm_val, selected.clone())
                        {
                            if let (Some(ai), Some(si)) = (arm_v.as_int(), sel.as_int()) {
                                selected = Some(Dynamic::from_ast(&c.ite(&ai, &si)));
                            } else if let (Some(ab), Some(sb)) = (arm_v.as_bool(), sel.as_bool()) {
                                selected = Some(Dynamic::from_ast(&c.ite(&ab, &sb)));
                            } else if let (Some(ar), Some(sr)) = (arm_v.as_real(), sel.as_real()) {
                                selected = Some(Dynamic::from_ast(&c.ite(&ar, &sr)));
                            } else if let (Some(aa), Some(sa)) = (arm_v.as_array(), sel.as_array())
                            {
                                selected = Some(Dynamic::from_ast(&c.ite(&aa, &sa)));
                            }
                        }
                    }

                    if let Some(val) = selected {
                        current_values.insert(var.clone(), val);
                    }
                }

                modified.extend(all_modified);
            }
        }
    }

    fn encode_match_arm_condition(
        &self,
        subject: &Dynamic<'ctx>,
        pattern: &MatchPattern,
    ) -> Option<Bool<'ctx>> {
        match pattern {
            MatchPattern::Wildcard => Some(Bool::from_bool(self.ctx, true)),
            MatchPattern::IntLit(v) => {
                let pat_expr = Spanned::new(Expr::IntLit(*v), crate::ast::span::Span::dummy());
                let pat = self.encoder.encode_expr(&pat_expr, &HashMap::new())?;
                Some(subject._eq(&pat))
            }
            MatchPattern::BoolLit(v) => {
                let pat_expr = Spanned::new(Expr::BoolLit(*v), crate::ast::span::Span::dummy());
                let pat = self.encoder.encode_expr(&pat_expr, &HashMap::new())?;
                Some(subject._eq(&pat))
            }
            MatchPattern::StringLit(v) => {
                let pat_expr =
                    Spanned::new(Expr::StringLit(v.clone()), crate::ast::span::Span::dummy());
                let pat = self.encoder.encode_expr(&pat_expr, &HashMap::new())?;
                Some(subject._eq(&pat))
            }
            MatchPattern::EnumVariant { enum_name, variant } => {
                let pat_expr = Spanned::new(
                    Expr::EnumVariant {
                        enum_name: enum_name.clone(),
                        variant: variant.clone(),
                    },
                    crate::ast::span::Span::dummy(),
                );
                let pat = self.encoder.encode_expr(&pat_expr, &HashMap::new())?;
                Some(subject._eq(&pat))
            }
        }
    }
}
