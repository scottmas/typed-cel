use crate::common::ast;
use crate::common::ast::{
    operators, CallExpr, EntryExpr, Expr, IdedEntryExpr, IdedExpr, ListExpr, LiteralValue,
    MapEntryExpr, MapExpr, SelectExpr, SourceInfo,
};
use crate::parser::gen::{
    BoolFalseContext, BoolTrueContext, BytesContext, CELListener, CELParserContextType,
    CalcContext, CalcContextAttrs, ConditionalAndContext, ConditionalOrContext,
    ConstantLiteralContext, ConstantLiteralContextAttrs, CreateListContext, CreateMessageContext,
    CreateStructContext, DoubleContext, ExprContext, GlobalCallContext, IdentContext, IndexContext,
    IndexContextAttrs, IntContext, ListInitContextAll, LogicalNotContext, LogicalNotContextAttrs,
    MapInitializerListContextAll, MemberCallContext, MemberCallContextAttrs, MemberExprContext,
    MemberExprContextAttrs, NegateContext, NegateContextAttrs, NestedContext, NullContext,
    PrimaryExprContext, PrimaryExprContextAttrs, RelationContext, RelationContextAttrs,
    SelectContext, SelectContextAttrs, StartContext, StartContextAttrs, StringContext, UintContext,
};
use crate::parser::{gen, macros, parse};
use antlr4rust::common_token_stream::CommonTokenStream;
use antlr4rust::error_listener::ErrorListener;
use antlr4rust::errors::ANTLRError;
use antlr4rust::parser::ParserNodeType;
use antlr4rust::parser_rule_context::ParserRuleContext;
use antlr4rust::recognizer::Recognizer;
use antlr4rust::token::{CommonToken, Token};
use antlr4rust::token_factory::TokenFactory;
use antlr4rust::tree::{ParseTree, ParseTreeListener, ParseTreeVisitorCompat, VisitChildren};
use antlr4rust::{InputStream, Parser as AntlrParser};
use std::cell::RefCell;
use std::error::Error;
use std::fmt::Display;
use std::mem;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

pub struct MacroExprHelper<'a> {
    helper: &'a mut ParserHelper,
    id: u64,
}

impl MacroExprHelper<'_> {
    pub fn next_expr(&mut self, expr: Expr) -> IdedExpr {
        self.helper.next_expr_for(self.id, expr)
    }

    pub(crate) fn pos_for(&self, id: u64) -> Option<(isize, isize)> {
        self.helper.source_info.pos_for(id)
    }

    /// A fresh id whose span is `authored`'s — or the macro call's, for a node with none.
    pub(crate) fn id_for(&mut self, authored: u64) -> u64 {
        let from = if self.helper.source_info.offset_for(authored).is_some() {
            authored
        } else {
            self.id
        };
        self.helper.next_id_for(from)
    }

    /// `expr` with a fresh id whose span is `authored`'s.
    pub(crate) fn expr_for(&mut self, authored: u64, expr: Expr) -> IdedExpr {
        IdedExpr {
            id: self.id_for(authored),
            expr,
        }
    }

    /// A deep copy of `e` in which every node has a fresh id carrying the span of the node it was
    /// copied from. A rewrite that writes one subtree twice needs two: the checker's type table
    /// and the backend's lowering are keyed by id.
    pub(crate) fn copy(&mut self, e: &IdedExpr) -> IdedExpr {
        let expr = match &e.expr {
            Expr::Select(s) => Expr::Select(ast::SelectExpr {
                operand: Box::new(self.copy(&s.operand)),
                field: s.field.clone(),
                test: s.test,
            }),
            Expr::Call(c) => Expr::Call(CallExpr {
                func_name: c.func_name.clone(),
                target: c.target.as_ref().map(|t| Box::new(self.copy(t))),
                args: c.args.iter().map(|a| self.copy(a)).collect(),
            }),
            Expr::List(l) => Expr::List(ast::ListExpr {
                elements: l.elements.iter().map(|x| self.copy(x)).collect(),
            }),
            Expr::Map(m) => Expr::Map(ast::MapExpr {
                entries: m
                    .entries
                    .iter()
                    .map(|entry| {
                        let EntryExpr::MapEntry(me) = &entry.expr;
                        IdedEntryExpr {
                            id: self.id_for(entry.id),
                            expr: EntryExpr::MapEntry(MapEntryExpr {
                                key: self.copy(&me.key),
                                value: self.copy(&me.value),
                            }),
                        }
                    })
                    .collect(),
            }),
            Expr::Comprehension(c) => Expr::Comprehension(Box::new(ast::ComprehensionExpr {
                iter_range: self.copy(&c.iter_range),
                iter_var: c.iter_var.clone(),
                iter_var2: c.iter_var2.clone(),
                accu_var: c.accu_var.clone(),
                accu_init: self.copy(&c.accu_init),
                loop_cond: self.copy(&c.loop_cond),
                loop_step: self.copy(&c.loop_step),
                result: self.copy(&c.result),
            })),
            other => other.clone(),
        };
        self.expr_for(e.id, expr)
    }

    /// Record what a node an optional-read rewrite produced stands for.
    pub(crate) fn mark(&mut self, id: u64, what: ast::OptionalRewrite) {
        self.helper.source_info.optional_reads.insert(id, what);
    }
}

#[derive(Debug)]
pub struct ParseErrors {
    pub errors: Vec<ParseError>,
}

impl Display for ParseErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, e) in self.errors.iter().enumerate() {
            if i != 0 {
                writeln!(f)?;
            }
            write!(f, "{e}")?;
        }
        Ok(())
    }
}

impl Error for ParseErrors {}

#[allow(dead_code)]
#[derive(Debug)]
pub struct ParseError {
    pub source: Option<Box<dyn Error + Send + Sync + 'static>>,
    pub pos: (isize, isize),
    pub msg: String,
    pub expr_id: u64,
    pub source_info: Option<Arc<SourceInfo>>,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ERROR: <input>:{}:{}: {}",
            self.pos.0, self.pos.1, self.msg
        )?;
        if let Some(info) = &self.source_info {
            if let Some(line) = info.snippet(self.pos.0 - 1) {
                write!(f, "\n| {line}")?;
                write!(f, "\n| {:.>width$}", "^", width = self.pos.1 as usize)?;
            }
        }
        Ok(())
    }
}

impl Error for ParseError {}

/// The hex digits of an int literal, sign included, or `None` if it is not hex.
///
/// The SIGN is part of the token — the grammar is `Int : sign=MINUS? tok=NUM_INT` — so it has to
/// come off before the prefix test: `"-0x55".strip_prefix("0x")` misses, and the decimal fallback
/// `"-0x55".parse::<i64>()` cannot read a radix, which is why the negative spelling failed at parse
/// while the decimal one worked.
///
/// The sign goes back ON for `from_str_radix` rather than being applied afterwards. Parsing the
/// magnitude and negating overflows on exactly `-0x8000000000000000`, whose magnitude is not
/// representable as a positive `i64` — the same boundary `Negator for Int` guards from the other
/// side.
///
/// Lowercase `0x` only, deliberately: Google's `CEL.g4` spells the token
/// `NUM_INT : DIGIT+ | '0x' HEXDIGIT+`, so `0XFF` never reaches this visitor at all and accepting
/// it here would invent a literal spelling the reference implementation rejects.
fn hex_digits(text: &str) -> Option<String> {
    match text.strip_prefix('-') {
        Some(rest) => rest.strip_prefix("0x").map(|hex| format!("-{hex}")),
        None => text.strip_prefix("0x").map(str::to_string),
    }
}

/// `removed: optional values`, as the parser says it: an optional list element `[?x]` and an
/// optional map entry `{?k: v}` build optional VALUES, which this dialect does not have. (An
/// optional READ, `.?f` and `[?k]`, parses; the checker refuses one no macro consumes.)
const OPTIONAL_SYNTAX_REMOVED: &str =
    "optional values are not in the typed-CEL dialect (removed: optional values): an optional READ \
     ends in `.orValue(<default>)` or `.hasValue()` — `x.?f.orValue(0)`, `m[?'k'].hasValue()`";

pub struct Parser {
    ast: ast::Ast,
    helper: ParserHelper,
    errors: Vec<ParseError>,
    max_recursion_depth: u16,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            ast: ast::Ast {
                expr: IdedExpr::default(),
            },
            helper: ParserHelper::default(),
            errors: Vec::default(),
            max_recursion_depth: 96,
        }
    }

    pub fn max_recursion_depth(mut self, max: u16) -> Self {
        self.max_recursion_depth = if max == u16::MAX { max } else { max + 1 };
        self
    }

    fn new_logic_manager(&self, func: &str, term: IdedExpr) -> LogicManager {
        LogicManager {
            function: func.to_string(),
            terms: vec![term],
            ops: vec![],
        }
    }

    fn global_call_or_macro(
        &mut self,
        id: u64,
        func_name: String,
        args: Vec<IdedExpr>,
    ) -> IdedExpr {
        match macros::find_expander(&func_name, None, &args) {
            None => IdedExpr {
                id,
                expr: Expr::Call(CallExpr {
                    target: None,
                    func_name,
                    args,
                }),
            },
            Some(expander) => {
                let mut helper = MacroExprHelper {
                    helper: &mut self.helper,
                    id,
                };
                match expander(&mut helper, None, args) {
                    Ok(expr) => expr,
                    Err(err) => self.report_parse_error(None, err),
                }
            }
        }
    }

    fn receiver_call_or_macro(
        &mut self,
        id: u64,
        func_name: String,
        target: IdedExpr,
        args: Vec<IdedExpr>,
    ) -> IdedExpr {
        match macros::find_expander(&func_name, Some(&target), &args) {
            None => IdedExpr {
                id,
                expr: Expr::Call(CallExpr {
                    target: Some(Box::new(target)),
                    func_name,
                    args,
                }),
            },
            Some(expander) => {
                let mut helper = MacroExprHelper {
                    helper: &mut self.helper,
                    id,
                };
                match expander(&mut helper, Some(target), args) {
                    Ok(expr) => expr,
                    Err(err) => self.report_parse_error(None, err),
                }
            }
        }
    }

    /// Parse, discarding the source map. Delegates to [`Self::parse_with_source_info`].
    pub fn parse(self, source: &str) -> Result<IdedExpr, ParseErrors> {
        self.parse_with_source_info(source).map(|(expr, _)| expr)
    }

    /// Parse, KEEPING the source map.
    ///
    /// `parse` drops the [`SourceInfo`] on the success path and attaches it only to errors, which
    /// is fine when parsing is the only phase that can fail. The checker runs afterwards, and
    /// an `IdedExpr` carries expression ids and no offsets — so without this a type error has
    /// nothing to point at but a number. Every diagnostic that names a column comes through here.
    pub fn parse_with_source_info(
        mut self,
        source: &str,
    ) -> Result<(IdedExpr, Arc<SourceInfo>), ParseErrors> {
        let parse_errors = Rc::new(RefCell::new(Vec::<ParseError>::new()));
        let stream = InputStream::new(source);
        let mut lexer = gen::CELLexer::new(stream);
        lexer.remove_error_listeners();
        lexer.add_error_listener(Box::new(ParserErrorListener {
            parse_errors: parse_errors.clone(),
        }));

        // todo! might want to avoid this cloning here...
        self.helper.source_info.source = source.into();

        let mut prsr = gen::CELParser::new(CommonTokenStream::new(lexer));
        prsr.remove_error_listeners();
        prsr.add_error_listener(Box::new(ParserErrorListener {
            parse_errors: parse_errors.clone(),
        }));
        prsr.add_parse_listener(Box::new(RecursionListener {
            max: self.max_recursion_depth,
            depth: 0,
        }));
        let r = match prsr.start() {
            Ok(t) => Ok(self.visit(t.deref())),
            Err(e) => Err(ParseError {
                source: Some(Box::new(e)),
                pos: (0, 0),
                msg: "UNKNOWN".to_string(),
                expr_id: 0,
                source_info: None,
            }),
        };

        let info = self.helper.source_info;
        let source_info = Arc::new(info);

        let mut errors = parse_errors.take();
        errors.extend(self.errors);
        errors.sort_by_key(|a| a.pos);

        if errors.is_empty() {
            r.map(|expr| (expr, source_info.clone()))
                .map_err(|e| ParseErrors { errors: vec![e] })
        } else {
            Err(ParseErrors {
                errors: errors
                    .into_iter()
                    .map(|mut e: ParseError| {
                        e.source_info = Some(source_info.clone());
                        e
                    })
                    .collect(),
            })
        }
    }

    fn map_initializer_list(&mut self, ctx: &MapInitializerListContextAll) -> Vec<IdedEntryExpr> {
        if ctx.keys.is_empty() {
            return vec![];
        }
        let mut entries = Vec::with_capacity(ctx.cols.len());
        let keys = &ctx.keys;
        let vals = &ctx.values;
        for (i, col) in ctx.cols.iter().enumerate() {
            if i >= keys.len() || i >= vals.len() {
                return vec![];
            }
            let id = self.helper.next_id(col);
            let key = self.visit(keys[i].as_ref());
            if let Some(opt) = keys[i].opt.as_ref() {
                self.report_error::<ParseError, _>(opt.as_ref(), None, OPTIONAL_SYNTAX_REMOVED);
                continue;
            }
            let value = self.visit(vals[i].as_ref());
            entries.push(IdedEntryExpr {
                id,
                expr: EntryExpr::MapEntry(MapEntryExpr { key, value }),
            })
        }
        entries
    }

    fn list_initializer_list(&mut self, ctx: &ListInitContextAll) -> Vec<IdedExpr> {
        let mut list = Vec::default();
        for e in ctx.elems.iter() {
            match &e.e {
                None => return Vec::default(),
                Some(exp) => {
                    if let Some(opt) = &e.opt {
                        self.report_error::<ParseError, _>(
                            opt.as_ref(),
                            None,
                            OPTIONAL_SYNTAX_REMOVED,
                        );
                        continue;
                    }
                    list.push(self.visit(exp.as_ref()));
                }
            }
        }
        list
    }

    fn report_error<E: Error + Send + Sync + 'static, S: Into<String>>(
        &mut self,
        token: &CommonToken,
        e: Option<E>,
        s: S,
    ) -> IdedExpr {
        let error = ParseError {
            source: e.map(|e| e.into()),
            pos: (token.line, token.column + 1),
            msg: s.into(),
            expr_id: 0,
            source_info: None,
        };
        self.report_parse_error(Some(token), error)
    }

    fn report_parse_error(&mut self, token: Option<&CommonToken>, mut e: ParseError) -> IdedExpr {
        let expr = if let Some(token) = token {
            self.helper.next_expr(token, Expr::default())
        } else {
            IdedExpr {
                id: 0,
                expr: Expr::default(),
            }
        };
        e.expr_id = expr.id;
        self.errors.push(e);
        expr
    }
}

struct RecursionListener {
    max: u16,
    depth: u16,
}

impl<'a> CELListener<'a> for RecursionListener {
    fn enter_expr(&mut self, _ctx: &ExprContext<'a>) {
        self.depth = self.depth.saturating_add(1);
    }

    fn exit_expr(&mut self, _ctx: &ExprContext<'a>) {
        self.depth = self.depth.saturating_sub(1);
    }
}

impl<'a> ParseTreeListener<'a, CELParserContextType> for RecursionListener {
    fn enter_every_rule(
        &mut self,
        ctx: &<CELParserContextType as ParserNodeType>::Type,
    ) -> Result<(), ANTLRError> {
        if self.depth > self.max || self.depth == u16::MAX {
            let pos = (ctx.start().get_start(), ctx.stop().get_stop());
            return Err(ANTLRError::OtherError(Arc::new(ParseError {
                source: None,
                pos,
                msg: format!("Recursion limit of {} exceeded", self.max),
                expr_id: 0,
                source_info: None,
            })));
        }
        Ok(())
    }

    fn exit_every_rule(
        &mut self,
        _ctx: &<CELParserContextType as ParserNodeType>::Type,
    ) -> Result<(), ANTLRError> {
        Ok(())
    }
}

struct ParserErrorListener {
    parse_errors: Rc<RefCell<Vec<ParseError>>>,
}

impl<'a, T: Recognizer<'a>> ErrorListener<'a, T> for ParserErrorListener {
    fn syntax_error(
        &self,
        _recognizer: &T,
        _offending_symbol: Option<&<T::TF as TokenFactory<'a>>::Inner>,
        line: isize,
        column: isize,
        msg: &str,
        _error: Option<&ANTLRError>,
    ) {
        self.parse_errors.borrow_mut().push(ParseError {
            source: None,
            pos: (line, column + 1),
            msg: format!("Syntax error: {msg}"),
            expr_id: 0,
            source_info: None,
        })
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}

impl ParseTreeVisitorCompat<'_> for Parser {
    type Node = gen::CELParserContextType;
    type Return = IdedExpr;
    fn temp_result(&mut self) -> &mut Self::Return {
        &mut self.ast.expr
    }

    fn visit(&mut self, node: &<Self::Node as ParserNodeType<'_>>::Type) -> Self::Return {
        //println!("{node:?}");
        self.visit_node(node);
        mem::take(self.temp_result())
    }

    fn aggregate_results(&self, _aggregate: Self::Return, next: Self::Return) -> Self::Return {
        next
    }
}

impl gen::CELVisitorCompat<'_> for Parser {
    fn visit_start(&mut self, ctx: &StartContext<'_>) -> Self::Return {
        match &ctx.expr() {
            None => self.report_error::<ParseError, _>(
                ctx.start().deref(),
                None,
                "No `ExprContextAll`!",
            ),
            Some(expr) => self.visit(expr.as_ref()),
        }
    }

    fn visit_expr(&mut self, ctx: &ExprContext<'_>) -> Self::Return {
        match &ctx.op {
            None => match &ctx.e {
                None => self.report_error::<ParseError, _>(
                    ctx.start().deref(),
                    None,
                    "No `ConditionalOrContextAll`!",
                ),
                Some(e) => <Self as ParseTreeVisitorCompat>::visit(self, e.as_ref()),
            },
            Some(op) => {
                if let (Some(e), Some(e1), Some(e2)) = (&ctx.e, &ctx.e1, &ctx.e2) {
                    let result = self.visit(e.as_ref());
                    let op_id = self.helper.next_id(op);
                    let if_true = self.visit(e1.as_ref());
                    let if_false = self.visit(e2.as_ref());
                    self.global_call_or_macro(
                        op_id,
                        operators::CONDITIONAL.to_string(),
                        vec![result, if_true, if_false],
                    )
                } else {
                    self.report_error::<ParseError, _>(
                        ctx.start().deref(),
                        None,
                        format!(
                            "Incomplete `ExprContext` for `{}` expression!",
                            operators::CONDITIONAL
                        ),
                    )
                }
            }
        }
    }

    fn visit_conditionalOr(&mut self, ctx: &ConditionalOrContext<'_>) -> Self::Return {
        let result = match &ctx.e {
            None => {
                self.report_error::<ParseError, _>(
                    ctx.start().deref(),
                    None,
                    "No `ConditionalAndContextAll`!",
                );
                IdedExpr::default()
            }
            Some(e) => <Self as ParseTreeVisitorCompat>::visit(self, e.as_ref()),
        };
        if ctx.ops.is_empty() {
            result
        } else {
            let mut l = self.new_logic_manager(operators::LOGICAL_OR, result);
            let rest = &ctx.e1;
            if ctx.ops.len() > rest.len() {
                // why is >= not ok?
                self.report_error::<ParseError, _>(
                    &ctx.start(),
                    None,
                    "unexpected character, wanted '||'",
                );
                return IdedExpr::default();
            }
            for (i, op) in ctx.ops.iter().enumerate() {
                let next = self.visit(rest[i].deref());
                let op_id = self.helper.next_id(op);
                l.add_term(op_id, next)
            }
            l.expr()
        }
    }

    fn visit_conditionalAnd(&mut self, ctx: &ConditionalAndContext<'_>) -> Self::Return {
        let result = match &ctx.e {
            None => self.report_error::<ParseError, _>(
                ctx.start().deref(),
                None,
                "No `RelationContextAll`!",
            ),
            Some(e) => <Self as ParseTreeVisitorCompat>::visit(self, e.as_ref()),
        };
        if ctx.ops.is_empty() {
            result
        } else {
            let mut l = self.new_logic_manager(operators::LOGICAL_AND, result);
            let rest = &ctx.e1;
            if ctx.ops.len() > rest.len() {
                // why is >= not ok?
                self.report_error::<ParseError, _>(
                    &ctx.start(),
                    None,
                    "unexpected character, wanted '&&'",
                );
                return IdedExpr::default();
            }
            for (i, op) in ctx.ops.iter().enumerate() {
                let next = self.visit(rest[i].deref());
                let op_id = self.helper.next_id(op);
                l.add_term(op_id, next)
            }
            l.expr()
        }
    }

    fn visit_relation(&mut self, ctx: &RelationContext<'_>) -> Self::Return {
        if ctx.op.is_none() {
            match ctx.calc() {
                None => self.report_error::<ParseError, _>(
                    ctx.start().deref(),
                    None,
                    "No `CalcContextAll`!",
                ),
                Some(calc) => <Self as ParseTreeVisitorCompat>::visit(self, calc.as_ref()),
            }
        } else {
            match &ctx.op {
                None => <Self as ParseTreeVisitorCompat>::visit_children(self, ctx),
                Some(op) => {
                    if let (Some(lhs), Some(rhs)) = (ctx.relation(0), ctx.relation(1)) {
                        let lhs = self.visit(lhs.as_ref());
                        let op_id = self.helper.next_id(op.as_ref());
                        let rhs = self.visit(rhs.as_ref());
                        match operators::find_operator(op.get_text()) {
                            None => {
                                self.report_error::<ParseError, _>(
                                    op.as_ref(),
                                    None,
                                    format!("Unknown `{}` operator!", op.get_text()),
                                );
                                IdedExpr::default()
                            }
                            Some(op) => {
                                self.global_call_or_macro(op_id, op.to_string(), vec![lhs, rhs])
                            }
                        }
                    } else {
                        self.report_error::<ParseError, _>(
                            ctx.start().deref(),
                            None,
                            format!("Incomplete `RelationContext` for `{:?}`!", ctx.op),
                        )
                    }
                }
            }
        }
    }

    fn visit_calc(&mut self, ctx: &CalcContext<'_>) -> Self::Return {
        match &ctx.op {
            None => match &ctx.unary() {
                None => self.report_error::<ParseError, _>(
                    ctx.start().deref(),
                    None,
                    "No `UnaryContextAll`!",
                ),
                Some(unary) => self.visit(unary.as_ref()),
            },
            Some(op) => {
                if let (Some(lhs), Some(rhs)) = (ctx.calc(0), ctx.calc(1)) {
                    let lhs = self.visit(lhs.as_ref());
                    let op_id = self.helper.next_id(op);
                    let rhs = self.visit(rhs.as_ref());
                    match operators::find_operator(op.get_text()) {
                        None => self.report_error::<ParseError, _>(
                            op,
                            None,
                            format!("Unknown `{}` operator!", op.get_text()),
                        ),
                        Some(op) => {
                            self.global_call_or_macro(op_id, op.to_string(), vec![lhs, rhs])
                        }
                    }
                } else {
                    self.report_error::<ParseError, _>(
                        ctx.start().deref(),
                        None,
                        "Incomplete `CalcContext`!",
                    )
                }
            }
        }
    }

    fn visit_MemberExpr(&mut self, ctx: &MemberExprContext<'_>) -> Self::Return {
        match &ctx.member() {
            None => {
                self.report_error::<ParseError, _>(&ctx.start(), None, "No `MemberContextAll`!")
            }
            Some(ctx) => <Self as ParseTreeVisitorCompat>::visit(self, ctx.as_ref()),
        }
    }

    fn visit_LogicalNot(&mut self, ctx: &LogicalNotContext<'_>) -> Self::Return {
        match &ctx.member() {
            None => {
                self.report_error::<ParseError, _>(&ctx.start(), None, "No `MemberContextAll`!");
                IdedExpr::default()
            }
            Some(member) => {
                // ONE call per operator. A run used to collapse to a single application, which is
                // right for an odd count by luck and wrong for every even one: `!!true` answered
                // `false`, and the corpus's 32 of them answered `false` where the language says
                // `true`.
                //
                // Ids are allocated for the OPERATORS first, left to right, and the operand last —
                // the order cel-go produces and the order `tests::test` pins (`!a` is
                // `!_(a^#2)^#1`). Visiting the operand first reads more naturally and renumbers
                // every expression in the tree.
                let op_ids: Vec<u64> = ctx.ops.iter().map(|op| self.helper.next_id(op)).collect();
                let mut target = self.visit(member.as_ref());
                for op_id in op_ids.into_iter().rev() {
                    target = self.global_call_or_macro(
                        op_id,
                        operators::LOGICAL_NOT.to_string(),
                        vec![target],
                    );
                }
                target
            }
        }
    }

    fn visit_Negate(&mut self, ctx: &NegateContext<'_>) -> Self::Return {
        match &ctx.member() {
            None => {
                self.report_error::<ParseError, _>(&ctx.start(), None, "No `MemberContextAll`!")
            }
            Some(member) => {
                // ONE call per operator — see `visit_LogicalNot` for why a run must not collapse.
                //
                // Ids are allocated for the OPERATORS first, left to right, and the operand last —
                // the order cel-go produces and the order `tests::test` pins (`!a` is
                // `!_(a^#2)^#1`). Visiting the operand first reads more naturally and renumbers
                // every expression in the tree.
                let op_ids: Vec<u64> = ctx.ops.iter().map(|op| self.helper.next_id(op)).collect();
                let mut target = self.visit(member.as_ref());
                for op_id in op_ids.into_iter().rev() {
                    target = self.global_call_or_macro(
                        op_id,
                        operators::NEGATE.to_string(),
                        vec![target],
                    );
                }
                target
            }
        }
    }

    fn visit_MemberCall(&mut self, ctx: &MemberCallContext<'_>) -> Self::Return {
        if let (Some(operand), Some(id), Some(open)) = (&ctx.member(), &ctx.id, &ctx.open) {
            let operand = self.visit(operand.as_ref());
            let id = id.get_text();
            let op_id = self.helper.next_id(open.as_ref());
            let args = ctx
                .args
                .iter()
                .flat_map(|arg| &arg.e)
                .map(|arg| self.visit(arg.deref()))
                .collect::<Vec<IdedExpr>>();
            self.receiver_call_or_macro(op_id, id.to_string(), operand, args)
        } else {
            self.report_error::<ParseError, _>(
                &ctx.start(),
                None,
                "Incomplete `MemberCallContext`!",
            )
        }
    }

    fn visit_Select(&mut self, ctx: &SelectContext<'_>) -> Self::Return {
        if let (Some(member), Some(id), Some(op)) = (&ctx.member(), &ctx.id, &ctx.op) {
            let operand = self.visit(member.as_ref());
            let field = id.get_text();
            if ctx.opt.is_some() {
                // `x.?f` is spec CEL's optional select, `_?._(x, "f")`. Kept as that call so the
                // `orValue`/`hasValue`/`has` macros can rewrite it into guards
                // (`added: optional reads`); one no macro consumes is refused by the checker
                // (`DELETED_FUNCTIONS`, `_?._`).
                let field_id = self.helper.next_id(&id.start());
                let field = IdedExpr {
                    id: field_id,
                    expr: Expr::Literal(LiteralValue::String(field.into())),
                };
                return self.helper.next_expr(
                    op.as_ref(),
                    Expr::Call(CallExpr {
                        target: None,
                        func_name: operators::OPT_SELECT.to_string(),
                        args: vec![operand, field],
                    }),
                );
            }
            self.helper.next_expr(
                op.as_ref(),
                Expr::Select(SelectExpr {
                    operand: Box::new(operand),
                    field,
                    test: false,
                }),
            )
        } else {
            self.report_error::<ParseError, _>(&ctx.start(), None, "Incomplete `SelectContext`!")
        }
    }

    fn visit_PrimaryExpr(&mut self, ctx: &PrimaryExprContext<'_>) -> Self::Return {
        match &ctx.primary() {
            None => {
                self.report_error::<ParseError, _>(&ctx.start(), None, "No `PrimaryContextAll`!")
            }
            Some(primary) => <Self as ParseTreeVisitorCompat>::visit(self, primary.as_ref()),
        }
    }

    fn visit_Index(&mut self, ctx: &IndexContext<'_>) -> Self::Return {
        if let (Some(member), Some(index)) = (&ctx.member(), &ctx.index) {
            let target = self.visit(member.as_ref());
            match &ctx.op {
                None => self.report_error::<ParseError, _>(&ctx.start(), None, "No `Index`!"),
                Some(op) => {
                    let op_id = self.helper.next_id(op);
                    let index = self.visit(index.as_ref());
                    // `m[?k]` is spec CEL's optional index, `_[?_](m, k)`; see `visit_Select`.
                    let func = if ctx.opt.is_some() {
                        operators::OPT_INDEX
                    } else {
                        operators::INDEX
                    };
                    self.global_call_or_macro(op_id, func.to_string(), vec![target, index])
                }
            }
        } else {
            self.report_error::<ParseError, _>(&ctx.start(), None, "Incomplete `IndexContext`!")
        }
    }

    fn visit_Ident(&mut self, ctx: &IdentContext<'_>) -> Self::Return {
        match &ctx.id {
            None => {
                self.report_error::<ParseError, _>(&ctx.start(), None, "No `Identifier`!");
                IdedExpr::default()
            }
            Some(id) => {
                let ident = id.clone().text;
                self.helper
                    .next_expr(id.deref(), Expr::Ident(ident.to_string()))
            }
        }
    }

    fn visit_GlobalCall(&mut self, ctx: &GlobalCallContext<'_>) -> Self::Return {
        match &ctx.id {
            None => IdedExpr::default(),
            Some(id) => {
                let mut id = id.get_text().to_string();
                if ctx.leadingDot.is_some() {
                    id = format!(".{id}");
                }
                let op_id = self.helper.next_id_for_token(ctx.op.as_deref());
                let args = ctx
                    .args
                    .iter()
                    .flat_map(|arg| &arg.e)
                    .map(|arg| self.visit(arg.deref()))
                    .collect::<Vec<IdedExpr>>();
                self.global_call_or_macro(op_id, id, args)
            }
        }
    }

    fn visit_Nested(&mut self, ctx: &NestedContext<'_>) -> Self::Return {
        match &ctx.e {
            None => {
                self.report_error::<ParseError, _>(
                    ctx.start().deref(),
                    None,
                    "No `ExprContextAll`!",
                );
                IdedExpr::default()
            }
            Some(e) => self.visit(e.as_ref()),
        }
    }

    fn visit_CreateList(&mut self, ctx: &CreateListContext<'_>) -> Self::Return {
        let list_id = self.helper.next_id_for_token(ctx.op.as_deref());
        let elements = match &ctx.elems {
            None => Vec::default(),
            Some(elements) => self.list_initializer_list(elements.deref()),
        };
        IdedExpr {
            id: list_id,
            expr: Expr::List(ListExpr::new(elements)),
        }
    }

    fn visit_CreateStruct(&mut self, ctx: &CreateStructContext<'_>) -> Self::Return {
        let struct_id = self.helper.next_id_for_token(ctx.op.as_deref());
        let entries = match &ctx.entries {
            Some(entries) => self.map_initializer_list(entries.deref()),
            None => Vec::default(),
        };
        IdedExpr {
            id: struct_id,
            expr: Expr::Map(MapExpr { entries }),
        }
    }

    /// `removed: protobuf` — message construction, refused at PARSE.
    ///
    /// The grammar still HAS the production, because `src/parser/gen/` is generated from Google's
    /// `CEL.g4` and is not ours to edit; what is ours is what the visitor does with it. Refusing
    /// here rather than in the AST is what keeps the error a recoverable diagnostic with a source
    /// position instead of a panic, and it is why `Expr::Struct` can be gone entirely.
    fn visit_CreateMessage(&mut self, ctx: &CreateMessageContext<'_>) -> Self::Return {
        let mut message_name = String::new();
        for id in &ctx.ids {
            if !message_name.is_empty() {
                message_name.push('.');
            }
            message_name.push_str(id.get_text());
        }
        if ctx.leadingDot.is_some() {
            message_name = format!(".{message_name}");
        }
        self.report_error::<ParseError, _>(
            &ctx.start(),
            None,
            format!(
                "message construction `{message_name}{{...}}` is not in the typed-CEL dialect \
                 (removed: protobuf)"
            ),
        )
    }

    fn visit_ConstantLiteral(&mut self, ctx: &ConstantLiteralContext<'_>) -> Self::Return {
        if let Some(literal) = ctx.literal().as_deref() {
            <Self as ParseTreeVisitorCompat>::visit(self, literal)
        } else {
            self.report_error::<ParseError, _>(&ctx.start(), None, "Incomplete ConstantLiteral!")
        }
    }

    fn visit_Int(&mut self, ctx: &IntContext<'_>) -> Self::Return {
        let string = ctx.get_text();
        if let Some(token) = ctx.tok.as_ref() {
            // An `i64`, else — unsigned, and past `i64::MAX` — a `u64`: one number type, held
            // exactly either way. Past `u64::MAX` is refused rather than rounded.
            let (digits, radix) = match hex_digits(&string) {
                Some(hex) => (hex, 16),
                None => (string.clone(), 10),
            };
            let lit = match i64::from_str_radix(&digits, radix) {
                Ok(v) => LiteralValue::Int(v),
                Err(e) => match u64::from_str_radix(&digits, radix) {
                    Ok(v) if !digits.starts_with('-') => LiteralValue::UInt(v),
                    _ => return self.report_error(token, Some(e), "invalid int literal"),
                },
            };
            self.helper.next_expr(token, Expr::Literal(lit))
        } else {
            self.report_error::<ParseError, _>(&ctx.start(), None, "Incomplete Int!")
        }
    }

    /// `removed: uint` — a `u`-suffixed literal, refused at PARSE.
    ///
    /// The grammar still lexes `1u` because `src/parser/gen/` is Google's `CEL.g4`; what the
    /// visitor does with it is ours. Refusing here rather than widening to `Int` is deliberate: a
    /// policy that spells `1u` was written against a language with two integer types, and silently
    /// reinterpreting it would make the removal invisible to whoever wrote it.
    fn visit_Uint(&mut self, ctx: &UintContext<'_>) -> Self::Return {
        self.report_error::<ParseError, _>(
            &ctx.start(),
            None,
            format!(
                "`{}` is a uint literal, which is not in the typed-CEL dialect (removed: uint) \
                 — write it without the `u` suffix",
                ctx.get_text()
            ),
        )
    }

    fn visit_Double(&mut self, ctx: &DoubleContext<'_>) -> Self::Return {
        let string = ctx.get_text();
        if let Some(token) = ctx.tok.as_ref() {
            match string.parse::<f64>() {
                Ok(d) if d.is_finite() => self
                    .helper
                    .next_expr(token, Expr::Literal(LiteralValue::Double(d.into()))),
                Err(e) => self.report_error(token, Some(e), "invalid double literal"),
                _ => self.report_error(token, None::<ParseError>, "invalid double literal"),
            }
        } else {
            self.report_error::<ParseError, _>(
                &ctx.start(),
                None::<ParseError>,
                "Incomplete double!",
            )
        }
    }

    fn visit_String(&mut self, ctx: &StringContext<'_>) -> Self::Return {
        if let Some(token) = ctx.tok.as_deref() {
            match parse::parse_string(&ctx.get_text()) {
                Ok(string) => self
                    .helper
                    .next_expr(token, Expr::Literal(LiteralValue::String(string.into()))),
                Err(e) => self.report_error::<ParseError, _>(
                    token,
                    None,
                    format!("invalid string literal: {e:?}"),
                ),
            }
        } else {
            self.report_error::<ParseError, _>(
                &ctx.start(),
                None::<ParseError>,
                "Incomplete string!",
            )
        }
    }

    fn visit_Bytes(&mut self, ctx: &BytesContext<'_>) -> Self::Return {
        if let Some(token) = ctx.tok.as_deref() {
            // The WHOLE token, prefixes and delimiters included. Cutting `[2..len-1]` here
            // assumed one prefix character and one quote, so a triple-quoted literal kept two of
            // its own delimiters in the value and `bR'…'` lost a byte off each end.
            match parse::parse_bytes(&ctx.get_text()) {
                Ok(bytes) => self
                    .helper
                    .next_expr(token, Expr::Literal(LiteralValue::Bytes(bytes.into()))),
                Err(e) => {
                    self.report_error::<ParseError, _>(
                        token,
                        None,
                        format!("invalid bytes literal: {e:?}"),
                    );
                    IdedExpr::default()
                }
            }
        } else {
            self.report_error::<ParseError, _>(
                &ctx.start(),
                None::<ParseError>,
                "Incomplete bytes!",
            )
        }
    }

    fn visit_BoolTrue(&mut self, ctx: &BoolTrueContext<'_>) -> Self::Return {
        match ctx.tok.as_deref() {
            Some(tok) => self
                .helper
                .next_expr(tok, Expr::Literal(LiteralValue::Boolean(true.into()))),
            None => self.report_error::<ParseError, _>(&ctx.start(), None, "Incomplete bool!"),
        }
    }

    fn visit_BoolFalse(&mut self, ctx: &BoolFalseContext<'_>) -> Self::Return {
        match ctx.tok.as_deref() {
            Some(token) => self
                .helper
                .next_expr(token, Expr::Literal(LiteralValue::Boolean(false.into()))),
            None => self.report_error::<ParseError, _>(&ctx.start(), None, "Incomplete bool!"),
        }
    }

    fn visit_Null(&mut self, ctx: &NullContext<'_>) -> Self::Return {
        match ctx.tok.as_deref() {
            Some(token) => self
                .helper
                .next_expr(token, Expr::Literal(LiteralValue::Null)),
            None => self.report_error::<ParseError, _>(&ctx.start(), None, "Incomplete null!"),
        }
    }
}

pub struct ParserHelper {
    source_info: SourceInfo,
    next_id: u64,
}

impl Default for ParserHelper {
    fn default() -> Self {
        Self {
            source_info: SourceInfo::default(),
            next_id: 1,
        }
    }
}

impl ParserHelper {
    fn next_id(&mut self, token: &CommonToken) -> u64 {
        let id = self.next_id;
        self.source_info
            .add_offset(id, token.start as u32, token.stop as u32);
        self.next_id += 1;
        id
    }

    fn next_id_for_token(&mut self, token: Option<&CommonToken>) -> u64 {
        match token {
            None => 0,
            Some(token) => self.next_id(token),
        }
    }

    fn next_id_for(&mut self, id: u64) -> u64 {
        let (start, stop) = self.source_info.offset_for(id).expect("invalid offset");
        let id = self.next_id;
        self.source_info.add_offset(id, start, stop);
        self.next_id += 1;
        id
    }

    pub fn next_expr(&mut self, token: &CommonToken, expr: Expr) -> IdedExpr {
        IdedExpr {
            id: self.next_id(token),
            expr,
        }
    }

    pub fn next_expr_for(&mut self, id: u64, expr: Expr) -> IdedExpr {
        IdedExpr {
            id: self.next_id_for(id),
            expr,
        }
    }
}

struct LogicManager {
    function: String,
    terms: Vec<IdedExpr>,
    ops: Vec<u64>,
}

impl LogicManager {
    pub(crate) fn expr(mut self) -> IdedExpr {
        if self.terms.len() == 1 {
            self.terms.pop().expect("expected at least one term")
        } else {
            self.balanced_tree(0, self.ops.len() - 1)
        }
    }

    pub(crate) fn add_term(&mut self, op_id: u64, expr: IdedExpr) {
        self.terms.push(expr);
        self.ops.push(op_id);
    }

    fn balanced_tree(&mut self, lo: usize, hi: usize) -> IdedExpr {
        let mid = (lo + hi).div_ceil(2);

        let left = if mid == lo {
            mem::take(&mut self.terms[mid])
        } else {
            self.balanced_tree(lo, mid - 1)
        };

        let right = if mid == hi {
            mem::take(&mut self.terms[mid + 1])
        } else {
            self.balanced_tree(mid + 1, hi)
        };

        IdedExpr {
            id: self.ops[mid],
            expr: Expr::Call(CallExpr {
                target: None,
                func_name: self.function.clone(),
                args: vec![left, right],
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::ast::{ComprehensionExpr, EntryExpr, Expr, LiteralValue};
    use crate::IdedExpr;
    use std::iter;

    #[derive(Default)]
    struct TestInfo {
        // I contains the input expression to be parsed.
        i: &'static str,

        // P contains the type/id adorned debug output of the expression tree.
        p: &'static str,

        // E contains the expected error output for a failed parse, or "" if the parse is expected to be successful.
        e: &'static str,
        // L contains the expected source adorned debug output of the expression tree.
        // l: String,

        // M contains the expected adorned debug output of the macro calls map
        // m: String,
    }

    #[test]
    fn test_bad_input() {
        let expressions = [
            "1 + ()", "/", ".", "@foo", "x(1,)", "\x0a", "\n", "", "!-\u{1}",
        ];
        for expr in expressions {
            assert!(
                Parser::new().parse(expr).is_err(),
                "Expression `{}` should not parse",
                expr
            );
        }
    }

    #[test]
    fn test_comments() {
        let expression = r#"
        // This is a comment
        this.is.not()

        // We don't care!

        "#;
        assert!(Parser::new().parse(expression).is_ok());
    }

    #[test]
    fn recursion_limits() {
        let expressions = [
            "[[[1]]]",
            "(((1)))",
            "{1: {2: {3: 'none'}}}",
            "type(type(type(1)))",
            "[{'a': size([])}]",
            "{}.map(a, a.map(b, b.map(c, c)))",
        ];
        for expr in expressions {
            assert!(
                Parser::new().max_recursion_depth(3).parse(expr).is_ok(),
                "Expression `{}` should parse",
                expr
            );
            assert!(
                Parser::new().max_recursion_depth(2).parse(expr).is_err(),
                "Expression `{}` should not parse",
                expr
            );
        }
        let expressions = [
            "[[[[[[[[[[1]]]]]]]]]]",
            "((((((((((1))))))))))",
            "{1: {2: {3: {4: {5: {6: {1: {2: {3: {4: 'none'}}}}}}}}}}",
            "type(type(type(type(type(type(type(type(type(type(1))))))))))",
            "[{'a': size([{'1':size([{'1':size([[]])}])}])}]",
        ];
        for expr in expressions {
            assert!(
                Parser::new().max_recursion_depth(10).parse(expr).is_ok(),
                "Expression `{}` should parse",
                expr
            );
            assert!(
                Parser::new().max_recursion_depth(9).parse(expr).is_err(),
                "Expression `{}` should not parse",
                expr
            );
        }
        assert!(Parser::new().max_recursion_depth(0).parse("1 + 1").is_ok());
        assert!(Parser::new()
            .max_recursion_depth(0)
            .parse("(1 + 1)")
            .is_err());
    }

    #[test]
    fn malformed_nested_expression_does_not_panic() {
        let expression = "ma[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[\x0c\0\0\0\0\0\0\0[[[[[[[putTo?[[[[[[[[[[ep";

        assert!(Parser::new()
            .max_recursion_depth(48)
            .parse(expression)
            .is_err());
    }

    #[test]
    fn test() {
        let test_cases = [
            TestInfo {
                i: r#""A""#,
                p: r#""A"^#1:*expr.Constant_StringValue#"#,
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: r#"true"#,
                p: r#"true^#1:*expr.Constant_BoolValue#"#,
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: r#"false"#,
                p: r#"false^#1:*expr.Constant_BoolValue#"#,
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "0",
                p: "0^#1:*expr.Constant_Int64Value#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "42",
                p: "42^#1:*expr.Constant_Int64Value#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "0xF",
                p: "15^#1:*expr.Constant_Int64Value#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "0u",
                p: "",
                e: "ERROR: <input>:1:1: `0u` is a uint literal, which is not in the typed-CEL dialect (removed: uint) — write it without the `u` suffix
| 0u
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "23u",
                p: "",
                e: "ERROR: <input>:1:1: `23u` is a uint literal, which is not in the typed-CEL dialect (removed: uint) — write it without the `u` suffix
| 23u
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "24u",
                p: "",
                e: "ERROR: <input>:1:1: `24u` is a uint literal, which is not in the typed-CEL dialect (removed: uint) — write it without the `u` suffix
| 24u
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "0xFu",
                p: "",
                e: "ERROR: <input>:1:1: `0xFu` is a uint literal, which is not in the typed-CEL dialect (removed: uint) — write it without the `u` suffix
| 0xFu
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "-1",
                p: "-1^#1:*expr.Constant_Int64Value#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "4--4",
                p: r#"_-_(
    4^#1:*expr.Constant_Int64Value#,
    -4^#3:*expr.Constant_Int64Value#
)^#2:*expr.Expr_CallExpr#"#,
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "4--4.1",
                p: r#"_-_(
    4^#1:*expr.Constant_Int64Value#,
    -4.1^#3:*expr.Constant_DoubleValue#
)^#2:*expr.Expr_CallExpr#"#,
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: r#"b"abc""#,
                p: r#"b"abc"^#1:*expr.Constant_BytesValue#"#,
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "23.39",
                p: "23.39^#1:*expr.Constant_DoubleValue#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "!a",
                p: "!_(
    a^#2:*expr.Expr_IdentExpr#
)^#1:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "null",
                p: "null^#1:*expr.Constant_NullValue#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a",
                p: "a^#1:*expr.Expr_IdentExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a?b:c",
                p: "_?_:_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#,
    c^#4:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a || b",
                p: "_||_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#2:*expr.Expr_IdentExpr#
)^#3:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a || b || c || d || e || f ",
                p: "_||_(
    _||_(
        _||_(
            a^#1:*expr.Expr_IdentExpr#,
            b^#2:*expr.Expr_IdentExpr#
        )^#3:*expr.Expr_CallExpr#,
        c^#4:*expr.Expr_IdentExpr#
    )^#5:*expr.Expr_CallExpr#,
    _||_(
        _||_(
            d^#6:*expr.Expr_IdentExpr#,
            e^#8:*expr.Expr_IdentExpr#
        )^#9:*expr.Expr_CallExpr#,
        f^#10:*expr.Expr_IdentExpr#
    )^#11:*expr.Expr_CallExpr#
)^#7:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a && b",
                p: "_&&_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#2:*expr.Expr_IdentExpr#
)^#3:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a && b && c && d && e && f && g",
                p: "_&&_(
    _&&_(
        _&&_(
            a^#1:*expr.Expr_IdentExpr#,
            b^#2:*expr.Expr_IdentExpr#
        )^#3:*expr.Expr_CallExpr#,
        _&&_(
            c^#4:*expr.Expr_IdentExpr#,
            d^#6:*expr.Expr_IdentExpr#
        )^#7:*expr.Expr_CallExpr#
    )^#5:*expr.Expr_CallExpr#,
    _&&_(
        _&&_(
            e^#8:*expr.Expr_IdentExpr#,
            f^#10:*expr.Expr_IdentExpr#
        )^#11:*expr.Expr_CallExpr#,
        g^#12:*expr.Expr_IdentExpr#
    )^#13:*expr.Expr_CallExpr#
)^#9:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a && b && c && d || e && f && g && h",
                p: "_||_(
    _&&_(
        _&&_(
            a^#1:*expr.Expr_IdentExpr#,
            b^#2:*expr.Expr_IdentExpr#
        )^#3:*expr.Expr_CallExpr#,
        _&&_(
            c^#4:*expr.Expr_IdentExpr#,
            d^#6:*expr.Expr_IdentExpr#
        )^#7:*expr.Expr_CallExpr#
    )^#5:*expr.Expr_CallExpr#,
    _&&_(
        _&&_(
            e^#8:*expr.Expr_IdentExpr#,
            f^#9:*expr.Expr_IdentExpr#
        )^#10:*expr.Expr_CallExpr#,
        _&&_(
            g^#11:*expr.Expr_IdentExpr#,
            h^#13:*expr.Expr_IdentExpr#
        )^#14:*expr.Expr_CallExpr#
    )^#12:*expr.Expr_CallExpr#
)^#15:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a + b",
                p: "_+_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a - b",
                p: "_-_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a * b",
                p: "_*_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a / b",
                p: "_/_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a % b",
                p: "_%_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a in b",
                p: "@in(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a == b",
                p: "_==_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a != b",
                p: "_!=_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a > b",
                p: "_>_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a >= b",
                p: "_>=_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a < b",
                p: "_<_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a <= b",
                p: "_<=_(
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a.b",
                p: "a^#1:*expr.Expr_IdentExpr#.b^#2:*expr.Expr_SelectExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a.b.c",
                p: "a^#1:*expr.Expr_IdentExpr#.b^#2:*expr.Expr_SelectExpr#.c^#3:*expr.Expr_SelectExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a[b]",
                p: "_[_](
    a^#1:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "(a)",
                p: "a^#1:*expr.Expr_IdentExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "((a))",
                p: "a^#1:*expr.Expr_IdentExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a()",
                p: "a()^#1:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a(b)",
                p: "a(
    b^#2:*expr.Expr_IdentExpr#
)^#1:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a(b, c)",
                p: "a(
    b^#2:*expr.Expr_IdentExpr#,
    c^#3:*expr.Expr_IdentExpr#
)^#1:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a.b()",
                p: "a^#1:*expr.Expr_IdentExpr#.b()^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "a.b(c)",
                p: "a^#1:*expr.Expr_IdentExpr#.b(
    c^#3:*expr.Expr_IdentExpr#
)^#2:*expr.Expr_CallExpr#",
                e: "",
                ..Default::default()
            },
            // `removed: protobuf`. These three parsed to `Expr_StructExpr` upstream; the map
            // literals immediately below (`{}`, `{a: b, c: d}`) are a DIFFERENT production and
            // still parse. The pair is the point: deleting message construction by deleting the
            // shared brace handling would take map literals with it.
            TestInfo {
                i: "foo{ }",
                p: "",
                e: "ERROR: <input>:1:1: message construction `foo{...}` is not in the typed-CEL dialect (removed: protobuf)
| foo{ }
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "foo{ a:b, c:d }",
                p: "",
                e: "ERROR: <input>:1:1: message construction `foo{...}` is not in the typed-CEL dialect (removed: protobuf)
| foo{ a:b, c:d }
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "{}",
                p: "{}^#1:*expr.Expr_StructExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "{a: b, c: d}",
                p: "{
    a^#3:*expr.Expr_IdentExpr#:b^#4:*expr.Expr_IdentExpr#^#2:*expr.Expr_CreateStruct_Entry#,
    c^#6:*expr.Expr_IdentExpr#:d^#7:*expr.Expr_IdentExpr#^#5:*expr.Expr_CreateStruct_Entry#
}^#1:*expr.Expr_StructExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "[]",
                p: "[]^#1:*expr.Expr_ListExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "[a]",
                p: "[
    a^#2:*expr.Expr_IdentExpr#
]^#1:*expr.Expr_ListExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "[a, b, c]",
                p: "[
    a^#2:*expr.Expr_IdentExpr#,
    b^#3:*expr.Expr_IdentExpr#,
    c^#4:*expr.Expr_IdentExpr#
]^#1:*expr.Expr_ListExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "has(m.f)",
                p: "m^#2:*expr.Expr_IdentExpr#.f~test-only~^#4:*expr.Expr_SelectExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "m.exists(v, f)",
                p: "__comprehension__(
// Variable
v,
// Target
m^#1:*expr.Expr_IdentExpr#,
// Accumulator
@result,
// Init
false^#5:*expr.Constant_BoolValue#,
// LoopCondition
@not_strictly_false(
    !_(
        @result^#6:*expr.Expr_IdentExpr#
    )^#7:*expr.Expr_CallExpr#
)^#8:*expr.Expr_CallExpr#,
// LoopStep
_||_(
    @result^#9:*expr.Expr_IdentExpr#,
    f^#4:*expr.Expr_IdentExpr#
)^#10:*expr.Expr_CallExpr#,
// Result
@result^#11:*expr.Expr_IdentExpr#)^#12:*expr.Expr_ComprehensionExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "m.all(v, f)",
                p: "__comprehension__(
// Variable
v,
// Target
m^#1:*expr.Expr_IdentExpr#,
// Accumulator
@result,
// Init
true^#5:*expr.Constant_BoolValue#,
// LoopCondition
@not_strictly_false(
    @result^#6:*expr.Expr_IdentExpr#
)^#7:*expr.Expr_CallExpr#,
// LoopStep
_&&_(
    @result^#8:*expr.Expr_IdentExpr#,
    f^#4:*expr.Expr_IdentExpr#
)^#9:*expr.Expr_CallExpr#,
// Result
@result^#10:*expr.Expr_IdentExpr#)^#11:*expr.Expr_ComprehensionExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "m.existsOne(v, f)",
                p: "__comprehension__(
// Variable
v,
// Target
m^#1:*expr.Expr_IdentExpr#,
// Accumulator
@result,
// Init
0^#5:*expr.Constant_Int64Value#,
// LoopCondition
true^#6:*expr.Constant_BoolValue#,
// LoopStep
_?_:_(
    f^#4:*expr.Expr_IdentExpr#,
    _+_(
        @result^#7:*expr.Expr_IdentExpr#,
        1^#8:*expr.Constant_Int64Value#
    )^#9:*expr.Expr_CallExpr#,
    @result^#10:*expr.Expr_IdentExpr#
)^#11:*expr.Expr_CallExpr#,
// Result
_==_(
    @result^#12:*expr.Expr_IdentExpr#,
    1^#13:*expr.Constant_Int64Value#
)^#14:*expr.Expr_CallExpr#)^#15:*expr.Expr_ComprehensionExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "m.map(v, f)",
                p: "__comprehension__(
// Variable
v,
// Target
m^#1:*expr.Expr_IdentExpr#,
// Accumulator
@result,
// Init
[]^#5:*expr.Expr_ListExpr#,
// LoopCondition
true^#6:*expr.Constant_BoolValue#,
// LoopStep
_+_(
    @result^#7:*expr.Expr_IdentExpr#,
    [
        f^#4:*expr.Expr_IdentExpr#
    ]^#8:*expr.Expr_ListExpr#
)^#9:*expr.Expr_CallExpr#,
// Result
@result^#10:*expr.Expr_IdentExpr#)^#11:*expr.Expr_ComprehensionExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "m.map(v, p, f)",
                p: "__comprehension__(
// Variable
v,
// Target
m^#1:*expr.Expr_IdentExpr#,
// Accumulator
@result,
// Init
[]^#6:*expr.Expr_ListExpr#,
// LoopCondition
true^#7:*expr.Constant_BoolValue#,
// LoopStep
_?_:_(
    p^#4:*expr.Expr_IdentExpr#,
    _+_(
        @result^#8:*expr.Expr_IdentExpr#,
        [
            f^#5:*expr.Expr_IdentExpr#
        ]^#9:*expr.Expr_ListExpr#
    )^#10:*expr.Expr_CallExpr#,
    @result^#11:*expr.Expr_IdentExpr#
)^#12:*expr.Expr_CallExpr#,
// Result
@result^#13:*expr.Expr_IdentExpr#)^#14:*expr.Expr_ComprehensionExpr#",
                e: "",
                ..Default::default()
            },
            TestInfo {
                i: "m.filter(v, p)",
                p: "__comprehension__(
// Variable
v,
// Target
m^#1:*expr.Expr_IdentExpr#,
// Accumulator
@result,
// Init
[]^#5:*expr.Expr_ListExpr#,
// LoopCondition
true^#6:*expr.Constant_BoolValue#,
// LoopStep
_?_:_(
    p^#4:*expr.Expr_IdentExpr#,
    _+_(
        @result^#7:*expr.Expr_IdentExpr#,
        [
            v^#3:*expr.Expr_IdentExpr#
        ]^#8:*expr.Expr_ListExpr#
    )^#9:*expr.Expr_CallExpr#,
    @result^#10:*expr.Expr_IdentExpr#
)^#11:*expr.Expr_CallExpr#,
// Result
@result^#12:*expr.Expr_IdentExpr#)^#13:*expr.Expr_ComprehensionExpr#",
                e: "",
                ..Default::default()
            },
            // Parse error tests
            TestInfo {
                i: "0xFFFFFFFFFFFFFFFFF",
                p: "",
                e: "ERROR: <input>:1:1: invalid int literal
| 0xFFFFFFFFFFFFFFFFF
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "0xFFFFFFFFFFFFFFFFFu",
                p: "",
                e: "ERROR: <input>:1:1: `0xFFFFFFFFFFFFFFFFFu` is a uint literal, which is not in the typed-CEL dialect (removed: uint) — write it without the `u` suffix
| 0xFFFFFFFFFFFFFFFFFu
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "1.99e90000009",
                p: "",
                e: "ERROR: <input>:1:1: invalid double literal
| 1.99e90000009
| ^",
                ..Default::default()
            },
            TestInfo {
                i: "{",
                p: "",
                e: "ERROR: <input>:1:2: Syntax error: mismatched input '<EOF>' expecting {'[', '{', '}', '(', '.', ',', '-', '!', '?', 'true', 'false', 'null', NUM_FLOAT, NUM_INT, NUM_UINT, STRING, BYTES, IDENTIFIER}
| {
| .^",
                ..Default::default()
            },
            TestInfo {
                i: "*@a | b",
                p: "",
                e: "ERROR: <input>:1:1: Syntax error: extraneous input '*' expecting {'[', '{', '(', '.', '-', '!', 'true', 'false', 'null', NUM_FLOAT, NUM_INT, NUM_UINT, STRING, BYTES, IDENTIFIER}
| *@a | b
| ^
ERROR: <input>:1:2: Syntax error: token recognition error at: '@'
| *@a | b
| .^
ERROR: <input>:1:5: Syntax error: token recognition error at: '| '
| *@a | b
| ....^
ERROR: <input>:1:7: Syntax error: extraneous input 'b' expecting <EOF>
| *@a | b
| ......^",
                ..Default::default()
            },
            TestInfo {
                i: "a | b",
                p: "",
                e: "ERROR: <input>:1:3: Syntax error: token recognition error at: '| '
| a | b
| ..^
ERROR: <input>:1:5: Syntax error: extraneous input 'b' expecting <EOF>
| a | b
| ....^",
                ..Default::default()
            },
            // An optional read PARSES, as spec CEL's calls; the checker (or a macro) owns it.
            TestInfo {
                i: "a.?b && a[?b]",
                p: "_&&_(
    _?._(
        a^#1:*expr.Expr_IdentExpr#,
        \"b\"^#2:*expr.Constant_StringValue#
    )^#3:*expr.Expr_CallExpr#,
    _[?_](
        a^#4:*expr.Expr_IdentExpr#,
        b^#6:*expr.Expr_IdentExpr#
    )^#5:*expr.Expr_CallExpr#
)^#7:*expr.Expr_CallExpr#",
                ..Default::default()
            },
            TestInfo {
                i: "[?a, ?b]",
                p: "",
                e: "ERROR: <input>:1:2: optional values are not in the typed-CEL dialect (removed: optional values): an optional READ ends in `.orValue(<default>)` or `.hasValue()` — `x.?f.orValue(0)`, `m[?'k'].hasValue()`
| [?a, ?b]
| .^
ERROR: <input>:1:6: optional values are not in the typed-CEL dialect (removed: optional values): an optional READ ends in `.orValue(<default>)` or `.hasValue()` — `x.?f.orValue(0)`, `m[?'k'].hasValue()`
| [?a, ?b]
| .....^",
                ..Default::default()
            },
            TestInfo {
                i: "{?\'key\': value}",
                p: "",
                e: "ERROR: <input>:1:2: optional values are not in the typed-CEL dialect (removed: optional values): an optional READ ends in `.orValue(<default>)` or `.hasValue()` — `x.?f.orValue(0)`, `m[?'k'].hasValue()`
| {?\'key\': value}
| .^",
                ..Default::default()
            },
            // Two removals in one expression, and BOTH diagnostics survive — a parse error is a
            // recoverable list rather than a stop at the first refusal.
            TestInfo {
                i: "Msg{?field: value} && {?\'key\': value}",
                p: "",
                e: "ERROR: <input>:1:1: message construction `Msg{...}` is not in the typed-CEL dialect (removed: protobuf)
| Msg{?field: value} && {?\'key\': value}
| ^
ERROR: <input>:1:24: optional values are not in the typed-CEL dialect (removed: optional values): an optional READ ends in `.orValue(<default>)` or `.hasValue()` — `x.?f.orValue(0)`, `m[?'k'].hasValue()`
| Msg{?field: value} && {?\'key\': value}
| .......................^",
                ..Default::default()
            },
            TestInfo {
                i: "has(m)",
                p: "",
                e: "ERROR: <input>:1:5: invalid argument to has() macro
| has(m)
| ....^",
                ..Default::default()
            },
            TestInfo {
                i: "1.all(2, 3)",
                p: "",
                e: "ERROR: <input>:1:7: argument must be a simple name
| 1.all(2, 3)
| ......^",
                ..Default::default()
            },
        ];

        for test_case in test_cases {
            let parser = Parser::new();
            let result = parser.parse(test_case.i);
            if !test_case.p.is_empty() {
                assert_eq!(
                    to_go_like_string(result.as_ref().expect("Expected an AST")),
                    test_case.p,
                    "Expr `{}` failed",
                    test_case.i
                );
            }

            if !test_case.e.is_empty() {
                assert_eq!(
                    format!("{}", result.as_ref().expect_err("Expected an Err!")),
                    test_case.e,
                    "Error on `{}` failed",
                    test_case.i
                )
            }
        }
    }

    fn to_go_like_string(expr: &IdedExpr) -> String {
        let mut writer = DebugWriter::default();
        writer.buffer(expr);
        writer.done()
    }

    struct DebugWriter {
        buffer: String,
        indents: usize,
        line_start: bool,
    }

    impl Default for DebugWriter {
        fn default() -> Self {
            Self {
                buffer: String::default(),
                indents: 0,
                line_start: true,
            }
        }
    }

    impl DebugWriter {
        fn buffer(&mut self, expr: &IdedExpr) -> &Self {
            let e = match &expr.expr {
                Expr::Unspecified => "UNSPECIFIED!",
                Expr::Call(call) => {
                    if let Some(target) = &call.target {
                        self.buffer(target);
                        self.push(".");
                    }
                    self.push(call.func_name.as_str());
                    self.push("(");
                    if !call.args.is_empty() {
                        self.inc_indent();
                        self.newline();
                        for i in 0..call.args.len() {
                            if i > 0 {
                                self.push(",");
                                self.newline();
                            }
                            self.buffer(&call.args[i]);
                        }
                        self.dec_indent();
                        self.newline();
                    }
                    self.push(")");
                    &format!("^#{}:{}#", expr.id, "*expr.Expr_CallExpr")
                }
                Expr::Comprehension(comprehension) => {
                    self.push("__comprehension__(\n");
                    self.push_comprehension(comprehension);
                    &format!(")^#{}:{}#", expr.id, "*expr.Expr_ComprehensionExpr")
                }
                Expr::Ident(id) => &format!("{}^#{}:{}#", id, expr.id, "*expr.Expr_IdentExpr"),
                Expr::List(list) => {
                    self.push("[");
                    if !list.elements.is_empty() {
                        self.inc_indent();
                        self.newline();
                        for (i, element) in list.elements.iter().enumerate() {
                            if i > 0 {
                                self.push(",");
                                self.newline();
                            }
                            self.buffer(element);
                        }
                        self.dec_indent();
                        self.newline();
                    }
                    self.push("]");
                    &format!("^#{}:{}#", expr.id, "*expr.Expr_ListExpr")
                }
                Expr::Literal(val) => match val {
                    LiteralValue::String(s) => &format!(
                        "\"{}\"^#{}:{}#",
                        s.inner(),
                        expr.id,
                        "*expr.Constant_StringValue"
                    ),
                    LiteralValue::Boolean(b) => {
                        &format!("{}^#{}:{}#", b.inner(), expr.id, "*expr.Constant_BoolValue")
                    }
                    LiteralValue::Int(i) => {
                        &format!("{}^#{}:{}#", i, expr.id, "*expr.Constant_Int64Value")
                    }
                    LiteralValue::UInt(u) => {
                        &format!("{}^#{}:{}#", u, expr.id, "*expr.Constant_Uint64Value")
                    }
                    LiteralValue::Double(f) => &format!(
                        "{}^#{}:{}#",
                        f.inner(),
                        expr.id,
                        "*expr.Constant_DoubleValue"
                    ),
                    LiteralValue::Bytes(bytes) => &format!(
                        "b\"{}\"^#{}:{}#",
                        String::from_utf8_lossy(bytes),
                        expr.id,
                        "*expr.Constant_BytesValue"
                    ),
                    LiteralValue::Null => {
                        &format!("null^#{}:{}#", expr.id, "*expr.Constant_NullValue")
                    }
                },
                Expr::Map(map) => {
                    self.push("{");
                    self.inc_indent();
                    if !map.entries.is_empty() {
                        self.newline();
                    }
                    for (i, entry) in map.entries.iter().enumerate() {
                        match &entry.expr {
                            EntryExpr::MapEntry(e) => {
                                self.buffer(&e.key);
                                self.push(":");
                                self.buffer(&e.value);
                                self.push(&format!(
                                    "^#{}:{}#",
                                    entry.id, "*expr.Expr_CreateStruct_Entry"
                                ));
                            }
                        }
                        if i < map.entries.len() - 1 {
                            self.push(",");
                        }
                        self.newline();
                    }
                    self.dec_indent();
                    self.push("}");
                    &format!("^#{}:{}#", expr.id, "*expr.Expr_StructExpr")
                }
                Expr::Select(select) => {
                    self.buffer(select.operand.deref());
                    let suffix = if select.test { "~test-only~" } else { "" };
                    &format!(
                        ".{}{}^#{}:{}#",
                        select.field, suffix, expr.id, "*expr.Expr_SelectExpr"
                    )
                }
            };
            self.push(e);
            self
        }

        fn push(&mut self, literal: &str) {
            self.indent();
            self.buffer.push_str(literal);
        }

        fn indent(&mut self) {
            if self.line_start {
                self.line_start = false;
                self.buffer.push_str(
                    iter::repeat_n("    ", self.indents)
                        .collect::<String>()
                        .as_str(),
                )
            }
        }

        fn newline(&mut self) {
            self.buffer.push('\n');
            self.line_start = true;
        }

        fn inc_indent(&mut self) {
            self.indents += 1;
        }

        fn dec_indent(&mut self) {
            self.indents -= 1;
        }

        fn done(self) -> String {
            self.buffer
        }

        fn push_comprehension(&mut self, comprehension: &ComprehensionExpr) {
            self.push("// Variable\n");
            self.push(comprehension.iter_var.as_str());
            self.push(",\n");
            self.push("// Target\n");
            self.buffer(&comprehension.iter_range);
            self.push(",\n");
            self.push("// Accumulator\n");
            self.push(comprehension.accu_var.as_str());
            self.push(",\n");
            self.push("// Init\n");
            self.buffer(&comprehension.accu_init);
            self.push(",\n");
            self.push("// LoopCondition\n");
            self.buffer(&comprehension.loop_cond);
            self.push(",\n");
            self.push("// LoopStep\n");
            self.buffer(&comprehension.loop_step);
            self.push(",\n");
            self.push("// Result\n");
            self.buffer(&comprehension.result);
        }
    }
}
