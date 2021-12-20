use std::{cell::Cell, collections::VecDeque, path::Path};

use anyhow::Context;
use bytes::Bytes;
use ethnum::U256;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use tap::Tap;

use crate::{
    containers::{List, Map, Symbol},
    context::{Ctx, CtxLocation, CtxResult, ModuleId, ToCtx, ToCtxErr},
    grammar::BinOp,
};

use super::{RawConstExpr, RawDefn, RawExpr, RawProgram, RawTypeBind, RawTypeExpr};

/// Parse a string as an entire program.
pub fn parse_program(input: &str, source: ModuleId) -> CtxResult<Ctx<RawProgram>> {
    log::debug!("parsing {} chars at {}", input.len(), source);
    let root_ctx = CtxLocation {
        source,
        start_offset: 0,
        end_offset: 0,
    };
    let pair = RawParser::parse(Rule::program, input)
        .map_err(|err| {
            let location = err.location.clone();
            let (start_offset, end_offset) = match location {
                pest::error::InputLocation::Pos(p) => (p, p),
                pest::error::InputLocation::Span(p) => p,
            };
            let message = err
                .to_string()
                .lines()
                .last()
                .unwrap()
                .trim()
                .trim_start_matches('=')
                .trim()
                .to_string();
            anyhow::anyhow!("{}", message).with_ctx(CtxLocation {
                source,
                start_offset,
                end_offset,
            })
        })?
        .next()
        .context("no pairs produced by parser")
        .err_ctx(Some(root_ctx))?;
    let ctx = p2ctx(&pair, source);
    assert_eq!(pair.as_rule(), Rule::program);
    let children: Vec<_> = pair.into_inner().collect();
    // take the definitions, then the expression
    let definitions: List<Ctx<RawDefn>> = children
        .iter()
        .filter(|child| child.as_rule() == Rule::definition)
        .map(|child| parse_definition(child.clone().into_inner().next().unwrap(), source))
        .collect();
    let body = if let Some(last_child) = children
        .into_iter()
        .find(|c| c.as_rule() != Rule::definition)
    {
        parse_expr(last_child, source)
    } else {
        RawExpr::LitNum(U256::new(0)).with_ctx(Some(ctx))
    };
    Ok(RawProgram { definitions, body }.with_ctx(Some(ctx)))
}

fn parse_definition(pair: Pair<Rule>, source: ModuleId) -> Ctx<RawDefn> {
    log::trace!("defn rule {:?} on {:?}", pair.as_rule(), pair.as_str());
    match pair.as_rule() {
        Rule::fun_def | Rule::fun_def_gen => {
            let ctx = p2ctx(&pair, source);
            let rule = pair.as_rule();
            let has_rettype =
                pair.clone().into_inner().count() == if rule == Rule::fun_def { 4 } else { 5 };
            let mut children = pair.into_inner();
            let fun_name = children.next().unwrap();
            let (cgvars, genvars) = if rule == Rule::fun_def_gen {
                let mut cgvars = List::new();
                let mut genvars = List::new();
                for elem in children.next().unwrap().into_inner() {
                    let elem_ctx = p2ctx(&elem, source);
                    match elem.as_rule() {
                        Rule::cgvar_name => &mut cgvars,
                        Rule::type_name => &mut genvars,
                        _ => unreachable!(),
                    }
                    .push_back(Symbol::from(elem.as_str()).with_ctx(elem_ctx));
                }
                (cgvars, genvars)
            } else {
                (List::new(), List::new())
            };
            let fun_name = Symbol::from(fun_name.as_str()).with_ctx(p2ctx(&fun_name, source));
            let fun_args = parse_fun_args(children.next().unwrap(), source);
            let ret_type = if has_rettype {
                Some(parse_type_expr(children.next().unwrap(), source))
            } else {
                None
            };
            let body = parse_expr(children.next().unwrap(), source);
            RawDefn::Function {
                name: fun_name,
                cgvars,
                genvars,
                args: fun_args,
                rettype: ret_type,
                body,
            }
            .with_ctx(ctx)
        }
        Rule::struct_def => {
            let ctx = p2ctx(&pair, source);
            let mut children = pair.into_inner();
            let struct_name = children.next().unwrap();
            let struct_name =
                Symbol::from(struct_name.as_str()).with_ctx(p2ctx(&struct_name, source));
            let struct_elems = children.next().unwrap();
            let elems = parse_fun_args(struct_elems, source);
            RawDefn::Struct {
                name: struct_name,
                fields: elems,
            }
            .with_ctx(ctx)
        }
        Rule::require => {
            let ctx = p2ctx(&pair, source);
            let path = source.relative(pair.into_inner().next().unwrap().into_inner().as_str());
            RawDefn::Require(path).with_ctx(ctx)
        }
        Rule::require_lib => {
            let ctx = p2ctx(&pair, source);
            let children: Vec<_> = pair.into_inner().map(|p| p.as_str().to_string()).collect();
            RawDefn::Require(ModuleId::from_path(Path::new(&format!(
                "${}",
                children.join("/")
            ))))
            .with_ctx(ctx)
        }
        Rule::provide => {
            let ctx = p2ctx(&pair, source);
            let name = Symbol::from(pair.into_inner().next().unwrap().as_str());
            RawDefn::Provide(name).with_ctx(ctx)
        }
        Rule::alias => {
            let ctx = p2ctx(&pair, source);
            let mut children = pair.into_inner();
            let name = children.next().unwrap();
            let texpr = parse_type_expr(children.next().unwrap(), source);
            RawDefn::TypeAlias(
                Symbol::from(name.as_str()).with_ctx(p2ctx(&name, source)),
                texpr,
            )
            .with_ctx(ctx)
        }
        _ => unreachable!(),
    }
}

fn parse_fun_args(pair: Pair<Rule>, source: ModuleId) -> List<Ctx<RawTypeBind>> {
    let mut children = pair.into_inner();
    let mut toret = List::new();
    while let Some(var_name) = children.next() {
        let var_name = Symbol::from(var_name.as_str()).with_ctx(p2ctx(&var_name, source));
        let var_type = children.next().unwrap();
        let var_type = parse_type_expr(var_type, source);
        let ctx = var_type.ctx();
        toret.push_back(
            RawTypeBind {
                name: var_name,
                bind: var_type,
            }
            .with_ctx(ctx),
        )
    }
    toret
}

fn parse_type_expr(pair: Pair<Rule>, source: ModuleId) -> Ctx<RawTypeExpr> {
    log::trace!("type_expr rule {:?} on {:?}", pair.as_rule(), pair.as_str());
    let ctx = p2ctx(&pair, source);
    match pair.as_rule() {
        Rule::type_union => pair
            .into_inner()
            .map(|c| parse_type_expr(c, source))
            .reduce(|a, b| RawTypeExpr::Union(a, b).with_ctx(ctx))
            .unwrap(),
        Rule::type_vector => RawTypeExpr::Vector(
            pair.into_inner()
                .map(|c| parse_type_expr(c, source))
                .collect(),
        )
        .with_ctx(ctx),
        Rule::type_vectorof => {
            let mut children = pair.into_inner();
            let inner_type = parse_type_expr(children.next().unwrap(), source);
            let length = parse_const_expr(children.next().unwrap(), source);
            RawTypeExpr::Vectorof(inner_type, length).with_ctx(ctx)
        }
        Rule::type_dynvectorof => {
            let mut children = pair.into_inner();
            let inner_type = parse_type_expr(children.next().unwrap(), source);
            RawTypeExpr::DynVectorof(inner_type).with_ctx(ctx)
        }
        Rule::type_name => RawTypeExpr::Sym(Symbol::from(pair.as_str())).with_ctx(ctx),
        Rule::type_natrange => {
            let mut children = pair.into_inner();
            let left = parse_const_expr(children.next().unwrap(), source);
            let right = children
                .next()
                .map(|c| parse_const_expr(c, source))
                .unwrap_or_else(|| left.clone());
            RawTypeExpr::NatRange(left, right).with_ctx(ctx)
        }
        Rule::type_bytes => {
            let inner = parse_const_expr(pair.into_inner().next().unwrap(), source);
            RawTypeExpr::Bytes(inner).with_ctx(ctx)
        }
        Rule::type_dynbytes => RawTypeExpr::DynBytes.with_ctx(ctx),
        Rule::type_qmark => {
            let mut children = pair.into_inner();
            let inner_type = parse_type_expr(children.next().unwrap(), source);
            RawTypeExpr::Union(
                RawTypeExpr::NatRange(
                    RawConstExpr::Lit(U256::from(0u8)).into(),
                    RawConstExpr::Lit(U256::from(0u8)).into(),
                )
                .into(),
                inner_type,
            )
            .with_ctx(ctx)
        }
        _ => unreachable!(),
    }
}

fn parse_const_expr(pair: Pair<Rule>, source: ModuleId) -> Ctx<RawConstExpr> {
    let ctx = p2ctx(&pair, source);
    match pair.as_rule() {
        Rule::const_add_expr | Rule::const_mult_expr => {
            let mut children = pair.into_inner();
            let mut head = parse_const_expr(children.next().unwrap(), source);
            while let Some(op) = children.next() {
                let arg = parse_const_expr(children.next().unwrap(), source);
                head = match op.as_rule() {
                    Rule::add => RawConstExpr::Plus(head, arg),
                    Rule::mul => RawConstExpr::Mult(head, arg),
                    _ => unreachable!(),
                }
                .with_ctx(ctx)
            }
            head
        }
        Rule::nat_literal => {
            RawConstExpr::Lit(U256::from_str_radix(pair.as_str(), 10).unwrap_or_default())
                .with_ctx(ctx)
        }
        Rule::cgvar_name => RawConstExpr::Sym(Symbol::from(pair.as_str())).with_ctx(ctx),
        _ => unreachable!(),
    }
}

fn parse_expr(pair: Pair<Rule>, source: ModuleId) -> Ctx<RawExpr> {
    thread_local! {
        static RECUSION_COUNTER: Cell<usize> = Cell::new(0);
    }
    let current_counter = RECUSION_COUNTER.with(|a| {
        let ctr = a.get();
        a.set(ctr + 1);
        ctr
    });
    scopeguard::defer!(RECUSION_COUNTER.with(|a| a.set(a.get() - 1)));
    let levels = std::iter::repeat(" ")
        .take(current_counter)
        .fold(String::from(""), |a, b| (a.tap_mut(|a| a.push_str(b))));
    log::trace!(
        "{}expr rule {:?} on {:?}",
        levels,
        pair.as_rule(),
        pair.as_str()
    );
    let ctx = p2ctx(&pair, source);
    match pair.as_rule() {
        Rule::unsafe_expr => {
            let inner = parse_expr(pair.into_inner().next().unwrap(), source);
            RawExpr::Unsafe(inner).with_ctx(ctx)
        }
        Rule::extern_expr => {
            let inner = pair.into_inner().next().unwrap();
            let ictx = p2ctx(&inner, source);
            let inner = snailquote::unescape(inner.as_str()).unwrap();
            RawExpr::Extern(inner.with_ctx(ictx)).with_ctx(ctx)
        }
        Rule::if_expr => {
            let mut children = pair.into_inner().map(|c| parse_expr(c, source));
            let condition = children.next().unwrap();
            let x = children.next().unwrap();
            let y = children.next().unwrap();
            RawExpr::If(condition, x, y).with_ctx(ctx)
        }
        Rule::fail_expr => RawExpr::Fail.with_ctx(ctx),
        Rule::assert_expr => {
            // shallow desugaring
            let mut children = pair.into_inner().map(|c| parse_expr(c, source));
            let condition = children.next().unwrap();
            let x = children.next().unwrap();
            RawExpr::If(condition, x, RawExpr::Fail.into()).with_ctx(ctx)
        }
        Rule::let_expr => {
            let mut children = pair.into_inner();
            let var_name = children.next().unwrap();
            let var_name = Symbol::from(var_name.as_str()).with_ctx(p2ctx(&var_name, source));
            let var_binding = parse_expr(children.next().unwrap(), source);
            let body = parse_expr(children.next().unwrap(), source);
            RawExpr::Let(var_name, var_binding, body).with_ctx(ctx)
        }
        Rule::let_q_expr => {
            let mut children = pair.into_inner();
            let var_name = children.next().unwrap();
            let var_name = Symbol::from(var_name.as_str()).with_ctx(p2ctx(&var_name, source));
            let var_binding = parse_expr(children.next().unwrap(), source);
            let body = parse_expr(children.next().unwrap(), source);
            let body_container =
                RawExpr::BinOp(BinOp::Land.into(), RawExpr::Var(*var_name).into(), body);
            RawExpr::Let(var_name, var_binding, body_container.into()).with_ctx(ctx)
        }
        Rule::for_expr => {
            let mut children = pair.into_inner();
            let var_name = children.next().unwrap();
            let var_name = Symbol::from(var_name.as_str()).with_ctx(p2ctx(&var_name, source));
            let var_binding = parse_expr(children.next().unwrap(), source);
            let body = parse_expr(children.next().unwrap(), source);
            RawExpr::For(var_name, var_binding, body).with_ctx(ctx)
        }
        Rule::fold_expr => {
            let mut children = pair.into_inner();
            let var_name = children.next().unwrap();
            let var_name = Symbol::from(var_name.as_str()).with_ctx(p2ctx(&var_name, source));
            let var_binding = parse_expr(children.next().unwrap(), source);
            let accum_name = children.next().unwrap();
            let accum_name = Symbol::from(accum_name.as_str()).with_ctx(p2ctx(&accum_name, source));
            let accum_binding = parse_expr(children.next().unwrap(), source);
            let body = parse_expr(children.next().unwrap(), source);
            RawExpr::ForFold(var_name, var_binding, accum_name, accum_binding, body).with_ctx(ctx)
        }
        Rule::rel_expr
        | Rule::add_expr
        | Rule::mult_expr
        | Rule::logic_expr
        | Rule::bitlogic_expr
        | Rule::shift_expr => {
            let mut children: Vec<_> = pair.into_inner().collect();
            let mut toret = parse_expr(children.remove(0), source);
            for pair in children.chunks_exact(2) {
                if let [op, child] = pair {
                    toret = RawExpr::BinOp(
                        match op.as_rule() {
                            Rule::add => BinOp::Add,
                            Rule::sub => BinOp::Sub,
                            Rule::mul => BinOp::Mul,
                            Rule::div => BinOp::Div,
                            Rule::modulo => BinOp::Mod,
                            Rule::equal => BinOp::Eq,
                            Rule::append => BinOp::Append,
                            Rule::land => BinOp::Land,
                            Rule::lor => BinOp::Lor,
                            Rule::le => BinOp::Le,
                            Rule::lt => BinOp::Lt,
                            Rule::ge => BinOp::Ge,
                            Rule::gt => BinOp::Gt,
                            Rule::band => BinOp::Band,
                            Rule::bor => BinOp::Bor,
                            Rule::bxor => BinOp::Bxor,
                            Rule::lshift => BinOp::Lshift,
                            Rule::rshift => BinOp::Rshift,
                            _ => unreachable!(),
                        }
                        .with_ctx(p2ctx(child, source)),
                        toret.clone(),
                        parse_expr(child.clone(), source),
                    )
                    .with_ctx(ctx);
                }
            }
            toret
        }
        Rule::extern_call_expr => {
            let mut children = pair.into_inner();
            let fun_name = children.next().unwrap();
            let fun_name = snailquote::unescape(fun_name.as_str())
                .unwrap()
                .with_ctx(p2ctx(&fun_name, source));
            let mut args = List::new();
            for arg in children.next().unwrap().into_inner() {
                args.push_back(parse_expr(arg, source));
            }
            RawExpr::ExternApply(fun_name, args).with_ctx(ctx)
        }
        Rule::apply_expr => {
            let mut children = pair.into_inner();
            let mut toret = parse_expr(children.next().unwrap(), source);
            for child in children {
                match child.as_rule() {
                    Rule::call_args => {
                        let arguments = child.into_inner();
                        let arguments: List<Ctx<RawExpr>> =
                            arguments.map(|a| parse_expr(a, source)).collect();
                        toret = RawExpr::Apply(toret, arguments).with_ctx(ctx);
                    }
                    Rule::field_access => {
                        let field_name = child.into_inner().next().unwrap();
                        let field_ctx = p2ctx(&field_name, source);
                        let field_name = Symbol::from(field_name.as_str()).with_ctx(field_ctx);
                        toret = RawExpr::Field(toret, field_name).with_ctx(ctx);
                    }
                    Rule::vector_ref => {
                        let index = child.into_inner().next().unwrap();
                        toret = RawExpr::VectorRef(toret, parse_expr(index, source)).with_ctx(ctx);
                    }
                    Rule::vector_slice => {
                        let mut cc = child.into_inner();
                        let left_idx = cc.next().unwrap();
                        let right_idx = cc.next().unwrap();
                        toret = RawExpr::VectorSlice(
                            toret,
                            parse_expr(left_idx, source),
                            parse_expr(right_idx, source),
                        )
                        .with_ctx(ctx);
                    }
                    Rule::vector_update => {
                        let children: List<Ctx<RawExpr>> =
                            child.into_inner().map(|c| parse_expr(c, source)).collect();
                        toret =
                            RawExpr::VectorUpdate(toret, children[0].clone(), children[1].clone())
                                .with_ctx(ctx);
                    }
                    Rule::as_type => {
                        let mut children = child.into_inner();
                        let type_expr = parse_type_expr(children.next().unwrap(), source);
                        toret = RawExpr::AsType(toret, type_expr).with_ctx(ctx);
                    }
                    Rule::into_type => {
                        let mut children = child.into_inner();
                        let type_expr = parse_type_expr(children.next().unwrap(), source);
                        toret = RawExpr::Transmute(toret, type_expr).with_ctx(ctx);
                    }
                    _ => unreachable!(),
                }
            }
            toret
        }
        Rule::nat_literal => {
            RawExpr::LitNum(U256::from_str_radix(pair.as_str(), 10).unwrap_or_default())
                .with_ctx(ctx)
        }
        Rule::var_name => RawExpr::Var(Symbol::from(pair.as_str())).with_ctx(ctx),
        Rule::is_type => {
            let mut children = pair.into_inner();
            let var_name = children.next().unwrap();
            let type_expr = parse_type_expr(children.next().unwrap(), source);
            RawExpr::IsType(Symbol::from(var_name.as_str()), type_expr).with_ctx(ctx)
        }
        Rule::vector_literal => {
            let children = pair
                .into_inner()
                .into_iter()
                .map(|c| parse_expr(c, source))
                .collect();
            RawExpr::LitVec(children).with_ctx(ctx)
        }
        Rule::bytes_literal => {
            let children = pair
                .into_inner()
                .into_iter()
                .map(|c| parse_expr(c, source))
                .collect();
            RawExpr::LitBVec(children).with_ctx(ctx)
        }
        Rule::for_literal => {
            let mut children = pair.into_inner();
            let body = parse_expr(children.next().unwrap(), source);
            let varname = children.next().unwrap();
            let varname = Symbol::from(varname.as_str()).with_ctx(p2ctx(&varname, source));
            let varbind = parse_expr(children.next().unwrap(), source);
            RawExpr::For(varname, varbind, body).with_ctx(ctx)
        }
        Rule::cgvar_name => RawExpr::CgVar(Symbol::from(pair.as_str())).with_ctx(ctx),
        Rule::struct_literal => {
            let mut children = pair.into_inner();
            let name = Symbol::from(children.next().unwrap().as_str());
            let mut bindings = Map::new();
            while let Some(field_name) = children.next() {
                let field_contents = parse_expr(children.next().unwrap(), source);
                bindings.insert(Symbol::from(field_name.as_str()), field_contents);
            }
            RawExpr::LitStruct(name, bindings).with_ctx(ctx)
        }
        Rule::loop_expr => {
            let mut children: VecDeque<_> = pair.into_inner().collect();
            let iterations = parse_const_expr(children.pop_front().unwrap(), source);
            let end_with = parse_expr(children.pop_back().unwrap(), source);
            let inner: List<_> = children
                .into_iter()
                .map(|c| parse_setbang(c, source))
                .collect();
            RawExpr::Loop(iterations, inner, end_with).with_ctx(ctx)
        }
        Rule::string_literal => {
            let true_repr = snailquote::unescape(pair.as_str()).unwrap();
            RawExpr::LitBytes(Bytes::copy_from_slice(true_repr.as_bytes())).with_ctx(ctx)
        }
        Rule::hex_literal => {
            let inner = pair.as_str();
            let inner = &inner[2..inner.len() - 1];
            let decoded = hex::decode(inner).unwrap();
            RawExpr::LitBytes(decoded.into()).with_ctx(ctx)
        }
        Rule::EOI => RawExpr::LitNum(U256::from(0u8)).with_ctx(None),
        _ => unreachable!(),
    }
}

fn parse_setbang(pair: Pair<Rule>, source: ModuleId) -> (Symbol, Ctx<RawExpr>) {
    let mut children = pair.into_inner();
    let var_name = Symbol::from(children.next().unwrap().as_str());
    let value = parse_expr(children.next().unwrap(), source);
    (var_name, value)
}

fn p2ctx(pair: &Pair<Rule>, source: ModuleId) -> CtxLocation {
    CtxLocation {
        source,
        start_offset: pair.as_span().start(),
        end_offset: pair.as_span().end(),
    }
}

#[derive(Parser)]
#[grammar = "grammar/grammar.pest"]
struct RawParser;

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use log::LevelFilter;
    #[test]
    fn test_parse() {
        init_logs();
        eprintln!(
            "{:?}",
            parse_program(
                r#"def range<$n>(x: {$n..$n}) =
                    let accum = [] in 
                    let ctr = 0 :: Nat in
                    accum
            "#,
                ModuleId::from_path(Path::new("placeholder.melo"))
            )
            .unwrap()
        );
    }

    fn init_logs() {
        let _ = env_logger::builder()
            .is_test(true)
            .format_timestamp(None)
            .filter_level(LevelFilter::Trace)
            .try_init();
    }
}
