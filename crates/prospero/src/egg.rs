use egg::{Analysis, Id, Language as _, PatternAst};

use ordered_float::NotNan;

use crate::parser::Instruction;
pub use crate::parser::ValueType;

pub type Constant = NotNan<ValueType>;
egg::define_language! {
    pub enum Prospero {
        "var-x" = VarX,
        "var-y" = VarY,
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "max" = Max([Id; 2]),
        "min" = Min([Id; 2]),
        "neg" = Neg(Id),
        "sq" = Square(Id),
        "root" = Sqrt(Id),
        // TODO(akesling): Add an absolute value instruction to merge sqrt and square
        Const(Constant),
    }
}
pub type EGraph = egg::EGraph<Prospero, ConstantFold>;

/// Based on https://github.com/egraphs-good/egg/blob/c917025f3b45d8f3456f0e02dbecffa2edea84c7/tests/math.rs#L48
#[derive(Default)]
pub struct ConstantFold;
impl Analysis<Prospero> for ConstantFold {
    type Data = Option<(Constant, PatternAst<Prospero>)>;

    fn make(egraph: &mut EGraph, enode: &Prospero) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            Prospero::Const(c) => (*c, format!("{}", c).parse().unwrap()),
            Prospero::Add([a, b]) => (
                x(a)? + x(b)?,
                format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Prospero::Sub([a, b]) => (
                x(a)? - x(b)?,
                format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Prospero::Mul([a, b]) => (
                x(a)? * x(b)?,
                format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Prospero::Max([a, b]) => (
                NotNan::<ValueType>::max(x(a)?, x(b)?),
                format!("(max {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Prospero::Min([a, b]) => (
                NotNan::<ValueType>::min(x(a)?, x(b)?),
                format!("(max {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Prospero::Neg(a) => (-x(a)?, format!("(neg {})", x(a)?).parse().unwrap()),
            Prospero::Square(a) => (
                NotNan::<ValueType>::new(ValueType::powf(x(a)?.into(), 2.0)).unwrap(),
                format!("(sq {})", x(a)?).parse().unwrap(),
            ),
            Prospero::Sqrt(a) => (
                NotNan::<ValueType>::new(ValueType::powf(x(a)?.into(), 0.5)).unwrap(),
                format!("(root {})", x(a)?).parse().unwrap(),
            ),
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> egg::DidMerge {
        egg::merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            egg::DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let data = egraph[id].data.clone();
        if let Some((c, pat)) = data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(Prospero::Const(c));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &egg::Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(n) = &egraph[subst[var]].data {
            *(n.0) != 0.0
        } else {
            true
        }
    }
}

#[rustfmt::skip]
fn make_rules() -> Vec<egg::Rewrite<Prospero, ConstantFold>> {
    use egg::rewrite as rw;
    vec![
        rw!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("commute-max"; "(max ?a ?b)" => "(max ?b ?a)"),
        rw!("commute-min"; "(min ?a ?b)" => "(min ?b ?a)"),

        rw!("assoc-max"; "(max ?a (max ?b ?c))" => "(max (max ?a ?b) ?c)"),
        rw!("assoc-min"; "(min ?a (min ?b ?c))" => "(min (min ?a ?b) ?c)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

        rw!("distribute"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

        rw!("build-square"; "(* ?a ?a)" => "(sq ?a)"),
        rw!("decompose-square"; "(sq ?a)" => "(* ?a ?a)"),
        // TODO(akesling): Add absolute value as an instruction.

        rw!("neg-sub"; "(neg ?a)" => "(- 0.0 ?a)"),
        rw!("sub-neg"; "(- 0.0 ?a)" => "(neg ?a)"),

        rw!("sub-add"; "(- ?a ?b)" => "(+ ?a (neg ?b))"),

        rw!("add-0"; "(+ ?a 0.0)" => "?a"),
        rw!("sub-0"; "(- ?a 0.0)" => "?a"),
        rw!("sub-same"; "(- ?a ?a)" => "0.0"),
        rw!("neg-0"; "(neg (neg ?a))" => "?a"),
        rw!("mul-0"; "(* ?a 0.0)" => "0.0"),
        rw!("mul-1"; "(* ?a 1.0)" => "?a"),
        rw!("root-1"; "(root 1.0)" => "1.0"),
        rw!("sq-1"; "(sq 1.0)" => "1.0"),

        //rw!("sq-mul"; "(* (sq ?a ?b) (sq ?a ?c))" => "(sq ?a (+ ?b ?c))"),
    ]
}

fn expr_from_program(program: &[Instruction]) -> anyhow::Result<egg::RecExpr<Prospero>> {
    use egg::Id;
    use Instruction::*;

    Ok(egg::RecExpr::<Prospero>::from(
        program
            .iter()
            .map(|inst| {
                Ok(match inst {
                    VarX => Prospero::VarX,
                    VarY => Prospero::VarY,
                    Const(c) => Prospero::Const(NotNan::new(*c)?),
                    Add(a, b) => Prospero::Add([Id::from(*a), Id::from(*b)]),
                    Sub(a, b) => Prospero::Sub([Id::from(*a), Id::from(*b)]),
                    Mul(a, b) => Prospero::Mul([Id::from(*a), Id::from(*b)]),
                    Max(a, b) => Prospero::Max([Id::from(*a), Id::from(*b)]),
                    Min(a, b) => Prospero::Min([Id::from(*a), Id::from(*b)]),
                    Neg(a) => Prospero::Neg(Id::from(*a)),
                    Square(a) => Prospero::Square(Id::from(*a)),
                    Sqrt(a) => Prospero::Sqrt(Id::from(*a)),
                })
            })
            .collect::<anyhow::Result<Vec<_>>>()?,
    ))
}

fn program_from_expr(expr: &egg::RecExpr<Prospero>) -> anyhow::Result<Vec<Instruction>> {
    use Instruction::*;

    expr.as_ref()
        .iter()
        .map(|node| {
            Ok(match node {
                Prospero::VarX => VarX,
                Prospero::VarY => VarY,
                Prospero::Const(c) => Const(c.into_inner()),
                Prospero::Add([a, b]) => Add((*a).into(), (*b).into()),
                Prospero::Sub([a, b]) => Sub((*a).into(), (*b).into()),
                Prospero::Mul([a, b]) => Mul((*a).into(), (*b).into()),
                Prospero::Max([a, b]) => Max((*a).into(), (*b).into()),
                Prospero::Min([a, b]) => Min((*a).into(), (*b).into()),
                Prospero::Neg(a) => Neg((*a).into()),
                Prospero::Square(a) => Square((*a).into()),
                Prospero::Sqrt(a) => Sqrt((*a).into()),
            })
        })
        .collect()
}

pub fn simplify(program: &[Instruction]) -> anyhow::Result<Vec<Instruction>> {
    let expr = expr_from_program(program)?;

    let runner: egg::Runner<Prospero, ConstantFold> = egg::Runner::default()
        .with_iter_limit(3)
        .with_expr(&expr)
        .run(&make_rules());
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);
    let (best_cost, best) = extractor.find_best(root);
    log::debug!("Simplified |{}| to |{}| with cost {}", expr.len(), best.len(), best_cost);

    program_from_expr(&best)
}
