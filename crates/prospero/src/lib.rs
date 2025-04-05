use std::path;

use anyhow::{anyhow, bail};

use egg::{Analysis, Id, Language as _, PatternAst};
use ordered_float::NotNan;

type ValueType = f64;

#[derive(Clone, Debug)]
pub enum Instruction {
    VarX,
    VarY,
    Const(ValueType),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Max(usize, usize),
    Min(usize, usize),
    Neg(usize),
    Square(usize),
    Sqrt(usize),
}

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

        rw!("add-0"; "(+ ?a 0.0)" => "?a"),
        rw!("mul-0"; "(* ?a 0.0)" => "0.0"),
        rw!("mul-1"; "(* ?a 1.0)" => "?a"),
        rw!("root-1"; "(root 1.0)" => "1.0"),
        rw!("sq-1"; "(sq 1.0)" => "1.0"),

        rw!("sq-mul"; "(* (sq ?a ?b) (sq ?a ?c))" => "(sq ?a (+ ?b ?c))"),
    ]
}

impl Instruction {
    fn parse(line: &str) -> anyhow::Result<Instruction> {
        use Instruction::*;

        let mut parts = line.splitn(3, ' ');
        let _ = parts.next();
        let Some(op) = parts.next() else {
            bail!("No op found for '{line}'");
        };
        let args = parts.next();

        Ok(match (op, args) {
            ("var-x", None) => VarX,
            ("var-y", None) => VarY,
            ("const", Some(args)) => Const(args.trim().parse::<ValueType>()?),
            ("add", Some(rest)) => {
                let mut tokens = rest.split(" ");
                let addr1 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                let addr2 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                Add(addr1, addr2)
            }
            ("sub", Some(rest)) => {
                let mut tokens = rest.split(" ");
                let addr1 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                let addr2 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                Sub(addr1, addr2)
            }
            ("mul", Some(rest)) => {
                let mut tokens = rest.split(" ");
                let addr1 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                let addr2 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                Mul(addr1, addr2)
            }
            ("max", Some(rest)) => {
                let mut tokens = rest.split(" ");
                let addr1 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                let addr2 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                Max(addr1, addr2)
            }
            ("min", Some(rest)) => {
                let mut tokens = rest.split(" ");
                let addr1 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                let addr2 =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                Min(addr1, addr2)
            }
            ("neg", Some(rest)) => {
                let mut tokens = rest.split(" ");
                let addr =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                Neg(addr)
            }
            ("square", Some(rest)) => {
                let mut tokens = rest.split(" ");
                let addr =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                Square(addr)
            }
            ("sqrt", Some(rest)) => {
                let mut tokens = rest.split(" ");
                let addr =
                    usize::from_str_radix(&tokens.next().ok_or(anyhow!(""))?.trim()[1..], 16)?;
                Sqrt(addr)
            }
            _ => bail!("Operation not recognized for line: {line}"),
        })
    }
}

pub fn parse(input: &str) -> anyhow::Result<Vec<Instruction>> {
    input
        .split("\n")
        .filter_map(|line| {
            if line.starts_with("#") || line.is_empty() {
                None
            } else {
                Some(Instruction::parse(line.trim()))
            }
        })
        .collect::<anyhow::Result<Vec<Instruction>>>()
}

fn interpret_point(program: &[Instruction], x: ValueType, y: ValueType) -> bool {
    let mut context: Vec<ValueType> = vec![0.0; program.len()];
    for (i, inst) in program.iter().enumerate() {
        context[i] = match *inst {
            Instruction::VarX => x,
            Instruction::VarY => y,
            Instruction::Const(c) => c,
            Instruction::Add(addr1, addr2) => context[addr1] + context[addr2],
            Instruction::Sub(addr1, addr2) => context[addr1] - context[addr2],
            Instruction::Mul(addr1, addr2) => context[addr1] * context[addr2],
            Instruction::Max(addr1, addr2) => ValueType::max(context[addr1], context[addr2]),
            Instruction::Min(addr1, addr2) => ValueType::min(context[addr1], context[addr2]),
            Instruction::Neg(addr) => -context[addr],
            Instruction::Square(addr) => context[addr].powf(2.0),
            Instruction::Sqrt(addr) => context[addr].powf(0.5),
        };
    }

    *context.last().unwrap() < 0.0
}

fn index_to_point(i: usize, span: ValueType) -> ValueType {
    ((i as ValueType) / span) * 2.0 - 1.0
}

pub fn interpret_image(program: &[Instruction], width: usize, height: usize) -> Vec<Vec<bool>> {
    let mut image = vec![vec![false; width]; height];
    let span_x = width as ValueType;
    let span_y = height as ValueType;

    // NOTE: Overall iteration goes from (-1, 1) in the "upper left"
    // to (1, -1) in the "lower right"
    let y_points: Vec<(usize, ValueType)> = (0..height)
        .map(|i| (i, index_to_point(height - i - 1, span_y)))
        .collect();
    let x_points: Vec<(usize, ValueType)> =
        (0..width).map(|i| (i, index_to_point(i, span_x))).collect();

    // From 1 to -1
    for (y_i, y) in y_points.into_iter() {
        // From -1 to 1
        for (x_i, x) in x_points.iter() {
            image[y_i][*x_i] = interpret_point(program, *x, y);
        }
    }
    image
}

pub async fn render(pixels: Vec<Vec<bool>>, path: &path::Path) -> anyhow::Result<()> {
    use tokio::io::AsyncWriteExt as _;

    let mut file = tokio::fs::File::create(path).await?;
    file.write_all(&format!("P5\n{} {}\n255\n", pixels.len(), pixels[0].len()).into_bytes())
        .await?;
    // NOTE: PPM pixel data is column-major.
    for line in pixels.into_iter() {
        file.write_all(
            &line
                .into_iter()
                .map(|p| if p { 255u8 } else { 0u8 })
                .collect::<Vec<u8>>(),
        )
        .await?;
    }
    Ok(())
}
