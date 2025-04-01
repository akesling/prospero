use std::path;

use anyhow::{anyhow, bail, Context};
use clap::Parser;

#[derive(clap::Parser, Debug)]
#[command(author, version, about, long_about = None, arg_required_else_help = true)]
struct Args {
    /// The file to interpret
    #[arg(long)]
    input: path::PathBuf,

    /// The path to write image to
    #[arg(long)]
    output: path::PathBuf,
}

type ValueType = f64;

#[derive(Clone, Debug)]
enum Instruction {
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

fn parse(input: &str) -> anyhow::Result<Vec<Instruction>> {
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

fn interpret_image(program: &[Instruction], width: usize, height: usize) -> Vec<Vec<bool>> {
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

async fn render(pixels: Vec<Vec<bool>>, path: &path::Path) -> anyhow::Result<()> {
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

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let contents = tokio::fs::read_to_string(&args.input).await?;
    let program = parse(&contents)?;
    let pixels = interpret_image(&program, 1024, 1024);
    render(pixels, &args.output).await?;

    Ok(())
}
