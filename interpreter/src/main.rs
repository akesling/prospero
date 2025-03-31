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

#[derive(Clone, Debug)]
enum Instruction {
    VarX,
    VarY,
    Const(f64),
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
            ("const", Some(args)) => Const(args.trim().parse::<f64>()?),
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

fn interpret_point(program: &[Instruction], x: f64, y: f64) -> bool {
    let mut context: Vec<f64> = vec![0.0; program.len()];
    for (i, inst) in program.iter().enumerate() {
        context[i] = match *inst {
            Instruction::VarX => x,
            Instruction::VarY => y,
            Instruction::Const(c) => c,
            Instruction::Add(addr1, addr2) => context[addr1] + context[addr2],
            Instruction::Sub(addr1, addr2) => context[addr1] - context[addr2],
            Instruction::Mul(addr1, addr2) => context[addr1] * context[addr2],
            Instruction::Max(addr1, addr2) => f64::max(context[addr1], context[addr2]),
            Instruction::Min(addr1, addr2) => f64::min(context[addr1], context[addr2]),
            Instruction::Neg(addr) => -context[addr],
            Instruction::Square(addr) => context[addr].powf(2.0),
            Instruction::Sqrt(addr) => context[addr].powf(0.5),
        };
    }

    *context.last().unwrap() < 0.0
}

fn index_to_point(i: usize, span: f64) -> f64 {
    ((i as f64) / span) * 2.0 - 1.0
}

fn interpret_image(program: &[Instruction], width: usize, height: usize) -> Vec<Vec<bool>> {
    let mut image = vec![vec![false; height]; width];
    let span_x = width as f64;
    let span_y = height as f64;
    let x_points: Vec<(usize, f64)> = (0..width).map(|x| (x, index_to_point(x, span_x))).collect();
    let y_points: Vec<(usize, f64)> = if width == height {
        x_points.clone()
    } else {
        (0..height)
            .map(|y| (y, index_to_point(y, span_y)))
            .collect()
    };

    for (x_i, x) in x_points.into_iter() {
        for (y_i, y) in y_points.iter() {
            image[x_i][*y_i] = interpret_point(program, x, *y);
        }
    }
    image
}

async fn render(pixels: Vec<Vec<bool>>, path: &path::Path) -> anyhow::Result<()> {
    use tokio::io::AsyncWriteExt as _;

    let mut file = tokio::fs::File::create(path).await?;
    file.write_all(&format!("P5\n{} {}\n255\n", pixels.len(), pixels[0].len()).into_bytes())
        .await?;
    for line in pixels {
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
