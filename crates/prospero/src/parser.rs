use anyhow::{anyhow, bail};

pub type ValueType = f64;

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
