use std::path;

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

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let contents = tokio::fs::read_to_string(&args.input).await?;
    let program = prospero::parse(&contents)?;
    let pixels = prospero::interpret_image(&program, 1024, 1024);
    prospero::render(pixels, &args.output).await?;

    Ok(())
}
