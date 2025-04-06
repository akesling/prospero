use std::path;

use anyhow::{bail, Context};
use clap::Parser;

#[derive(clap::Parser, Debug)]
#[command(author, version, about, long_about = None, arg_required_else_help = true)]
struct Args {
    #[command(subcommand)]
    command: Command,

    /// Log level pairs of the form <MODULE>:<LEVEL>.
    #[arg(long)]
    log_levels: Option<Vec<String>>,
}

#[derive(clap::Parser, Debug)]
struct HaikuOptions {}

async fn haiku(_options: &HaikuOptions) -> anyhow::Result<()> {
    prospero::print_haiku()
}

#[derive(clap::Parser, Debug)]
struct InterpretOptions {
    /// The file to interpret
    #[arg(long)]
    input: path::PathBuf,

    /// The path to write image to
    #[arg(long)]
    output: path::PathBuf,

    #[arg(long)]
    egg: bool,
}

async fn interpet(options: &InterpretOptions) -> anyhow::Result<()> {
    let contents = tokio::fs::read_to_string(&options.input).await?;
    let mut program = prospero::parser::parse(&contents)?;
    if options.egg {
        program = prospero::egg::simplify(&program)?;
    }
    let pixels = prospero::interpreter::interpret_image(&program, 1024, 1024);
    prospero::write_ppm(&pixels, &options.output).await?;

    Ok(())
}

#[derive(clap::Subcommand, Debug)]
enum Command {
    /// Print a random haiku
    Haiku(HaikuOptions),
    /// Interpret input and write image to output
    Interpret(InterpretOptions),
}

/// Convert a series of <MODULE>:<LEVEL> pairs into actionable `(module, LevelFilter)` pairs
fn as_level_pairs(config: &[String]) -> anyhow::Result<Vec<(&str, simplelog::LevelFilter)>> {
    let mut pairs = Vec::with_capacity(config.len());
    for c in config {
        let tokens: Vec<&str> = c.split(":").collect();
        if tokens.len() != 2 {
            bail!("Flag config pair was not of the form <MODULE>:<LEVEL>: '{c}'");
        }
        pairs.push((
            tokens[0],
            match tokens[1].to_lowercase().as_str() {
                "trace" => simplelog::LevelFilter::Trace,
                "debug" => simplelog::LevelFilter::Debug,
                "info" => simplelog::LevelFilter::Info,
                "warn" => simplelog::LevelFilter::Warn,
                "error" => simplelog::LevelFilter::Error,
                _ => bail!("Unrecognized level name in '{c}'"),
            },
        ))
    }

    Ok(pairs)
}

fn initialize_logging(
    module_path_filters: &[(&str, simplelog::LevelFilter)],
) -> anyhow::Result<()> {
    simplelog::CombinedLogger::init(
        module_path_filters
            .iter()
            .map(|(module_path_filter, level)| {
                simplelog::TermLogger::new(
                    *level,
                    simplelog::ConfigBuilder::new()
                        .add_filter_allow(module_path_filter.to_string())
                        .build(),
                    simplelog::TerminalMode::Mixed,
                    simplelog::ColorChoice::Auto,
                ) as Box<dyn simplelog::SharedLogger>
            })
            .collect(),
    )
    .map_err(|e| e.into())
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let levels_arg: Option<Vec<String>> = args.log_levels;

    let log_levels: Vec<(&str, simplelog::LevelFilter)> = {
        let mut log_levels = std::collections::BTreeMap::from([
            ("prospero", simplelog::LevelFilter::Debug),
            // If compiled via Bazel, "neutronstar" binary crate module will be named "bin"
            //("bin", simplelog::LevelFilter::Debug),
        ]);

        for (module, level) in levels_arg
            .as_deref()
            .map(as_level_pairs)
            .unwrap_or(Ok(vec![]))
            .context("Log level override parsing failed")?
        {
            log_levels.insert(module, level);
        }
        log_levels.into_iter().collect()
    };
    let _ = initialize_logging(&log_levels[..]);

    match args.command {
        Command::Haiku(options) => haiku(&options).await?,
        Command::Interpret(options) => interpet(&options).await?,
    }
    Ok(())
}
