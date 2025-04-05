use std::path;

pub mod egg;
pub mod interpreter;
pub mod parser;
mod utils;

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
