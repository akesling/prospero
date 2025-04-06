use std::path;

use anyhow::{anyhow, Context as _};
use itertools::Itertools as _;

pub mod egg;
pub mod interpreter;
pub mod parser;
mod utils;

pub async fn write_ppm(pixels: &[Vec<bool>], path: &path::Path) -> anyhow::Result<()> {
    use tokio::io::AsyncWriteExt as _;

    let mut file = tokio::fs::File::create(path).await?;
    file.write_all(&format!("P5\n{} {}\n255\n", pixels.len(), pixels[0].len()).into_bytes())
        .await?;
    // NOTE: PPM pixel data is column-major.
    for line in pixels.iter() {
        file.write_all(
            &line
                .iter()
                .map(|&p| if p { 255u8 } else { 0u8 })
                .collect::<Vec<u8>>(),
        )
        .await?;
    }
    Ok(())
}

pub async fn load_ppm(path: &path::Path) -> anyhow::Result<Vec<Vec<bool>>> {
    let ppm_contents: Vec<u8> = tokio::fs::read(path).await?;
    let mut line_offsets = ppm_contents
        .iter()
        .enumerate()
        .filter(|&(_, &b)| b == b'\n');
    let dims_start: usize = {
        let (dims_offset, _) = line_offsets
            .next()
            .ok_or(anyhow!("File didn't have line offset header"))?;
        dims_offset + 1
    };
    let (max_pix_value, _) = line_offsets.next().ok_or(anyhow!(
        "File didn't have the expected number of header lines"
    ))?;
    let body_start: usize = {
        let (body_offset, _) = line_offsets.next().ok_or(anyhow!(
            "File didn't have the expected number of header lines"
        ))?;
        body_offset + 1
    };

    let dims: Vec<usize> =
        String::from_utf8(Vec::from(&ppm_contents[dims_start..(max_pix_value - 1)]))
            .context("Dimensions header line was not utf8")?
            .trim()
            .split(' ')
            .map(|tok: &str| tok.parse::<usize>().context("Dimension failed to parse"))
            .collect::<anyhow::Result<Vec<usize>>>()?;

    let pixels: Vec<Vec<bool>> = ppm_contents[body_start..]
        .iter()
        .map(|&c| c == 255u8)
        .chunks(dims[0])
        .into_iter()
        .map(|chunk| chunk.collect())
        .collect();

    Ok(pixels)
}

#[cfg(test)]
mod test {
    use super::*;

    #[tokio::test]
    async fn ppm_write_load_eq() {
        let tmpfile = tempfile::NamedTempFile::new().unwrap();
        let contents = vec![
            vec![true, true, true, false],
            vec![false, false, true, false],
            vec![false, false, true, false],
            vec![false, false, true, true],
        ];
        write_ppm(&contents, tmpfile.path())
            .await
            .expect("Temp file failed to write successfully");

        let loaded = load_ppm(tmpfile.path())
            .await
            .expect("Temp file failed to load successfully");
        assert_eq!(contents, loaded);
    }
}
