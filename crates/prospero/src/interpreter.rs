use crate::parser::{Instruction, ValueType};
use crate::utils::index_to_point;

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
