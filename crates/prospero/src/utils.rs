use crate::parser::ValueType;

pub fn index_to_point(i: usize, span: ValueType) -> ValueType {
    ((i as ValueType) / span) * 2.0 - 1.0
}
